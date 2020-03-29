use crate::generate::src::{quote, Src};
use grammer::context::{Context, IRule, IStr};
use grammer::forest::NodeShape;
use grammer::rule::{Fields, MatchesEmpty, Rule, RuleWithFields, SepKind};
use grammer::{proc_macro, scannerless};

use indexmap::{indexmap, IndexMap, IndexSet};
use std::borrow::Cow;
use std::collections::BTreeSet;
use std::fmt::{self, Write as _};
use std::hash::Hash;
use std::ops::Add;
use std::rc::Rc;
use std::{iter, mem};

pub trait RustInputPat: Eq + Hash + fmt::Debug {
    fn rust_pat_ty() -> Src;
    fn rust_slice_ty() -> Src;
    fn rust_matcher(&self) -> Src;
}

impl<S: Eq + Hash + fmt::Debug + AsRef<str>> RustInputPat for scannerless::Pat<S> {
    fn rust_pat_ty() -> Src {
        quote!(gll::grammer::scannerless::Pat<&'static str>)
    }
    fn rust_slice_ty() -> Src {
        quote!(str)
    }
    fn rust_matcher(&self) -> Src {
        match self {
            scannerless::Pat::String(s) => Src::new(s.as_ref()),
            scannerless::Pat::Range(start, end) => quote!(#start..=#end),
        }
    }
}

impl RustInputPat for proc_macro::Pat {
    fn rust_pat_ty() -> Src {
        quote!(
            gll::grammer::proc_macro::Pat<
                &'static [gll::grammer::proc_macro::FlatTokenPat<&'static str>],
            >
        )
    }
    fn rust_slice_ty() -> Src {
        quote!([gll::grammer::proc_macro::FlatToken])
    }
    fn rust_matcher(&self) -> Src {
        let pats_src = self.0.iter().map(|pat| pat.rust_matcher());
        quote!(&[#(#pats_src),*] as &[_])
    }
}

impl RustInputPat for proc_macro::FlatTokenPat<String> {
    fn rust_pat_ty() -> Src {
        quote!(gll::grammer::proc_macro::FlatTokenPat<&'static str>)
    }
    fn rust_slice_ty() -> Src {
        quote!([gll::grammer::proc_macro::FlatToken])
    }
    fn rust_matcher(&self) -> Src {
        let variant = match self {
            proc_macro::FlatTokenPat::Delim(c) => quote!(Delim(#c)),
            proc_macro::FlatTokenPat::Ident(s) => {
                let s = s
                    .as_ref()
                    .map_or_else(|| quote!(None), |x| quote!(Some(#x)));
                quote!(Ident(#s))
            }
            proc_macro::FlatTokenPat::Punct { ch, joint } => {
                let ch = ch.map_or_else(|| quote!(None), |x| quote!(Some(#x)));
                let joint = joint.map_or_else(|| quote!(None), |x| quote!(Some(#x)));
                quote!(Punct { ch: #ch, joint: #joint })
            }
            proc_macro::FlatTokenPat::Literal => quote!(Literal),
        };
        quote!(gll::grammer::proc_macro::FlatTokenPat::#variant)
    }
}

struct RuleMap<'a> {
    named: &'a IndexMap<IStr, RuleWithFields>,
    anon: IndexSet<IRule>,
}

struct RustField {
    ty: Src,

    /// Whether the field might not always be present, i.e. whether it's wrapped
    /// in `Option<...>` (this is not encoded in `ty` to avoid repeated wrapping).
    refutable: bool,
}

impl RustField {
    fn handle_ty(&self) -> Src {
        let ty = &self.ty;
        let handle_ty = quote!(Handle<'a, 'i, I, #ty>);
        if self.refutable {
            quote!(Option<#handle_ty>)
        } else {
            handle_ty
        }
    }
}

type RustFields = IndexMap<IStr, RustField>;

enum RustVariant {
    // `Foo:X`, the whole top-level field is wrapped `Foo(X)`.
    Newtype(RustField),

    // `Bar:{ x:X y:Y }`, subfields are extracted into `Bar { x: X, y: Y }`.
    StructLike(RustFields),
}

enum RustAdt {
    Struct(RustFields),
    Enum(IndexMap<IStr, (RuleWithFields, RustVariant)>),
}

trait RuleWithFieldsMethods<Pat> {
    fn rust_fields(self, cx: &Context<Pat>, records: &mut BTreeSet<Vec<String>>) -> RustFields;
    fn rust_adt(self, cx: &Context<Pat>, records: &mut BTreeSet<Vec<String>>) -> RustAdt;
    fn traverse_shape(self, cx: &Context<Pat>, rust_fields: &RustFields) -> Src;
}

impl<Pat: RustInputPat> RuleWithFieldsMethods<Pat> for RuleWithFields {
    fn rust_fields(self, cx: &Context<Pat>, records: &mut BTreeSet<Vec<String>>) -> RustFields {
        let children = match &cx[self.fields] {
            Fields::Leaf(None) => return indexmap! {},
            Fields::Leaf(Some(field)) => {
                let mut sub = RuleWithFields {
                    rule: self.rule,
                    fields: field.sub,
                };

                let refutable = match cx[sub.rule] {
                    Rule::Opt(child) => match &cx[sub.fields] {
                        // `x:{ y:Y? }`
                        Fields::Leaf(Some(_)) => false,

                        // `x:X?`
                        Fields::Leaf(None) => {
                            sub.rule = child;
                            true
                        }

                        // `x:{ y:Y z:Z }?`
                        Fields::Aggregate(children) => {
                            sub.rule = child;
                            sub.fields = children[0];
                            true
                        }
                    },
                    _ => false,
                };

                let repeat = match cx[sub.rule] {
                    Rule::RepeatMany(elem, _) | Rule::RepeatMore(elem, _) => {
                        match &cx[sub.fields] {
                            // `xs:{ ys:Y* }`
                            Fields::Leaf(Some(_)) => false,

                            // `xs:X*`
                            Fields::Leaf(None) => {
                                sub.rule = elem;
                                true
                            }

                            // `xs:{ y:Y z:Z }*`
                            Fields::Aggregate(children) => {
                                sub.rule = elem;
                                sub.fields = children[0];
                                true
                            }
                        }
                    }
                    _ => false,
                };

                let subfields = sub.rust_fields(cx, records);
                let ty = if !subfields.is_empty() {
                    let rec_fields_name: Vec<_> =
                        subfields.keys().map(|&name| cx[name].to_string()).collect();
                    let rec_ident = Src::ident(&(rec_fields_name.join("__") + "__"));
                    let rec_fields_handle_ty = subfields.values().map(|field| field.handle_ty());
                    let shape = sub.traverse_shape(cx, &subfields);

                    records.insert(rec_fields_name);

                    quote!(_forest::typed::WithShape<
                        _rec::#rec_ident<#(#rec_fields_handle_ty),*>,
                        _forest::typed::shape!(#shape),
                        [usize; <_forest::typed::shape!(#shape) as _forest::typed::Shape>::STATE_LEN],
                    >)
                } else {
                    match cx[sub.rule] {
                        Rule::Call(r) => {
                            let ident = Src::ident(&cx[r]);
                            quote!(#ident<'a, 'i, I>)
                        }
                        _ => quote!(()),
                    }
                };

                return indexmap! {
                    field.name => RustField {
                        ty: if repeat { quote!([#ty]) } else { ty },
                        refutable,
                    },
                };
            }
            Fields::Aggregate(children) => children,
        };
        let mut child_fields = |rule, i| {
            let child = RuleWithFields {
                rule,
                fields: children
                    .get(i)
                    .cloned()
                    .unwrap_or_else(|| cx.intern(Fields::Leaf(None))),
            };
            child.rust_fields(cx, records)
        };

        match cx[self.rule] {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::Call(_)
            | Rule::RepeatMany(..)
            | Rule::RepeatMore(..) => unreachable!(),
            Rule::Concat([left, right]) => {
                let mut fields = child_fields(left, 0);
                for (name, field) in child_fields(right, 1) {
                    assert!(!fields.contains_key(&name), "duplicate field {}", &cx[name]);
                    fields.insert(name, field);
                }
                fields
            }
            Rule::Or(ref cases) => {
                let mut child_fields = |i| {
                    let mut fields = child_fields(cases[i], i);
                    for field in fields.values_mut() {
                        field.refutable = true;
                    }
                    fields
                };
                let mut fields = child_fields(0);
                for i in 1..cases.len() {
                    for (name, field) in child_fields(i) {
                        use indexmap::map::Entry;

                        match fields.entry(name) {
                            Entry::Occupied(entry) => {
                                let entry = entry.into_mut();

                                // HACK(eddyb) find a way to compare `Src` w/o
                                // printing (`to_ugly_string`).
                                if field.ty.to_ugly_string() != entry.ty.to_ugly_string() {
                                    entry.ty = quote!(());
                                }
                            }
                            Entry::Vacant(entry) => {
                                entry.insert(field);
                            }
                        }
                    }
                }
                fields
            }
            Rule::Opt(rule) => {
                let mut fields = child_fields(rule, 0);
                for field in fields.values_mut() {
                    field.refutable = true;
                }
                fields
            }
        }
    }

    fn rust_adt(self, cx: &Context<Pat>, records: &mut BTreeSet<Vec<String>>) -> RustAdt {
        match (&cx[self.rule], &cx[self.fields]) {
            (Rule::Or(cases), Fields::Aggregate(children)) => {
                let variants: Option<IndexMap<_, _>> = cases
                    .iter()
                    .enumerate()
                    .map(|(i, &rule)| match cx[children[i]] {
                        Fields::Leaf(Some(field)) => {
                            let child = RuleWithFields {
                                rule,
                                fields: field.sub,
                            };
                            let subfields = child.rust_fields(cx, records);
                            let variant = if subfields.is_empty() {
                                let variant = RuleWithFields {
                                    rule,
                                    fields: children[i],
                                };
                                let variant_fields = variant.rust_fields(cx, records);
                                assert_eq!(variant_fields.len(), 1);
                                RustVariant::Newtype(variant_fields.into_iter().next().unwrap().1)
                            } else {
                                RustVariant::StructLike(subfields)
                            };
                            Some((field.name, (child, variant)))
                        }
                        _ => None,
                    })
                    .collect();

                if let Some(variants) = variants {
                    // Make sure no name collision happened between variants.
                    if variants.len() == cases.len() {
                        return RustAdt::Enum(variants);
                    }
                }
            }
            _ => {}
        }

        RustAdt::Struct(self.rust_fields(cx, records))
    }

    fn traverse_shape(self, cx: &Context<Pat>, rust_fields: &RustFields) -> Src {
        let children = match &cx[self.fields] {
            Fields::Leaf(None) => return quote!(_),
            Fields::Leaf(Some(field)) => {
                let (i, _, rust_field) = rust_fields.get_full(&field.name).unwrap();

                // HACK(eddyb) account for the fact that `x:X?` is `x:{X?}`.
                let shape = quote!(#i);
                if let Rule::Opt(_) = cx[self.rule] {
                    if rust_field.refutable {
                        return quote!([#shape]);
                    }
                }
                return shape;
            }
            Fields::Aggregate(children) => children,
        };
        let child = |rule, i| RuleWithFields {
            rule,
            fields: children
                .get(i)
                .cloned()
                .unwrap_or_else(|| cx.intern(Fields::Leaf(None))),
        };

        match cx[self.rule] {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::Call(_)
            | Rule::RepeatMany(..)
            | Rule::RepeatMore(..) => unreachable!(),
            Rule::Concat([left, right]) => {
                let left = child(left, 0).traverse_shape(cx, rust_fields);
                let right = child(right, 1).traverse_shape(cx, rust_fields);
                quote!((#left #right))
            }
            Rule::Or(ref cases) => {
                let cases_shape = cases
                    .iter()
                    .enumerate()
                    .map(|(i, &rule)| child(rule, i).traverse_shape(cx, rust_fields));
                quote!({ _ @ #(#cases_shape)* })
            }
            Rule::Opt(rule) => {
                let shape = child(rule, 0).traverse_shape(cx, rust_fields);
                quote!([#shape])
            }
        }
    }
}

trait RuleMethods<Pat>: Sized {
    fn node_kind(self, cx: &Context<Pat>, rules: &mut RuleMap<'_>) -> NodeKind;
}

impl<Pat: RustInputPat> RuleMethods<Pat> for IRule {
    fn node_kind(self, cx: &Context<Pat>, rules: &mut RuleMap<'_>) -> NodeKind {
        if let Rule::Call(r) = cx[self] {
            return NodeKind::NamedRule(cx[r].to_string());
        }

        if let Some((i, _)) = rules.anon.get_full(&self) {
            return NodeKind::Anon(i);
        }
        let i = rules.anon.len();
        rules.anon.insert(self);
        NodeKind::Anon(i)
    }
}

#[derive(Clone)]
enum NodeKind {
    NamedRule(String),
    Anon(usize),
}

impl NodeKind {
    fn ident(&self) -> Src {
        match self {
            NodeKind::NamedRule(name) => Src::ident(name),
            NodeKind::Anon(i) => Src::ident(format!("_{}", i)),
        }
    }
}

impl NodeKind {
    fn to_src(&self) -> Src {
        let ident = self.ident();
        quote!(_P::#ident)
    }
}

trait NodeShapeMethods<Pat>: Sized {
    fn to_src(&self, cx: &Context<Pat>, rules: &mut RuleMap<'_>) -> Src;
}

impl<Pat: RustInputPat> NodeShapeMethods<Pat> for NodeShape<IRule> {
    fn to_src(&self, cx: &Context<Pat>, rules: &mut RuleMap<'_>) -> Src {
        let shape = self.map(|rule| rule.node_kind(cx, rules).to_src());
        let variant = match shape {
            NodeShape::Opaque => quote!(Opaque),
            NodeShape::Alias(inner) => quote!(Alias(#inner)),
            NodeShape::Choice(count) => quote!(Choice(#count)),
            NodeShape::Opt(inner) => quote!(Opt(#inner)),
            NodeShape::Split(left, right) => quote!(Split(#left, #right)),
        };
        quote!(NodeShape::#variant)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum CodeLabel {
    NamedRule(String),
    Nested { parent: Rc<CodeLabel>, i: usize },
}

impl CodeLabel {
    fn flattened_name(&self) -> Cow<'_, str> {
        match self {
            CodeLabel::NamedRule(r) => r.into(),
            CodeLabel::Nested { parent, i } => {
                let mut name = parent.flattened_name().into_owned();
                name += "__";
                let _ = write!(name, "{}", i);
                name.into()
            }
        }
    }

    fn flattened_ident(&self) -> Src {
        Src::ident(self.flattened_name())
    }
}

impl CodeLabel {
    fn to_src(&self) -> Src {
        let ident = self.flattened_ident();
        quote!(_C::#ident)
    }
}

// FIXME(eddyb) this is a bit pointless, as it's exported as a free function.
trait GrammarGenerateMethods<Pat> {
    fn generate_rust(&self, cx: &Context<Pat>) -> Src;
}

pub fn generate<Pat: MatchesEmpty + RustInputPat>(cx: &Context<Pat>, g: &grammer::Grammar) -> Src {
    g.generate_rust(cx)
}

impl<Pat: MatchesEmpty + RustInputPat> GrammarGenerateMethods<Pat> for grammer::Grammar {
    fn generate_rust(&self, cx: &Context<Pat>) -> Src {
        self.check(cx);

        let mut rules = RuleMap {
            named: &self.rules,
            anon: IndexSet::new(),
        };

        let mut out = concat!(
            include_str!("templates/imports.rs"),
            include_str!("templates/header.rs")
        )
        .parse::<Src>()
        .unwrap();

        let mut records = BTreeSet::new();

        for (&name, &rule) in rules.named {
            let rust_adt = rule.rust_adt(cx, &mut records);
            out += declare_rule(name, rule, &rust_adt, cx, &mut rules) + impl_parse_with(cx, name);
        }

        let records = records.into_iter().map(|fields| {
            let ident = Src::ident(&(fields.join("__") + "__"));
            // FIXME(eddyb) figure out a more efficient way to reuse
            // iterators with `quote!(...)` than `.collect::<Vec<_>>()`.
            let f_ident = fields.iter().map(Src::ident).collect::<Vec<_>>();
            let f_len = fields.len();

            quote!(
                #[derive(Copy, Clone)]
                pub struct #ident<#(#f_ident),*> {
                    #(pub #f_ident: #f_ident),*
                }

                impl<#(#f_ident),*> fmt::Debug for #ident<#(#f_ident),*>
                where
                    #(#f_ident: fmt::Debug),*
                {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.debug_map()
                            #(.entry(&FieldName(stringify!(#f_ident)), &self.#f_ident))*
                            .finish()
                    }
                }

                impl<'a, 'i, I, #(#f_ident),*> _forest::typed::FromShapeFields<'a, 'i, _G, I> for #ident<#(#f_ident),*>
                where
                    I: gll::grammer::input::Input,
                    #(#f_ident: _forest::typed::FromShapeFields<'a, 'i, _G, I, Fields = [Option<Node<'i, _G>>; 1]>),*
                {
                    type Output = #ident<#(#f_ident::Output),*>;
                    type Fields = [Option<Node<'i, _G>>; #f_len];

                    fn from_shape_fields(
                        forest: &'a _forest::ParseForest<'i, _G, I>,
                        [#(#f_ident),*]: <Self as _forest::typed::FromShapeFields<'a, 'i, _G, I>>::Fields,
                    ) -> Self::Output {
                        #ident {
                            #(#f_ident: #f_ident::from_shape_fields(forest, [#f_ident])),*
                        }
                    }
                }
            )
        });
        out += quote!(pub mod _rec {
            use super::{_forest, _G, Node};
            use std::fmt;

            // FIXME(eddyb) move this somewhere else.
            struct FieldName<'a>(&'a str);
            impl fmt::Debug for FieldName<'_> {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    f.write_str(self.0)
                }
            }

            #(#records)*
        });

        let mut code_labels = IndexMap::new();
        out += define_parse_fn(cx, &mut rules, &mut code_labels);

        // HACK(eddyb) these two loops use `rule.node_kind(cx, &mut rules)`
        // to fill `rules.anon` with all the non-`Rule::Call` rules being used.
        // FIXME(eddyb) maybe just rely on the interner? would that contain trash?
        for &name in rules.named.keys() {
            cx.intern(Rule::Call(name))
                .node_shape(cx, Some(rules.named))
                .map(|rule| rule.node_kind(cx, &mut rules));
        }

        let mut i = 0;
        while i < rules.anon.len() {
            let rule = *rules.anon.get_index(i).unwrap();
            rule.node_shape(cx, Some(rules.named))
                .map(|rule| rule.node_kind(cx, &mut rules));
            // HACK(eddyb) this is needed because `NodeShape` doesn't
            // encode `Choice` cases directly, only their count.
            if let Rule::Or(cases) = &cx[rule] {
                for &rule in cases {
                    rule.node_kind(cx, &mut rules);
                }
            }
            i += 1;
        }

        // FIXME(eddyb) get rid of this? how? (see comment before the loops above)
        let all_rules: Vec<_> = rules
            .named
            .keys()
            .map(|&name| cx.intern(Rule::Call(name)))
            .chain(rules.anon.iter().cloned())
            .collect();

        out + declare_node_kind(cx, &mut rules, &all_rules)
            + impl_debug_for_handle_any(cx, &mut rules, &all_rules)
            + code_label_decl_and_impls(cx, &mut rules, &code_labels)
    }
}

#[must_use]
struct Continuation<'a, 'r, Pat> {
    cx: &'a Context<Pat>,
    rules: Option<&'a mut RuleMap<'r>>,
    code_labels: &'a mut IndexMap<Rc<CodeLabel>, usize>,
    fn_code_label: &'a mut Rc<CodeLabel>,
    code_label_arms: &'a mut Vec<Src>,
    code: Code,
    nested_frames: Vec<Option<(Rc<CodeLabel>, Rc<CodeLabel>)>>,
}

#[derive(Clone)]
enum Code {
    Inline(Src),
    Label(Rc<CodeLabel>),
}

impl<'r, Pat> Continuation<'_, 'r, Pat> {
    fn next_code_label(&mut self) -> Rc<CodeLabel> {
        let counter = self
            .code_labels
            .entry(self.fn_code_label.clone())
            .or_insert(0);
        let label = Rc::new(CodeLabel::Nested {
            parent: self.fn_code_label.clone(),
            i: *counter,
        });
        *counter += 1;
        label
    }

    fn clone(&mut self) -> Continuation<'_, 'r, Pat> {
        Continuation {
            cx: self.cx,
            rules: self.rules.as_mut().map(|rules| &mut **rules),
            code_labels: self.code_labels,
            fn_code_label: self.fn_code_label,
            code_label_arms: self.code_label_arms,
            code: self.code.clone(),
            nested_frames: self.nested_frames.clone(),
        }
    }

    fn to_inline(&mut self) -> &mut Src {
        if let Code::Label(ref label) = self.code {
            let label_src = label.to_src();
            self.code = Code::Inline(quote!(
                rt.spawn(#label_src);
            ));
        }

        match self.code {
            Code::Inline(ref mut code) => code,
            Code::Label(_) => unreachable!(),
        }
    }

    fn to_label(&mut self) -> &mut Rc<CodeLabel> {
        match self.code {
            Code::Label(ref mut label) => label,
            Code::Inline(_) => {
                let label = self.next_code_label();
                self.reify_as(label);
                self.to_label()
            }
        }
    }

    fn reify_as(&mut self, label: Rc<CodeLabel>) {
        let code = self.to_inline();
        let label_src = label.to_src();
        let code = quote!(#label_src => {#code});
        self.code_label_arms.push(code);
        self.code = Code::Label(label);
    }
}

trait ContFn<Pat> {
    fn apply<'a, 'r>(self, cont: Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat>;
}

impl<Pat, F> ContFn<Pat> for F
where
    F: for<'a, 'r> FnOnce(Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat>,
{
    fn apply<'a, 'r>(self, cont: Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat> {
        self(cont)
    }
}

struct Compose<F, G>(F, G);

impl<Pat, F: ContFn<Pat>, G: ContFn<Pat>> ContFn<Pat> for Compose<F, G> {
    fn apply<'a, 'r>(self, cont: Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat> {
        self.1.apply(self.0.apply(cont))
    }
}

#[must_use]
struct Thunk<F>(F);

impl<F> Thunk<F> {
    fn new<Pat>(f: F) -> Self
    where
        F: for<'a, 'r> FnOnce(Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat>,
    {
        Thunk(f)
    }
}

impl<F, G> Add<Thunk<G>> for Thunk<F> {
    type Output = Thunk<Compose<G, F>>;
    fn add(self, other: Thunk<G>) -> Self::Output {
        Thunk(Compose(other.0, self.0))
    }
}

impl<Pat, F: ContFn<Pat>> ContFn<Pat> for Thunk<F> {
    fn apply<'a, 'r>(self, cont: Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat> {
        self.0.apply(cont)
    }
}

macro_rules! thunk {
    ($($t:tt)*) => {{
        let prefix = quote!($($t)*);
        Thunk::new(move |mut cont| {
            let code = cont.to_inline();
            let suffix = mem::replace(code, prefix);
            *code += suffix;
            cont
        })
    }}
}

fn pop_saved<Pat, F: ContFn<Pat>>(f: impl FnOnce(Src) -> Thunk<F>) -> Thunk<impl ContFn<Pat>> {
    thunk!(let saved = rt.take_saved();)
        + f(quote!(saved))
        + Thunk::new(|mut cont| {
            if let Some(&None) = cont.nested_frames.last() {
                *cont.nested_frames.last_mut().unwrap() =
                    Some((cont.to_label().clone(), cont.fn_code_label.clone()));
                *cont.fn_code_label = cont.next_code_label();
                cont.code_labels.insert(cont.fn_code_label.clone(), 0);
                cont.code = Code::Inline(quote!());
                cont = ret().apply(cont);
            }
            cont.nested_frames.push(None);
            cont
        })
}

fn push_saved<Pat: RustInputPat>(rule: IRule) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(move |mut cont| {
        let rules = cont.rules.as_mut().unwrap();
        let node_kind_src = rule.node_kind(cont.cx, rules).to_src();
        thunk!(rt.save(#node_kind_src);).apply(cont)
    }) + Thunk::new(move |mut cont| {
        if let Some((ret_label, outer_fn_label)) = cont.nested_frames.pop().unwrap() {
            let inner_fn_label = mem::replace(cont.fn_code_label, outer_fn_label);
            cont.reify_as(inner_fn_label);
            cont = call(mem::replace(cont.to_label(), ret_label)).apply(cont);
        }
        cont
    })
}

fn check<Pat>(condition: Src) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(move |mut cont| {
        let code = cont.to_inline();
        *code = quote!(
            if #condition {
                #code
            }
        );
        cont
    })
}

fn call<Pat>(callee: Rc<CodeLabel>) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(move |mut cont| {
        let label = cont.to_label().clone();
        let callee_src = callee.to_src();
        let label_src = label.to_src();
        cont.code = Code::Inline(quote!(
            rt.call(#callee_src, #label_src);
        ));
        cont
    })
}

fn ret<Pat>() -> Thunk<impl ContFn<Pat>> {
    thunk!(rt.ret();)
        + Thunk::new(|mut cont| {
            assert!(cont.to_inline().is_empty());
            cont
        })
}

trait ForEachThunk<Pat> {
    fn for_each_thunk(
        self,
        cont: &mut Continuation<'_, '_, Pat>,
        f: impl FnMut(Continuation<'_, '_, Pat>),
    );
}

impl<Pat, F> ForEachThunk<Pat> for Thunk<F>
where
    F: ContFn<Pat>,
{
    fn for_each_thunk(
        self,
        cont: &mut Continuation<'_, '_, Pat>,
        mut f: impl FnMut(Continuation<'_, '_, Pat>),
    ) {
        f(self.apply(cont.clone()));
    }
}

impl<Pat, T, U> ForEachThunk<Pat> for (T, U)
where
    T: ForEachThunk<Pat>,
    U: ForEachThunk<Pat>,
{
    fn for_each_thunk(
        self,
        cont: &mut Continuation<'_, '_, Pat>,
        mut f: impl FnMut(Continuation<'_, '_, Pat>),
    ) {
        self.0.for_each_thunk(cont, &mut f);
        self.1.for_each_thunk(cont, &mut f);
    }
}

struct ThunkIter<I>(I);

impl<Pat, I, T> ForEachThunk<Pat> for ThunkIter<I>
where
    I: Iterator<Item = T>,
    T: ForEachThunk<Pat>,
{
    fn for_each_thunk(
        self,
        cont: &mut Continuation<'_, '_, Pat>,
        mut f: impl FnMut(Continuation<'_, '_, Pat>),
    ) {
        self.0.for_each(|x| {
            x.for_each_thunk(cont, &mut f);
        });
    }
}

fn parallel<Pat>(thunks: impl ForEachThunk<Pat>) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(|mut cont| {
        cont.to_label();
        let mut code = quote!();
        let mut child_nested_frames = None;
        let nested_frames = cont.nested_frames.clone();
        thunks.for_each_thunk(&mut cont, |mut child_cont| {
            if let Some(prev) = child_nested_frames {
                assert_eq!(child_cont.nested_frames.len(), prev);
            } else {
                child_nested_frames = Some(child_cont.nested_frames.len());
            }
            if let Some(Some((ret_label, outer_fn_label))) =
                child_cont.nested_frames.last().cloned()
            {
                if let None = nested_frames[child_cont.nested_frames.len() - 1] {
                    let inner_fn_label = mem::replace(child_cont.fn_code_label, outer_fn_label);
                    child_cont.reify_as(inner_fn_label);
                    child_cont =
                        call(mem::replace(child_cont.to_label(), ret_label)).apply(child_cont);
                    *child_cont.nested_frames.last_mut().unwrap() = None;
                }
            }
            assert_eq!(
                child_cont.nested_frames[..],
                nested_frames[..child_cont.nested_frames.len()]
            );
            code += child_cont.to_inline().clone();
        });
        cont.code = Code::Inline(code);
        if let Some(child_nested_frames) = child_nested_frames {
            while cont.nested_frames.len() > child_nested_frames {
                assert_eq!(cont.nested_frames.pop(), Some(None));
            }
        }
        cont
    })
}

fn opt<Pat>(thunk: Thunk<impl ContFn<Pat>>) -> Thunk<impl ContFn<Pat>> {
    parallel((thunk, thunk!()))
}

fn fix<Pat, F: ContFn<Pat>>(f: impl FnOnce(Rc<CodeLabel>) -> Thunk<F>) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(|mut cont| {
        let nested_frames = mem::replace(&mut cont.nested_frames, vec![]);
        let ret_label = cont.to_label().clone();
        cont.code = Code::Inline(quote!());
        let label = cont.next_code_label();
        let outer_fn_label = mem::replace(cont.fn_code_label, label.clone());
        cont.code_labels.insert(label.clone(), 0);

        cont = (reify_as(label.clone()) + f(label) + ret()).apply(cont);

        *cont.fn_code_label = outer_fn_label;
        cont.nested_frames = nested_frames;
        cont = call(mem::replace(cont.to_label(), ret_label)).apply(cont);
        cont
    })
}

fn reify_as<Pat>(label: Rc<CodeLabel>) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(|mut cont| {
        cont.reify_as(label);
        cont
    })
}

fn forest_add_choice<Pat: RustInputPat>(rule: IRule, choice: usize) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(move |mut cont| {
        if let Some(rules) = &mut cont.rules.as_mut() {
            let node_kind_src = rule.node_kind(cont.cx, rules).to_src();
            cont = thunk!(rt.forest_add_choice(#node_kind_src, #choice);).apply(cont);
        }
        cont
    })
}

fn concat_and_forest_add<Pat: RustInputPat>(
    rule: IRule,
    left: IRule,
    right: Thunk<impl ContFn<Pat>>,
) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(move |mut cont| {
        if let Some(rules) = cont.rules.as_mut() {
            let node_kind_src = rule.node_kind(cont.cx, rules).to_src();
            (left.generate_parse()
                + push_saved(left)
                + right
                + pop_saved(move |saved| {
                    thunk!(rt.forest_add_split(
                    #node_kind_src,
                    #saved,
                );)
                }))
            .apply(cont)
        } else {
            (left.generate_parse() + right).apply(cont)
        }
    })
}

trait RuleGenerateMethods<Pat> {
    fn generate_parse(
        self,
    ) -> Thunk<Box<dyn for<'a, 'r> FnOnce(Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat>>>;
}

impl<Pat: RustInputPat> RuleGenerateMethods<Pat> for IRule {
    fn generate_parse(
        self,
    ) -> Thunk<Box<dyn for<'a, 'r> FnOnce(Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat>>>
    {
        Thunk::new(Box::new(
            move |cont: Continuation<'_, '_, Pat>| match cont.cx[self] {
                Rule::Empty => cont,
                Rule::Eat(ref pat) => {
                    let pat = pat.rust_matcher();
                    check(quote!(let Some(mut rt) = rt.input_consume_left(#pat))).apply(cont)
                }
                Rule::Call(r) => {
                    call(Rc::new(CodeLabel::NamedRule(cont.cx[r].to_string()))).apply(cont)
                }
                Rule::Concat([left, right]) => {
                    concat_and_forest_add(self, left, right.generate_parse()).apply(cont)
                }
                Rule::Or(ref cases) => {
                    parallel(ThunkIter(cases.iter().enumerate().map(|(i, &rule)| {
                        rule.generate_parse() + forest_add_choice(self, i)
                    })))
                    .apply(cont)
                }
                Rule::Opt(rule) => opt(rule.generate_parse()).apply(cont),
                Rule::RepeatMany(elem, None) => {
                    let more = cont.cx.intern(Rule::RepeatMore(elem, None));
                    fix(|label| opt(concat_and_forest_add(more, elem, call(label)))).apply(cont)
                }
                Rule::RepeatMany(elem, Some(sep)) => opt(cont
                    .cx
                    .intern(Rule::RepeatMore(elem, Some(sep)))
                    .generate_parse())
                .apply(cont),
                Rule::RepeatMore(elem, None) => {
                    fix(|label| concat_and_forest_add(self, elem, opt(call(label)))).apply(cont)
                }
                Rule::RepeatMore(elem, Some((sep, SepKind::Simple))) => {
                    let tail = cont.cx.intern(Rule::Concat([sep, self]));
                    fix(|label| {
                        concat_and_forest_add(
                            self,
                            elem,
                            opt(concat_and_forest_add(tail, sep, call(label))),
                        )
                    })
                    .apply(cont)
                }
                Rule::RepeatMore(elem, Some((sep, SepKind::Trailing))) => {
                    let tail = cont.cx.intern(Rule::Concat([
                        sep,
                        cont.cx
                            .intern(Rule::RepeatMany(elem, Some((sep, SepKind::Trailing)))),
                    ]));
                    fix(|label| {
                        concat_and_forest_add(
                            self,
                            elem,
                            opt(concat_and_forest_add(
                                tail,
                                sep,
                                // FIXME(eddyb) this would imply `RepeatMany` w/ `SepKind::Trailing`
                                // could be optimized slightly.
                                opt(call(label)),
                            )),
                        )
                    })
                    .apply(cont)
                }
            },
        ))
    }
}

fn impl_parse_with<Pat>(cx: &Context<Pat>, name: IStr) -> Src
where
    Pat: RustInputPat,
{
    let ident = Src::ident(&cx[name]);
    let code_label = Rc::new(CodeLabel::NamedRule(cx[name].to_string()));
    let code_label_src = code_label.to_src();
    let node_kind = NodeKind::NamedRule(cx[name].to_string());
    let node_kind_src = node_kind.to_src();
    let rust_pat_ty = Pat::rust_pat_ty();
    let rust_slice_ty = Pat::rust_slice_ty();
    quote!(
        impl<I> #ident<'_, '_, I>
            where I: gll::grammer::input::Input<Slice = #rust_slice_ty>,
        {
            pub fn parse(input: I)
                -> Result<
                    OwnedHandle<I, Self>,
                    gll::grammer::parser::ParseError<I::SourceInfoPoint, #rust_pat_ty>,
                >
            {
                gll::runtime::Runtime::parse(
                    _G,
                    input,
                    #code_label_src,
                    #node_kind_src,
                ).map(|forest_and_node| OwnedHandle {
                    forest_and_node,
                    _marker: PhantomData,
                })
            }
        }

        // FIXME(eddyb) these two impls cannot be easily implemented by a trait
        // because of how `Handle<'a, 'i, I, X<'a, 'i, I>>` links together the
        // lifetime parameters of `Handle` and those of `X`.
        impl<I: gll::grammer::input::Input> OwnedHandle<I, #ident<'_, '_, I>> {
            pub fn with<R>(&self, f: impl for<'a, 'i> FnOnce(Handle<'a, 'i, I, #ident<'a, 'i, I>>) -> R) -> R {
                self.forest_and_node.unpack_ref(|_, forest_and_node| {
                    let (ref forest, node) = *forest_and_node;
                    f(Handle {
                        node,
                        forest,
                        _marker: PhantomData,
                    })
                })
            }
        }

        impl<I: gll::grammer::input::Input> fmt::Debug for OwnedHandle<I, #ident<'_, '_, I>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.with(|handle| handle.fmt(f))
            }
        }
    )
}

fn declare_rule<Pat>(
    name: IStr,
    rule: RuleWithFields,
    rust_adt: &RustAdt,
    cx: &Context<Pat>,
    rules: &mut RuleMap<'_>,
) -> Src
where
    Pat: RustInputPat,
{
    let ident = Src::ident(&cx[name]);

    let rule_ty_def = match rust_adt {
        RustAdt::Enum(variants) => {
            let variants = variants.iter().map(|(&v_name, (_, variant))| {
                let variant_ident = Src::ident(&cx[v_name]);
                match variant {
                    RustVariant::Newtype(field) => {
                        let field_ty = field.handle_ty();
                        quote!(#variant_ident(#field_ty))
                    }
                    RustVariant::StructLike(v_fields) => {
                        let fields_ident = v_fields.keys().map(|&name| Src::ident(&cx[name]));
                        let fields_handle_ty = v_fields.values().map(|field| field.handle_ty());
                        quote!(#variant_ident {
                            #(#fields_ident: #fields_handle_ty),*
                        })
                    }
                }
            });
            quote!(
                #[allow(non_camel_case_types)]
                pub enum #ident<'a, 'i, I: gll::grammer::input::Input> {
                    #(#variants),*
                }
            )
        }
        RustAdt::Struct(fields) => {
            let fields_ident = fields.keys().map(|&name| Src::ident(&cx[name]));
            let fields_handle_ty = fields.values().map(|field| field.handle_ty());
            let marker_field = if fields.is_empty() {
                Some(quote!(_marker: PhantomData<(&'a (), &'i (), I)>,))
            } else {
                None
            };
            quote!(
                #[allow(non_camel_case_types)]
                pub struct #ident<'a, 'i, I: gll::grammer::input::Input> {
                    #(pub #fields_ident: #fields_handle_ty),*
                    #marker_field
                }
            )
        }
    };
    rule_ty_def
        + rule_debug_impl(cx, name, rust_adt)
        + impl_rule_traverse_impl(name, rule, rust_adt, cx, rules)
}

fn impl_rule_traverse_impl<Pat>(
    name: IStr,
    rule: RuleWithFields,
    rust_adt: &RustAdt,
    cx: &Context<Pat>,
    rules: &mut RuleMap<'_>,
) -> Src
where
    Pat: RustInputPat,
{
    let ident = Src::ident(&cx[name]);
    let field_handle_expr = |(i, field): (usize, &RustField)| {
        if field.refutable {
            quote!(Option::<Handle<'a, 'i, I, _>>::from_shape_fields(forest, [fields[#i]]))
        } else {
            quote!(Handle::from_shape_fields(forest, [fields[#i]]))
        }
    };

    let (total_fields, shape, from_shape) = match rust_adt {
        RustAdt::Enum(variants) => {
            let max_fields_len = variants
                .values()
                .map(|(_, variant)| match variant {
                    RustVariant::Newtype(_) => 0,
                    RustVariant::StructLike(v_fields) => v_fields.len(),
                })
                .max()
                .unwrap_or(0);
            // HACK(eddyb) only collected to a `Vec` to avoid `rules` borrow conflicts.
            let variants_kind = variants
                .values()
                .map(|(v_rule, _)| v_rule.rule.node_kind(cx, rules))
                .collect::<Vec<_>>();
            let variants_kind_src = variants_kind
                .iter()
                .map(|kind| kind.to_src())
                .collect::<Vec<_>>();
            let variants_shape = variants
                .values()
                .map(|(v_rule, variant)| match variant {
                    RustVariant::Newtype(_) => quote!(_),
                    RustVariant::StructLike(v_fields) => v_rule.traverse_shape(cx, v_fields),
                })
                .collect::<Vec<_>>();
            let variants_expr = variants.iter().map(|(&v_name, (_, variant))| {
                let variant_ident = Src::ident(&cx[v_name]);
                match variant {
                    RustVariant::Newtype(_) => quote!(#ident::#variant_ident(
                        Handle::from_shape_fields(forest, [fields[#max_fields_len]]),
                    )),
                    RustVariant::StructLike(v_fields) => {
                        let fields_ident = v_fields.keys().map(|&name| Src::ident(&cx[name]));
                        let fields_expr = v_fields.values().enumerate().map(field_handle_expr);
                        quote!(#ident::#variant_ident {
                            #(#fields_ident: #fields_expr),*
                        })
                    }
                }
            });

            (
                max_fields_len + 1,
                quote!({ #max_fields_len @ #(#variants_shape)* }),
                quote!(
                    match fields[#max_fields_len].unwrap().kind {
                        #(#variants_kind_src => #variants_expr,)*
                        _ => unreachable!(),
                    }
                ),
            )
        }
        RustAdt::Struct(fields) => {
            let fields_ident = fields.keys().map(|&name| Src::ident(&cx[name]));
            let fields_expr = fields.values().enumerate().map(field_handle_expr);
            let marker_field = if fields.is_empty() {
                Some(quote!(_marker: { let _ = forest; let [] = fields; PhantomData },))
            } else {
                None
            };

            (
                fields.len(),
                rule.traverse_shape(cx, fields),
                quote!(
                    #ident {
                        #(#fields_ident: #fields_expr),*
                        #marker_field
                    }
                ),
            )
        }
    };

    quote!(
    impl<'i, I> _forest::typed::Shaped for #ident<'_, 'i, I>
        where I: gll::grammer::input::Input,
    {
        type Shape = _forest::typed::shape!(#shape);
        type State = [usize; <_forest::typed::shape!(#shape) as _forest::typed::Shape>::STATE_LEN];
    }
    impl<'a, 'i, I>
        _forest::typed::FromShapeFields<'a, 'i, _G, I>
            for #ident<'a, 'i, I>
        where I: gll::grammer::input::Input,
    {
        type Output = Self;
        type Fields = [Option<Node<'i, _G>>; #total_fields];

        fn from_shape_fields(
            forest: &'a _forest::ParseForest<'i, _G, I>,
            fields: <Self as _forest::typed::FromShapeFields<'a, 'i, _G, I>>::Fields,
        ) -> Self {
            #from_shape
        }
    }
    )
}

fn rule_debug_impl<Pat>(cx: &Context<Pat>, name: IStr, rust_adt: &RustAdt) -> Src {
    let name = &cx[name];
    let ident = Src::ident(name);
    let body = match rust_adt {
        RustAdt::Enum(variants) => {
            let variants_pat = variants.iter().map(|(&v_name, (_, variant))| {
                let variant_ident = Src::ident(&cx[v_name]);
                match variant {
                    RustVariant::Newtype(_) => quote!(#ident::#variant_ident(x)),
                    RustVariant::StructLike(v_fields) => {
                        let fields_ident = v_fields.keys().map(|&name| Src::ident(&cx[name]));
                        let fields_var_ident = v_fields
                            .keys()
                            .map(|&field_name| Src::ident(format!("f_{}", &cx[field_name])));
                        quote!(#ident::#variant_ident {
                            #(#fields_ident: #fields_var_ident,)*
                        })
                    }
                }
            });
            let variants_body = variants.iter().map(|(&v_name, (_, variant))| {
                let variant_path_str = format!("{}::{}", name, &cx[v_name]);
                match variant {
                    RustVariant::Newtype(_) => {
                        quote!(f.debug_tuple(#variant_path_str).field(x).finish(),)
                    }
                    RustVariant::StructLike(v_fields) => {
                        let fields_debug = v_fields.iter().map(|(field_name, field)| {
                            let field_name = &cx[*field_name];
                            let field_var_ident = Src::ident(format!("f_{}", field_name));
                            if field.refutable {
                                quote!(if let Some(field) = #field_var_ident {
                                    d.field(#field_name, field);
                                })
                            } else {
                                quote!(d.field(#field_name, #field_var_ident);)
                            }
                        });

                        quote!({
                            let mut d = f.debug_struct(#variant_path_str);
                            #(#fields_debug)*
                            d.finish()
                        })
                    }
                }
            });

            quote!(match self {
                #(#variants_pat => #variants_body)*
            })
        }
        RustAdt::Struct(fields) => {
            let fields_debug = fields.iter().map(|(&field_name, field)| {
                let field_name = &cx[field_name];
                let field_ident = Src::ident(field_name);
                if field.refutable {
                    quote!(if let Some(ref field) = self.#field_ident {
                       d.field(#field_name, field);
                    })
                } else {
                    quote!(d.field(#field_name, &self.#field_ident);)
                }
            });
            quote!(
                let mut d = f.debug_struct(#name);
                #(#fields_debug)*
                d.finish()
            )
        }
    };
    quote!(impl<I: gll::grammer::input::Input> fmt::Debug for #ident<'_, '_, I> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            #body
        }
    })
}

fn define_parse_fn<Pat>(
    cx: &Context<Pat>,
    rules: &mut RuleMap<'_>,
    code_labels: &mut IndexMap<Rc<CodeLabel>, usize>,
) -> Src
where
    Pat: RustInputPat,
{
    let mut code_label_arms = vec![];
    for (&name, rule) in rules.named {
        let code_label = Rc::new(CodeLabel::NamedRule(cx[name].to_string()));
        let rules = if cx[rule.fields] == Fields::Leaf(None) {
            None
        } else {
            Some(&mut *rules)
        };
        (rule.rule.generate_parse() + ret())
            .apply(Continuation {
                cx,
                rules,
                code_labels,
                fn_code_label: &mut code_label.clone(),
                code_label_arms: &mut code_label_arms,
                code: Code::Inline(quote!()),
                nested_frames: vec![],
            })
            .reify_as(code_label);
    }

    let rust_pat_ty = Pat::rust_pat_ty();
    let rust_slice_ty = Pat::rust_slice_ty();
    quote!(impl<I> gll::runtime::CodeStep<I, #rust_pat_ty> for _C
        where I: gll::grammer::input::Input<Slice = #rust_slice_ty>,
    {
        fn step<'i>(self, mut rt: gll::runtime::Runtime<'_, 'i, _C, I, #rust_pat_ty>) {
            match self {
                #(#code_label_arms)*
            }
        }
    })
}

fn declare_node_kind<Pat: RustInputPat>(
    cx: &Context<Pat>,
    rules: &mut RuleMap<'_>,
    all_rules: &[IRule],
) -> Src {
    // FIXME(eddyb) figure out a more efficient way to reuse
    // iterators with `quote!(...)` than `.collect::<Vec<_>>()`.
    let nodes_kind = all_rules
        .iter()
        .map(|rule| rule.node_kind(cx, rules))
        .collect::<Vec<_>>();
    let nodes_kind_src = nodes_kind
        .iter()
        .map(|kind| kind.to_src())
        .collect::<Vec<_>>();
    let nodes_kind_ident = nodes_kind.iter().map(|kind| kind.ident());
    // HACK(eddyb) only collected to a `Vec` to avoid `rules` borrow conflicts.
    let nodes_desc = all_rules.iter().map(|&rule| rule.node_desc(cx));
    let nodes_doc = nodes_desc
        .clone()
        .map(|desc| format!("`{}`", desc.replace('`', "\\`")));
    let nodes_shape_src = all_rules
        .iter()
        .map(|&rule| rule.node_shape(cx, Some(rules.named)).to_src(cx, rules))
        .collect::<Vec<_>>();
    let nodes_shape_choices = all_rules
        .iter()
        .map(|&rule| {
            let choices = match &cx[rule] {
                Rule::Or(choices) => &choices[..],
                _ => &[],
            };
            let choices = choices
                .iter()
                .map(|rule| rule.node_kind(cx, rules).to_src());
            quote!([#(#choices,)*])
        })
        .collect::<Vec<_>>();

    quote!(
        pub struct _G;

        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
        pub enum _P {
            #(
                #[doc = #nodes_doc]
                #nodes_kind_ident,
            )*
        }

        impl _forest::GrammarReflector for _G {
            type NodeKind = _P;

            fn node_shape(&self, kind: _P) -> NodeShape<_P> {
                match kind {
                    #(#nodes_kind_src => #nodes_shape_src),*
                }
            }
            fn node_shape_choice_get(&self, kind: _P, i: usize) -> _P {
                match kind {
                    #(#nodes_kind_src => #nodes_shape_choices[i]),*
                }
            }
            fn node_desc(&self, kind: _P) -> String {
                let s = match kind {
                    #(#nodes_kind_src => #nodes_desc),*
                };
                s.to_string()
            }
        }
    )
}

fn impl_debug_for_handle_any<Pat: RustInputPat>(
    cx: &Context<Pat>,
    rules: &mut RuleMap<'_>,
    all_rules: &[IRule],
) -> Src {
    let arms = all_rules.iter().filter_map(|&rule| {
        let ty = match cx[rule] {
            Rule::Call(r) => {
                let ident = Src::ident(&cx[r]);
                quote!(#ident<'_, '_, _>)
            }
            Rule::RepeatMany(elem, _) | Rule::RepeatMore(elem, _) => match cx[elem] {
                Rule::Eat(_) => quote!([()]),
                Rule::Call(r) => {
                    let ident = Src::ident(&cx[r]);
                    quote!([#ident<'_, '_, _>])
                }
                _ => return None,
            },
            _ => return None,
        };
        let kind = rule.node_kind(cx, rules);
        let kind_src = kind.to_src();
        Some(quote!(#kind_src => write!(f, "{:?}", Handle::<_, #ty> {
                node: self.node,
                forest: self.forest,
                _marker: PhantomData,
            }),))
    });
    quote!(impl<I: gll::grammer::input::Input> fmt::Debug for Handle<'_, '_, I, Any> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self.node.kind {
                #(#arms)*
                _ => write!(f, "{:?}", Handle::<_, ()> {
                    node: self.node,
                    forest: self.forest,
                    _marker: PhantomData,
                }),
            }
        }
    })
}

fn code_label_decl_and_impls<Pat>(
    cx: &Context<Pat>,
    rules: &RuleMap<'_>,
    code_labels: &IndexMap<Rc<CodeLabel>, usize>,
) -> Src {
    let all_labels = rules
        .named
        .keys()
        .map(|&r| CodeLabel::NamedRule(cx[r].to_string()))
        .chain(code_labels.iter().flat_map(|(fn_label, &counter)| {
            iter::repeat(fn_label.clone())
                .zip(0..counter)
                .map(|(parent, i)| CodeLabel::Nested { parent, i })
        }))
        .map(Rc::new)
        .collect::<Vec<_>>();
    let all_labels_src = all_labels.iter().map(|label| label.to_src());
    let all_labels_ident = all_labels.iter().map(|label| label.flattened_ident());
    let all_labels_enclosing_fn = all_labels
        .iter()
        .map(|label| match &**label {
            CodeLabel::Nested { parent, .. } if !code_labels.contains_key(label) => parent,
            _ => label,
        })
        .map(|label| label.to_src());

    quote!(
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
        enum _C {
            #(#all_labels_ident),*
        }
        impl gll::runtime::CodeLabel for _C {
            type GrammarReflector = _G;

            fn enclosing_fn(self) -> Self {
                match self {
                    #(#all_labels_src => #all_labels_enclosing_fn),*
                }
            }
        }
    )
}
