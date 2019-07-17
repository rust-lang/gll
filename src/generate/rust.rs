use crate::generate::src::{quote, Src};
use crate::parse_node::ParseNodeShape;
use crate::scannerless::Pat as SPat;
use grammer::context::{Context, IRule, IStr};
use grammer::rule::{FieldPathset, MatchesEmpty, Rule, RuleWithNamedFields, SepKind};

use indexmap::{IndexMap, IndexSet};
use std::borrow::Cow;
use std::fmt::Write as FmtWrite;
use std::hash::Hash;
use std::ops::Add;
use std::rc::Rc;
use std::{iter, mem};

pub trait RustInputPat {
    fn rust_slice_ty() -> Src;
    fn rust_matcher(&self) -> Src;
}

impl<S: AsRef<str>> RustInputPat for SPat<S> {
    fn rust_slice_ty() -> Src {
        quote!(str)
    }
    fn rust_matcher(&self) -> Src {
        match self {
            SPat::String(s) => Src::new(s.as_ref()),
            SPat::Range(start, end) => quote!(#start..=#end),
        }
    }
}

struct RuleMap<'a> {
    named: &'a IndexMap<IStr, RuleWithNamedFields>,
    anon: IndexSet<IRule>,
}

struct Variant {
    rule: IRule,
    name: IStr,
    fields: IndexMap<IStr, FieldPathset>,
}

trait RuleWithNamedFieldsMethods<Pat> {
    fn find_variant_fields(&self, cx: &mut Context<Pat>) -> Option<Vec<Variant>>;
}

impl<Pat> RuleWithNamedFieldsMethods<Pat> for RuleWithNamedFields {
    fn find_variant_fields(&self, cx: &mut Context<Pat>) -> Option<Vec<Variant>> {
        if let Rule::Or(cases) = &cx[self.rule] {
            if self.fields.is_empty() {
                return None;
            }

            let mut variant_names = vec![None; cases.len()];
            let mut variant_fields = vec![IndexMap::new(); cases.len()];
            for (&field, paths) in &self.fields {
                for path in &paths.0 {
                    match path[..] {
                        [] => return None,
                        [variant] => {
                            let old_name = variant_names[variant].replace(field);
                            if old_name.is_some() {
                                return None;
                            }
                        }
                        // FIXME: use [variant, rest @ ..] when possible.
                        _ => {
                            variant_fields[path[0]]
                                .entry(field)
                                .or_insert_with(FieldPathset::default)
                                .0
                                .insert(path[1..].to_vec());
                        }
                    }
                }
            }
            cases
                .iter()
                .cloned()
                .zip(variant_names)
                .zip(variant_fields)
                .map(|((rule, name), fields)| {
                    Some(Variant {
                        rule,
                        name: name?,
                        fields,
                    })
                })
                .collect()
        } else {
            None
        }
    }
}

trait RuleMethods<Pat>: Sized {
    fn field_pathset_type(self, cx: &Context<Pat>, paths: &FieldPathset) -> Src;
    fn field_type(self, cx: &Context<Pat>, path: &[usize]) -> Src;
    fn parse_node_kind(self, cx: &Context<Pat>, rules: &mut RuleMap<'_>) -> ParseNodeKind;
    fn parse_node_desc(self, cx: &Context<Pat>, rules: &mut RuleMap<'_>) -> String;
    fn parse_node_shape(
        self,
        cx: &mut Context<Pat>,
        rules: &mut RuleMap<'_>,
    ) -> ParseNodeShape<Self>;
}

impl<Pat: Eq + Hash + RustInputPat> RuleMethods<Pat> for IRule {
    fn field_pathset_type(self, cx: &Context<Pat>, paths: &FieldPathset) -> Src {
        let ty = self.field_type(cx, paths.0.get_index(0).unwrap());
        if paths.0.len() > 1 {
            // HACK(eddyb) find a way to compare `Src` w/o printing (`to_ugly_string`).
            let ty_string = ty.to_ugly_string();
            for path in paths.0.iter().skip(1) {
                if self.field_type(cx, path).to_ugly_string() != ty_string {
                    return quote!(());
                }
            }
        }
        ty
    }

    fn field_type(self, cx: &Context<Pat>, path: &[usize]) -> Src {
        match cx[self] {
            Rule::Empty | Rule::Eat(_) => {
                assert_eq!(path, []);
                quote!(())
            }
            Rule::Call(r) => {
                let ident = Src::ident(&cx[r]);
                quote!(#ident<'a, 'i, I>)
            }
            Rule::Concat(rules) => {
                if path.is_empty() {
                    return quote!(());
                }
                rules[path[0]].field_type(cx, &path[1..])
            }
            Rule::Or(ref cases) => cases[path[0]].field_type(cx, &path[1..]),
            Rule::Opt(rule) => [rule][path[0]].field_type(cx, &path[1..]),
            Rule::RepeatMany(elem, _) | Rule::RepeatMore(elem, _) => {
                assert_eq!(path, []);
                let elem = elem.field_type(cx, &[]);
                quote!([#elem])
            }
        }
    }

    fn parse_node_kind(self, cx: &Context<Pat>, rules: &mut RuleMap<'_>) -> ParseNodeKind {
        if let Rule::Call(r) = cx[self] {
            return ParseNodeKind::NamedRule(cx[r].to_string());
        }

        if let Some((i, _)) = rules.anon.get_full(&self) {
            return ParseNodeKind::Anon(i);
        }
        let i = rules.anon.len();
        rules.anon.insert(self);
        ParseNodeKind::Anon(i)
    }

    fn parse_node_desc(self, cx: &Context<Pat>, rules: &mut RuleMap<'_>) -> String {
        match cx[self] {
            Rule::Empty => "".to_string(),
            Rule::Eat(ref pat) => pat.rust_matcher().to_pretty_string(),
            Rule::Call(r) => cx[r].to_string(),
            Rule::Concat([left, right]) => format!(
                "({} {})",
                left.parse_node_desc(cx, rules),
                right.parse_node_desc(cx, rules)
            ),
            Rule::Or(ref cases) => {
                assert!(cases.len() > 1);
                let mut desc = format!("({}", cases[0].parse_node_desc(cx, rules));
                for rule in &cases[1..] {
                    desc += " | ";
                    desc += &rule.parse_node_desc(cx, rules);
                }
                desc + ")"
            }
            Rule::Opt(rule) => format!("{}?", rule.parse_node_desc(cx, rules)),
            Rule::RepeatMany(elem, None) => format!("{}*", elem.parse_node_desc(cx, rules)),
            Rule::RepeatMany(elem, Some((sep, SepKind::Simple))) => format!(
                "{}* % {}",
                elem.parse_node_desc(cx, rules),
                sep.parse_node_desc(cx, rules)
            ),
            Rule::RepeatMany(elem, Some((sep, SepKind::Trailing))) => format!(
                "{}* %% {}",
                elem.parse_node_desc(cx, rules),
                sep.parse_node_desc(cx, rules)
            ),
            Rule::RepeatMore(elem, None) => format!("{}+", elem.parse_node_desc(cx, rules)),
            Rule::RepeatMore(elem, Some((sep, SepKind::Simple))) => format!(
                "{}+ % {}",
                elem.parse_node_desc(cx, rules),
                sep.parse_node_desc(cx, rules)
            ),
            Rule::RepeatMore(elem, Some((sep, SepKind::Trailing))) => format!(
                "{}+ %% {}",
                elem.parse_node_desc(cx, rules),
                sep.parse_node_desc(cx, rules)
            ),
        }
    }

    fn parse_node_shape(
        self,
        cx: &mut Context<Pat>,
        rules: &mut RuleMap<'_>,
    ) -> ParseNodeShape<Self> {
        match cx[self] {
            Rule::Empty | Rule::Eat(_) => ParseNodeShape::Opaque,
            Rule::Call(name) => {
                let rule = &rules.named[&name];
                if rule.fields.is_empty() {
                    ParseNodeShape::Opaque
                } else {
                    ParseNodeShape::Alias(rule.rule)
                }
            }
            Rule::Concat([left, right]) => ParseNodeShape::Split(left, right),
            Rule::Or(_) => ParseNodeShape::Choice,
            Rule::Opt(rule) => ParseNodeShape::Opt(rule),
            Rule::RepeatMany(elem, sep) => {
                ParseNodeShape::Opt(cx.intern(Rule::RepeatMore(elem, sep)))
            }
            Rule::RepeatMore(rule, None) => {
                ParseNodeShape::Split(rule, cx.intern(Rule::RepeatMany(rule, None)))
            }
            Rule::RepeatMore(elem, Some((sep, SepKind::Simple))) => {
                let tail = cx.intern(Rule::Concat([sep, self]));
                ParseNodeShape::Split(elem, cx.intern(Rule::Opt(tail)))
            }
            Rule::RepeatMore(elem, Some((sep, SepKind::Trailing))) => {
                let many = cx.intern(Rule::RepeatMany(elem, Some((sep, SepKind::Trailing))));
                let tail = cx.intern(Rule::Concat([sep, many]));
                ParseNodeShape::Split(elem, cx.intern(Rule::Opt(tail)))
            }
        }
    }
}

#[derive(Clone)]
enum ParseNodeKind {
    NamedRule(String),
    Anon(usize),
}

impl ParseNodeKind {
    fn ident(&self) -> Src {
        match self {
            ParseNodeKind::NamedRule(name) => Src::ident(name),
            ParseNodeKind::Anon(i) => Src::ident(format!("_{}", i)),
        }
    }
}

impl ParseNodeKind {
    fn to_src(&self) -> Src {
        let ident = self.ident();
        quote!(_P::#ident)
    }
}

impl ParseNodeShape<IRule> {
    fn to_src<Pat: Eq + Hash + RustInputPat>(
        &self,
        cx: &mut Context<Pat>,
        rules: &mut RuleMap<'_>,
    ) -> Src {
        let shape = self.map(|rule| rule.parse_node_kind(cx, rules).to_src());
        let variant = match shape {
            ParseNodeShape::Opaque => quote!(Opaque),
            ParseNodeShape::Alias(inner) => quote!(Alias(#inner)),
            ParseNodeShape::Choice => quote!(Choice),
            ParseNodeShape::Opt(inner) => quote!(Opt(#inner)),
            ParseNodeShape::Split(left, right) => quote!(Split(#left, #right)),
        };
        quote!(ParseNodeShape::#variant)
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
    fn generate_rust(&self, cx: &mut Context<Pat>) -> Src;
}

pub fn generate<Pat: Eq + Hash + MatchesEmpty + RustInputPat>(
    cx: &mut Context<Pat>,
    g: &grammer::Grammar,
) -> Src {
    g.generate_rust(cx)
}

impl<Pat: Eq + Hash + MatchesEmpty + RustInputPat> GrammarGenerateMethods<Pat>
    for grammer::Grammar
{
    fn generate_rust(&self, cx: &mut Context<Pat>) -> Src {
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

        for (&name, rule) in rules.named {
            out += declare_rule(name, rule, cx, &mut rules) + impl_parse_with(cx, name);
        }

        let mut code_labels = IndexMap::new();
        out += define_parse_fn(cx, &mut rules, &mut code_labels);

        for &name in rules.named.keys() {
            cx.intern(Rule::Call(name))
                .parse_node_shape(cx, &mut rules)
                .map(|rule| rule.parse_node_kind(cx, &mut rules));
        }

        let mut i = 0;
        while i < rules.anon.len() {
            let rule = *rules.anon.get_index(i).unwrap();
            rule.parse_node_shape(cx, &mut rules)
                .map(|rule| rule.parse_node_kind(cx, &mut rules));
            i += 1;
        }

        let all_rules: Vec<_> = rules
            .named
            .keys()
            .map(|&name| cx.intern(Rule::Call(name)))
            .chain(rules.anon.iter().cloned())
            .collect();

        out + declare_parse_node_kind(cx, &mut rules, &all_rules)
            + impl_debug_for_handle_any(cx, &mut rules, &all_rules)
            + code_label_decl_and_impls(cx, &mut rules, &code_labels)
    }
}

#[must_use]
struct Continuation<'a, 'r, Pat> {
    cx: &'a mut Context<Pat>,
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

fn push_saved<Pat: Eq + Hash + RustInputPat>(rule: IRule) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(move |mut cont| {
        let rules = cont.rules.as_mut().unwrap();
        let parse_node_kind_src = rule.parse_node_kind(cont.cx, rules).to_src();
        thunk!(rt.save(#parse_node_kind_src);).apply(cont)
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

fn forest_add_choice<Pat: Eq + Hash + RustInputPat>(
    rule: IRule,
    choice: IRule,
) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(move |mut cont| {
        if let Some(rules) = &mut cont.rules.as_mut() {
            let parse_node_kind_src = rule.parse_node_kind(cont.cx, rules).to_src();
            let choice_src = choice.parse_node_kind(cont.cx, rules).to_src();
            cont = thunk!(rt.forest_add_choice(#parse_node_kind_src, #choice_src);).apply(cont);
        }
        cont
    })
}

fn concat_and_forest_add<Pat: Eq + Hash + RustInputPat>(
    rule: IRule,
    left: IRule,
    right: Thunk<impl ContFn<Pat>>,
) -> Thunk<impl ContFn<Pat>> {
    Thunk::new(move |mut cont| {
        if let Some(rules) = cont.rules.as_mut() {
            let parse_node_kind_src = rule.parse_node_kind(cont.cx, rules).to_src();
            (left.generate_parse()
                + push_saved(left)
                + right
                + pop_saved(move |saved| {
                    thunk!(rt.forest_add_split(
                    #parse_node_kind_src,
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

    fn generate_traverse_shape(
        self,
        refutable: bool,
        cx: &mut Context<Pat>,
        rules: &mut RuleMap<'_>,
    ) -> Src;
}

impl<Pat: Eq + Hash + RustInputPat> RuleGenerateMethods<Pat> for IRule {
    fn generate_parse(
        self,
    ) -> Thunk<Box<dyn for<'a, 'r> FnOnce(Continuation<'a, 'r, Pat>) -> Continuation<'a, 'r, Pat>>>
    {
        Thunk::new(Box::new(
            move |cont: Continuation<'_, '_, Pat>| match cont.cx[self] {
                Rule::Empty => cont,
                Rule::Eat(ref pat) => {
                    let pat = pat.rust_matcher();
                    check(quote!(let Some(mut rt) = rt.input_consume_left(&(#pat)))).apply(cont)
                }
                Rule::Call(r) => {
                    call(Rc::new(CodeLabel::NamedRule(cont.cx[r].to_string()))).apply(cont)
                }
                Rule::Concat([left, right]) => {
                    concat_and_forest_add(self, left, right.generate_parse()).apply(cont)
                }
                Rule::Or(ref cases) => {
                    // HACK(eddyb) only clones a `Vec` to avoid `cx` borrow conflicts.
                    let cases = cases.clone();
                    parallel(ThunkIter(cases.iter().map(|&rule| {
                        rule.generate_parse() + forest_add_choice(self, rule)
                    })))
                    .apply(cont)
                }
                Rule::Opt(rule) => opt(rule.generate_parse()).apply(cont),
                Rule::RepeatMany(elem, None) => {
                    let more = cont.cx.intern(Rule::RepeatMore(elem, None));
                    fix(|label| opt(concat_and_forest_add(more, elem, call(label)))).apply(cont)
                }
                Rule::RepeatMany(elem, Some(sep)) => {
                    let rule = cont.cx.intern(Rule::RepeatMore(elem, Some(sep)));
                    opt(rule.generate_parse()).apply(cont)
                }
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
                    let many = cont
                        .cx
                        .intern(Rule::RepeatMany(elem, Some((sep, SepKind::Trailing))));
                    let tail = cont.cx.intern(Rule::Concat([sep, many]));
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

    fn generate_traverse_shape(
        self,
        refutable: bool,
        cx: &mut Context<Pat>,
        rules: &mut RuleMap<'_>,
    ) -> Src {
        match cx[self] {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::Call(_)
            | Rule::RepeatMany(..)
            | Rule::RepeatMore(..) => {
                if refutable {
                    quote!(?)
                } else {
                    quote!(_)
                }
            }
            Rule::Concat([left, right]) => {
                let left = left.generate_traverse_shape(refutable, cx, rules);
                let right = right.generate_traverse_shape(refutable, cx, rules);
                quote!((#left, #right))
            }
            Rule::Or(ref cases) => {
                // HACK(eddyb) only clones a `Vec` to avoid `cx` borrow conflicts.
                let cases = cases.clone();
                let cases_idx = cases.iter().enumerate().map(|(i, _)| {
                    let i_var_ident = Src::ident(format!("_{}", i));
                    // HACK(eddyb) workaround `quote!(#i)` producing `0usize`.
                    let i = ::proc_macro2::Literal::usize_unsuffixed(i);
                    quote!(#i #i_var_ident)
                });
                // HACK(eddyb) only collected to a `Vec` to avoid `cx` borrow conflicts.
                let cases_shape = cases
                    .iter()
                    .map(|rule| rule.generate_traverse_shape(true, cx, rules))
                    .collect::<Vec<_>>();
                let cases_node_kind = cases.iter().map(|rule| rule.parse_node_kind(cx, rules));
                let cases_node_kind_src = cases_node_kind.map(|kind| kind.to_src());
                quote!({ #(#cases_idx: #cases_node_kind_src => #cases_shape,)* })
            }
            Rule::Opt(rule) => {
                let shape = rule.generate_traverse_shape(true, cx, rules);
                quote!([#shape])
            }
        }
    }
}

fn impl_parse_with<Pat>(cx: &mut Context<Pat>, name: IStr) -> Src
where
    Pat: RustInputPat,
{
    let ident = Src::ident(&cx[name]);
    let code_label = Rc::new(CodeLabel::NamedRule(cx[name].to_string()));
    let code_label_src = code_label.to_src();
    let parse_node_kind = ParseNodeKind::NamedRule(cx[name].to_string());
    let parse_node_kind_src = parse_node_kind.to_src();
    let rust_slice_ty = Pat::rust_slice_ty();
    quote!(
        impl<I> #ident<'_, '_, I>
            where I: gll::input::Input<Slice = #rust_slice_ty>,
        {
            pub fn parse(input: I)
                -> Result<
                    OwnedHandle<I, Self>,
                    gll::parser::ParseError<I::SourceInfoPoint>,
                >
            {
                gll::runtime::Runtime::parse(
                    _G,
                    input,
                    #code_label_src,
                    #parse_node_kind_src,
                ).map(|forest_and_node| OwnedHandle {
                    forest_and_node,
                    _marker: PhantomData,
                })
            }
        }

        impl<I: gll::input::Input> OwnedHandle<I, #ident<'_, '_, I>> {
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
    )
}

fn declare_rule<Pat>(
    name: IStr,
    rule: &RuleWithNamedFields,
    cx: &mut Context<Pat>,
    rules: &mut RuleMap<'_>,
) -> Src
where
    Pat: Eq + Hash + RustInputPat,
{
    let ident = Src::ident(&cx[name]);
    let variants = rule.find_variant_fields(cx);
    let variants: Option<&[Variant]> = variants.as_ref().map(|x| &**x);

    let field_handle_ty = |cx: &Context<Pat>, rule: IRule, paths| {
        let ty = rule.field_pathset_type(cx, paths);
        let handle_ty = quote!(Handle<'a, 'i, I, #ty>);
        if rule.field_pathset_is_refutable(cx, paths) {
            quote!(Option<#handle_ty>)
        } else {
            handle_ty
        }
    };

    let rule_ty_def = if let Some(variants) = variants {
        let variants = variants.iter().map(|v| {
            let variant_ident = Src::ident(&cx[v.name]);
            if v.fields.is_empty() {
                let field_ty = v.rule.field_type(cx, &[]);
                quote!(#variant_ident(Handle<'a, 'i, I, #field_ty>))
            } else {
                let fields_ident = v.fields.keys().map(|&name| Src::ident(&cx[name]));
                let fields_ty = v
                    .fields
                    .values()
                    .map(|paths| field_handle_ty(cx, v.rule, paths));
                quote!(#variant_ident {
                    #(#fields_ident: #fields_ty),*
                })
            }
        });
        quote!(
            #[allow(non_camel_case_types)]
            pub enum #ident<'a, 'i, I: gll::input::Input> {
                #(#variants),*
            }
        )
    } else {
        let fields_ident = rule.fields.keys().map(|&name| Src::ident(&cx[name]));
        let fields_ty = rule
            .fields
            .values()
            .map(|paths| field_handle_ty(cx, rule.rule, paths));
        let marker_field = if rule.fields.is_empty() {
            Some(quote!(_marker: PhantomData<(&'a (), &'i (), I)>,))
        } else {
            None
        };
        quote!(
            #[allow(non_camel_case_types)]
            pub struct #ident<'a, 'i, I: gll::input::Input> {
                #(pub #fields_ident: #fields_ty),*
                #marker_field
            }
        )
    };
    rule_ty_def
        + rule_debug_impls(cx, name, &rule, variants)
        + impl_rule_from_forest(name, &rule, variants, cx, rules)
        + impl_rule_one_and_all(name, &rule, variants, cx, rules)
}

fn impl_rule_from_forest<Pat>(
    name: IStr,
    rule: &RuleWithNamedFields,
    variants: Option<&[Variant]>,
    cx: &mut Context<Pat>,
    rules: &mut RuleMap<'_>,
) -> Src
where
    Pat: Eq + Hash + RustInputPat,
{
    let ident = Src::ident(&cx[name]);
    let field_handle_expr = |cx: &Context<Pat>, rule: IRule, paths: &FieldPathset| {
        let paths_expr = paths.0.iter().map(|path| {
            // HACK(eddyb) workaround `quote!(#i)` producing `0usize`.
            let path = path
                .iter()
                .cloned()
                .map(::proc_macro2::Literal::usize_unsuffixed);
            quote!(_r #(.#path)*)
        });
        if rule.field_pathset_is_refutable(cx, paths) {
            quote!(None #(.or(#paths_expr))* .map(|node| Handle {
                node,
                forest,
                _marker: PhantomData,
            }))
        } else {
            assert_eq!(paths.0.len(), 1);
            quote!(Handle {
                node: #(#paths_expr)*,
                forest,
                _marker: PhantomData,
            })
        }
    };

    let methods = if let Some(variants) = variants {
        // HACK(eddyb) only collected to a `Vec` to avoid `cx` borrow conflicts.
        let variants_shape = variants
            .iter()
            .map(|v| v.rule.generate_traverse_shape(false, cx, rules))
            .collect::<Vec<_>>();
        let variants_from_forest_ident = variants
            .iter()
            .map(|v| Src::ident(format!("{}_from_forest", cx[v.name])));
        let variants_body = variants.iter().map(|v| {
            let variant_ident = Src::ident(&cx[v.name]);
            if v.fields.is_empty() {
                quote!(#ident::#variant_ident(Handle {
                    node: _node,
                    forest,
                    _marker: PhantomData,
                }))
            } else {
                let fields_ident = v.fields.keys().map(|&name| Src::ident(&cx[name]));
                let fields_expr = v
                    .fields
                    .values()
                    .map(|paths| field_handle_expr(cx, v.rule, paths));
                quote!(#ident::#variant_ident {
                    #(#fields_ident: #fields_expr),*
                })
            }
        });

        quote!(#(
            #[allow(non_snake_case)]
            fn #variants_from_forest_ident(
                forest: &'a gll::forest::ParseForest<'i, _G, I>,
                _node: ParseNode<'i, _P>,
                _r: traverse!(typeof(ParseNode<'i, _P>) #variants_shape),
            ) -> Self {
                #variants_body
            }
        )*)
    } else {
        let shape = rule.rule.generate_traverse_shape(false, cx, rules);
        let fields_ident = rule.fields.keys().map(|&name| Src::ident(&cx[name]));
        let fields_expr = rule
            .fields
            .values()
            .map(|paths| field_handle_expr(cx, rule.rule, paths));
        let marker_field = if rule.fields.is_empty() {
            Some(quote!(_marker: { let _ = forest; PhantomData },))
        } else {
            None
        };
        quote!(
            fn from_forest(
                forest: &'a gll::forest::ParseForest<'i, _G, I>,
                _node: ParseNode<'i, _P>,
                _r: traverse!(typeof(ParseNode<'i, _P>) #shape),
            ) -> Self {
                #ident {
                    #(#fields_ident: #fields_expr),*
                    #marker_field
                }
            }
        )
    };

    quote!(impl<'a, 'i, I: gll::input::Input> #ident<'a, 'i, I> {
        #methods
    })
}

fn impl_rule_one_and_all<Pat>(
    name: IStr,
    rule: &RuleWithNamedFields,
    variants: Option<&[Variant]>,
    cx: &mut Context<Pat>,
    rules: &mut RuleMap<'_>,
) -> Src
where
    Pat: Eq + Hash + RustInputPat,
{
    let ident = Src::ident(&cx[name]);
    let (one, all) = if let Some(variants) = variants {
        // FIXME(eddyb) figure out a more efficient way to reuse
        // iterators with `quote!(...)` than `.collect::<Vec<_>>()`.
        let i_ident = (0..variants.len())
            .map(|i| Src::ident(format!("_{}", i)))
            .collect::<Vec<_>>();
        let variants_from_forest_ident = variants
            .iter()
            .map(|v| Src::ident(format!("{}_from_forest", cx[v.name])))
            .collect::<Vec<_>>();
        let variants_kind = variants
            .iter()
            .map(|v| v.rule.parse_node_kind(cx, rules))
            .collect::<Vec<_>>();
        let variants_kind_src = variants_kind
            .iter()
            .map(|kind| kind.to_src())
            .collect::<Vec<_>>();
        let variants_shape = variants
            .iter()
            .map(|v| v.rule.generate_traverse_shape(false, cx, rules))
            .collect::<Vec<_>>();

        (
            quote!(
                let node = forest.one_choice(node)?;
                match node.kind {
                    #(#variants_kind_src => {
                        let r = traverse!(one(forest, node) #variants_shape);
                        #ident::#variants_from_forest_ident(self.forest, node, r)
                    })*
                    _ => unreachable!()
                }
            ),
            quote!(
                #[derive(Clone)]
                enum Iter<#(#i_ident),*> {
                    #(#i_ident(#i_ident)),*
                }
                impl<T #(, #i_ident: Iterator<Item = T>)*> Iterator for Iter<#(#i_ident),*>
                {
                    type Item = T;
                    fn next(&mut self) -> Option<T> {
                        match self {
                            #(Iter::#i_ident(iter) => iter.next()),*
                        }
                    }
                }

                forest.all_choices(node).flat_map(move |node| {
                    match node.kind {
                        #(#variants_kind_src => Iter::#i_ident(
                            traverse!(all(forest) #variants_shape)
                                .apply(node)
                                .map(move |r| #ident::#variants_from_forest_ident(self.forest, node, r))
                        ),)*
                        _ => unreachable!(),
                    }
                })
            ),
        )
    } else {
        let shape = rule.rule.generate_traverse_shape(false, cx, rules);
        (
            quote!(
                let r = traverse!(one(forest, node) #shape);
                #ident::from_forest(self.forest, node, r)
            ),
            quote!(
                traverse!(all(forest) #shape)
                    .apply(node)
                    .map(move |r| #ident::from_forest(self.forest, node, r))
            ),
        )
    };

    quote!(impl<'a, 'i, I> Handle<'a, 'i, I, #ident<'a, 'i, I>>
        where I: gll::input::Input,
    {
        pub fn one(self) -> Result<#ident<'a, 'i, I>, Ambiguity<Self>> {
            // HACK(eddyb) using a closure to catch `Err`s from `?`
            (|| Ok({
                let forest = self.forest;
                let node = forest.unpack_alias(self.node);
                #one
            }))().map_err(|gll::forest::MoreThanOne| Ambiguity(self))
        }

        pub fn all(self) -> impl Iterator<Item = #ident<'a, 'i, I>> {
            let forest = self.forest;
            let node = forest.unpack_alias(self.node);
            #all
        }
    })
}

fn rule_debug_impls<Pat>(
    cx: &mut Context<Pat>,
    name: IStr,
    rule: &RuleWithNamedFields,
    variants: Option<&[Variant]>,
) -> Src {
    rule_debug_impl(cx, name, rule, variants)
        + rule_handle_debug_impl(cx, name, !rule.fields.is_empty())
}

fn rule_debug_impl<Pat>(
    cx: &mut Context<Pat>,
    name: IStr,
    rule: &RuleWithNamedFields,
    variants: Option<&[Variant]>,
) -> Src {
    let name = &cx[name];
    let ident = Src::ident(name);
    let body = if let Some(variants) = variants {
        let variants_pat = variants.iter().map(|v| {
            let variant_ident = Src::ident(&cx[v.name]);
            if v.fields.is_empty() {
                quote!(#ident::#variant_ident(x))
            } else {
                let fields_ident = v.fields.keys().map(|&name| Src::ident(&cx[name]));
                let fields_var_ident = v
                    .fields
                    .keys()
                    .map(|&field_name| Src::ident(format!("f_{}", cx[field_name])));
                quote!(#ident::#variant_ident {
                    #(#fields_ident: #fields_var_ident,)*
                })
            }
        });
        let variants_body = variants.iter().map(|v| {
            let variant_path_str = format!("{}::{}", name, cx[v.name]);
            if v.fields.is_empty() {
                quote!(f.debug_tuple(#variant_path_str).field(x).finish(),)
            } else {
                let fields_debug = v.fields.iter().map(|(field_name, paths)| {
                    let field_name = &cx[*field_name];
                    let field_var_ident = Src::ident(format!("f_{}", field_name));
                    if v.rule.field_pathset_is_refutable(cx, paths) {
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
        });

        quote!(match self {
            #(#variants_pat => #variants_body)*
        })
    } else {
        let fields_debug = rule.fields.iter().map(|(field_name, paths)| {
            let field_name = &cx[*field_name];
            let field_ident = Src::ident(field_name);
            if rule.rule.field_pathset_is_refutable(cx, paths) {
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
    };
    quote!(impl<I: gll::input::Input> fmt::Debug for #ident<'_, '_, I> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            #body
        }
    })
}

fn rule_handle_debug_impl<Pat>(cx: &mut Context<Pat>, name: IStr, has_fields: bool) -> Src {
    let ident = Src::ident(&cx[name]);
    let body = if !has_fields {
        quote!()
    } else {
        quote!(
            write!(f, " => ")?;
            let mut first = true;
            for x in self.all() {
                if !first {
                    write!(f, " | ")?;
                }
                first = false;
                fmt::Debug::fmt(&x, f)?;
            }
        )
    };
    quote!(
        impl<'a, 'i, I: gll::input::Input> fmt::Debug for Handle<'a, 'i, I, #ident<'a, 'i, I>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{:?}", self.source_info())?;
                #body
                Ok(())
            }
        }

        impl<I: gll::input::Input> fmt::Debug for OwnedHandle<I, #ident<'_, '_, I>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.with(|handle| handle.fmt(f))
            }
        }
    )
}

fn define_parse_fn<Pat>(
    cx: &mut Context<Pat>,
    rules: &mut RuleMap<'_>,
    code_labels: &mut IndexMap<Rc<CodeLabel>, usize>,
) -> Src
where
    Pat: Eq + Hash + RustInputPat,
{
    let mut code_label_arms = vec![];
    for (&name, rule) in rules.named {
        let code_label = Rc::new(CodeLabel::NamedRule(cx[name].to_string()));
        let rules = if rule.fields.is_empty() {
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

    let rust_slice_ty = Pat::rust_slice_ty();
    quote!(impl<I> gll::runtime::CodeStep<I> for _C
        where I: gll::input::Input<Slice = #rust_slice_ty>,
    {
        fn step<'i>(self, mut rt: gll::runtime::Runtime<'_, 'i, _C, I>) {
            match self {
                #(#code_label_arms)*
            }
        }
    })
}

fn declare_parse_node_kind<Pat: Eq + Hash + RustInputPat>(
    cx: &mut Context<Pat>,
    rules: &mut RuleMap<'_>,
    all_rules: &[IRule],
) -> Src {
    // FIXME(eddyb) figure out a more efficient way to reuse
    // iterators with `quote!(...)` than `.collect::<Vec<_>>()`.
    let nodes_kind = all_rules
        .iter()
        .map(|rule| rule.parse_node_kind(cx, rules))
        .collect::<Vec<_>>();
    let nodes_kind_src = nodes_kind
        .iter()
        .map(|kind| kind.to_src())
        .collect::<Vec<_>>();
    let nodes_kind_ident = nodes_kind.iter().map(|kind| kind.ident());
    // HACK(eddyb) only collected to a `Vec` to avoid `cx`/`rules` borrow conflicts.
    let nodes_doc = all_rules
        .iter()
        .map(|&rule| format!("`{}`", rule.parse_node_desc(cx, rules).replace('`', "\\`")))
        .collect::<Vec<_>>();
    let nodes_desc = all_rules
        .iter()
        .map(|&rule| rule.parse_node_desc(cx, rules))
        .collect::<Vec<_>>();
    let nodes_shape_src = all_rules
        .iter()
        .map(|&rule| rule.parse_node_shape(cx, rules).to_src(cx, rules))
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

        impl gll::forest::GrammarReflector for _G {
            type ParseNodeKind = _P;

            fn parse_node_shape(&self, kind: _P) -> ParseNodeShape<_P> {
                match kind {
                    #(#nodes_kind_src => #nodes_shape_src),*
                }
            }
            fn parse_node_desc(&self, kind: _P) -> String {
                let s = match kind {
                    #(#nodes_kind_src => #nodes_desc),*
                };
                s.to_string()
            }
        }
    )
}

fn impl_debug_for_handle_any<Pat: Eq + Hash + RustInputPat>(
    cx: &mut Context<Pat>,
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
        let kind = rule.parse_node_kind(cx, rules);
        let kind_src = kind.to_src();
        Some(quote!(#kind_src => write!(f, "{:?}", Handle::<_, #ty> {
                node: self.node,
                forest: self.forest,
                _marker: PhantomData,
            }),))
    });
    quote!(impl<I: gll::input::Input> fmt::Debug for Handle<'_, '_, I, Any> {
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
    cx: &mut Context<Pat>,
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
            type ParseNodeKind = _P;

            fn enclosing_fn(self) -> Self {
                match self {
                    #(#all_labels_src => #all_labels_enclosing_fn),*
                }
            }
        }
    )
}
