use generate::src::{quotable_to_src, quote, Src, ToSrc};
use grammar::ParseNodeShape;
use grammar::{Grammar, MatchesEmpty, Rc, Rule, RuleWithNamedFields};

use ordermap::{Entry, OrderMap, OrderSet};
use std::borrow::Cow;
use std::cell::RefCell;
use std::fmt::Write as FmtWrite;
use std::hash::Hash;
use std::ops::Add;
use std::{iter, mem};

pub trait RustInputPat {
    fn rust_slice_ty() -> Src;
    fn rust_matcher(&self) -> Src;
}

impl<S: AsRef<str>> RustInputPat for ::scannerless::Pat<S> {
    fn rust_slice_ty() -> Src {
        quote!(str)
    }
    fn rust_matcher(&self) -> Src {
        match self {
            ::scannerless::Pat::String(s) => Src::new(s.as_ref()),
            ::scannerless::Pat::Range(start, end) => quote!(#start..=#end),
        }
    }
}

struct RuleMap<'a, Pat> {
    named: &'a OrderMap<String, RuleWithNamedFields<Pat>>,
    anon: RefCell<OrderSet<Rc<Rule<Pat>>>>,
    desc: RefCell<OrderMap<Rc<Rule<Pat>>, String>>,
    anon_shape: RefCell<OrderMap<Rc<Rule<Pat>>, ParseNodeShape<ParseNodeKind>>>,
}

struct ParseNode {
    kind: ParseNodeKind,
    desc: String,
    shape: ParseNodeShape<ParseNodeKind>,
    ty: Option<Src>,
}

struct Variant<'a, Pat> {
    rule: Rc<Rule<Pat>>,
    name: &'a str,
    fields: OrderMap<&'a str, OrderSet<Vec<usize>>>,
}

impl<Pat: PartialEq> RuleWithNamedFields<Pat> {
    fn find_variant_fields(&self) -> Option<Vec<Variant<'_, Pat>>> {
        if let Rule::Or(cases) = &*self.rule {
            if self.fields.is_empty() {
                return None;
            }
            let mut variants: Vec<_> = cases
                .iter()
                .map(|rule| Variant {
                    rule: rule.clone(),
                    name: "",
                    fields: OrderMap::new(),
                })
                .collect();
            for (field, paths) in &self.fields {
                for path in paths {
                    if path.len() == 0 {
                        return None;
                    }
                    if path.len() == 1 {
                        if variants[path[0]].name != "" {
                            return None;
                        }
                        variants[path[0]].name = field;
                    } else {
                        variants[path[0]]
                            .fields
                            .entry(&field[..])
                            .or_insert_with(OrderSet::new)
                            .insert(path[1..].to_vec());
                    }
                }
            }
            if variants.iter().any(|x| x.name == "") {
                return None;
            }
            Some(variants)
        } else {
            None
        }
    }
}

impl<Pat> Rule<Pat> {
    fn field_pathset_type(&self, paths: &OrderSet<Vec<usize>>) -> Src {
        let ty = self.field_type(paths.get_index(0).unwrap());
        if paths.len() > 1 {
            // HACK(eddyb) find a way to compare `Src` w/o printing (`to_ugly_string`).
            let ty_string = ty.to_ugly_string();
            for path in paths.iter().skip(1) {
                if self.field_type(path).to_ugly_string() != ty_string {
                    return quote!(());
                }
            }
        }
        ty
    }

    fn field_type(&self, path: &[usize]) -> Src {
        match self {
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) => {
                assert_eq!(path, []);
                quote!(())
            }
            Rule::Call(r) => {
                let ident = Src::ident(r);
                quote!(#ident<'a, 'i, I>)
            }
            Rule::Concat(rules) => {
                if path.is_empty() {
                    return quote!(());
                }
                rules[path[0]].field_type(&path[1..])
            }
            Rule::Or(cases) => cases[path[0]].field_type(&path[1..]),
            Rule::Opt(rule) => [rule][path[0]].field_type(&path[1..]),
            Rule::RepeatMany(elem, _) | Rule::RepeatMore(elem, _) => {
                assert_eq!(path, []);
                let elem = elem.field_type(&[]);
                quote!([#elem])
            }
        }
    }
}

impl<Pat: Ord + Hash + RustInputPat> Rc<Rule<Pat>> {
    fn parse_node_kind(&self, rules: &RuleMap<Pat>) -> ParseNodeKind {
        if let Rule::Call(r) = &**self {
            return ParseNodeKind::NamedRule(r.clone());
        }

        if let Some((i, _)) = rules.anon.borrow().get_full(self) {
            return ParseNodeKind::Anon(i);
        }
        let i = rules.anon.borrow().len();
        rules.anon.borrow_mut().insert(self.clone());
        ParseNodeKind::Anon(i)
    }

    fn parse_node_desc(&self, rules: &RuleMap<Pat>) -> String {
        if let Some(desc) = rules.desc.borrow().get(self) {
            return desc.clone();
        }
        let desc = match &**self {
            Rule::Empty => "".to_string(),
            Rule::Eat(pat) => pat.rust_matcher().to_pretty_string(),
            Rule::NegativeLookahead(pat) => format!("!{}", pat.rust_matcher().to_pretty_string()),
            Rule::Call(r) => r.clone(),
            Rule::Concat([left, right]) => format!(
                "({} {})",
                left.parse_node_desc(rules),
                right.parse_node_desc(rules)
            ),
            Rule::Or(cases) => {
                assert!(cases.len() > 1);
                let mut desc = format!("({}", cases[0].parse_node_desc(rules));
                for rule in &cases[1..] {
                    desc += " | ";
                    desc += &rule.parse_node_desc(rules);
                }
                desc + ")"
            }
            Rule::Opt(rule) => format!("{}?", rule.parse_node_desc(rules)),
            Rule::RepeatMany(elem, None) => format!("{}*", elem.parse_node_desc(rules)),
            Rule::RepeatMany(elem, Some(sep)) => format!(
                "{}* % {}",
                elem.parse_node_desc(rules),
                sep.parse_node_desc(rules)
            ),
            Rule::RepeatMore(elem, None) => format!("{}+", elem.parse_node_desc(rules)),
            Rule::RepeatMore(elem, Some(sep)) => format!(
                "{}+ % {}",
                elem.parse_node_desc(rules),
                sep.parse_node_desc(rules)
            ),
        };
        match rules.desc.borrow_mut().entry(self.clone()) {
            Entry::Vacant(entry) => entry.insert(desc).clone(),
            Entry::Occupied(_) => unreachable!(),
        }
    }

    fn fill_parse_node_shape(&self, rules: &RuleMap<Pat>) {
        if rules.anon_shape.borrow().contains_key(self) {
            return;
        }
        let shape = match &**self {
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) => ParseNodeShape::Opaque,
            Rule::Call(_) => return,
            Rule::Concat([left, right]) => {
                ParseNodeShape::Split(left.parse_node_kind(rules), right.parse_node_kind(rules))
            }
            Rule::Or(_) => ParseNodeShape::Choice,
            Rule::Opt(rule) => ParseNodeShape::Opt(rule.parse_node_kind(rules)),
            Rule::RepeatMany(elem, sep) => ParseNodeShape::Opt(
                Rc::new(Rule::RepeatMore(elem.clone(), sep.clone())).parse_node_kind(rules),
            ),
            Rule::RepeatMore(rule, None) => ParseNodeShape::Split(
                rule.parse_node_kind(rules),
                Rc::new(Rule::RepeatMany(rule.clone(), None)).parse_node_kind(rules),
            ),
            Rule::RepeatMore(elem, Some(sep)) => ParseNodeShape::Split(
                elem.parse_node_kind(rules),
                Rc::new(Rule::Opt(Rc::new(Rule::Concat([
                    sep.clone(),
                    self.clone(),
                ]))))
                .parse_node_kind(rules),
            ),
        };
        rules.anon_shape.borrow_mut().insert(self.clone(), shape);
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

impl ToSrc for ParseNodeKind {
    fn to_src(&self) -> Src {
        let ident = self.ident();
        quote!(_P::#ident)
    }
}
quotable_to_src!(ParseNodeKind);

impl ToSrc for ParseNodeShape<ParseNodeKind> {
    fn to_src(&self) -> Src {
        let variant = match self {
            ParseNodeShape::Opaque => quote!(Opaque),
            ParseNodeShape::Alias(inner) => quote!(Alias(#inner)),
            ParseNodeShape::Choice => quote!(Choice),
            ParseNodeShape::Opt(inner) => quote!(Opt(#inner)),
            ParseNodeShape::Split(left, right) => quote!(Split(#left, #right)),
        };
        quote!(ParseNodeShape::#variant)
    }
}
quotable_to_src!(ParseNodeShape<ParseNodeKind>);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum CodeLabel {
    NamedRule(String),
    Nested { parent: Rc<CodeLabel>, i: usize },
}

impl CodeLabel {
    fn flattened_name(&self) -> Cow<str> {
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

impl ToSrc for Rc<CodeLabel> {
    fn to_src(&self) -> Src {
        let ident = self.flattened_ident();
        quote!(_C::#ident)
    }
}
quotable_to_src!(Rc<CodeLabel>);

impl<Pat: Ord + Hash + MatchesEmpty + RustInputPat> Grammar<Pat> {
    pub fn generate_rust(&self) -> Src {
        self.check();

        let rules = &RuleMap {
            named: &self.rules,
            anon: RefCell::new(OrderSet::new()),
            desc: RefCell::new(OrderMap::new()),
            anon_shape: RefCell::new(OrderMap::new()),
        };

        let mut out = concat!(
            include_str!("templates/imports.rs"),
            include_str!("templates/header.rs")
        )
        .parse::<Src>()
        .unwrap();

        for (name, rule) in rules.named {
            out += declare_rule(name, rule, rules) + impl_parse_with::<Pat>(name);
        }

        let mut code_labels = OrderMap::new();
        out += define_parse_fn(rules, &mut code_labels);

        let mut i = 0;
        while i < rules.anon.borrow().len() {
            let rule = rules.anon.borrow().get_index(i).unwrap().clone();
            rule.fill_parse_node_shape(rules);
            i += 1;
        }
        let all_parse_nodes: Vec<ParseNode> = rules
            .named
            .iter()
            .map(|(name, rule)| {
                let ident = Src::ident(name);
                ParseNode {
                    kind: ParseNodeKind::NamedRule(name.to_string()),
                    desc: name.clone(),
                    shape: if rule.fields.is_empty() {
                        ParseNodeShape::Opaque
                    } else {
                        ParseNodeShape::Alias(rule.rule.parse_node_kind(rules))
                    },
                    ty: Some(quote!(#ident<_>)),
                }
            })
            .chain(rules.anon.borrow().iter().map(|rule| ParseNode {
                kind: rule.parse_node_kind(rules),
                desc: rule.parse_node_desc(rules),
                shape: rules.anon_shape.borrow()[rule].clone(),
                ty: match &**rule {
                    Rule::RepeatMany(elem, _) | Rule::RepeatMore(elem, _) => match &**elem {
                        Rule::Eat(_) => Some(quote!([()])),
                        Rule::Call(r) => {
                            let ident = Src::ident(r);
                            Some(quote!([#ident<_>]))
                        }
                        _ => None,
                    },
                    _ => None,
                },
            }))
            .collect();

        out + declare_parse_node_kind(&all_parse_nodes)
            + impl_debug_for_handle_any(&all_parse_nodes)
            + code_label_decl_and_impls(rules, &code_labels)
    }
}

#[must_use]
struct Continuation<'a> {
    code_labels: &'a mut OrderMap<Rc<CodeLabel>, usize>,
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

impl<'a> Continuation<'a> {
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

    fn clone(&mut self) -> Continuation {
        Continuation {
            code_labels: self.code_labels,
            fn_code_label: self.fn_code_label,
            code_label_arms: self.code_label_arms,
            code: self.code.clone(),
            nested_frames: self.nested_frames.clone(),
        }
    }

    fn to_inline(&mut self) -> &mut Src {
        // HACK(eddyb) remove `self.code` juggling post-NLL
        let replacement = match self.code {
            Code::Inline(_) => None,
            Code::Label(ref label) => Some(Code::Inline(quote!(
                c.code = #label;
                p.threads.spawn(c, _range);
            ))),
        };
        if let Some(replacement) = replacement {
            self.code = replacement;
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
        // HACK(eddyb) remove awkward scope post-NLL
        let code = {
            let code = self.to_inline();
            quote!(#label => {#code})
        };
        self.code_label_arms.push(code);
        self.code = Code::Label(label);
    }
}

trait ContFn {
    fn apply(self, cont: Continuation) -> Continuation;
}

impl<F: FnOnce(Continuation) -> Continuation> ContFn for F {
    fn apply(self, cont: Continuation) -> Continuation {
        self(cont)
    }
}

struct Compose<F, G>(F, G);

impl<F: ContFn, G: ContFn> ContFn for Compose<F, G> {
    fn apply(self, cont: Continuation) -> Continuation {
        self.1.apply(self.0.apply(cont))
    }
}

#[must_use]
struct Thunk<F>(F);

impl<F> Thunk<F> {
    fn new(f: F) -> Self
    where
        F: FnOnce(Continuation) -> Continuation,
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

impl<F: ContFn> ContFn for Thunk<F> {
    fn apply(self, cont: Continuation) -> Continuation {
        self.0.apply(cont)
    }
}

macro_rules! thunk {
    ($($t:tt)*) => {{
        let prefix = quote!($($t)*);
        Thunk::new(move |mut cont| {
            // HACK(eddyb) remove awkward scope post-NLL
            {
                let code = cont.to_inline();
                *code += mem::replace(code, prefix);
            }
            cont
        })
    }}
}

fn pop_state<F: ContFn>(f: impl FnOnce(Src) -> Thunk<F>) -> Thunk<impl ContFn> {
    f(quote!(c.state))
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

fn push_state(state: Src) -> Thunk<impl ContFn> {
    thunk!(c.state = #state;)
        + Thunk::new(move |mut cont| {
            if let Some((ret_label, outer_fn_label)) = cont.nested_frames.pop().unwrap() {
                let inner_fn_label = mem::replace(cont.fn_code_label, outer_fn_label);
                cont.reify_as(inner_fn_label);
                cont = call(mem::replace(cont.to_label(), ret_label)).apply(cont);
            }
            cont
        })
}

fn check(condition: Src) -> Thunk<impl ContFn> {
    Thunk::new(move |mut cont| {
        // HACK(eddyb) remove awkward scope post-NLL
        {
            let code = cont.to_inline();
            *code = quote!(
                if #condition {
                    #code
                }
            );
        }
        cont
    })
}

fn call(callee: Rc<CodeLabel>) -> Thunk<impl ContFn> {
    Thunk::new(move |mut cont| {
        // HACK(eddyb) remove awkward scope post-NLL
        cont.code = {
            let label = cont.to_label().clone();
            Code::Inline(quote!(
                c.code = #label;
                p.call(Call { callee: #callee, range: _range }, c);
            ))
        };
        cont
    })
}

fn ret() -> Thunk<impl ContFn> {
    thunk!(p.ret(c, _range);)
        + Thunk::new(|mut cont| {
            assert!(cont.to_inline().is_empty());
            cont
        })
}

fn sppf_add(parse_node_kind: &ParseNodeKind, child: Src) -> Thunk<impl ContFn> {
    thunk!(p.sppf.add(#parse_node_kind, c.fn_input.subtract_suffix(_range), #child);)
}

trait ForEachThunk {
    fn for_each_thunk(self, cont: &mut Continuation, f: impl FnMut(Continuation));
}

impl<F> ForEachThunk for Thunk<F>
where
    F: ContFn,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        f(self.apply(cont.clone()));
    }
}

impl<T, U> ForEachThunk for (T, U)
where
    T: ForEachThunk,
    U: ForEachThunk,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        self.0.for_each_thunk(cont, &mut f);
        self.1.for_each_thunk(cont, &mut f);
    }
}

struct ThunkIter<I>(I);

impl<I, T> ForEachThunk for ThunkIter<I>
where
    I: Iterator<Item = T>,
    T: ForEachThunk,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        self.0.for_each(|x| {
            x.for_each_thunk(cont, &mut f);
        });
    }
}

fn parallel(thunks: impl ForEachThunk) -> Thunk<impl ContFn> {
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

fn opt(thunk: Thunk<impl ContFn>) -> Thunk<impl ContFn> {
    parallel((thunk, thunk!()))
}

fn fix<F: ContFn>(f: impl FnOnce(Rc<CodeLabel>) -> Thunk<F>) -> Thunk<impl ContFn> {
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

fn reify_as(label: Rc<CodeLabel>) -> Thunk<impl ContFn> {
    Thunk::new(|mut cont| {
        cont.reify_as(label);
        cont
    })
}

impl<Pat: Ord + Hash + RustInputPat> Rc<Rule<Pat>> {
    fn generate_parse<'a>(&'a self, rules: Option<&'a RuleMap<Pat>>) -> Thunk<impl ContFn + 'a> {
        Thunk::new(move |cont| match (&**self, rules) {
            (Rule::Empty, _) => cont,
            (Rule::Eat(pat), _) => {
                // HACK(eddyb) remove extra variables post-NLL
                let pat = pat.rust_matcher();
                let cont = check(quote!(let Some(_range) = p.input_consume_left(_range, #pat)))
                    .apply(cont);
                cont
            }
            (Rule::NegativeLookahead(pat), _) => {
                // HACK(eddyb) remove extra variables post-NLL
                let pat = pat.rust_matcher();
                let cont = check(quote!(p.input_consume_left(_range, #pat).is_none())).apply(cont);
                cont
            }
            (Rule::Call(r), _) => call(Rc::new(CodeLabel::NamedRule(r.clone()))).apply(cont),
            (Rule::Concat([left, right]), None) => {
                (left.generate_parse(None) + right.generate_parse(None)).apply(cont)
            }
            (Rule::Concat([left, right]), Some(rules)) => {
                (thunk!(assert_eq!(_range.start(), c.fn_input.start());)
                    + left.generate_parse(Some(rules))
                    + push_state(quote!(c.fn_input.subtract_suffix(_range).len()))
                    + right.generate_parse(Some(rules))
                    + pop_state(|state| sppf_add(&self.parse_node_kind(rules), state)))
                .apply(cont)
            }
            (Rule::Or(cases), None) => parallel(ThunkIter(
                cases.iter().map(|rule| rule.generate_parse(None)),
            ))
            .apply(cont),
            (Rule::Or(cases), Some(rules)) => {
                (thunk!(assert_eq!(_range.start(), c.fn_input.start());)
                    + parallel(ThunkIter(cases.iter().map(|rule| {
                        let parse_node_kind = rule.parse_node_kind(rules);
                        push_state(quote!(#parse_node_kind.to_usize()))
                            + rule.generate_parse(Some(rules))
                    })))
                    + pop_state(|state| sppf_add(&self.parse_node_kind(rules), state)))
                .apply(cont)
            }
            (Rule::Opt(rule), _) => opt(rule.generate_parse(rules)).apply(cont),
            (Rule::RepeatMany(rule, None), None) => {
                fix(|label| opt(rule.generate_parse(None) + call(label))).apply(cont)
            }
            (Rule::RepeatMany(rule, None), Some(rules)) => fix(|label| {
                let more = Rc::new(Rule::RepeatMore(rule.clone(), None));
                opt(thunk!(assert_eq!(_range.start(), c.fn_input.start());)
                    + rule.generate_parse(Some(rules))
                    + push_state(quote!(c.fn_input.subtract_suffix(_range).len()))
                    + call(label)
                    + pop_state(move |state| sppf_add(&more.parse_node_kind(rules), state)))
            })
            .apply(cont),
            (Rule::RepeatMany(elem, Some(sep)), rules) => {
                // HACK(eddyb) remove extra variables post-NLL
                let rule = Rc::new(Rule::RepeatMore(elem.clone(), Some(sep.clone())));
                let cont = opt(rule.generate_parse(rules)).apply(cont);
                cont
            }
            (Rule::RepeatMore(rule, None), None) => {
                fix(|label| rule.generate_parse(None) + opt(call(label))).apply(cont)
            }
            (Rule::RepeatMore(elem, Some(sep)), None) => {
                fix(|label| elem.generate_parse(None) + opt(sep.generate_parse(None) + call(label)))
                    .apply(cont)
            }
            (Rule::RepeatMore(rule, None), Some(rules)) => fix(|label| {
                thunk!(assert_eq!(_range.start(), c.fn_input.start());)
                    + rule.generate_parse(Some(rules))
                    + push_state(quote!(c.fn_input.subtract_suffix(_range).len()))
                    + opt(call(label))
                    + pop_state(|state| sppf_add(&self.parse_node_kind(rules), state))
            })
            .apply(cont),
            (Rule::RepeatMore(elem, Some(sep)), Some(rules)) => fix(|label| {
                thunk!(assert_eq!(_range.start(), c.fn_input.start());)
                    + elem.generate_parse(Some(rules))
                    + push_state(quote!(c.fn_input.subtract_suffix(_range).len()))
                    + opt(thunk!(assert_eq!(_range.start(), c.fn_input.start());)
                        + sep.generate_parse(None)
                        + push_state(quote!(c.fn_input.subtract_suffix(_range).len()))
                        + call(label)
                        + pop_state(|state| {
                            sppf_add(
                                &Rc::new(Rule::Concat([sep.clone(), self.clone()]))
                                    .parse_node_kind(rules),
                                state,
                            )
                        }))
                    + pop_state(|state| sppf_add(&self.parse_node_kind(rules), state))
            })
            .apply(cont),
        })
    }
}

impl<Pat: Ord + Hash + RustInputPat> Rule<Pat> {
    fn generate_traverse_shape(&self, refutable: bool, rules: &RuleMap<Pat>) -> Src {
        match self {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::NegativeLookahead(_)
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
                let left = left.generate_traverse_shape(refutable, rules);
                let right = right.generate_traverse_shape(refutable, rules);
                quote!((#left, #right))
            }
            Rule::Or(cases) => {
                let cases_idx = cases.iter().enumerate().map(|(i, _)| {
                    let i_var_ident = Src::ident(format!("_{}", i));
                    // HACK(eddyb) workaround `quote!(#i)` producing `0usize`.
                    let i = ::proc_macro2::Literal::usize_unsuffixed(i);
                    quote!(#i #i_var_ident)
                });
                let cases_node_kind = cases.iter().map(|rule| rule.parse_node_kind(rules));
                let cases_shape = cases
                    .iter()
                    .map(|rule| rule.generate_traverse_shape(true, rules));
                quote!({ #(#cases_idx: #cases_node_kind => #cases_shape,)* })
            }
            Rule::Opt(rule) => {
                let shape = rule.generate_traverse_shape(true, rules);
                quote!([#shape])
            }
        }
    }
}

fn impl_parse_with<Pat>(name: &str) -> Src
where
    Pat: RustInputPat,
{
    let ident = Src::ident(name);
    let code_label = Rc::new(CodeLabel::NamedRule(name.to_string()));
    let parse_node_kind = ParseNodeKind::NamedRule(name.to_string());
    let rust_slice_ty = Pat::rust_slice_ty();
    quote!(impl<'a, 'i, I> #ident<'a, 'i, I>
        where I: ::gll::runtime::Input<Slice = #rust_slice_ty>,
    {
        pub fn parse_with<R>(
            input: I,
            f: impl for<'b, 'i2> FnOnce(
                &'b ::gll::runtime::Parser<'i2, _P, _C, I>,
                ParseResult<'b, 'i2, I, #ident<'b, 'i2, I>>,
            ) -> R,
        ) -> R {
            ::gll::runtime::Parser::with(input, |mut parser, range| {
                let call = Call {
                    callee: #code_label,
                    range,
                };
                parser.threads.spawn(
                    Continuation {
                        code: call.callee,
                        fn_input: call.range,
                        state: 0,
                    },
                    call.range,
                );
                parse(&mut parser);
                let result = parser.memoizer.longest_result(call);
                f(&parser, result.ok_or(ParseError::NoParse).and_then(|range| {
                    let handle = Handle {
                        node: ParseNode { kind: #parse_node_kind, range },
                        parser: &parser,
                        _marker: PhantomData,
                    };
                    if range == call.range {
                        Ok(handle)
                    } else {
                        Err(ParseError::TooShort(handle))
                    }
                }))
            })
        }
    })
}

fn declare_rule<Pat>(name: &str, rule: &RuleWithNamedFields<Pat>, rules: &RuleMap<Pat>) -> Src
where
    Pat: Ord + Hash + RustInputPat,
{
    let ident = Src::ident(name);
    let variants = rule.find_variant_fields();
    let variants: Option<&[Variant<'_, Pat>]> = variants.as_ref().map(|x| &**x);

    let field_handle_ty = |rule: &Rule<_>, paths| {
        let ty = rule.field_pathset_type(paths);
        let handle_ty = quote!(Handle<'a, 'i, I, #ty>);
        if rule.field_pathset_is_refutable(paths) {
            quote!(Option<#handle_ty>)
        } else {
            handle_ty
        }
    };

    let rule_ty_def = if let Some(variants) = variants {
        let variants = variants.iter().map(|v| {
            let variant_ident = Src::ident(v.name);
            if v.fields.is_empty() {
                let field_ty = v.rule.field_type(&[]);
                quote!(#variant_ident(Handle<'a, 'i, I, #field_ty>))
            } else {
                let fields_ident = v.fields.keys().map(Src::ident);
                let fields_ty = v
                    .fields
                    .values()
                    .map(|paths| field_handle_ty(&v.rule, paths));
                quote!(#variant_ident {
                    #(#fields_ident: #fields_ty),*
                })
            }
        });
        quote!(
            #[allow(non_camel_case_types)]
            pub enum #ident<'a, 'i: 'a, I: 'a + ::gll::runtime::Input> {
                #(#variants),*
            }
        )
    } else {
        let fields_ident = rule.fields.keys().map(Src::ident);
        let fields_ty = rule
            .fields
            .values()
            .map(|paths| field_handle_ty(&rule.rule, paths));
        let marker_field = if rule.fields.is_empty() {
            Some(quote!(_marker: PhantomData<(&'a (), &'i (), I)>,))
        } else {
            None
        };
        quote!(
            #[allow(non_camel_case_types)]
            pub struct #ident<'a, 'i: 'a, I: 'a + ::gll::runtime::Input> {
                #(pub #fields_ident: #fields_ty),*
                #marker_field
            }
        )
    };
    rule_ty_def
        + rule_debug_impls(name, &rule, variants)
        + impl_rule_from_sppf(name, &rule, variants, rules)
        + impl_rule_one_and_all(name, &rule, variants, rules)
}

fn impl_rule_from_sppf<Pat>(
    name: &str,
    rule: &RuleWithNamedFields<Pat>,
    variants: Option<&[Variant<'_, Pat>]>,
    rules: &RuleMap<Pat>,
) -> Src
where
    Pat: Ord + Hash + RustInputPat,
{
    let ident = Src::ident(name);
    let field_handle_expr = |rule: &Rule<_>, paths: &OrderSet<Vec<usize>>| {
        let paths_expr = paths.iter().map(|path| {
            // HACK(eddyb) workaround `quote!(#i)` producing `0usize`.
            let path = path
                .iter()
                .cloned()
                .map(::proc_macro2::Literal::usize_unsuffixed);
            quote!(_r #(.#path)*)
        });
        if rule.field_pathset_is_refutable(paths) {
            quote!(None #(.or(#paths_expr))* .map(|node| Handle {
                node,
                parser,
                _marker: PhantomData,
            }))
        } else {
            assert_eq!(paths.len(), 1);
            quote!(Handle {
                node: #(#paths_expr)*,
                parser,
                _marker: PhantomData,
            })
        }
    };

    let methods = if let Some(variants) = variants {
        let variants_from_sppf_ident = variants
            .iter()
            .map(|v| Src::ident(format!("{}_from_sppf", v.name)));
        let variants_shape = variants
            .iter()
            .map(|v| v.rule.generate_traverse_shape(false, rules));
        let variants_body = variants.iter().map(|v| {
            let variant_ident = Src::ident(&v.name);
            if v.fields.is_empty() {
                quote!(#ident::#variant_ident(Handle {
                    node: _node,
                    parser,
                    _marker: PhantomData,
                }))
            } else {
                let fields_ident = v.fields.keys().map(Src::ident);
                let fields_expr = v
                    .fields
                    .values()
                    .map(|paths| field_handle_expr(&v.rule, paths));
                quote!(#ident::#variant_ident {
                    #(#fields_ident: #fields_expr),*
                })
            }
        });

        quote!(#(
            #[allow(non_snake_case)]
            fn #variants_from_sppf_ident(
                parser: &'a ::gll::runtime::Parser<'i, _P, _C, I>,
                _node: ParseNode<'i, _P>,
                _r: traverse!(typeof(ParseNode<'i, _P>) #variants_shape),
            ) -> Self {
                #variants_body
            }
        )*)
    } else {
        let shape = rule.rule.generate_traverse_shape(false, rules);
        let fields_ident = rule.fields.keys().map(Src::ident);
        let fields_expr = rule
            .fields
            .values()
            .map(|paths| field_handle_expr(&rule.rule, paths));
        let marker_field = if rule.fields.is_empty() {
            Some(quote!(_marker: PhantomData,))
        } else {
            None
        };
        quote!(
            fn from_sppf(
                parser: &'a ::gll::runtime::Parser<'i, _P, _C, I>,
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

    quote!(impl<'a, 'i, I: ::gll::runtime::Input> #ident<'a, 'i, I> {
        #methods
    })
}

fn impl_rule_one_and_all<Pat>(
    name: &str,
    rule: &RuleWithNamedFields<Pat>,
    variants: Option<&[Variant<'_, Pat>]>,
    rules: &RuleMap<Pat>,
) -> Src
where
    Pat: Ord + Hash + RustInputPat,
{
    let ident = Src::ident(name);
    let (one, all) = if let Some(variants) = variants {
        // FIXME(eddyb) figure out a more efficient way to reuse
        // iterators with `quote!(...)` than `.collect::<Vec<_>>()`.
        let i_ident = (0..variants.len())
            .map(|i| Src::ident(format!("_{}", i)))
            .collect::<Vec<_>>();
        let variants_from_sppf_ident = variants
            .iter()
            .map(|v| Src::ident(format!("{}_from_sppf", v.name)))
            .collect::<Vec<_>>();
        let variants_kind = variants
            .iter()
            .map(|v| v.rule.parse_node_kind(rules))
            .collect::<Vec<_>>();
        let variants_shape = variants
            .iter()
            .map(|v| v.rule.generate_traverse_shape(false, rules))
            .collect::<Vec<_>>();

        (
            quote!(
                let node = _sppf.one_choice(node)?;
                match node.kind {
                    #(#variants_kind => {
                        let r = traverse!(one(_sppf, node) #variants_shape);
                        #ident::#variants_from_sppf_ident(self.parser, node, r)
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

                _sppf.all_choices(node).flat_map(move |node| {
                    match node.kind {
                        #(#variants_kind => Iter::#i_ident(
                            traverse!(all(_sppf) #variants_shape)
                                .apply(node)
                                .map(move |r| #ident::#variants_from_sppf_ident(self.parser, node, r))
                        ),)*
                        _ => unreachable!(),
                    }
                })
            ),
        )
    } else {
        let shape = rule.rule.generate_traverse_shape(false, rules);
        (
            quote!(
                let r = traverse!(one(_sppf, node) #shape);
                #ident::from_sppf(self.parser, node, r)
            ),
            quote!(
                traverse!(all(_sppf) #shape)
                    .apply(node)
                    .map(move |r| #ident::from_sppf(self.parser, node, r))
            ),
        )
    };

    quote!(impl<'a, 'i, I> Handle<'a, 'i, I, #ident<'a, 'i, I>>
        where I: ::gll::runtime::Input,
    {
        pub fn one(self) -> Result<#ident<'a, 'i, I>, Ambiguity<Self>> {
            // HACK(eddyb) using a closure to catch `Err`s from `?`
            (|| Ok({
                let _sppf = &self.parser.sppf;
                let node = self.node.unpack_alias();
                #one
            }))().map_err(|::gll::runtime::MoreThanOne| Ambiguity(self))
        }

        pub fn all(self) -> impl Iterator<Item = #ident<'a, 'i, I>> {
            let _sppf = &self.parser.sppf;
            let node = self.node.unpack_alias();
            #all
        }
    })
}

fn rule_debug_impls<Pat>(
    name: &str,
    rule: &RuleWithNamedFields<Pat>,
    variants: Option<&[Variant<'_, Pat>]>,
) -> Src {
    rule_debug_impl(name, rule, variants) + rule_handle_debug_impl(name, !rule.fields.is_empty())
}

fn rule_debug_impl<Pat>(
    name: &str,
    rule: &RuleWithNamedFields<Pat>,
    variants: Option<&[Variant<'_, Pat>]>,
) -> Src {
    let ident = Src::ident(name);
    let body = if let Some(variants) = variants {
        let variants_pat = variants.iter().map(|v| {
            let variant_ident = Src::ident(&v.name);
            if v.fields.is_empty() {
                quote!(#ident::#variant_ident(x))
            } else {
                let fields_ident = v.fields.keys().map(Src::ident);
                let fields_var_ident = v
                    .fields
                    .keys()
                    .map(|field_name| Src::ident(format!("f_{}", field_name)));
                quote!(#ident::#variant_ident {
                    #(#fields_ident: #fields_var_ident,)*
                })
            }
        });
        let variants_body = variants.iter().map(|v| {
            let variant_path_str = format!("{}::{}", name, v.name);
            if v.fields.is_empty() {
                quote!(f.debug_tuple(#variant_path_str).field(x).finish(),)
            } else {
                let fields_debug = v.fields.iter().map(|(field_name, paths)| {
                    let field_var_ident = Src::ident(format!("f_{}", field_name));
                    if v.rule.field_pathset_is_refutable(paths) {
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
            let field_ident = Src::ident(field_name);
            if rule.rule.field_pathset_is_refutable(paths) {
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
    quote!(impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for #ident<'a, 'i, I> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            #body
        }
    })
}

fn rule_handle_debug_impl(name: &str, has_fields: bool) -> Src {
    let ident = Src::ident(name);
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
    quote!(impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, #ident<'a, 'i, I>> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:?}", self.source_info())?;
            #body
            Ok(())
        }
    })
}

fn define_parse_fn<Pat>(
    rules: &RuleMap<Pat>,
    code_labels: &mut OrderMap<Rc<CodeLabel>, usize>,
) -> Src
where
    Pat: Ord + Hash + RustInputPat,
{
    let mut code_label_arms = vec![];
    for (name, rule) in rules.named {
        let code_label = Rc::new(CodeLabel::NamedRule(name.clone()));
        let rules = if rule.fields.is_empty() {
            None
        } else {
            Some(rules)
        };
        (rule.rule.generate_parse(rules) + ret())
            .apply(Continuation {
                code_labels,
                fn_code_label: &mut code_label.clone(),
                code_label_arms: &mut code_label_arms,
                code: Code::Inline(quote!()),
                nested_frames: vec![],
            })
            .reify_as(code_label);
    }

    let rust_slice_ty = Pat::rust_slice_ty();
    quote!(fn parse<I>(p: &mut ::gll::runtime::Parser<_P, _C, I>)
        where I: ::gll::runtime::Input<Slice = #rust_slice_ty>,
    {
        while let Some(Call { callee: mut c, range: _range }) = p.threads.steal() {
            match c.code {
                #(#code_label_arms)*
            }
        }
    })
}

fn declare_parse_node_kind(all_parse_nodes: &[ParseNode]) -> Src {
    let nodes_i = (0..all_parse_nodes.len()).map(|i| {
        // HACK(eddyb) workaround `quote!(#i)` producing `0usize`.
        let i = ::proc_macro2::Literal::usize_unsuffixed(i);
        quote!(#i)
    });
    // FIXME(eddyb) figure out a more efficient way to reuse
    // iterators with `quote!(...)` than `.collect::<Vec<_>>()`.
    let nodes_kind = all_parse_nodes
        .iter()
        .map(|node| &node.kind)
        .collect::<Vec<_>>();
    let nodes_kind_ident = nodes_kind.iter().map(|kind| kind.ident());
    let nodes_desc = all_parse_nodes
        .iter()
        .map(|node| Src::new(format!("`{}`", node.desc.replace('`', "\\`"))))
        .collect::<Vec<_>>();
    let nodes_shape = all_parse_nodes.iter().map(|node| &node.shape);

    quote!(
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
        pub enum _P {
            #(
                #[doc = #nodes_desc]
                #nodes_kind_ident,
            )*
        }
        impl fmt::Display for _P {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let s = match *self {
                    #(#nodes_kind => #nodes_desc),*
                };
                write!(f, "{}", s)
            }
        }
        impl ParseNodeKind for _P {
            fn shape(self) -> ParseNodeShape<Self> {
                match self {
                    #(#nodes_kind => #nodes_shape),*
                }
            }
            fn from_usize(i: usize) -> Self {
                match i {
                    #(#nodes_i => #nodes_kind,)*
                    _ => unreachable!(),
                }
            }
            fn to_usize(self) -> usize { self as usize }
        }
    )
}

fn impl_debug_for_handle_any(all_parse_nodes: &[ParseNode]) -> Src {
    let arms = all_parse_nodes
        .iter()
        .filter_map(|ParseNode { kind, ty, .. }| {
            ty.as_ref().map(|ty| {
                quote!(#kind => write!(f, "{:?}", Handle::<_, #ty> {
                node: self.node,
                parser: self.parser,
                _marker: PhantomData,
            }),)
            })
        });
    quote!(impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, Any> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self.node.kind {
                #(#arms)*
                _ => write!(f, "{:?}", Handle::<_, ()> {
                    node: self.node,
                    parser: self.parser,
                    _marker: PhantomData,
                }),
            }
        }
    })
}

fn code_label_decl_and_impls<Pat>(
    rules: &RuleMap<Pat>,
    code_labels: &OrderMap<Rc<CodeLabel>, usize>,
) -> Src {
    let all_labels = rules
        .named
        .keys()
        .map(|r| CodeLabel::NamedRule(r.clone()))
        .chain(code_labels.iter().flat_map(|(fn_label, &counter)| {
            iter::repeat(fn_label.clone())
                .zip(0..counter)
                .map(|(parent, i)| CodeLabel::Nested { parent, i })
        }))
        .map(Rc::new)
        .collect::<Vec<_>>();
    let all_labels_ident = all_labels.iter().map(|label| label.flattened_ident());
    let all_labels_enclosing_fn = all_labels.iter().map(|label| match &**label {
        CodeLabel::Nested { parent, .. } if !code_labels.contains_key(label) => parent,
        _ => label,
    });

    quote!(
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
        pub enum _C {
            #(#all_labels_ident),*
        }
        impl CodeLabel for _C {
            fn enclosing_fn(self) -> Self {
                match self {
                    #(#all_labels => #all_labels_enclosing_fn),*
                }
            }
        }
    )
}
