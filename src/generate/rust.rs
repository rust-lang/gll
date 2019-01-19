use grammar::ParseNodeShape;
use grammar::{Grammar, MatchesEmpty, Rc, Rule, RuleWithNamedFields};
use ordermap::{OrderMap, OrderSet};
use scannerless;
use std::cell::RefCell;
use std::fmt;
use std::fmt::Write as FmtWrite;
use std::hash::Hash;
use std::io::Write;
use std::mem;
use std::ops::Add;
use std::process::{Command, Stdio};

pub trait RustInputPat {
    fn rust_slice_ty() -> String;
    fn rust_matcher(&self) -> String;
}

impl<S: AsRef<str>> RustInputPat for scannerless::Pat<S> {
    fn rust_slice_ty() -> String {
        "str".to_string()
    }
    fn rust_matcher(&self) -> String {
        match self {
            scannerless::Pat::String(s) => format!("{:?}", s.as_ref()),
            scannerless::Pat::Range(start, end) => format!("{:?}", start..=end),
        }
    }
}

type ParseNodeMap<Pat> =
    OrderMap<Rc<Rule<Pat>>, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct ParseNode {
    kind: ParseNodeKind,
    shape: ParseNodeShape<ParseNodeKind>,
    ty: Option<String>,
}

struct Variant<'a, Pat> {
    rule: Rc<Rule<Pat>>,
    name: &'a str,
    fields: OrderMap<&'a str, OrderSet<Vec<usize>>>,
}

impl<Pat: PartialEq> RuleWithNamedFields<Pat> {
    fn find_variant_fields(
        &self,
    ) -> Option<Vec<Variant<'_, Pat>>> {
        if let Rule::Or(rules) = &*self.rule {
            if self.fields.is_empty() {
                return None;
            }
            let mut variants: Vec<_> = rules
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
    fn field_pathset_type(&self, paths: &OrderSet<Vec<usize>>) -> String {
        let ty = self.field_type(paths.get_index(0).unwrap());
        for path in paths.iter().skip(1) {
            if self.field_type(path) != ty {
                return "()".to_string();
            }
        }
        ty
    }
    fn field_type(&self, path: &[usize]) -> String {
        match self {
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) => {
                assert_eq!(path, []);
                "()".to_string()
            }
            Rule::Call(r) => format!("{}<'a, 'i, I>", r),
            Rule::Concat(rules) => {
                if path.is_empty() {
                    return "()".to_string();
                }
                rules[path[0]].field_type(&path[1..])
            }
            Rule::Or(rules) => rules[path[0]].field_type(&path[1..]),
            Rule::Opt(rule) => [rule][path[0]].field_type(&path[1..]),
            Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => {
                assert_eq!(path, []);
                format!("[{}]", rule.field_type(&[]))
            }
        }
    }
}

impl<Pat: Ord + Hash + RustInputPat> Rc<Rule<Pat>> {
    fn parse_node_kind(
        &self,
        parse_nodes: &RefCell<ParseNodeMap<Pat>>,
    ) -> ParseNodeKind {
        if let Some((kind, _)) = parse_nodes.borrow().get(self) {
            return kind.clone();
        }
        let kind = match &**self {
            Rule::Empty => ParseNodeKind("()".to_string()),
            Rule::Eat(pat) => ParseNodeKind(pat.rust_matcher()),
            Rule::NegativeLookahead(pat) => ParseNodeKind(format!("!{}", pat.rust_matcher())),
            Rule::Call(r) => return ParseNodeKind(r.clone()),
            Rule::Concat([left, right]) => ParseNodeKind(format!(
                "({} {})",
                left.parse_node_kind(parse_nodes).0,
                right.parse_node_kind(parse_nodes).0
            )),
            Rule::Or(rules) => {
                assert!(rules.len() > 1);
                let mut s = String::from("(");
                for (i, rule) in rules.iter().enumerate() {
                    if i > 0 {
                        s.push_str(" | ");
                    }
                    s.push_str(&rule.parse_node_kind(parse_nodes).0);
                }
                s.push(')');
                ParseNodeKind(s)
            }
            Rule::Opt(rule) => ParseNodeKind(format!("({}?)", rule.parse_node_kind(parse_nodes).0)),
            Rule::RepeatMany(rule, None) => {
                ParseNodeKind(format!("({}*)", rule.parse_node_kind(parse_nodes).0))
            }
            Rule::RepeatMany(elem, Some(sep)) => ParseNodeKind(format!(
                "({}* % {})",
                elem.parse_node_kind(parse_nodes).0,
                sep.parse_node_kind(parse_nodes).0
            )),
            Rule::RepeatMore(rule, None) => ParseNodeKind(format!(
                // FIXME(rust-lang-nursery/rustfmt#3004) work around rustfmt removing trailing +.
                "({}+ HACK)",
                rule.parse_node_kind(parse_nodes).0
            )),
            Rule::RepeatMore(elem, Some(sep)) => ParseNodeKind(format!(
                "({}+ % {})",
                elem.parse_node_kind(parse_nodes).0,
                sep.parse_node_kind(parse_nodes).0
            )),
        };
        assert!(
            parse_nodes
                .borrow_mut()
                .insert(self.clone(), (kind.clone(), None))
                .is_none()
        );
        kind
    }

    fn fill_parse_node_shape(
        &self,
        parse_nodes: &RefCell<
            OrderMap<Self, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>,
        >,
    ) {
        if parse_nodes.borrow()[self].1.is_some() {
            return;
        }
        let shape = match &**self {
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) => ParseNodeShape::Opaque,
            Rule::Call(_) => unreachable!(),
            Rule::Concat([left, right]) => ParseNodeShape::Split(
                left.parse_node_kind(parse_nodes),
                right.parse_node_kind(parse_nodes),
            ),
            Rule::Or(_) => ParseNodeShape::Choice,
            Rule::Opt(rule) => ParseNodeShape::Opt(rule.parse_node_kind(parse_nodes)),
            Rule::RepeatMany(elem, sep) => ParseNodeShape::Opt(
                Rc::new(Rule::RepeatMore(elem.clone(), sep.clone())).parse_node_kind(parse_nodes),
            ),
            Rule::RepeatMore(rule, None) => ParseNodeShape::Split(
                rule.parse_node_kind(parse_nodes),
                Rc::new(Rule::RepeatMany(rule.clone(), None)).parse_node_kind(parse_nodes),
            ),
            Rule::RepeatMore(elem, Some(sep)) => ParseNodeShape::Split(
                elem.parse_node_kind(parse_nodes),
                Rc::new(Rule::Opt(Rc::new(Rule::Concat([
                    sep.clone(),
                    self.clone(),
                ]))))
                .parse_node_kind(parse_nodes),
            ),
        };
        parse_nodes.borrow_mut().get_mut(self).unwrap().1 = Some(shape);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ParseNodeKind(String);

impl fmt::Display for ParseNodeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "P!({})", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CodeLabel(String);

impl fmt::Display for CodeLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "_C::{}", self.0)
    }
}

#[derive(Default)]
pub struct Options {
    /// Disable generating macros (e.g. `P!(...)` sugar for `_P::...`).
    pub no_macros: bool,

    _nonexhaustive: (),
}

macro_rules! put {
    ($out:ident, $($x:expr),*) => {{ $(write!($out, "{}", $x).unwrap();)* }}
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<Pat: Ord + Hash + MatchesEmpty + RustInputPat> Grammar<Pat> {
    pub fn generate_rust(&self) -> String {
        self.generate_rust_with_options(Options::default())
    }
    pub fn generate_rust_with_options(&self, options: Options) -> String {
        self.check();

        let parse_nodes = RefCell::new(OrderMap::new());
        let mut named_parse_nodes = vec![];
        let mut code_labels = OrderMap::new();

        let mut out = String::new();

        let rust_slice_ty = Pat::rust_slice_ty();
        for (name, rule) in &self.rules {
            declare_rule(name, rule, &parse_nodes, &mut out);
            impl_parse_with(name, &rust_slice_ty, &mut out);
        }

        define_parse_fn(&mut named_parse_nodes, &parse_nodes, &mut code_labels, &self.rules, &mut out);

        let mut i = 0;
        while i < parse_nodes.borrow().len() {
            let rule = parse_nodes.borrow().get_index(i).unwrap().0.clone();
            rule.fill_parse_node_shape(&parse_nodes);
            i += 1;
        }
        let mut all_parse_nodes: Vec<ParseNode> = named_parse_nodes.into_iter().map(|(k, s)| {
            ParseNode { kind: k.clone(), shape: s, ty: Some(format!("{}<_>", k.0)) }
        }).chain(parse_nodes.into_inner().into_iter().map(|(r, (k, s))| {
            ParseNode {
                kind: k,
                shape: s.unwrap(),
                ty: match &*r {
                    Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => match &**rule {
                        Rule::Eat(_) => Some("[()]".to_string()),
                        Rule::Call(r) => Some(format!("[{}<_>]", r)),
                        _ => None,
                    },
                    _ => None,
                },
            }
        })).collect();
        all_parse_nodes.sort();

        put!(out, "#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]");
        put!(out, "pub enum _P {");
        for i in 0..all_parse_nodes.len() {
            put!(out," _", i, ",");
        }
        put!(out, "}");

        // substitution mappings to use if macros are disabled
        let substitute_opt: Option<Vec<(String, String)>>;
        let mut macros = String::new();
        if options.no_macros {
            substitute_opt = Some(all_parse_nodes.iter().enumerate().map(|(i, ParseNode { kind, .. })| {
                (kind.to_string(), format!("_P::_{}", i))
            }).collect());
        } else {
            substitute_opt = None;

            put!(macros, "macro_rules! P {");
            for (i, ParseNode { kind, .. }) in all_parse_nodes.iter().enumerate() {
                put!(macros, "(", kind.0, ") => (_P::_", i, ");");
            }
            put!(macros, "}");
        }

        p_impls(&all_parse_nodes, &mut out);
        impl_debug_for_handle_any(&all_parse_nodes, &mut out);
        c_declaration_and_impls(&self.rules, &code_labels, &mut out);

        let prefix = String::from(concat!(
            include_str!("templates/imports.rs"),
            include_str!("templates/header.rs")
        ));

        // Macros must be defined before any usages. The `prefix` does not use any macros.
        let mut out = prefix + &*macros + &*out;
 
        // In the case of `no_macros`, replace macro invocations of `P!(...)` with `_P::...`
        if let Some(substitute) = substitute_opt {
            for (from, to) in substitute {
                out = out.replace(&from, &to);
            }
        }

        rustfmt(&mut out);
        out
    }
}

#[must_use]
struct Continuation<'a> {
    code_labels: &'a mut OrderMap<CodeLabel, usize>,
    fn_code_label: &'a mut CodeLabel,
    code_label_arms: &'a mut String,
    code: Code,
    nested_frames: Vec<Option<(CodeLabel, CodeLabel)>>,
}

#[derive(Clone)]
enum Code {
    Inline(String),
    Label(CodeLabel),
}

impl<'a> Continuation<'a> {
    fn next_code_label(&mut self) -> CodeLabel {
        let counter = self
            .code_labels
            .entry(self.fn_code_label.clone())
            .or_insert(0);
        let label = CodeLabel(format!("{}__{}", self.fn_code_label.0, counter));
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

    fn to_inline(&mut self) -> &mut String {
        // HACK(eddyb) remove `self.code` juggling post-NLL
        let replacement = match self.code {
            Code::Inline(_) => None,
            Code::Label(ref label) => Some(Code::Inline(format!(
                "
                c.code = {};
                p.threads.spawn(c, _range);",
                label
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

    fn to_label(&mut self) -> &mut CodeLabel {
        match self.code {
            Code::Label(ref mut label) => label,
            Code::Inline(_) => {
                let label = self.next_code_label();
                self.reify_as(label);
                self.to_label()
            }
        }
    }

    #[cfg_attr(rustfmt, rustfmt_skip)]
    fn reify_as(&mut self, label: CodeLabel) {
        let code = format!("
            {} => {{{}
            }}", label, self.to_inline());
        self.code_label_arms.push_str(&code);
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
    ($($x:expr),*) => {{
        let mut prefix = String::new();
        $(write!(prefix, "{}", $x).unwrap();)*
        Thunk::new(move |mut cont| {
            cont.to_inline().insert_str(0, &prefix);
            cont
        })
    }}
}

fn pop_state<F: ContFn>(f: impl FnOnce(&str) -> Thunk<F>) -> Thunk<impl ContFn> {
    f("c.state") + Thunk::new(|mut cont| {
        if let Some(&None) = cont.nested_frames.last() {
            *cont.nested_frames.last_mut().unwrap() =
                Some((cont.to_label().clone(), cont.fn_code_label.clone()));
            *cont.fn_code_label = cont.next_code_label();
            cont.code_labels.insert(cont.fn_code_label.clone(), 0);
            cont.code = Code::Inline(String::new());
            cont = ret().apply(cont);
        }
        cont.nested_frames.push(None);
        cont
    })
}

fn push_state(state: &str) -> Thunk<impl ContFn> {
    thunk!(
        "
                c.state = ",
        state,
        ";"
    ) + Thunk::new(move |mut cont| {
        if let Some((ret_label, outer_fn_label)) = cont.nested_frames.pop().unwrap() {
            let inner_fn_label = mem::replace(cont.fn_code_label, outer_fn_label);
            cont.reify_as(inner_fn_label);
            cont = call(mem::replace(cont.to_label(), ret_label)).apply(cont);
        }
        cont
    })
}

fn check<'a>(condition: &'a str) -> Thunk<impl ContFn + 'a> {
    Thunk::new(move |mut cont| {
        // HACK(eddyb) remove awkward scope post-NLL
        {
            let code = cont.to_inline();
            *code = format!(
                "
                    if {} {{{}
                    }}",
                condition,
                code.replace("\n", "\n    ")
            );
        }
        cont
    })
}

fn call(callee: CodeLabel) -> Thunk<impl ContFn> {
    Thunk::new(move |mut cont| {
        cont.code = Code::Inline(format!(
            "
                c.code = {};
                p.call(Call {{ callee: {}, range: _range }}, c);",
            cont.to_label(),
            callee
        ));
        cont
    })
}

fn ret() -> Thunk<impl ContFn> {
    thunk!(
        "
                p.ret(c, _range);"
    ) + Thunk::new(|mut cont| {
        assert_eq!(cont.to_inline(), "");
        cont
    })
}

fn sppf_add(parse_node_kind: &ParseNodeKind, child: &str) -> Thunk<impl ContFn> {
    thunk!(
        "
                p.sppf.add(",
        parse_node_kind,
        ", c.fn_input.subtract_suffix(_range), ",
        child,
        ");"
    )
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
        let mut code = String::new();
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
            code.push_str(child_cont.to_inline());
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
    parallel((thunk, thunk!("")))
}

fn fix<F: ContFn>(f: impl FnOnce(CodeLabel) -> Thunk<F>) -> Thunk<impl ContFn> {
    Thunk::new(|mut cont| {
        let nested_frames = mem::replace(&mut cont.nested_frames, vec![]);
        let ret_label = cont.to_label().clone();
        cont.code = Code::Inline(String::new());
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

fn reify_as(label: CodeLabel) -> Thunk<impl ContFn> {
    Thunk::new(|mut cont| {
        cont.reify_as(label);
        cont
    })
}

impl<Pat: Ord + Hash + RustInputPat> Rc<Rule<Pat>> {
    #[cfg_attr(rustfmt, rustfmt_skip)]
    fn generate_parse<'a>(
        &'a self,
        parse_nodes: Option<&'a RefCell<OrderMap<Self, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>>>
    ) -> Thunk<impl ContFn + 'a> {
        Thunk::new(move |cont| match (&**self, parse_nodes) {
            (Rule::Empty, _) => cont,
            (Rule::Eat(pat), _) => {
                // HACK(eddyb) remove extra variables post-NLL
                let code = format!("let Some(_range) = p.input_consume_left(_range, {})", pat.rust_matcher());
                let cont = check(&code).apply(cont);
                cont
            }
            (Rule::NegativeLookahead(pat), _) => {
                // HACK(eddyb) remove extra variables post-NLL
                let code = format!("p.input_consume_left(_range, {}).is_none()", pat.rust_matcher());
                let cont = check(&code).apply(cont);
                cont
            }
            (Rule::Call(r), _) => call(CodeLabel(r.clone())).apply(cont),
            (Rule::Concat([left, right]), None) => (
                left.generate_parse(None) +
                right.generate_parse(None)
            ).apply(cont),
            (Rule::Concat([left, right]), Some(parse_nodes)) => (
                thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                left.generate_parse(Some(parse_nodes)) +
                push_state("c.fn_input.subtract_suffix(_range).len()") +
                right.generate_parse(Some(parse_nodes)) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            ).apply(cont),
            (Rule::Or(rules), None) => {
                parallel(ThunkIter(rules.iter().map(|rule| {
                    rule.generate_parse(None)
                }))).apply(cont)
            }
            (Rule::Or(rules), Some(parse_nodes)) => (
                thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                parallel(ThunkIter(rules.iter().map(|rule| {
                    push_state(&format!("{}.to_usize()", rule.parse_node_kind(parse_nodes))) +
                    rule.generate_parse(Some(parse_nodes))
                }))) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            ).apply(cont),
            (Rule::Opt(rule), _) => opt(rule.generate_parse(parse_nodes)).apply(cont),
            (Rule::RepeatMany(rule, None), None) => fix(|label| {
                opt(rule.generate_parse(None) + call(label))
            }).apply(cont),
            (Rule::RepeatMany(rule, None), Some(parse_nodes)) => fix(|label| {
                let more = Rc::new(Rule::RepeatMore(rule.clone(), None));
                opt(
                    thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                    rule.generate_parse(Some(parse_nodes)) +
                    push_state("c.fn_input.subtract_suffix(_range).len()") +
                    call(label) +
                    pop_state(move |state| sppf_add(&more.parse_node_kind(parse_nodes), state))
                )
            }).apply(cont),
            (Rule::RepeatMany(elem, Some(sep)), parse_nodes) => {
                // HACK(eddyb) remove extra variables post-NLL
                let rule = Rc::new(Rule::RepeatMore(elem.clone(), Some(sep.clone())));
                let cont = opt(rule.generate_parse(parse_nodes)).apply(cont);
                cont
            }
            (Rule::RepeatMore(rule, None), None) => fix(|label| {
                rule.generate_parse(None) + opt(call(label))
            }).apply(cont),
            (Rule::RepeatMore(elem, Some(sep)), None) => fix(|label| {
                elem.generate_parse(None) + opt(sep.generate_parse(None) + call(label))
            }).apply(cont),
            (Rule::RepeatMore(rule, None), Some(parse_nodes)) => fix(|label| {
                thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                rule.generate_parse(Some(parse_nodes)) +
                push_state("c.fn_input.subtract_suffix(_range).len()") +
                opt(call(label)) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            }).apply(cont),
            (Rule::RepeatMore(elem, Some(sep)), Some(parse_nodes)) => fix(|label| {
                thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                elem.generate_parse(Some(parse_nodes)) +
                push_state("c.fn_input.subtract_suffix(_range).len()") +
                opt(
                    thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                    sep.generate_parse(None) +
                    push_state("c.fn_input.subtract_suffix(_range).len()") +
                    call(label) +
                    pop_state(|state| {
                        sppf_add(&Rc::new(Rule::Concat([
                            sep.clone(),
                            self.clone(),
                        ])).parse_node_kind(parse_nodes), state)
                    })
                ) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            }).apply(cont),
        })
    }
}

impl<Pat: Ord + Hash + RustInputPat> Rule<Pat> {
    fn generate_traverse_shape(
        &self,
        refutable: bool,
        parse_nodes: &RefCell<
            OrderMap<Rc<Self>, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>,
        >,
    ) -> String {
        match self {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::NegativeLookahead(_)
            | Rule::Call(_)
            | Rule::RepeatMany(..)
            | Rule::RepeatMore(..) => {
                if refutable {
                    "?".to_string()
                } else {
                    "_".to_string()
                }
            }
            Rule::Concat([left, right]) => format!(
                "({}, {})",
                left.generate_traverse_shape(refutable, parse_nodes),
                right.generate_traverse_shape(refutable, parse_nodes)
            ),
            Rule::Or(rules) => {
                let mut s = String::from("{ ");
                for (i, rule) in rules.iter().enumerate() {
                    write!(
                        s,
                        "{} _{}: {} => {},",
                        i,
                        i,
                        rule.parse_node_kind(parse_nodes),
                        rule.generate_traverse_shape(true, parse_nodes)
                    ).unwrap();
                }
                write!(s, " }}").unwrap();
                s
            }
            Rule::Opt(rule) => format!("[{}]", rule.generate_traverse_shape(true, parse_nodes)),
        }
    }
}

fn impl_parse_with(name: &str, rust_slice_ty: &str, out: &mut String) {
    put!(out, "
    impl<'a, 'i, I: ::gll::runtime::Input<Slice = ", rust_slice_ty, ">> ", name, "<'a, 'i, I> {
        pub fn parse_with<R>(
            input: I,
            f: impl for<'b, 'i2> FnOnce(
                &'b ::gll::runtime::Parser<'i2, _P, _C, I>,
                ParseResult<'b, 'i2, I, ", name, "<'b, 'i2, I>>,
            ) -> R,
        ) -> R {
            ::gll::runtime::Parser::with(input, |mut parser, range| {
                let call = Call {
                    callee: ", CodeLabel(name.to_string()), ",
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
                        node: ParseNode { kind: ", ParseNodeKind(name.to_string()), ", range },
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
    }")
}

fn declare_rule<Pat>(
    name: &str,
    rule: &RuleWithNamedFields<Pat>,
    parse_nodes: &RefCell<ParseNodeMap<Pat>>,
    out: &mut String,
)
where
    Pat: Ord + Hash + RustInputPat,
{
    let variants = rule.find_variant_fields();

    // Declare rule type
    if let Some(variants) = &variants {
        put!(out, "pub enum ", name, "<'a, 'i: 'a, I: 'a + ::gll::runtime::Input> {");
        for Variant { rule, name: variant_name, fields } in variants {
            if fields.is_empty() {
                put!(out, variant_name, "(Handle<'a, 'i, I, ", rule.field_type(&[]), ">),");
            } else {
                put!(out, variant_name, " {");
                for (field_name, paths) in fields {
                    let refutable = rule.field_pathset_is_refutable(paths);
                    put!(out, field_name, ": ");
                    if refutable {
                        put!(out, "Option<");
                    }
                    put!(out, "Handle<'a, 'i, I, ", rule.field_pathset_type(paths), ">");
                    if refutable {
                        put!(out, ">");
                    }
                    put!(out, ",");
                }
                put!(out, "},");
            }
        }
        put!(out, "}");
    } else {
        put!(out, "#[allow(non_camel_case_types)]");
        put!(out, "pub struct ", name, "<'a, 'i: 'a, I: 'a + ::gll::runtime::Input> {");
        for (field_name, paths) in &rule.fields {
            let refutable = rule.rule.field_pathset_is_refutable(paths);
            put!(out, "pub ", field_name, ": ");
            if refutable {
                put!(out, "Option<");
            }
            put!(out, "Handle<'a, 'i, I, ", rule.rule.field_pathset_type(paths), ">");
            if refutable {
                put!(out, ">");
            }
            put!(out, ",");
        }
        if rule.fields.is_empty() {
            put!(out, "_marker: PhantomData<(&'a (), &'i (), I)>,");
        }
        put!(out, "}");
    }

    // Implement `Debug`;
    rule_debug_impls(name, &rule, variants.as_ref().map(|x| &**x), out);

    put!(out, "impl<'a, 'i, I: ::gll::runtime::Input> ", name, "<'a, 'i, I> {"); // -- start impl
    if let Some(variants) = &variants {
        for Variant { rule, name: variant_name, fields } in variants {
            put!(out, "
                #[allow(non_snake_case)]
                fn ", variant_name, "_from_sppf(
                    parser: &'a ::gll::runtime::Parser<'i, _P, _C, I>,
                    _node: ParseNode<'i, _P>,
                    _r: traverse!(typeof(ParseNode<'i, _P>) ", rule.generate_traverse_shape(false, parse_nodes), "),
                ) -> Self {" //-- start fn
            );
            if fields.is_empty() {
                put!(out, name, "::", variant_name, "(Handle { node: _node, parser, _marker: PhantomData, })");
            } else {
                put!(out, name, "::", variant_name, " {"); // --start variant
                for (field_name, paths) in fields {
                    if rule.field_pathset_is_refutable(&paths) {
                        put!(out, field_name, ": None.or(_r"); // -- start paren
                        for path in paths {
                            for p in path {
                                put!(out, " .", p);
                            }
                        }
                        put!(out, ").map(|node| Handle {
                            node,
                            parser,
                            _marker: PhantomData,
                        }),"); // -- end paren
                    } else {
                        put!(out, field_name, ": Handle { node: _r");
                        assert_eq!(paths.len(), 1);
                        for p in paths.get_index(0).unwrap() {
                            put!(out, " .", p);
                        }
                        put!(out, ", parser, _marker: PhantomData, },");
                    }
                }
                put!(out, "}"); // -- end variant
            }
            put!(out, "}"); // -- end fn
        }
    } else {
        put!(out, "
            fn from_sppf(
                parser: &'a ::gll::runtime::Parser<'i, _P, _C, I>,
                _node: ParseNode<'i, _P>,
                _r: traverse!(typeof(ParseNode<'i, _P>) ", rule.rule.generate_traverse_shape(false, &parse_nodes), "),
            ) -> Self {", // -- start fn
            name,
            "{"); // -- start struct
        for (field_name, paths) in &rule.fields {
            if rule.rule.field_pathset_is_refutable(paths) {
                put!(out, field_name, ": None");
                for path in paths {
                    put!(out, ".or(_r");
                    for p in path {
                        put!(out, " .", p);
                    }
                    put!(out, ")");
                }
                put!(out, ".map(|node| Handle {
                    node,
                    parser,
                    _marker: PhantomData,
                }),");
            } else {
                put!(out, field_name, ": Handle { node: _r");
                assert_eq!(paths.len(), 1);
                for p in paths.get_index(0).unwrap() {
                    put!(out, " .", p);
                }
                put!(out, ", parser, _marker: PhantomData, },");
            }
        }

        if rule.fields.is_empty() {
            put!(out, "_marker: PhantomData,");
        }
        put!(out, "}}"); // -- end struct -- end fn
    }
    put!(out, "}"); // -- end impl

    put!(out, "
        impl<'a, 'i, I: ::gll::runtime::Input> Handle<'a, 'i, I, ", name, "<'a, 'i, I>> {
            pub fn one(self) -> Result<", name, "<'a, 'i, I>, Ambiguity<Self>> {
                // HACK(eddyb) using a closure to catch `Err`s from `?`
                (|| Ok({
                    #[allow(unused_variables)]
                    let sppf = &self.parser.sppf;
                    let node = self.node.unpack_alias();");
    {
        if let Some(variants) = &variants {
            put!(out, "
                let node = sppf.one_choice(node)?;
                match node.kind {");
            for Variant { rule, name: variant_name, .. } in variants {
                put!(out, rule.parse_node_kind(&parse_nodes), " => {
                    let r = traverse!(one(sppf, node) ", rule.generate_traverse_shape(false, &parse_nodes), ");
                    ", name, "::", variant_name, "_from_sppf(self.parser, node, r)
                }");
            }
            put!(out, "_ => unreachable!()");
            put!(out, "}");
        } else {
            put!(out, "
                let r = traverse!(one(sppf, node) ", rule.rule.generate_traverse_shape(false, &parse_nodes), ");
                ", name, "::from_sppf(self.parser, node, r)");
        }
    }
    put!(out, "
        }))().map_err(|::gll::runtime::MoreThanOne| Ambiguity(self))
        }
        pub fn all(self) -> impl Iterator<Item = ", name, "<'a, 'i, I>> {
            #[allow(unused_variables)]
            let sppf = &self.parser.sppf;
            let node = self.node.unpack_alias();");
    if let Some(variants) = &variants {
        put!(out, "#[derive(Clone)] enum Iter<");
        for i in 0..variants.len() {
            put!(out, "_", i, ",");
        }
        put!(out, "> {");
        for i in 0..variants.len() {
            put!(out, "_", i, "(_", i, "),");
        }
        put!(out, "}");
        put!(out, "impl<T, ");
        for i in 0..variants.len() {
            put!(out, "_", i, ": Iterator<Item = T>,");
        }
        put!(out, "> Iterator for Iter<");
        for i in 0..variants.len() {
            put!(out, "_", i, ",");
        }
        put!(out, ">
        {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                match self {");
                    for i in 0..variants.len() {
                        put!(out, "
                    Iter::_", i, "(iter) => iter.next(),");
                    }
                    put!(out, "
                }
            }
        }
        sppf.all_choices(node).flat_map(move |node| {
            match node.kind {");
                    for (i, Variant { rule, name: variant_name,  .. }) in
                        variants.iter().enumerate()
                    {
                        put!(out, "
                ", rule.parse_node_kind(&parse_nodes), " => Iter::_", i, "(
                    traverse!(all(sppf) ", rule.generate_traverse_shape(false, &parse_nodes), ")
                        .apply(node)
                        .map(move |r| ", name, "::", variant_name, "_from_sppf(self.parser, node, r))
                ),");
                    }
                    put!(out, "
                _ => unreachable!(),
            }
        })");
    } else {
        put!(out, "
            traverse!(all(sppf) ", rule.rule.generate_traverse_shape(false, &parse_nodes), ")
                .apply(node)
                .map(move |r| ", name, "::from_sppf(self.parser, node, r))");
    }
    put!(out, "} }");
}

fn rule_debug_impls<Pat>(
    name: &str,
    rule: &RuleWithNamedFields<Pat>,
    variants: Option<&[Variant<'_, Pat>]>,
    out: &mut String
) {
    rule_debug_impl(name, rule, variants, out);
    rule_handle_debug_impl(name, !rule.fields.is_empty(), out);
}

fn rule_debug_impl<Pat>(
    name: &str,
    rule: &RuleWithNamedFields<Pat>,
    variants: Option<&[Variant<'_, Pat>]>,
    out: &mut String
) {
    put!(out, "impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for ", name, "<'a, 'i, I> {");
    put!(out, "fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {");
    if let Some(variants) = variants {
        put!(out, "match self {");
        for Variant { rule: variant_rule, name: variant_name, fields } in variants {
            if fields.is_empty() {
                put!(out, name, "::", variant_name,
                    "(x) => f.debug_tuple(\"",
                    name, "::", variant_name, 
                    "\").field(x).finish(),");
            } else {
                put!(out, name, "::", variant_name, " { ");
                for field_name in fields.keys() {
                    put!(out, field_name, ": f_", field_name, ", ");
                }
                put!(out, "} => {");
                {
                    put!(out, "let mut d = f.debug_struct(\"", name, "::", variant_name, "\");");
                    for (field_name, paths) in fields {
                        if variant_rule.field_pathset_is_refutable(paths) {
                            put!(out, "if let Some(field) = f_", field_name, " { d.field(\"", field_name,"\", field); }");
                        } else {
                            put!(out, "d.field(\"", field_name,"\", f_", field_name, ");");
                        }
                    }
                    put!(out, "d.finish()");
                }
                put!(out, "}");
            }
        }
        put!(out, "}");
    } else {
        put!(out, "let mut d = f.debug_struct(\"", name, "\");");
        for (field_name, paths) in &rule.fields {
            if rule.rule.field_pathset_is_refutable(paths) {
                put!(out, "if let Some(ref field) = self.", field_name, " {
                    d.field(\"", field_name,"\", field);
                }");
            } else {
                put!(out, "d.field(\"", field_name,"\", &self.", field_name, ");");
            }
        }
        put!(out, "d.finish()");
    }
    put!(out, "}"); // end of `fmt`
    put!(out, "}"); // end of `Debug for ...`
}

fn rule_handle_debug_impl(name: &str, has_fields: bool, out: &mut String) {
    if !has_fields {
        put!(out, "
            impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, ", name, "<'a, 'i, I>> {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    write!(f, \"{:?}\", self.source_info())
                }
            }
        ");
    } else {
        put!(out, "
            impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, ", name, "<'a, 'i, I>> {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    write!(f, \"{:?} => \", self.source_info())?;
                    let mut first = true;
                    for x in self.all() {
                        if !first {
                            write!(f, \" | \")?;
                        }
                        first = false;
                        fmt::Debug::fmt(&x, f)?;
                    }
                    Ok(())
                }
            }
        ")
    }
}

fn define_parse_fn<Pat>(
    named_parse_nodes: &mut Vec<(ParseNodeKind, ParseNodeShape<ParseNodeKind>)>,
    parse_nodes: &RefCell<ParseNodeMap<Pat>>,
    code_labels: &mut OrderMap<CodeLabel, usize>,
    rules: &OrderMap<String, RuleWithNamedFields<Pat>>,
    out: &mut String,
)
where
    Pat: Ord + Hash + RustInputPat,
{
    put!(out, "
        fn parse<I>(p: &mut ::gll::runtime::Parser<_P, _C, I>)
        where I: ::gll::runtime::Input<Slice = ", Pat::rust_slice_ty() ,">
        {
            while let Some(Call { callee: mut c, range: _range }) = p.threads.steal() {
                match c.code {");
    for (name, rule) in rules {
        let parse_nodes = if rule.fields.is_empty() {
            None
        } else {
            Some(parse_nodes)
        };
        let code_label = CodeLabel(name.to_string());
        let parse_node_kind = ParseNodeKind(name.to_string());
        let shape = if let Some(parse_nodes) = parse_nodes {
            ParseNodeShape::Alias(rule.rule.parse_node_kind(parse_nodes))
        } else {
            ParseNodeShape::Opaque
        };
        named_parse_nodes.push((parse_node_kind.clone(), shape));

        put!(out, (
            reify_as(code_label.clone()) +
            rule.rule.generate_parse(parse_nodes) +
            ret()
        ).apply(Continuation {
            code_labels,
            fn_code_label: &mut code_label.clone(),
            code_label_arms: &mut String::new(),
            code: Code::Inline(String::new()),
            nested_frames: vec![],
        }).code_label_arms);
    }
    put!(out, "} } }");
}

fn p_impls(all_parse_nodes: &[ParseNode], out: &mut String) {
    put!(out, "impl fmt::Display for _P {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let s = match *self {"); // -- start fmt::Display -- start fn fmt -- start match
    for ParseNode { kind, .. } in all_parse_nodes {
        put!(out, kind, " => ", format!("{:?}", kind.0), ",");
    }
    put!(out, "};"); // -- end match
    put!(out, "write!(f, \"{}\", s)");
    put!(out, "} }"); // -- end fn fmt -- end fmt::Display

    put!(out, "impl ParseNodeKind for _P {
        fn shape(self) -> ParseNodeShape<Self> {
            match self {"); // -- start ParseNodeKind for _P -- start fn shape -- start match
    for ParseNode { kind, shape, .. } in all_parse_nodes {
        put!(out, kind, " => ParseNodeShape::", shape, ",");
    }
    put!(out, "} }"); // -- end match --end fn shape

    put!(out, "fn from_usize(i: usize) -> Self {
        match i {"); // -- start from_usize -- start match

    for i in 0..all_parse_nodes.len() {
        put!(out, "
        ", i, " => _P::_", i, ",");
    }
    put!(out, "_ => unreachable!(),");
    put!(out, "} }"); // -- end match -- end from_usize
    put!(out, "fn to_usize(self) -> usize { self as usize }");
    put!(out, "}"); // -- end ParseNodeKind for _P
}

fn impl_debug_for_handle_any(all_parse_nodes: &[ParseNode], out: &mut String) {
    put!(out, "impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, Any> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self.node.kind {"); // -- start fmt::Debug -- start fn fmt -- start match
    for ParseNode { kind, shape: _, ty } in all_parse_nodes {
        if let Some(ty) = ty {
            put!(out, "
        ", kind, " => write!(f, \"{:?}\", Handle::<_, ", ty, "> {
            node: self.node,
            parser: self.parser,
            _marker: PhantomData,
        }),");
        }
    }
    put!(out, "
        _ => write!(f, \"{:?}\", Handle::<_, ()> {
            node: self.node,
            parser: self.parser,
            _marker: PhantomData,
        }),");
    put!(out, "} } }"); // -- end fmt::Debug -- end fn fmt -- end match
}

fn c_declaration_and_impls<Pat>(
    rules: &OrderMap<String, RuleWithNamedFields<Pat>>,
    code_labels: &OrderMap<CodeLabel, usize>,
    out: &mut String,
)
{
    put!(out, "
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
        pub enum _C {");
    for (name, _) in rules {
        put!(out, name, ",");
    }
    for (fn_label, &counter) in code_labels {
        for i in 0..counter {
            put!(out, fn_label.0, "__", i, ",");
        }
    }
    put!(out, "}");

    put!(out, "impl CodeLabel for _C {
        fn enclosing_fn(self) -> Self {
            match self {"); // -- start CodeLabel -- start fn enclosing_fn -- start match
    for (name, _) in rules {
        put!(out, "_C::", name, " => _C::", name, ",");
    }
    for (fn_label, &counter) in code_labels {
        for i in 0..counter {
            let label = CodeLabel(format!("{}__{}", fn_label.0, i));
            let code_label = if code_labels.contains_key(&label) { &label } else { fn_label };
            put!(out, label, " => ", code_label, ",");
        }
    }
    put!(out, "} } }"); // -- end match -- end fn enclosing_fn -- end CodeLabel
}

fn rustfmt(out: &mut String) {
    // HACK(eddyb) don't try to feed input to `rustfmt` without
    // knowing that it will at least try to read it.
    // *Somehow* (despite libstd ignoring it) we can get SIGPIPE.
    let has_rustfmt = Command::new("rustfmt")
        .arg("-V")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .and_then(|child| child.wait_with_output().map(|o| o.status.success()))
        .unwrap_or(false);

    if !has_rustfmt { return; }

    let rustfmt = Command::new("rustfmt")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn();

    if let Ok(mut rustfmt) = rustfmt {
        let stdin_result = {
            let stdin = rustfmt.stdin.as_mut().unwrap();
            stdin.write_all(out.as_bytes())
        };

        if let Ok(output) = rustfmt.wait_with_output() {
            if output.status.success() {
                stdin_result.unwrap();
                *out = String::from_utf8_lossy(&output.stdout).to_string();
            }
        }
    }
}
