//! Recursive type definitions (step L1.23, DESIGN.md sec:type_language): a group of mutually
//! recursive definitions, checked when it is defined and instantiated at its arguments.
//!
//! A group is accepted when it is
//! - *contractive*: every cycle of recursive occurrences passes through a constructor (a tuple
//!   component, an atom payload, or a morphism bound or value), so a type unfolds to its
//!   parts in finitely many steps;
//! - *regular*: every recursive occurrence passes the group's parameters unchanged, so a type
//!   has finitely many components;
//! - *monotone in emptiness*: no recursive occurrence stands under a complement, to the right
//!   of `\`, or in the guarantee of a morphism type whose value type may be empty or mentions
//!   the group, since `type T = (T) -> (#a & #b)` is inhabited exactly when it is empty.
//!
//! A value type that mentions a parameter may be empty when that parameter is: it counts as
//! possibly empty when it is empty with every parameter empty, or has a parameter under a
//! complement or to the right of `\`, where a larger argument shrinks it.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::{Arc, OnceLock};

use super::Type;

/// A type expression in a definition's body.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    /// The definition's parameter of this index.
    Param(usize),
    /// The group's definition of this index, at these arguments.
    Ref(usize, Vec<Expr>),
    /// A type that does not mention the group.
    Type(Type),
    /// `a | b | …`.
    Union(Vec<Expr>),
    /// `a & b & …`.
    And(Vec<Expr>),
    /// `!a`.
    Not(Box<Expr>),
    /// `a \ b`.
    Diff(Box<Expr>, Box<Expr>),
    /// `(a, b, …)`.
    Tuple(Vec<Expr>),
    /// `#name(a, b, …)`, whose payload is the tuple of its items.
    Atom(String, Vec<Expr>),
    /// The morphism type with this guarantee, permission and value type.
    Morphism(Box<Expr>, Box<Expr>, Box<Expr>),
}

impl Expr {
    /// `K -> V`, exact.
    pub fn exact(key: Expr, value: Expr) -> Expr {
        Expr::Morphism(Box::new(key.clone()), Box::new(key), Box::new(value))
    }

    /// Applies `f` to `self` and every expression in it.
    fn walk(&self, f: &mut impl FnMut(&Expr)) {
        f(self);
        for e in self.children() {
            e.walk(f);
        }
    }

    fn children(&self) -> Vec<&Expr> {
        match self {
            Expr::Param(_) | Expr::Type(_) => Vec::new(),
            Expr::Ref(_, xs)
            | Expr::Union(xs)
            | Expr::And(xs)
            | Expr::Tuple(xs)
            | Expr::Atom(_, xs) => xs.iter().collect(),
            Expr::Not(a) => vec![a],
            Expr::Diff(a, b) => vec![a, b],
            Expr::Morphism(l, u, v) => vec![l, u, v],
        }
    }
}

/// A definition `type name(params) = body`.
#[derive(Clone, Debug)]
pub struct Def {
    /// Its name.
    pub name: String,
    /// Its parameters' names.
    pub params: Vec<String>,
    /// Its body.
    pub body: Expr,
}

/// A checked group of mutually recursive definitions.
#[derive(Clone, Debug)]
pub struct Group(Arc<Checked>);

#[derive(Debug)]
struct Checked {
    defs: Vec<Def>,
    /// Each body as a shared tree.
    bodies: Vec<Arc<Node>>,
}

/// An expression as a shared tree, each node knowing whether it mentions the group, so that a
/// part kept unevaluated is shared rather than copied, and no node's flag is computed twice.
#[derive(PartialEq, Debug)]
struct Node {
    recursive: bool,
    e: Shape,
}

#[derive(PartialEq, Debug)]
enum Shape {
    Param(usize),
    Ref(usize, Vec<Arc<Node>>),
    Type(Type),
    Union(Vec<Arc<Node>>),
    And(Vec<Arc<Node>>),
    Not(Arc<Node>),
    Diff(Arc<Node>, Arc<Node>),
    Tuple(Vec<Arc<Node>>),
    Atom(String, Vec<Arc<Node>>),
    Morphism(Arc<Node>, Arc<Node>, Arc<Node>),
}

impl Node {
    fn of(e: &Expr) -> Arc<Node> {
        let all = |xs: &[Expr]| xs.iter().map(Node::of).collect::<Vec<_>>();
        let e = match e {
            Expr::Param(i) => Shape::Param(*i),
            Expr::Ref(i, xs) => Shape::Ref(*i, all(xs)),
            Expr::Type(t) => Shape::Type(t.clone()),
            Expr::Union(xs) => Shape::Union(all(xs)),
            Expr::And(xs) => Shape::And(all(xs)),
            Expr::Not(a) => Shape::Not(Node::of(a)),
            Expr::Diff(a, b) => Shape::Diff(Node::of(a), Node::of(b)),
            Expr::Tuple(xs) => Shape::Tuple(all(xs)),
            Expr::Atom(name, xs) => Shape::Atom(name.clone(), all(xs)),
            Expr::Morphism(l, u, v) => Shape::Morphism(Node::of(l), Node::of(u), Node::of(v)),
        };
        let recursive =
            matches!(e, Shape::Ref(..)) || e.children().into_iter().any(|c| c.recursive);
        Arc::new(Node { recursive, e })
    }
}

impl Shape {
    fn children(&self) -> Vec<&Arc<Node>> {
        match self {
            Shape::Param(_) | Shape::Type(_) => Vec::new(),
            Shape::Ref(_, xs)
            | Shape::Union(xs)
            | Shape::And(xs)
            | Shape::Tuple(xs)
            | Shape::Atom(_, xs) => xs.iter().collect(),
            Shape::Not(a) => vec![a],
            Shape::Diff(a, b) => vec![a, b],
            Shape::Morphism(l, u, v) => vec![l, u, v],
        }
    }
}

/// Why a group is rejected: the definition at fault and the reason.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rejection {
    /// The index of the definition.
    pub def: usize,
    /// The reason, naming the definition.
    pub message: String,
}

impl Group {
    /// The group of `defs`, if it is contractive, regular and monotone in emptiness.
    pub fn new(defs: Vec<Def>) -> Result<Group, Rejection> {
        let bodies = defs.iter().map(|d| Node::of(&d.body)).collect();
        let g = Group(Arc::new(Checked { defs, bodies }));
        g.regular()?;
        g.contractive()?;
        g.monotone()?;
        Ok(g)
    }

    /// The definitions.
    pub fn defs(&self) -> &[Def] {
        &self.0.defs
    }

    fn reject(&self, def: usize, why: String) -> Rejection {
        Rejection {
            def,
            message: format!("the type `{}` {why}", self.0.defs[def].name),
        }
    }

    fn regular(&self) -> Result<(), Rejection> {
        let arity = self.0.defs[0].params.len();
        for (i, d) in self.0.defs.iter().enumerate() {
            if d.params.len() != arity {
                return Err(self.reject(
                    i,
                    "takes other parameters than the definitions it is recursive with".into(),
                ));
            }
            let mut bad = None;
            d.body.walk(&mut |e| {
                if let Expr::Ref(_, args) = e {
                    let same = args.len() == arity
                        && args.iter().enumerate().all(|(k, a)| *a == Expr::Param(k));
                    if !same && bad.is_none() {
                        bad = Some(e.clone());
                    }
                }
            });
            if let Some(e) = bad {
                return Err(self.reject(
                    i,
                    format!(
                        "is not regular: its recursive occurrence `{}` changes the parameters, \
                         so the type has no end of components",
                        self.show(i, &e)
                    ),
                ));
            }
        }
        Ok(())
    }

    fn contractive(&self) -> Result<(), Rejection> {
        // The definitions each one names outside every constructor.
        let bare: Vec<Vec<usize>> = self
            .0
            .defs
            .iter()
            .map(|d| {
                let mut out = BTreeSet::new();
                unguarded(&d.body, &mut out);
                out.into_iter().collect()
            })
            .collect();
        match first_on_cycle(&bare) {
            Some(start) => Err(self.reject(
                start,
                "is not contractive: it reaches itself with no constructor between".into(),
            )),
            None => Ok(()),
        }
    }

    fn monotone(&self) -> Result<(), Rejection> {
        for (i, body) in self.0.bodies.iter().enumerate() {
            if let Some(why) = self.flipped(body) {
                return Err(self.reject(i, format!("is not monotone in emptiness: {why}")));
            }
        }
        Ok(())
    }

    /// Where in `e` a recursive occurrence stands at a place that makes emptiness not
    /// monotone, if one does.
    fn flipped(&self, e: &Node) -> Option<String> {
        match &e.e {
            Shape::Not(a) if a.recursive => {
                Some("a recursive occurrence stands under a complement".into())
            }
            Shape::Diff(_, b) if b.recursive => {
                Some("a recursive occurrence stands to the right of `\\`".into())
            }
            Shape::Morphism(l, _, v) if l.recursive && (v.recursive || self.may_be_empty(v)) => {
                Some(
                    "a recursive occurrence stands in the guaranteed domain of a morphism type \
                     whose value type may be empty or mentions the group"
                        .into(),
                )
            }
            _ => e.e.children().into_iter().find_map(|c| self.flipped(c)),
        }
    }

    /// Whether `v`, which mentions no recursive occurrence, is empty at some arguments.
    fn may_be_empty(&self, v: &Node) -> bool {
        let none = vec![Type::empty(); self.0.defs[0].params.len()];
        shrinks(v, false) || eval(v, &Arc::new(Env::ground(none))).is_empty()
    }

    /// The group's types at `args`, one per definition. Each is a recursive node that unfolds
    /// to its body.
    ///
    /// # Panics
    ///
    /// When `args` is not one type per parameter.
    pub fn instance(&self, args: Vec<Type>) -> Vec<Type> {
        assert_eq!(
            args.len(),
            self.0.defs[0].params.len(),
            "one argument per parameter"
        );
        let env = Arc::new(Env {
            group: Some(self.clone()),
            args,
            members: OnceLock::new(),
        });
        let members: Vec<Type> = (0..self.0.defs.len())
            .map(|i| {
                let e = env.clone();
                let named = e.clone();
                Type::rec(
                    move || named.name(i),
                    move || eval(&e.group().0.bodies[i], &e),
                )
            })
            .collect();
        env.members
            .set(members.clone())
            .expect("the members are set once");
        members
    }

    /// `e`, an expression of definition `def`, in the surface syntax.
    fn show(&self, def: usize, e: &Expr) -> String {
        Show {
            defs: &self.0.defs,
            params: &self.0.defs[def].params,
            args: None,
            e: &Node::of(e),
        }
        .to_string()
    }
}

/// Whether a parameter in `e` stands under a complement or to the right of `\\`, where a larger
/// argument shrinks `e`; `under` says whether `e` itself does.
fn shrinks(e: &Node, under: bool) -> bool {
    match &e.e {
        Shape::Param(_) => under,
        Shape::Not(a) => shrinks(a, true),
        Shape::Diff(a, b) => shrinks(a, under) || shrinks(b, true),
        s => s.children().into_iter().any(|c| shrinks(c, under)),
    }
}

/// The lowest vertex of `edges` on a cycle, if one is: Tarjan's strongly connected components,
/// each edge read once, with an explicit stack. A search from each vertex in turn read the
/// graph once per vertex.
fn first_on_cycle(edges: &[Vec<usize>]) -> Option<usize> {
    const NEW: usize = usize::MAX;
    let n = edges.len();
    let (mut index, mut low, mut on) = (vec![NEW; n], vec![0; n], vec![false; n]);
    let (mut stack, mut next, mut first) = (Vec::new(), 0, None);
    for s in 0..n {
        if index[s] != NEW {
            continue;
        }
        let mut calls = vec![(s, 0)];
        (index[s], low[s], on[s], next) = (next, next, true, next + 1);
        stack.push(s);
        while let Some((v, k)) = calls.last_mut() {
            let v = *v;
            if let Some(&w) = edges[v].get(*k) {
                *k += 1;
                if index[w] == NEW {
                    (index[w], low[w], on[w], next) = (next, next, true, next + 1);
                    stack.push(w);
                    calls.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            calls.pop();
            if let Some(&(u, _)) = calls.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                if component.len() > 1 || edges[v].contains(&v) {
                    let m = component
                        .into_iter()
                        .min()
                        .expect("a component has a vertex");
                    first = Some(first.map_or(m, |f: usize| f.min(m)));
                }
            }
        }
    }
    first
}

/// The definitions `e` names outside every constructor.
fn unguarded(e: &Expr, out: &mut BTreeSet<usize>) {
    match e {
        Expr::Ref(i, _) => {
            out.insert(*i);
        }
        Expr::Tuple(_) | Expr::Atom(..) | Expr::Morphism(..) => {}
        _ => {
            for c in e.children() {
                unguarded(c, out);
            }
        }
    }
}

/// What an expression is evaluated in: the arguments, and the group's types at them.
struct Env {
    group: Option<Group>,
    args: Vec<Type>,
    members: OnceLock<Vec<Type>>,
}

impl Env {
    fn ground(args: Vec<Type>) -> Env {
        Env {
            group: None,
            args,
            members: OnceLock::new(),
        }
    }

    fn group(&self) -> &Group {
        self.group
            .as_ref()
            .expect("a recursive occurrence is in a group")
    }

    /// The name of definition `i` at the arguments: `Tree(int)`.
    fn name(&self, i: usize) -> String {
        let d = &self.group().0.defs[i];
        match self.args.is_empty() {
            true => d.name.clone(),
            false => {
                let args: Vec<String> = self.args.iter().map(Type::to_string).collect();
                format!("{}({})", d.name, args.join(", "))
            }
        }
    }
}

fn eval(e: &Node, env: &Arc<Env>) -> Type {
    let all = |xs: &[Arc<Node>]| xs.iter().map(|x| eval(x, env)).collect::<Vec<_>>();
    let parts = |xs: &[Arc<Node>]| Type::tuple(xs.iter().map(|x| component(x, env)).collect());
    match &e.e {
        Shape::Param(i) => env.args[*i].clone(),
        Shape::Ref(i, _) => env.members.get().expect("members are set before use")[*i].clone(),
        Shape::Type(t) => t.clone(),
        Shape::Union(xs) => Type::union_all(all(xs)),
        Shape::And(xs) => Type::meet_all(all(xs)),
        Shape::Not(a) => !eval(a, env),
        Shape::Diff(a, b) => eval(a, env) - &eval(b, env),
        Shape::Tuple(xs) => parts(xs),
        Shape::Atom(name, xs) => Type::atom_with(name, &parts(xs)),
        Shape::Morphism(l, u, v) => {
            Type::morphism(component(l, env), component(u, env), component(v, env))
        }
    }
}

/// `e` in a constructor: when it mentions the group and is more than one occurrence, it is
/// kept as a node evaluated on first use, since evaluating it now could need the parts of the
/// type being built.
fn component(e: &Arc<Node>, env: &Arc<Env>) -> Type {
    if matches!(e.e, Shape::Ref(..)) || !e.recursive {
        return eval(e, env);
    }
    let (named, at) = (e.clone(), env.clone());
    let (e, env) = (e.clone(), env.clone());
    Type::rec(
        move || {
            Show {
                defs: &at.group().0.defs,
                params: &[],
                args: Some(&at.args),
                e: &named,
            }
            .to_string()
        },
        move || eval(&e, &env),
    )
}

/// An expression in the surface syntax, its parameters by name or, with `args`, by value.
struct Show<'a> {
    defs: &'a [Def],
    params: &'a [String],
    args: Option<&'a [Type]>,
    e: &'a Node,
}

impl fmt::Display for Show<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sub = |e: &'_ Node| {
            let s = Show { e, ..*self }.to_string();
            match e.e {
                Shape::Union(_) | Shape::And(_) | Shape::Diff(..) | Shape::Morphism(..) => {
                    format!("({s})")
                }
                _ => s,
            }
        };
        let list =
            |xs: &[Arc<Node>], sep: &str| xs.iter().map(|x| sub(x)).collect::<Vec<_>>().join(sep);
        match &self.e.e {
            Shape::Param(i) => match self.args {
                Some(args) => write!(f, "{}", args[*i]),
                None => f.write_str(&self.params[*i]),
            },
            Shape::Ref(i, args) if args.is_empty() => f.write_str(&self.defs[*i].name),
            Shape::Ref(i, args) => {
                let args: Vec<String> = args
                    .iter()
                    .map(|a| Show { e: a, ..*self }.to_string())
                    .collect();
                write!(f, "{}({})", self.defs[*i].name, args.join(", "))
            }
            Shape::Type(t) => write!(f, "{t}"),
            Shape::Union(xs) => f.write_str(&list(xs, " | ")),
            Shape::And(xs) => f.write_str(&list(xs, " & ")),
            Shape::Not(a) => write!(f, "!{}", sub(a)),
            Shape::Diff(a, b) => write!(f, "{} \\ {}", sub(a), sub(b)),
            Shape::Tuple(xs) => write!(f, "({})", list(xs, ", ")),
            Shape::Atom(name, xs) => write!(f, "#{name}({})", list(xs, ", ")),
            Shape::Morphism(l, u, v) if l == u => write!(f, "({}) -> {}", sub(l), sub(v)),
            Shape::Morphism(l, u, v) if l.e == Shape::Type(Type::empty()) => {
                write!(f, "{} ->? {}", sub(u), sub(v))
            }
            Shape::Morphism(l, u, v) => write!(f, "({} ⊆ dom ⊆ {}) -> {}", sub(l), sub(u), sub(v)),
        }
    }
}
