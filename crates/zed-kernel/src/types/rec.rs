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
//!   the group, since `type T = (T) -> (#a & #b)` is inhabited exactly when it is empty; nor
//!   in the guarantee of a morphism type whose guarantee and permission differ, or that stands
//!   under `&`, `\`, a complement or differing domain bounds, directly or through a definition
//!   named there (cross-review X14: `W = (W) -> int` is accepted, `((W) -> int) & top` and
//!   `R0 = (R1) -> int; R1 = (int, R0 & ((empty) -> int))` are not).
//!
//! A value type that mentions a parameter may be empty when that parameter is: it counts as
//! possibly empty when it is empty with every parameter empty, or has a parameter under a
//! complement or to the right of `\`, where a larger argument shrinks it.

use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::sync::{Arc, LazyLock, Mutex, OnceLock};

use super::bes::{Answer, Bes, Kind, decide};
use super::{Piece, Rope, Type, Verdict};
use crate::deep;

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

/// The instances made so far: one equal group at equal arguments gives one set of types, so that
/// equal definitions meet as equal types however often they were written. The text of the
/// definitions picks a bucket; `Def` equality, and the arguments' equality, pick the entry.
static INSTANCES: LazyLock<Mutex<HashMap<String, Vec<Instance>>>> = LazyLock::new(Mutex::default);

struct Instance {
    group: Group,
    args: Vec<Type>,
    members: Vec<Type>,
}

/// A checked group of mutually recursive definitions.
#[derive(Clone, Debug)]
pub struct Group(Arc<Checked>);

#[derive(Debug)]
struct Checked {
    defs: Vec<Def>,
    /// Each body as a shared tree.
    bodies: Vec<Arc<Node>>,
    /// Whether each definition is plain: on no cycle of the group and naming only plain
    /// definitions. A plain member is its unfolding, built as an ordinary type, so equal plain
    /// members of groups built apart are one type.
    plain: Vec<bool>,
    /// The plain definitions, each after those it names.
    order: Vec<usize>,
}

/// An expression as a shared tree, each node knowing whether it mentions the group, so that a
/// part kept unevaluated is shared rather than copied, and no node's flag is computed twice.
#[derive(PartialEq, Debug)]
struct Node {
    recursive: bool,
    /// Whether the node names a definition that is not plain.
    open: bool,
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
    /// The tree of `e`, given which definitions are plain; an index outside `plain` is not.
    fn of(e: &Expr, plain: &[bool]) -> Arc<Node> {
        let of = |x: &Expr| Node::of(x, plain);
        let all = |xs: &[Expr]| xs.iter().map(of).collect::<Vec<_>>();
        let e = match e {
            Expr::Param(i) => Shape::Param(*i),
            Expr::Ref(i, xs) => Shape::Ref(*i, all(xs)),
            Expr::Type(t) => Shape::Type(t.clone()),
            Expr::Union(xs) => Shape::Union(all(xs)),
            Expr::And(xs) => Shape::And(all(xs)),
            Expr::Not(a) => Shape::Not(of(a)),
            Expr::Diff(a, b) => Shape::Diff(of(a), of(b)),
            Expr::Tuple(xs) => Shape::Tuple(all(xs)),
            Expr::Atom(name, xs) => Shape::Atom(name.clone(), all(xs)),
            Expr::Morphism(l, u, v) => Shape::Morphism(of(l), of(u), of(v)),
        };
        let recursive =
            matches!(e, Shape::Ref(..)) || e.children().into_iter().any(|c| c.recursive);
        let open = match &e {
            Shape::Ref(i, _) => !plain.get(*i).copied().unwrap_or(false),
            _ => e.children().into_iter().any(|c| c.open),
        };
        Arc::new(Node { recursive, open, e })
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

/// A part of an expression or tree whose owner is being dropped (module `deep`): an expression
/// nested deep is freed in a loop, on any stack.
#[expect(dead_code, reason = "a part is held only to be dropped")]
enum Freed {
    Expr(Expr),
    Exprs(Vec<Expr>),
    Shape(Shape),
    Nodes(Vec<Arc<Node>>),
}

thread_local! {
    /// The parts of expressions and trees waiting to be dropped.
    static FREED: deep::Queue<Freed> = const { deep::Queue::new() };
}

fn free(part: Freed) {
    deep::free_in(&FREED, part);
}

/// An expression's parts are freed in a loop, not by recursion.
impl Drop for Expr {
    fn drop(&mut self) {
        match self {
            Expr::Param(_) | Expr::Type(_) => {}
            Expr::Ref(_, xs)
            | Expr::Union(xs)
            | Expr::And(xs)
            | Expr::Tuple(xs)
            | Expr::Atom(_, xs) => {
                if !xs.is_empty() {
                    free(Freed::Exprs(std::mem::take(xs)));
                }
            }
            Expr::Not(a) => free(Freed::Expr(std::mem::replace(&mut **a, Expr::Param(0)))),
            Expr::Diff(a, b) => {
                for x in [a, b] {
                    free(Freed::Expr(std::mem::replace(&mut **x, Expr::Param(0))));
                }
            }
            Expr::Morphism(l, u, v) => {
                for x in [l, u, v] {
                    free(Freed::Expr(std::mem::replace(&mut **x, Expr::Param(0))));
                }
            }
        }
    }
}

/// Queues the shape `n` holds, when `n` is its last owner.
fn free_node(n: &mut Arc<Node>) {
    if let Some(n) = Arc::get_mut(n) {
        free(Freed::Shape(std::mem::replace(&mut n.e, Shape::Param(0))));
    }
}

/// A tree's children are freed in a loop, as an expression's are.
impl Drop for Shape {
    fn drop(&mut self) {
        match self {
            Shape::Param(_) | Shape::Type(_) => {}
            Shape::Ref(_, xs)
            | Shape::Union(xs)
            | Shape::And(xs)
            | Shape::Tuple(xs)
            | Shape::Atom(_, xs) => {
                if !xs.is_empty() {
                    free(Freed::Nodes(std::mem::take(xs)));
                }
            }
            Shape::Not(a) => free_node(a),
            Shape::Diff(a, b) => {
                free_node(a);
                free_node(b);
            }
            Shape::Morphism(l, u, v) => {
                free_node(l);
                free_node(u);
                free_node(v);
            }
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
        let (plain, order) = plain(&defs);
        let bodies = defs.iter().map(|d| Node::of(&d.body, &plain)).collect();
        let g = Group(Arc::new(Checked {
            defs,
            bodies,
            plain,
            order,
        }));
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
        let bodies = &self.0.bodies;
        // A definition is constrained when it is named under `&`, `\`, a complement or the
        // domain bounds of a morphism type whose guarantee and permission differ, or is named
        // anywhere in a constrained definition: there a domain that is exact everywhere else
        // is narrowed, so the group's emptiness can flip.
        let mut constrained = vec![false; bodies.len()];
        let mut names: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); bodies.len()];
        for (i, body) in bodies.iter().enumerate() {
            refs(body, false, &mut constrained, &mut names[i]);
        }
        let mut stack: Vec<usize> = (0..bodies.len()).filter(|&i| constrained[i]).collect();
        while let Some(i) = stack.pop() {
            for &j in &names[i] {
                if !constrained[j] {
                    constrained[j] = true;
                    stack.push(j);
                }
            }
        }
        for (i, body) in bodies.iter().enumerate() {
            if let Some(why) = self.flipped(body, constrained[i]) {
                return Err(self.reject(i, format!("is not monotone in emptiness: {why}")));
            }
        }
        Ok(())
    }

    /// Where in `e` a recursive occurrence stands at a place that makes emptiness not
    /// monotone, if one does. `constrained` says whether `e` stands under `&`, `\`, a
    /// complement or differing domain bounds, here or where its definition is named.
    fn flipped(&self, e: &Node, constrained: bool) -> Option<String> {
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
            Shape::Morphism(l, u, _) if l.recursive && !same(l, u) => Some(
                "a recursive occurrence stands in the guaranteed domain of a morphism type \
                 whose guarantee and permission differ"
                    .into(),
            ),
            Shape::Morphism(l, ..) if l.recursive && constrained => Some(
                "a recursive occurrence stands in the domain of a morphism type that stands \
                 under `&`, `\\`, a complement or differing domain bounds, or in a definition \
                 named there"
                    .into(),
            ),
            Shape::Morphism(l, u, v) => {
                let inner = constrained || bounded(l, u);
                self.flipped(l, inner)
                    .or_else(|| self.flipped(u, inner))
                    .or_else(|| self.flipped(v, constrained))
            }
            Shape::And(_) | Shape::Not(_) | Shape::Diff(..) => {
                e.e.children()
                    .into_iter()
                    .find_map(|c| self.flipped(c, true))
            }
            Shape::Param(_)
            | Shape::Ref(..)
            | Shape::Type(_)
            | Shape::Union(_)
            | Shape::Tuple(_)
            | Shape::Atom(..) => {
                e.e.children()
                    .into_iter()
                    .find_map(|c| self.flipped(c, constrained))
            }
        }
    }

    /// Whether `v`, which mentions no recursive occurrence, is empty at some arguments.
    fn may_be_empty(&self, v: &Node) -> bool {
        let none = vec![Type::empty(); self.0.defs[0].params.len()];
        shrinks(v, false) || eval(v, &Arc::new(Env::ground(none))).is_empty()
    }

    /// The group's types at `args`, one per definition. Each is a recursive node that unfolds
    /// to its body, except that a plain definition is its body, built as an ordinary type.
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
        let same = |d: &[Def]| {
            d.len() == self.0.defs.len()
                && d.iter()
                    .zip(&self.0.defs)
                    .all(|(a, b)| a.name == b.name && a.params == b.params && a.body == b.body)
        };
        let key = format!("{:?}", self.0.defs);
        let mut table = INSTANCES
            .lock()
            .expect("no thread panics holding the table");
        let bucket = table.entry(key).or_default();
        if let Some(i) = bucket
            .iter()
            .find(|i| same(&i.group.0.defs) && i.args == args)
        {
            return i.members.clone();
        }
        let kept = args.clone();
        let env = Arc::new(Env {
            group: Some(self.clone()),
            args,
            members: (0..self.0.defs.len()).map(|_| OnceLock::new()).collect(),
            judged: OnceLock::new(),
        });
        let plain = &self.0.plain;
        for i in (0..self.0.defs.len()).filter(|&i| !plain[i]) {
            let e = env.clone();
            let named = e.clone();
            let j = e.clone();
            let t = Type::rec_judged(
                move || named.name(i),
                move || eval(&e.group().0.bodies[i], &e),
                move || j.judged.get_or_init(|| judge(&j))[i],
            );
            env.members[i].set(t).expect("a member is set once");
        }
        // A plain member names only plain members, each set before it.
        for &i in &self.0.order {
            let t = eval(&self.0.bodies[i], &env);
            env.members[i].set(t).expect("a member is set once");
        }
        let members: Vec<Type> = env
            .members
            .iter()
            .map(|m| m.get().expect("every member is set").clone())
            .collect();
        bucket.push(Instance {
            group: self.clone(),
            args: kept,
            members: members.clone(),
        });
        members
    }

    /// `e`, an expression of definition `def`, in the surface syntax.
    fn show(&self, def: usize, e: &Expr) -> String {
        Show {
            defs: &self.0.defs,
            params: &self.0.defs[def].params,
            args: None,
            e: &Node::of(e, &[]),
        }
        .to_string()
    }
}
/// Records in `names` each definition `e` names, and in `out` each it names at a constrained
/// place (`Group::flipped`); `constrained` says whether `e` itself stands at one.
fn refs(e: &Node, constrained: bool, out: &mut [bool], names: &mut BTreeSet<usize>) {
    let inner = match &e.e {
        Shape::Ref(i, _) => {
            names.insert(*i);
            out[*i] |= constrained;
            constrained
        }
        Shape::And(_) | Shape::Not(_) | Shape::Diff(..) => true,
        Shape::Morphism(l, u, v) => {
            let dom = constrained || bounded(l, u);
            refs(l, dom, out, names);
            refs(u, dom, out, names);
            refs(v, constrained, out, names);
            return;
        }
        Shape::Param(_) | Shape::Type(_) | Shape::Union(_) | Shape::Tuple(_) | Shape::Atom(..) => {
            constrained
        }
    };
    for c in e.e.children() {
        refs(c, inner, out, names);
    }
}

/// Whether the domain bounds `l` and `u` are written the same.
fn same(l: &Arc<Node>, u: &Arc<Node>) -> bool {
    Arc::ptr_eq(l, u) || l == u
}

/// Whether the domain bounds `l .. u` narrow the domain: they differ, the guarantee is not
/// `empty` and the permission is not `top`.
fn bounded(l: &Arc<Node>, u: &Arc<Node>) -> bool {
    let empty = matches!(&l.e, Shape::Type(t) if t.is_empty());
    let top = matches!(&u.e, Shape::Type(t) if Type::top().subtype(t));
    !same(l, u) && !empty && !top
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

/// The lowest vertex of `edges` on a cycle, if one is.
fn first_on_cycle(edges: &[Vec<usize>]) -> Option<usize> {
    on_cycle(edges).iter().position(|&c| c)
}

/// Whether each vertex of `edges` is on a cycle: Tarjan's strongly connected components, each
/// edge read once, with an explicit stack. A search from each vertex in turn read the graph once
/// per vertex.
fn on_cycle(edges: &[Vec<usize>]) -> Vec<bool> {
    const NEW: usize = usize::MAX;
    let n = edges.len();
    let (mut index, mut low, mut on) = (vec![NEW; n], vec![0; n], vec![false; n]);
    let (mut stack, mut next, mut cyclic) = (Vec::new(), 0, vec![false; n]);
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
                    for w in component {
                        cyclic[w] = true;
                    }
                }
            }
        }
    }
    cyclic
}

/// Whether each of `defs` is plain: on no cycle and naming only plain definitions; and the
/// plain definitions, each after those it names. A depth-first search with an explicit stack
/// settles each definition after those it names, reading each edge once.
fn plain(defs: &[Def]) -> (Vec<bool>, Vec<usize>) {
    let edges: Vec<Vec<usize>> = defs
        .iter()
        .map(|d| {
            let mut out = BTreeSet::new();
            d.body.walk(&mut |e| {
                if let Expr::Ref(i, _) = e {
                    out.insert(*i);
                }
            });
            out.into_iter().collect()
        })
        .collect();
    let cyclic = on_cycle(&edges);
    let (mut plain, mut order) = (vec![None; defs.len()], Vec::new());
    for s in 0..defs.len() {
        let mut calls = vec![(s, 0)];
        while let Some((v, k)) = calls.last_mut() {
            let v = *v;
            if plain[v].is_some() {
                calls.pop();
                continue;
            }
            // A definition on no cycle is not on the stack of calls when its names are read.
            match edges[v].get(*k) {
                Some(&w) if !cyclic[v] => {
                    *k += 1;
                    if plain[w].is_none() {
                        calls.push((w, 0));
                    }
                }
                _ => {
                    let p = !cyclic[v] && edges[v].iter().all(|&w| plain[w] == Some(true));
                    plain[v] = Some(p);
                    if p {
                        order.push(v);
                    }
                    calls.pop();
                }
            }
        }
    }
    (plain.into_iter().map(|p| p == Some(true)).collect(), order)
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
    /// Each member's type, set when the group is instantiated.
    members: Vec<OnceLock<Type>>,
    /// Each member's emptiness as the group decides it ([`judge`]), when first asked.
    judged: OnceLock<Vec<Option<bool>>>,
}

impl Env {
    fn ground(args: Vec<Type>) -> Env {
        Env {
            group: None,
            args,
            members: Vec::new(),
            judged: OnceLock::new(),
        }
    }

    fn group(&self) -> &Group {
        self.group
            .as_ref()
            .expect("a recursive occurrence is in a group")
    }

    /// The name of definition `i` at the arguments: `Tree(int)`.
    fn name(&self, i: usize) -> Rope {
        let d = &self.group().0.defs[i];
        match self.args.is_empty() {
            true => Rope::cat([Piece::from(d.name.as_str())]),
            false => Rope::joined(
                &format!("{}(", d.name),
                self.args.iter().map(Type::rope),
                ", ",
                ")",
            ),
        }
    }
}

fn eval(e: &Node, env: &Arc<Env>) -> Type {
    let all = |xs: &[Arc<Node>]| xs.iter().map(|x| eval(x, env)).collect::<Vec<_>>();
    let parts = |xs: &[Arc<Node>]| Type::tuple(xs.iter().map(|x| component(x, env)).collect());
    match &e.e {
        Shape::Param(i) => env.args[*i].clone(),
        Shape::Ref(i, _) => env.members[*i]
            .get()
            .expect("a member is set before use")
            .clone(),
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

/// `e` in a constructor: when it names a definition that is not plain and is more than one
/// occurrence, it is kept as a node evaluated on first use, since evaluating it now could need
/// the parts of the type being built.
fn component(e: &Arc<Node>, env: &Arc<Env>) -> Type {
    if matches!(e.e, Shape::Ref(..)) || !e.open {
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
            .rope()
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

impl Show<'_> {
    /// The text as a rope, which holds the texts of the types it names without copying them,
    /// so that the name of `Tree(Tree(..))` takes time linear in its text.
    fn rope(&self) -> Rope {
        let sub = |e: &'_ Node| {
            let r = Show { e, ..*self }.rope();
            match e.e {
                Shape::Union(_) | Shape::And(_) | Shape::Diff(..) | Shape::Morphism(..) => {
                    Rope::joined("(", [r], "", ")")
                }
                _ => r,
            }
        };
        let list = |head: &str, xs: &[Arc<Node>], sep: &str, tail: &str| {
            Rope::joined(head, xs.iter().map(|x| sub(x)), sep, tail)
        };
        match &self.e.e {
            Shape::Param(i) => match self.args {
                Some(args) => args[*i].rope(),
                None => Rope::cat([Piece::from(self.params[*i].as_str())]),
            },
            Shape::Ref(i, args) if args.is_empty() => {
                Rope::cat([Piece::from(self.defs[*i].name.as_str())])
            }
            Shape::Ref(i, args) => Rope::joined(
                &format!("{}(", self.defs[*i].name),
                args.iter().map(|a| Show { e: a, ..*self }.rope()),
                ", ",
                ")",
            ),
            Shape::Type(t) => t.rope(),
            Shape::Union(xs) => list("", xs, " | ", ""),
            Shape::And(xs) => list("", xs, " & ", ""),
            Shape::Not(a) => Rope::joined("!", [sub(a)], "", ""),
            Shape::Diff(a, b) => Rope::joined("", [sub(a), sub(b)], " \\ ", ""),
            Shape::Tuple(xs) => list("(", xs, ", ", ")"),
            Shape::Atom(name, xs) => list(&format!("#{name}("), xs, ", ", ")"),
            Shape::Morphism(l, u, v) if l == u => Rope::joined("(", [sub(l), sub(v)], ") -> ", ""),
            Shape::Morphism(l, u, v) if l.e == Shape::Type(Type::empty()) => {
                Rope::joined("", [sub(u), sub(v)], " ->? ", "")
            }
            Shape::Morphism(l, u, v) => Rope::cat([
                Piece::from("("),
                Piece::from(sub(l)),
                Piece::from(" ⊆ dom ⊆ "),
                Piece::from(sub(u)),
                Piece::from(") -> "),
                Piece::from(sub(v)),
            ]),
        }
    }
}

impl fmt::Display for Show<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.rope().strs().try_for_each(|s| f.write_str(s))
    }
}

/// Each member's emptiness at `env`'s arguments, as the group's fixed points decide it (module
/// `bes`, cross-review X14): a union is an `Or` node, a tuple or atom payload an `And` node, a
/// morphism type whose guarantee lies within its permission and is inhabited a `Mor` node of
/// its value type, and a part that does not mention the group `Top` or `Bot` by its own
/// emptiness. A cycle through a tuple is then empty and one through a morphism's value type
/// inhabited. `None` for each member when a recursive occurrence stands under `&`, `\` or a
/// complement, which the decider does not take, and for a member the decider refuses; the
/// coinductive search of module `empty` decides those. Time linear in the bodies, besides the
/// emptiness of their closed parts.
fn judge(env: &Arc<Env>) -> Vec<Option<bool>> {
    let bodies = &env.group().0.bodies;
    let refused = || vec![None; bodies.len()];
    let mut b = Bes::new();
    let mut stack = Vec::new();
    for e in bodies {
        stack.push((b.add(Kind::Bot, vec![]), e));
    }
    // A closed part is read by its verdict, never by `is_empty`, whose "inhabited" may be a
    // check that gave up: a member judged on it could be judged empty when it is not.
    while let Some((v, e)) = stack.pop() {
        let (kind, children) = match &e.e {
            _ if !e.recursive => match eval(e, env).verdict() {
                Verdict::Empty => (Kind::Bot, vec![]),
                Verdict::Inhabited => (Kind::Top, vec![]),
                Verdict::Refused(_) => return refused(),
            },
            Shape::Ref(i, _) => (Kind::Or, vec![*i as u32]),
            Shape::Union(xs) => (Kind::Or, kids(&mut b, &mut stack, xs)),
            Shape::Tuple(xs) | Shape::Atom(_, xs) => (Kind::And, kids(&mut b, &mut stack, xs)),
            Shape::Morphism(l, u, val) if l.recursive || u.recursive => {
                // Admitted only with equal bounds and a value type that is not empty.
                if val.recursive || eval(val, env).verdict() != Verdict::Inhabited {
                    return refused();
                }
                (Kind::Top, vec![])
            }
            Shape::Morphism(l, u, val) => {
                let (l, u) = (eval(l, env), eval(u, env));
                // A key promised and not permitted leaves no morphism; with no key promised the
                // empty morphism is one.
                match (l.subtype_verdict(&u), l.verdict()) {
                    (Verdict::Refused(_), _) | (_, Verdict::Refused(_)) => return refused(),
                    (Verdict::Inhabited, _) => (Kind::Bot, vec![]),
                    (Verdict::Empty, Verdict::Empty) => (Kind::Top, vec![]),
                    (Verdict::Empty, Verdict::Inhabited) => {
                        (Kind::Mor, kids(&mut b, &mut stack, [val]))
                    }
                }
            }
            Shape::And(_) | Shape::Not(_) | Shape::Diff(..) => return refused(),
            Shape::Param(_) | Shape::Type(_) => unreachable!("a closed part is not recursive"),
        };
        b.set(v, kind, children);
    }
    b.seal();
    decide(&b).answers[..bodies.len()]
        .iter()
        .map(|a| match a {
            Answer::Empty => Some(true),
            Answer::Inhabited => Some(false),
            Answer::Refused => None,
        })
        .collect()
}

/// The node of each of `xs`: a member's own for a recursive occurrence, so that the graph has
/// the group's shape and the decider's refusals do not depend on how a body is written; else a
/// new node, queued on `stack` to be set from its expression.
fn kids<'a>(
    b: &mut Bes,
    stack: &mut Vec<(u32, &'a Arc<Node>)>,
    xs: impl IntoIterator<Item = &'a Arc<Node>>,
) -> Vec<u32> {
    xs.into_iter()
        .map(|x| {
            if let Shape::Ref(i, _) = x.e {
                return i as u32;
            }
            let c = b.add(Kind::Bot, vec![]);
            stack.push((c, x));
            c
        })
        .collect()
}
