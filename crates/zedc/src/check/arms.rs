//! The ints the tests around an expression allow it: the scope of the reduced product
//! ([`crate::store::product`]) at each arm of an `if`, at the second side of `&&` and `||`
//! and in each case of a condition. A bit word's operand (L1.39a) and the exponent of `**`
//! (L1.17) are read through it, so `if n >= 0 { popCount(n) }` is accepted (DESIGN.md L1.39:
//! a test narrows a scope).
//!
//! Each condition the walk meets makes two nodes, the scopes where it holds and where it does
//! not, built from the node it is checked under; `!` swaps them, the second side of `a && b` is
//! checked under `a`'s holding node, so `a && b` holds at `b`'s, and fails at the join of the
//! two failing nodes, and `||` is the same with the outcomes swapped. A node's scope is
//! computed the first time a read under it needs it, from its parent's, which the memo keeps,
//! so a nest of `k` tests or a chain of `k` sides of `&&` costs `k` narrowings, each the size
//! of one test and of the projections its change makes due, and a program with no read under a
//! test computes none. A narrowing is not always the size of its test: see the tradeoff at
//! [`Ck::compute`].
//!
//! A name bound in an arm, `k = n - 1`, is read as its value in the scope of the node it was
//! bound under, once for the binder.
//!
//! Complexity tradeoff: a test or operand is translated only through literals, names, integer
//! and boolean operators; any other subexpression (a call, a field, an `is` test) is an
//! opaque int of its own span, so `if f(n) >= 0 { popCount(f(n)) }` is rejected, the two
//! calls being different atoms, and an `is` test narrows only through `Facts`. Why: the
//! translation is one pass per root, memoized by span, with no structural equality of
//! subterms, which is what would make two equal calls one atom. Trigger: a test on a call or
//! field that the operand repeats. Test:
//! `l01_39a_bit_words::narrowing::a_test_on_a_call_the_operand_repeats_is_rejected_and_its_named_value_accepted`.
//! COMPLEXITY.md row C26. A complete solution names the repeated value
//! (`m = f(n); if m >= 0 { popCount(m) }` works today), or hash-conses the translated terms
//! so equal calls are one atom.

use super::*;
use crate::store::cell::Premises;
use crate::store::lattice::Lattice;
use crate::store::product::{self, Product, Scope};
use imbl::ordmap::DiffItem;
use std::collections::VecDeque;
use zed_kernel::Shared;

/// One node: a scope the walk is in, or was.
enum Node<'a> {
    /// No test decides here.
    Root,
    /// The scope of `parent` where `test` gave `outcome`.
    Assume {
        parent: usize,
        test: &'a Expr,
        outcome: bool,
        /// The products of the names of the test, from their types where it is checked.
        fresh: Rc<Vec<(Arc<str>, Product)>>,
    },
    /// Either of two scopes: the join of their cases.
    Join(usize, usize),
}

/// An expression as a kernel term the reduced product reads, and the names in it bound by a
/// `name = value` binder, whose values the scope is told of before it is read.
struct Translated {
    term: Term,
    binders: Vec<usize>,
    /// The names of binders in it, in the scope, with the binders.
    vars: Vec<(Arc<str>, usize)>,
}

/// For one node, each name to the nearest node at or above it where a lookup of that name
/// continues: in `narrowed`, a test that changed the name's product ([`Arms::narrows`]); in
/// `read`, a test that reads the name. An `Assume` maps its names to itself; a `Join` the names
/// its two sides map differently, found by the maps' difference as [`Scope::join`] finds its
/// names.
#[derive(Clone)]
struct Chains {
    narrowed: imbl::OrdMap<Arc<str>, usize>,
    read: imbl::OrdMap<Arc<str>, usize>,
}

/// What a scope or a binder's product waits on.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Item {
    Scope(usize),
    Bound(usize),
}

/// The nodes of the walk, the scopes computed of them and the nodes the walk is in.
pub(super) struct Arms<'a> {
    nodes: Vec<Node<'a>>,
    /// Each node's scope, once a read has needed it.
    scopes: Vec<Option<Scope>>,
    /// For each `Assume` whose scope is computed, the names whose products its test changed:
    /// the difference of the scope it was narrowed from and its own, or every name of its test
    /// when it made a reachable scope unreachable.
    narrows: Vec<Option<Vec<Arc<str>>>>,
    /// For each node, once a rejection under it has needed it, the two chains a lookup
    /// follows ([`Chains`]).
    chains: Vec<Option<Chains>>,
    /// For each test a rejection found had changed a name it does not read, the search of
    /// the relation that carried the change ([`Carried`]).
    carried: HashMap<usize, Carried>,
    /// The nodes the walk is in, innermost last.
    active: Vec<usize>,
    /// The node each binder was bound under, when it is not the root.
    bound_at: HashMap<usize, usize>,
    /// The type of each binder bound to a value of scalars and atoms.
    bound_ty: HashMap<usize, KType>,
    /// Each binder's value in the scope of its node, once a read has needed it.
    bound: HashMap<usize, Product>,
    /// The terms of the expressions read so far, by span.
    terms: HashMap<Span, Rc<Translated>>,
    /// The scope name of each binder a term has read.
    names: HashMap<usize, Arc<str>>,
}

impl<'a> Arms<'a> {
    pub(super) fn new() -> Self {
        Arms {
            nodes: vec![Node::Root],
            scopes: vec![None],
            narrows: vec![None],
            chains: vec![None],
            carried: HashMap::new(),
            active: Vec::new(),
            bound_at: HashMap::new(),
            bound_ty: HashMap::new(),
            bound: HashMap::new(),
            terms: HashMap::new(),
            names: HashMap::new(),
        }
    }

    /// The node the walk is in.
    pub(super) fn here(&self) -> usize {
        self.active.last().copied().unwrap_or(0)
    }

    fn add(&mut self, n: Node<'a>) -> usize {
        self.nodes.push(n);
        self.scopes.push(None);
        self.narrows.push(None);
        self.chains.push(None);
        self.nodes.len() - 1
    }

    /// The two nodes of the condition `test` checked here: where it holds and where it fails.
    fn test(&mut self, test: &'a Expr, fresh: Vec<(Arc<str>, Product)>) -> (usize, usize) {
        let parent = self.here();
        let fresh = Rc::new(fresh);
        let yes = self.add(Node::Assume {
            parent,
            test,
            outcome: true,
            fresh: fresh.clone(),
        });
        let no = self.add(Node::Assume {
            parent,
            test,
            outcome: false,
            fresh,
        });
        (yes, no)
    }

    /// The node where the walk is in `a` or in `b`.
    pub(super) fn join(&mut self, a: usize, b: usize) -> usize {
        if a == b {
            return a;
        }
        self.add(Node::Join(a, b))
    }

    /// The walk enters node `n`.
    pub(super) fn enter(&mut self, n: usize) {
        self.active.push(n);
    }

    /// The walk leaves the node it entered last.
    pub(super) fn leave(&mut self) {
        self.active.pop();
    }

    /// The binder `id` is bound here.
    pub(super) fn bind(&mut self, id: usize, ty: &Ty) {
        let here = self.here();
        if here != 0 {
            self.bound_at.insert(id, here);
        }
        if let Some(t) = plain(ty) {
            self.bound_ty.insert(id, t);
        }
    }

    /// The tests that bear on a read of `starts`, each a name with the node it is read under,
    /// innermost first, with the outcome each gave and whether it gave it in one case of a join
    /// only. A test is listed when it changed the product of a name looked up
    /// ([`Arms::narrows`]); then, unless the test alone gives the name that product
    /// ([`Arms::explains`]), the lookup goes on above it, from its parent, for each name of the
    /// test. A test that reads a name and leaves its product as it was is passed over: under
    /// `n >= 0`, the tests `ai >= n - 3` change no product of `n`, so a rejection on `ai` lists
    /// its own test and `n >= 0`. A test that changed a name it does not read, which the
    /// scope's relation carried it to, also brings in the tests of one shortest path of the
    /// relation from that name to a name the test reads ([`Carried`]): `a == b`, `b == c`,
    /// then `c >= -2` for a read of `a`; under `ai >= n` for each `i`, then `n >= -1`, a read of
    /// `a0` lists `a0 >= n` and `n >= -1`, not the other tests on `n`; the lookup stops there when
    /// the test and its path alone give the name its product ([`Arms::explains`]), so weaker
    /// tests `n >= -2`, … around them are not listed. Each step is a lookup in
    /// a persistent map, O(log n), each item is visited once, and the search of each carrying
    /// test is kept and resumed, so the cost is that of the tests listed and their names, and
    /// of each relation searched once, not of the tests the walk is in.
    pub(super) fn deciding(&mut self, starts: Vec<(Arc<str>, usize)>) -> Vec<(Span, bool, bool)> {
        for (_, s) in &starts {
            self.settle_chains(*s);
        }
        let chain = |n: usize, x: &Arc<str>| {
            self.chains[n]
                .as_ref()
                .expect("an ancestor of a settled node is settled")
                .narrowed
                .get(x)
                .copied()
        };
        // Each node listed, with whether every way it was reached passed through a join.
        let mut listed: HashMap<usize, bool> = HashMap::new();
        // A node to look at, the name looked up and whether a join was passed.
        type At = (usize, Arc<str>, bool);
        let mut visited: HashSet<At> = HashSet::new();
        let mut stack: Vec<At> = Vec::new();
        for (x, s) in starts {
            if let Some(k) = chain(s, &x) {
                stack.push((k, x, false));
            }
        }
        while let Some(at) = stack.pop() {
            if !visited.insert(at.clone()) {
                continue;
            }
            let (k, x, case) = at;
            match &self.nodes[k] {
                Node::Root => {}
                Node::Assume { parent, fresh, .. } => {
                    let all = listed.entry(k).or_insert(case);
                    *all &= case;
                    if self.explains(k, &[], &x) {
                        continue;
                    }
                    let push_names = |q: usize, case: bool, stack: &mut Vec<At>| {
                        if let Node::Assume { parent, fresh, .. } = &self.nodes[q] {
                            for (y, _) in fresh.iter() {
                                if let Some(r) = chain(*parent, y) {
                                    stack.push((r, y.clone(), case));
                                }
                            }
                        }
                    };
                    if fresh.iter().any(|(y, _)| *y == x) {
                        push_names(k, case, &mut stack);
                        continue;
                    }
                    let search = self
                        .carried
                        .entry(k)
                        .or_insert_with(|| Carried::new(*parent, fresh));
                    let path = search.path(&self.nodes, &self.chains, &x);
                    for &(q, joined) in &path {
                        let case = case || joined;
                        let all = listed.entry(q).or_insert(case);
                        *all &= case;
                    }
                    // The test and its path alone give `x` its product: no test above bears.
                    if self.explains(k, &path, &x) {
                        continue;
                    }
                    push_names(k, case, &mut stack);
                    if let Some(q) = chain(*parent, &x) {
                        stack.push((q, x.clone(), case));
                    }
                    for &(q, joined) in &path {
                        push_names(q, case || joined, &mut stack);
                    }
                }
                Node::Join(a, b) => {
                    for side in [*b, *a] {
                        if let Some(q) = chain(side, &x) {
                            stack.push((q, x.clone(), true));
                        }
                    }
                }
            }
        }
        let mut out: Vec<(usize, bool)> = listed.into_iter().collect();
        out.sort_unstable_by_key(|a| std::cmp::Reverse(a.0));
        out.into_iter()
            .map(|(k, case)| match &self.nodes[k] {
                Node::Assume { test, outcome, .. } => (test.span, *outcome, case),
                _ => unreachable!("only a test is listed"),
            })
            .collect()
    }

    /// Whether the test of node `k`, with the tests `path` of a path of the relation that
    /// carried it to `x` ([`Carried::path`]), alone, on their names as their types give them,
    /// gives `x` the product it has at `k`: then no test above `k` bears on `x` there, as under
    /// `n >= 0`, `n >= 1` the second gives `n` int[1..] alone, and under `ai >= n`, then
    /// `n >= -2`, `n >= -1`, the last with `ai >= n` gives `ai` int[-1..]. The tests are narrowed
    /// once more, together, on a scope of their names, which costs the size of the tests.
    fn explains(&self, k: usize, path: &[(usize, bool)], x: &Arc<str>) -> bool {
        let Some(at) = &self.scopes[k] else {
            return false;
        };
        let mut names: BTreeMap<Arc<str>, Product> = BTreeMap::new();
        let mut sides: Vec<(Term, bool)> = Vec::with_capacity(path.len() + 1);
        for q in path.iter().map(|&(q, _)| q).chain([k]) {
            let Node::Assume {
                test,
                outcome,
                fresh,
                ..
            } = &self.nodes[q]
            else {
                return false;
            };
            let Some(t) = self.terms.get(&test.span) else {
                return false;
            };
            for (y, p) in fresh.iter() {
                names.entry(y.clone()).or_insert_with(|| p.clone());
            }
            sides.push((t.term.clone(), *outcome));
        }
        let (test, outcome) = match sides.len() {
            1 => sides.pop().expect("one side"),
            _ => {
                let side = |(t, o): (Term, bool)| match o {
                    true => t,
                    false => Term::Prim(Prim::Not, vec![t]),
                };
                let all = sides
                    .into_iter()
                    .map(side)
                    .reduce(|a, b| Term::Prim(Prim::And, vec![a, b]));
                (all.expect("two sides or more"), true)
            }
        };
        let alone = Scope::new(names);
        let alone = alone.assume_case(&test, outcome, &Premises::new());
        alone.get(x) == at.get(x)
    }

    /// Computes [`Arms::chains`] of `n` and of every node it is computed from, each once, on an
    /// explicit stack; the memo is the visited set.
    fn settle_chains(&mut self, n: usize) {
        let mut stack = vec![(n, false)];
        while let Some((k, ready)) = stack.pop() {
            if self.chains[k].is_some() {
                continue;
            }
            if !ready {
                stack.push((k, true));
                let from = match &self.nodes[k] {
                    Node::Root => [None, None],
                    Node::Assume { parent, .. } => [Some(*parent), None],
                    Node::Join(a, b) => [Some(*a), Some(*b)],
                };
                for d in from.into_iter().flatten() {
                    if self.chains[d].is_none() {
                        stack.push((d, false));
                    }
                }
                continue;
            }
            let settled = |d: usize| self.chains[d].as_ref().expect("settled first");
            let chains = match &self.nodes[k] {
                Node::Root => Chains {
                    narrowed: imbl::OrdMap::new(),
                    read: imbl::OrdMap::new(),
                },
                Node::Assume { parent, fresh, .. } => {
                    let mut c = settled(*parent).clone();
                    for (x, _) in fresh.iter() {
                        c.read.insert(x.clone(), k);
                    }
                    // A scope no read computed is taken to change every name of its test.
                    match &self.narrows[k] {
                        Some(changed) => {
                            for x in changed.iter() {
                                c.narrowed.insert(x.clone(), k);
                            }
                        }
                        None => {
                            for (x, _) in fresh.iter() {
                                c.narrowed.insert(x.clone(), k);
                            }
                        }
                    }
                    c
                }
                Node::Join(a, b) => {
                    let (ca, cb) = (settled(*a), settled(*b));
                    Chains {
                        narrowed: joined(&ca.narrowed, &cb.narrowed, k),
                        read: joined(&ca.read, &cb.read, k),
                    }
                }
            };
            self.chains[k] = Some(chains);
        }
    }
}

/// A step of [`Carried`]'s search: the test that reached a name, the name it was reached
/// from and whether a join was passed.
type Reached = (usize, Arc<str>, bool);

/// For a test that changed names it does not read, which the scope's relation carried its
/// change to, a breadth-first search of the relation above it: from the names the test reads,
/// over the tests above it, each test joining the names it reads. Each name the search reached
/// keeps the test it was reached by and the name that test was reached from, so a lookup of a
/// name follows these back to the test and lists one shortest path. The search goes only as
/// far as a lookup needs, and later lookups resume it, so over all lookups each test above is
/// expanded once for each name it reads.
struct Carried {
    /// Where the tests above are looked up from: the carrying test's parent.
    above: usize,
    /// Each name reached: `None` for a name the carrying test reads, else the test that
    /// reached it, the name that test was reached from and whether a join was passed.
    via: HashMap<Arc<str>, Option<Reached>>,
    /// The names reached and not yet expanded, in the order reached.
    queue: VecDeque<(Arc<str>, bool)>,
    /// The tests whose names have been reached.
    expanded: HashSet<usize>,
}

impl Carried {
    fn new(above: usize, fresh: &[(Arc<str>, Product)]) -> Self {
        Carried {
            above,
            via: fresh.iter().map(|(y, _)| (y.clone(), None)).collect(),
            queue: fresh.iter().map(|(y, _)| (y.clone(), false)).collect(),
            expanded: HashSet::new(),
        }
    }

    /// The tests of one shortest path of the relation from `x` to a name the carrying test
    /// reads, nearest `x` first, each with whether a join was passed to reach it; none when
    /// the relation does not reach `x`.
    fn path(
        &mut self,
        nodes: &[Node<'_>],
        chains: &[Option<Chains>],
        x: &Arc<str>,
    ) -> Vec<(usize, bool)> {
        while !self.via.contains_key(x) {
            let Some((y, joined)) = self.queue.pop_front() else {
                return Vec::new();
            };
            self.expand(nodes, chains, &y, joined);
        }
        let mut out = Vec::new();
        let mut at = x;
        while let Some(Some((q, from, joined))) = self.via.get(at) {
            out.push((*q, *joined));
            at = from;
        }
        out
    }

    /// Reaches the names of each test above that reads `y`, following `y`'s chain of readers
    /// through both sides of each join, each node once.
    fn expand(
        &mut self,
        nodes: &[Node<'_>],
        chains: &[Option<Chains>],
        y: &Arc<str>,
        joined: bool,
    ) {
        let read = |n: usize| {
            chains[n]
                .as_ref()
                .expect("an ancestor of a settled node is settled")
                .read
                .get(y)
                .copied()
        };
        let mut seen = HashSet::new();
        let mut stack: Vec<(usize, bool)> =
            read(self.above).map(|q| (q, joined)).into_iter().collect();
        while let Some((k, case)) = stack.pop() {
            if !seen.insert(k) {
                continue;
            }
            match &nodes[k] {
                Node::Root => {}
                Node::Assume { parent, fresh, .. } => {
                    if self.expanded.insert(k) {
                        for (z, _) in fresh.iter() {
                            if !self.via.contains_key(z) {
                                self.via.insert(z.clone(), Some((k, y.clone(), case)));
                                self.queue.push_back((z.clone(), case));
                            }
                        }
                    }
                    stack.extend(read(*parent).map(|q| (q, case)));
                }
                Node::Join(a, b) => {
                    for side in [*b, *a] {
                        stack.extend(read(side).map(|q| (q, true)));
                    }
                }
            }
        }
    }
}

/// The chain of a join `k` of two nodes whose chains are `a` and `b`: `a`'s, with each name the
/// two map differently mapped to `k`.
fn joined(
    a: &imbl::OrdMap<Arc<str>, usize>,
    b: &imbl::OrdMap<Arc<str>, usize>,
    k: usize,
) -> imbl::OrdMap<Arc<str>, usize> {
    let mut m = a.clone();
    for d in a.diff(b) {
        let x = match d {
            DiffItem::Add(x, _) | DiffItem::Remove(x, _) => x,
            DiffItem::Update { old: (x, _), .. } => x,
        };
        m.insert(x.clone(), k);
    }
    m
}

/// The kernel primitive of the operator `o` of the text, for the operators a test is read by.
fn prim_of(o: &str) -> Option<Prim> {
    Some(match o {
        "+" => Prim::Add,
        "-" => Prim::Sub,
        "*" => Prim::Mul,
        "div" => Prim::IntDiv,
        "mod" => Prim::Mod,
        "==" => Prim::Eq,
        "!=" => Prim::Ne,
        "<" => Prim::Lt,
        "<=" => Prim::Le,
        ">" => Prim::Gt,
        ">=" => Prim::Ge,
        "&&" => Prim::And,
        "||" => Prim::Or,
        _ => return None,
    })
}

/// The scalars and atoms of `ty`, when it holds nothing else.
fn plain(ty: &Ty) -> Option<KType> {
    (ty.tuples.is_empty() && ty.fns.is_empty() && ty.vars.is_empty() && !ty.dynamic)
        .then(|| ty.set.clone())
}

/// The name of binder `id` in the scope: its text and its number, so two binders of one name
/// are two names, and a shadowing name says nothing of the one it shadows.
fn var(name: &str, id: usize) -> Arc<str> {
    format!("{name}@{id}").into()
}

impl<'a> Ck<'_, 'a> {
    /// The ints `e` may be here: what its text shows ([`Ck::known`]) met with what the tests
    /// the walk is in show of it; and whether a test narrowed it.
    pub(super) fn ints_here(&mut self, e: &'a Expr) -> (IntervalSet, bool) {
        let k = self.known(e);
        if k.value.is_some() || self.arms.here() == 0 {
            return (k.ints, false);
        }
        let narrowed = self.ints_in_scope(e);
        let ints = k.ints.meet(&narrowed);
        let changed = ints != k.ints;
        (ints, changed)
    }

    /// The two nodes of the condition `e` checked here, where it holds and where it fails, with
    /// the products of its names taken from their types as they are here: a type an `is` has
    /// narrowed holds here, and may not where the scope is read.
    pub(super) fn test_nodes(&mut self, e: &'a Expr) -> (usize, usize) {
        let t = self.term(e);
        let fresh = t
            .vars
            .iter()
            .map(|(x, id)| {
                let p = match self.env.get(id).and_then(plain) {
                    Some(t) => Product::of_type(t),
                    None => Product::top(),
                };
                (x.clone(), p)
            })
            .collect();
        self.arms.test(e, fresh)
    }

    /// A note at each test the walk is in that bears on the operand `e`, innermost first, for a
    /// rejection whose operand a test narrowed ([`Arms::deciding`]): a test that changed a name
    /// `e` reads, or one the value of a name bound in an arm reads, where it was bound
    /// ([`Arms::bound`]), or one that changed a name such a test reads (`a == b` relates `b` to
    /// a test on `a`).
    pub(super) fn deciding_notes(&mut self, e: &'a Expr) -> Vec<Note> {
        let starts = self.read_names(e);
        self.arms
            .deciding(starts)
            .into_iter()
            .map(|(span, outcome, case)| Note {
                span,
                text: match case {
                    false => format!("this test is {outcome} here"),
                    true => format!("this test is {outcome} in one case here"),
                },
            })
            .collect()
    }

    /// The scope names `e` reads, each with the node it is read under: its own, under the node
    /// the walk is in, and those of the values of the names bound in an arm that it reads,
    /// through binders of binders, each binder once, under the node the binder was bound
    /// under, where its value is read ([`Item::Bound`]).
    fn read_names(&mut self, e: &'a Expr) -> Vec<(Arc<str>, usize)> {
        let t = self.term(e);
        let here = self.arms.here();
        let mut out: Vec<(Arc<str>, usize)> =
            t.vars.iter().map(|(x, _)| (x.clone(), here)).collect();
        let mut seen = HashSet::new();
        let mut stack = t.binders.clone();
        while let Some(b) = stack.pop() {
            if !seen.insert(b) {
                continue;
            }
            let Some(&value) = self.facts.get(&b) else {
                continue;
            };
            let v = self.term(value);
            let at = self.arms.bound_at.get(&b).copied().unwrap_or(0);
            out.extend(v.vars.iter().map(|(x, _)| (x.clone(), at)));
            stack.extend_from_slice(&v.binders);
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    /// The ints `e` may be in the scope of the node the walk is in.
    fn ints_in_scope(&mut self, e: &'a Expr) -> IntervalSet {
        let t = self.term(e);
        let here = self.arms.here();
        let mut wanted = vec![Item::Scope(here)];
        wanted.extend(t.binders.iter().map(|&b| Item::Bound(b)));
        self.settle(wanted);
        let s = self.arms.scopes[here].clone().expect("settled");
        let mut s = self.with_bound(s, &t.binders);
        product::forward(&t.term, &mut s).ints().clone()
    }

    /// `s` told of the values of `binders` it has no product of.
    fn with_bound(&self, mut s: Scope, binders: &[usize]) -> Scope {
        if s.bottom {
            return s;
        }
        for b in binders {
            let (Some(p), Some(name)) = (self.arms.bound.get(b), self.arms.names.get(b)) else {
                continue;
            };
            if !s.names.contains_key(name) {
                let e = Shared::new(Term::Var(name.clone()));
                s.bind(name, p.clone(), &e);
            }
        }
        s
    }

    /// Computes the scopes and binder products `wanted` needs, each once, on an explicit stack:
    /// an item is computed when every item it waits on is, and the memo is the visited set.
    fn settle(&mut self, wanted: Vec<Item>) {
        let mut entered = HashSet::new();
        let mut stack: Vec<(Item, bool)> = wanted.into_iter().map(|i| (i, false)).collect();
        while let Some((item, ready)) = stack.pop() {
            if self.computed(item) {
                continue;
            }
            if ready {
                self.compute(item);
            } else if entered.insert(item) {
                stack.push((item, true));
                for d in self.waits(item) {
                    if !self.computed(d) {
                        stack.push((d, false));
                    }
                }
            }
        }
    }

    fn computed(&self, item: Item) -> bool {
        match item {
            Item::Scope(n) => self.arms.scopes[n].is_some(),
            Item::Bound(b) => self.arms.bound.contains_key(&b),
        }
    }

    /// The items `item` is computed from.
    fn waits(&mut self, item: Item) -> Vec<Item> {
        match item {
            Item::Scope(n) => match self.arms.nodes[n] {
                Node::Root => Vec::new(),
                Node::Assume { parent, test, .. } => {
                    let t = self.term(test);
                    let mut out = vec![Item::Scope(parent)];
                    out.extend(t.binders.iter().map(|&b| Item::Bound(b)));
                    out
                }
                Node::Join(a, b) => vec![Item::Scope(a), Item::Scope(b)],
            },
            Item::Bound(b) => {
                let Some(&value) = self.facts.get(&b) else {
                    return Vec::new();
                };
                let t = self.term(value);
                let at = self.arms.bound_at.get(&b).copied().unwrap_or(0);
                let mut out = vec![Item::Scope(at)];
                out.extend(t.binders.iter().map(|&c| Item::Bound(c)));
                out
            }
        }
    }

    /// Computes `item` from the items it waits on. One still being computed, which only a
    /// cycle through binders could give, is read as saying nothing.
    fn compute(&mut self, item: Item) {
        match item {
            Item::Scope(n) => {
                let s = match self.arms.nodes[n] {
                    Node::Root => Scope::new([]),
                    Node::Assume {
                        parent,
                        test,
                        outcome,
                        ..
                    } => {
                        let t = self.term(test);
                        let p = self.scope_or_root(parent);
                        // A bound name the scope has no product of is its value, and any other
                        // name any value of its type where the test is checked. A scope no
                        // state reaches is told of none: it stays unreachable.
                        let mut p = self.with_bound(p, &t.binders);
                        if let Node::Assume { fresh, .. } = &self.arms.nodes[n]
                            && !p.bottom
                        {
                            for (x, q) in fresh.iter() {
                                if !p.names.contains_key(x) {
                                    p.bind(x, q.clone(), &Shared::new(Term::Var(x.clone())));
                                }
                            }
                        }
                        // Not shown, so a failing test leaves the names as they were
                        // (`assume_case`): emptying each costs the names in scope.
                        //
                        // Complexity tradeoff: the scope is settled whole, every name the test
                        // changes through the relation reduced, though a read needs only its own
                        // names. What is given up is time, not an answer: under `k` tests
                        // `ai >= n`, each of `k` tests on `n` that moves `n` projects all `k`
                        // blocks `ai >= n`, so the nest costs `k²` projections while one read
                        // needs `2k` (0.29 to 24.1 s at `k` = 25 to 200, 82 times for 8 times).
                        // Why: a scope is one reduced product, and settling it per name read
                        // needs a reduction that projects only the blocks on the path of the
                        // block-cut forest (`conjuncts::Blocks`) from the read name to those the
                        // new test touched, and that decides `bottom` without the whole scope.
                        // Trigger: many tests that move a name that many relations mention.
                        // Test: `l01_39a_bit_words::scaling::a_hub_settles_its_scopes_in_time_linear_in_the_tests`
                        // (ignored). COMPLEXITY.md C26, open item NARROW-hub-settle. A complete
                        // solution settles a scope lazily per name read along that path, at
                        // O(path log n) a read.
                        let s = p.assume_case(&t.term, outcome, &Premises::new());
                        // The names the test changed, for a rejection's notes: the two maps
                        // share all but what the test wrote, which the difference skips to.
                        let changed: Vec<Arc<str>> = match (p.bottom, s.bottom) {
                            (true, _) => Vec::new(),
                            (false, true) => t.vars.iter().map(|(x, _)| x.clone()).collect(),
                            (false, false) => p
                                .names
                                .diff(&s.names)
                                .map(|d| match d {
                                    DiffItem::Add(x, _) | DiffItem::Remove(x, _) => x.clone(),
                                    DiffItem::Update { old: (x, _), .. } => x.clone(),
                                })
                                .collect(),
                        };
                        self.arms.narrows[n] = Some(changed);
                        s
                    }
                    Node::Join(a, b) => self.scope_or_root(a).join(&self.scope_or_root(b)),
                };
                self.arms.scopes[n] = Some(s);
            }
            Item::Bound(b) => {
                let Some(&value) = self.facts.get(&b) else {
                    return;
                };
                let t = self.term(value);
                let at = self.arms.bound_at.get(&b).copied().unwrap_or(0);
                let s = self.scope_or_root(at);
                let mut s = self.with_bound(s, &t.binders);
                let mut p = product::forward(&t.term, &mut s);
                if let Some(ty) = self.arms.bound_ty.get(&b) {
                    p.ty.element = p.ty.element.meet(ty);
                }
                self.arms.bound.insert(b, p);
            }
        }
    }

    fn scope_or_root(&self, n: usize) -> Scope {
        self.arms.scopes[n]
            .clone()
            .unwrap_or_else(|| Scope::new([]))
    }

    /// `e` as a kernel term ([`Translated`]): its int and bool literals and the values its text
    /// shows ([`Ck::known`]), its names, its unary `-` and `!`, its integer operators, its
    /// comparisons, `&&` and `||`; anything else is a name of its own, by its span, which the
    /// scope knows nothing of. Built children first on an explicit stack, once for `e`.
    fn term(&mut self, e: &'a Expr) -> Rc<Translated> {
        if let Some(t) = self.arms.terms.get(&e.span) {
            return t.clone();
        }
        let (mut binders, mut vars) = (Vec::new(), Vec::new());
        let mut done: Vec<Term> = Vec::new();
        let mut stack = vec![(e, false)];
        while let Some((x, ready)) = stack.pop() {
            let opaque = || Term::Var(format!("?{}:{}", x.span.start, x.span.end).into());
            if ready {
                let t = match &x.kind {
                    ExprKind::Unary(o, _) => {
                        let a = done.pop().expect("an operand");
                        let p = if *o == "-" { Prim::Neg } else { Prim::Not };
                        Term::Prim(p, vec![a])
                    }
                    ExprKind::Binary(o, _, _) => {
                        let b = done.pop().expect("a second operand");
                        let a = done.pop().expect("a first operand");
                        Term::Prim(prim_of(o).expect("a translated operator"), vec![a, b])
                    }
                    _ => unreachable!("only operators wait on their operands"),
                };
                done.push(t);
                continue;
            }
            if let Some(v) = self.known(x).value {
                done.push(Term::Lit(v));
                continue;
            }
            match &x.kind {
                ExprKind::Bool(b) => done.push(Term::Lit(Value::Bool(*b))),
                ExprKind::Name(n) => match self.t.res.uses.get(&x.span) {
                    Some(Ref::Bound(ids)) if ids.len() == 1 => {
                        let id = ids[0];
                        let name = var(n, id);
                        if self.facts.contains_key(&id) {
                            binders.push(id);
                            self.arms.names.insert(id, name.clone());
                        }
                        vars.push((name.clone(), id));
                        done.push(Term::Var(name));
                    }
                    _ => done.push(opaque()),
                },
                ExprKind::Unary("-" | "!", a) => {
                    stack.push((x, true));
                    stack.push((a, false));
                }
                ExprKind::Binary(o, a, b) if prim_of(o).is_some() => {
                    stack.push((x, true));
                    stack.push((b, false));
                    stack.push((a, false));
                }
                _ => done.push(opaque()),
            }
        }
        binders.sort_unstable();
        binders.dedup();
        vars.sort_unstable();
        vars.dedup();
        let t = Rc::new(Translated {
            term: done.pop().expect("a term"),
            binders,
            vars,
        });
        self.arms.terms.insert(e.span, t.clone());
        t
    }
}
