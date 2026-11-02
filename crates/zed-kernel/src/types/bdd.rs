//! Reduced ordered binary decision diagrams over the types of one universe (DESIGN.md
//! sec:type_language): the form of the tuple and morphism parts.
//!
//! A diagram is a leaf, no value of the universe or every value, or a node `(atom & hi) |
//! (!atom & lo)`, with each atom smaller than every atom below it and `hi` and `lo` distinct.
//! Two diagrams over one order of atoms denote one Boolean function of their atoms exactly when
//! they are equal. The complement swaps the leaves, in time linear in the size of the diagram,
//! and a union or intersection takes each pair of nodes at most once, in time the product of
//! the two sizes: a union of clauses would make the complement of a union of `C` clauses of two
//! types each a union of `2^C` clauses.
//!
//! Nodes are shared: the nodes of a thread are kept in a table, so that one atom with one pair
//! of children is one node, and two equal diagrams built on one thread are one pointer. Each
//! node and expression keeps a hash of its contents made from its children's, and two are
//! ordered by it first, so a comparison reads their contents only when the hashes are equal.
//!
//! A diagram is canonical, so some functions have only diagrams exponential in the number of
//! their atoms: `(m1 & !n1) | … | (mC & !nC)`, with every `m` ordered before every `n`, has
//! `2^C` nodes. A union or intersection therefore keeps its diagram only when it has no more
//! nodes than its two operands together, and otherwise keeps the expression (`Part::Expr`),
//! built in constant time; so a diagram has no more nodes than the atoms written to build it.
//! A part is decided (module `empty`) by three-valued operations, each linear in its nodes: it
//! is evaluated with some atoms known (`Part::eval3`), restricted to them (`Part::restrict`),
//! settled on its shared subexpressions (`Part::settle`), and asked which atoms every value
//! takes or refuses (`Part::forced`). None of them walks paths, whose number can be
//! exponential in the nodes. Listing values takes one pass over the nodes (`Bdd::reaching`);
//! `Bdd::paths` remains for display.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering as Atomic};

use super::{Morphism, Op, Row, mix};

#[derive(Clone)]
pub(super) enum Bdd<A> {
    Leaf(bool),
    Node(Arc<Branch<A>>),
}

pub(super) struct Branch<A> {
    id: u64,
    digest: u64,
    atom: A,
    hi: Bdd<A>,
    lo: Bdd<A>,
}

type Table<A> = BTreeMap<(A, u64, u64), Arc<Branch<A>>>;

/// The atoms of a universe, each kind with its thread's table of nodes.
pub(super) trait Literal: Ord + Clone + 'static {
    fn table<R>(f: impl FnOnce(&mut Table<Self>) -> R) -> R;
    /// A hash of the atom, equal for equal atoms.
    fn digest(&self) -> u64;
}

thread_local! {
    static TUPLES: RefCell<Table<Row>> = const { RefCell::new(BTreeMap::new()) };
    static MORPHISMS: RefCell<Table<Morphism>> = const { RefCell::new(BTreeMap::new()) };
}

impl Literal for Row {
    fn table<R>(f: impl FnOnce(&mut Table<Self>) -> R) -> R {
        TUPLES.with(|t| f(&mut t.borrow_mut()))
    }
    fn digest(&self) -> u64 {
        Row::digest(self)
    }
}

impl Literal for Morphism {
    fn table<R>(f: impl FnOnce(&mut Table<Self>) -> R) -> R {
        MORPHISMS.with(|t| f(&mut t.borrow_mut()))
    }
    fn digest(&self) -> u64 {
        let m = mix(6, self.guarantee.digest());
        mix(mix(m, self.permission.digest()), self.value.digest())
    }
}

impl<A: Literal> Bdd<A> {
    pub(super) fn literal(a: A) -> Bdd<A> {
        Bdd::node(a, Bdd::Leaf(true), Bdd::Leaf(false))
    }

    fn id(&self) -> u64 {
        match self {
            Bdd::Leaf(b) => u64::from(*b),
            Bdd::Node(n) => n.id,
        }
    }

    fn digest(&self) -> u64 {
        match self {
            Bdd::Leaf(b) => mix(7, u64::from(*b)),
            Bdd::Node(n) => n.digest,
        }
    }

    fn node(atom: A, hi: Bdd<A>, lo: Bdd<A>) -> Bdd<A> {
        static NEXT: AtomicU64 = AtomicU64::new(2);
        if hi == lo {
            return hi;
        }
        let key = (atom, hi.id(), lo.id());
        if let Some(n) = A::table(|t| t.get(&key).cloned()) {
            return Bdd::Node(n);
        }
        let n = Arc::new(Branch {
            id: NEXT.fetch_add(1, Atomic::Relaxed),
            digest: mix(mix(key.0.digest(), hi.digest()), lo.digest()),
            atom: key.0.clone(),
            hi,
            lo,
        });
        A::table(|t| t.insert(key, n.clone()));
        Bdd::Node(n)
    }

    /// The union or intersection, or `None` when it would have more nodes than the two
    /// operands together.
    pub(super) fn zip(&self, other: &Bdd<A>, op: Op) -> Option<Bdd<A>> {
        let mut made = HashSet::new();
        self.apply(
            other,
            op,
            &mut HashMap::new(),
            &mut made,
            self.size() + other.size(),
        )
    }

    /// The number of nodes.
    fn size(&self) -> usize {
        let mut n = 0;
        self.atoms(&mut |_| {
            n += 1;
            true
        });
        n
    }

    fn apply(
        &self,
        other: &Bdd<A>,
        op: Op,
        memo: &mut HashMap<(u64, u64), Bdd<A>>,
        made: &mut HashSet<u64>,
        most: usize,
    ) -> Option<Bdd<A>> {
        match (op, self, other) {
            (Op::And, Bdd::Leaf(false), _) | (Op::And, _, Bdd::Leaf(false)) => {
                return Some(Bdd::Leaf(false));
            }
            (Op::Or, Bdd::Leaf(true), _) | (Op::Or, _, Bdd::Leaf(true)) => {
                return Some(Bdd::Leaf(true));
            }
            (_, Bdd::Leaf(_), x) | (_, x, Bdd::Leaf(_)) => return Some(x.clone()),
            _ if self.id() == other.id() => return Some(self.clone()),
            _ => {}
        }
        let key = (self.id(), other.id());
        if let Some(r) = memo.get(&key) {
            return Some(r.clone());
        }
        let (Bdd::Node(a), Bdd::Node(b)) = (self, other) else {
            unreachable!("both leaves were handled")
        };
        let r = match a.atom.cmp(&b.atom) {
            Ordering::Equal => Bdd::node(
                a.atom.clone(),
                a.hi.apply(&b.hi, op, memo, made, most)?,
                a.lo.apply(&b.lo, op, memo, made, most)?,
            ),
            Ordering::Less => Bdd::node(
                a.atom.clone(),
                a.hi.apply(other, op, memo, made, most)?,
                a.lo.apply(other, op, memo, made, most)?,
            ),
            Ordering::Greater => Bdd::node(
                b.atom.clone(),
                self.apply(&b.hi, op, memo, made, most)?,
                self.apply(&b.lo, op, memo, made, most)?,
            ),
        };
        // The result's nodes are among those made by this union or intersection.
        if let Bdd::Node(n) = &r
            && made.insert(n.id)
            && made.len() > most
        {
            return None;
        }
        memo.insert(key, r.clone());
        Some(r)
    }

    pub(super) fn not(&self) -> Bdd<A> {
        self.flip(&mut HashMap::new())
    }

    /// The diagram with each atom that `fix` decides replaced by its value, each node rebuilt
    /// once.
    fn restrict(
        &self,
        fix: &impl Fn(&A) -> Option<bool>,
        memo: &mut HashMap<u64, Bdd<A>>,
    ) -> Bdd<A> {
        let Bdd::Node(n) = self else {
            return self.clone();
        };
        if let Some(r) = memo.get(&n.id) {
            return r.clone();
        }
        let r = match fix(&n.atom) {
            Some(true) => n.hi.restrict(fix, memo),
            Some(false) => n.lo.restrict(fix, memo),
            None => Bdd::node(
                n.atom.clone(),
                n.hi.restrict(fix, memo),
                n.lo.restrict(fix, memo),
            ),
        };
        memo.insert(n.id, r.clone());
        r
    }

    /// The atoms taken on every path to `true`, and those refused on every path, found as the
    /// branches that dominate the `true` leaf: one pass over the nodes in topological order,
    /// each node's dominator the nearest common one of the branches into it.
    fn forced(&self) -> (Vec<A>, Vec<A>) {
        fn order<A>(
            b: &Bdd<A>,
            seen: &mut HashMap<u64, bool>,
            post: &mut Vec<Arc<Branch<A>>>,
        ) -> bool {
            let n = match b {
                Bdd::Leaf(v) => return *v,
                Bdd::Node(n) => n,
            };
            if let Some(r) = seen.get(&n.id) {
                return *r;
            }
            let hi = order(&n.hi, seen, post);
            let lo = order(&n.lo, seen, post);
            seen.insert(n.id, hi || lo);
            if hi || lo {
                post.push(n.clone());
            }
            hi || lo
        }
        let mut seen = HashMap::new();
        let mut post = Vec::new();
        if !order(self, &mut seen, &mut post) || post.is_empty() {
            return (Vec::new(), Vec::new());
        }
        // Dominator tree over the nodes, the branches between them, and the `true` leaf; a
        // branch is its node's index with `true` or `false` beside it.
        let mut index: HashMap<u64, usize> = HashMap::new();
        let mut up: Vec<usize> = Vec::new();
        let mut depth: Vec<usize> = Vec::new();
        let mut branch: Vec<Option<(usize, bool)>> = Vec::new();
        let leaf = 0;
        up.push(usize::MAX);
        depth.push(0);
        branch.push(None);
        fn meet(up: &[usize], depth: &[usize], mut a: usize, mut b: usize) -> usize {
            while a != b {
                if depth[a] >= depth[b] {
                    a = up[a];
                } else {
                    b = up[b];
                }
            }
            a
        }
        let nodes: Vec<Arc<Branch<A>>> = post.into_iter().rev().collect();
        for (k, n) in nodes.iter().enumerate() {
            index.insert(n.id, k + 1);
            up.push(if k == 0 { k + 1 } else { usize::MAX });
            depth.push(0);
            branch.push(None);
        }
        for (k, n) in nodes.iter().enumerate() {
            let u = k + 1;
            if u != 1 {
                depth[u] = depth[up[u]] + 1;
            }
            for (child, v) in [(&n.hi, true), (&n.lo, false)] {
                let c = match child {
                    Bdd::Leaf(true) => leaf,
                    Bdd::Leaf(false) => continue,
                    Bdd::Node(m) => match index.get(&m.id) {
                        Some(c) => *c,
                        None => continue,
                    },
                };
                let e = up.len();
                up.push(u);
                depth.push(depth[u] + 1);
                branch.push(Some((u, v)));
                up[c] = if up[c] == usize::MAX {
                    e
                } else {
                    meet(&up, &depth, up[c], e)
                };
            }
        }
        let (mut taken, mut refused) = (Vec::new(), Vec::new());
        let mut x = up[leaf];
        while x != 1 {
            if let Some((u, v)) = branch[x] {
                let a = nodes[u - 1].atom.clone();
                if v { taken.push(a) } else { refused.push(a) }
            }
            x = up[x];
        }
        (taken, refused)
    }

    fn flip(&self, memo: &mut HashMap<u64, Bdd<A>>) -> Bdd<A> {
        let Bdd::Node(n) = self else {
            return Bdd::Leaf(*self == Bdd::Leaf(false));
        };
        if let Some(r) = memo.get(&n.id) {
            return r.clone();
        }
        let r = Bdd::node(n.atom.clone(), n.hi.flip(memo), n.lo.flip(memo));
        memo.insert(n.id, r.clone());
        r
    }
}

impl<A> Bdd<A> {
    /// Whether `f` holds of every atom, each node visited once.
    pub(super) fn atoms(&self, f: &mut impl FnMut(&A) -> bool) -> bool {
        fn go<A>(b: &Bdd<A>, seen: &mut HashSet<u64>, f: &mut impl FnMut(&A) -> bool) -> bool {
            let Bdd::Node(n) = b else {
                return true;
            };
            !seen.insert(n.id) || (f(&n.atom) && go(&n.hi, seen, f) && go(&n.lo, seen, f))
        }
        go(self, &mut HashSet::new(), f)
    }

    /// Whether `f` holds of every path to the `true` leaf, given as the atoms it takes and those
    /// it refuses, in order, stopping at the first path where it does not. Below a node whose
    /// `hi` is `true` the `lo` path does not refuse the node's atom, since `a | (!a & L)` is
    /// `a | L`, so a union of atoms is a path per atom.
    pub(super) fn paths<'a>(&'a self, f: &mut impl FnMut(&[&'a A], &[&'a A]) -> bool) -> bool {
        self.walk(false, f)
    }

    /// [`Bdd::paths`]; with `prune`, `f` is also asked of each path's atoms taken so far with
    /// none refused, and the paths below are passed over when it holds: refusing more atoms
    /// only removes values, so if `f` holds of `pos` alone it holds of every path below.
    pub(super) fn walk<'a>(
        &'a self,
        prune: bool,
        f: &mut impl FnMut(&[&'a A], &[&'a A]) -> bool,
    ) -> bool {
        fn go<'a, A>(
            b: &'a Bdd<A>,
            prune: bool,
            pos: &mut Vec<&'a A>,
            neg: &mut Vec<&'a A>,
            f: &mut impl FnMut(&[&'a A], &[&'a A]) -> bool,
        ) -> bool {
            let n = match b {
                Bdd::Leaf(false) => return true,
                Bdd::Leaf(true) => return f(pos, neg),
                Bdd::Node(n) => n,
            };
            pos.push(&n.atom);
            let hi = (prune && !matches!(n.hi, Bdd::Leaf(false)) && f(pos, &[]))
                || go(&n.hi, prune, pos, neg, f);
            pos.pop();
            if !hi {
                return false;
            }
            let refuse = !matches!(n.hi, Bdd::Leaf(true));
            if refuse {
                neg.push(&n.atom);
            }
            let lo = go(&n.lo, prune, pos, neg, f);
            if refuse {
                neg.pop();
            }
            lo
        }
        go(self, prune, &mut Vec::new(), &mut Vec::new(), f)
    }

    /// Whether `f` holds of each node's atom and state, for the nodes whose `hi` is not
    /// `false`. The root has the state `start`; an edge to a node's `hi` passes on `take` of its
    /// state and its atom, an edge to its `lo` its state; a node's state is `join` of the states
    /// of the edges into it. Each node is visited once, after every node with an edge into it,
    /// so the time is linear in the nodes however many paths there are.
    pub(super) fn reaching<S>(
        &self,
        start: S,
        take: impl Fn(&S, &A) -> S,
        join: impl Fn(&S, &S) -> S,
        mut f: impl FnMut(&A, &S) -> bool,
    ) -> bool {
        let Bdd::Node(root) = self else {
            return true;
        };
        // Nodes in reverse postorder of a depth-first walk: each after those above it.
        let mut order: Vec<&Branch<A>> = Vec::new();
        let mut seen = HashSet::new();
        let mut stack: Vec<(&Branch<A>, bool)> = vec![(root, false)];
        while let Some((n, below)) = stack.pop() {
            if below {
                order.push(n);
                continue;
            }
            if !seen.insert(n.id) {
                continue;
            }
            stack.push((n, true));
            for c in [&n.lo, &n.hi] {
                if let Bdd::Node(c) = c
                    && !seen.contains(&c.id)
                {
                    stack.push((c, false));
                }
            }
        }
        let mut state: HashMap<u64, S> = HashMap::from([(root.id, start)]);
        for n in order.into_iter().rev() {
            let here = state.remove(&n.id).expect("a node is reached before it is visited");
            if !matches!(n.hi, Bdd::Leaf(false)) && !f(&n.atom, &here) {
                return false;
            }
            for (child, s) in [(&n.hi, take(&here, &n.atom)), (&n.lo, here)] {
                match child {
                    Bdd::Leaf(_) => {}
                    Bdd::Node(c) => {
                        let s = match state.remove(&c.id) {
                            Some(t) => join(&t, &s),
                            None => s,
                        };
                        state.insert(c.id, s);
                    }
                }
            }
        }
        true
    }

    /// Whether the path that `holds` chooses at each atom ends at `true`.
    pub(super) fn eval(&self, holds: impl Fn(&A) -> bool) -> bool {
        let mut b = self;
        loop {
            match b {
                Bdd::Leaf(v) => return *v,
                Bdd::Node(n) => b = if holds(&n.atom) { &n.hi } else { &n.lo },
            }
        }
    }
}

/// A tuple part of one length, or the morphism part: a diagram, or, when a connective's diagram
/// would have more nodes than its operands together, the connective applied to its operands.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum Part<A: Ord> {
    Bdd(Bdd<A>),
    Expr(Arc<Expr<A>>),
}

pub(super) struct Expr<A: Ord> {
    digest: u64,
    form: Form<A>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum Form<A: Ord> {
    Not(Part<A>),
    Or(Part<A>, Part<A>),
    And(Part<A>, Part<A>),
}

impl<A: Literal> Part<A> {
    /// The hash of the part's contents.
    pub(super) fn digest(&self) -> u64 {
        match self {
            Part::Bdd(b) => b.digest(),
            Part::Expr(e) => e.digest,
        }
    }

    pub(super) fn leaf(b: bool) -> Part<A> {
        Part::Bdd(Bdd::Leaf(b))
    }

    pub(super) fn literal(a: A) -> Part<A> {
        Part::Bdd(Bdd::literal(a))
    }

    /// Whether the part is no value (`Some(false)`) or every value (`Some(true)`) as built.
    pub(super) fn is_leaf(&self) -> Option<bool> {
        match self {
            Part::Bdd(Bdd::Leaf(b)) => Some(*b),
            _ => None,
        }
    }

    fn expr(form: Form<A>) -> Part<A> {
        let digest = match &form {
            Form::Not(p) => mix(8, p.digest()),
            Form::Or(a, b) => mix(mix(9, a.digest()), b.digest()),
            Form::And(a, b) => mix(mix(10, a.digest()), b.digest()),
        };
        Part::Expr(Arc::new(Expr { digest, form }))
    }

    pub(super) fn not(&self) -> Part<A> {
        match self {
            Part::Bdd(b) => Part::Bdd(b.not()),
            Part::Expr(e) => match &e.form {
                Form::Not(p) => p.clone(),
                _ => Part::expr(Form::Not(self.clone())),
            },
        }
    }

    pub(super) fn zip(&self, other: &Part<A>, op: Op) -> Part<A> {
        // A leaf that absorbs is the result; a leaf that does not leaves the other operand.
        let absorbs = op == Op::Or;
        match (self.is_leaf(), other.is_leaf()) {
            (Some(b), _) if b == absorbs => return self.clone(),
            (_, Some(b)) if b == absorbs => return other.clone(),
            (Some(_), _) => return other.clone(),
            (_, Some(_)) => return self.clone(),
            _ => {}
        }
        if let (Part::Bdd(a), Part::Bdd(b)) = (self, other)
            && let Some(r) = a.zip(b, op)
        {
            return Part::Bdd(r);
        }
        Part::expr(match op {
            Op::Or => Form::Or(self.clone(), other.clone()),
            Op::And => Form::And(self.clone(), other.clone()),
        })
    }

    /// Whether the value whose membership in each atom `holds` decides is in the part.
    pub(super) fn eval(&self, holds: &impl Fn(&A) -> bool) -> bool {
        fn go<A: Literal>(
            p: &Part<A>,
            holds: &impl Fn(&A) -> bool,
            memo: &mut HashMap<*const Expr<A>, bool>,
        ) -> bool {
            let e = match p {
                Part::Bdd(b) => return b.eval(holds),
                Part::Expr(e) => e,
            };
            if let Some(v) = memo.get(&Arc::as_ptr(e)) {
                return *v;
            }
            let v = match &e.form {
                Form::Not(a) => !go(a, holds, memo),
                Form::Or(a, b) => go(a, holds, memo) || go(b, holds, memo),
                Form::And(a, b) => go(a, holds, memo) && go(b, holds, memo),
            };
            memo.insert(Arc::as_ptr(e), v);
            v
        }
        go(self, holds, &mut HashMap::new())
    }

    /// The part's value on a set of values where `holds` gives each atom's: in every value
    /// (`Some(true)`), in none (`Some(false)`), or in some (`None`), by three-valued logic, each
    /// node and expression evaluated once. `Some(b)` is the part's value on every value of the
    /// set; `None` says nothing.
    pub(super) fn eval3(&self, holds: &impl Fn(&A) -> Option<bool>) -> Option<bool> {
        self.eval3_pinned(holds, &HashMap::new())
    }

    /// [`Part::eval3`], with each expression in `pins` taken to have the value beside it.
    fn eval3_pinned(
        &self,
        holds: &impl Fn(&A) -> Option<bool>,
        pins: &HashMap<*const Expr<A>, bool>,
    ) -> Option<bool> {
        fn bdd<A>(
            b: &Bdd<A>,
            holds: &impl Fn(&A) -> Option<bool>,
            memo: &mut HashMap<u64, Option<bool>>,
        ) -> Option<bool> {
            let n = match b {
                Bdd::Leaf(v) => return Some(*v),
                Bdd::Node(n) => n,
            };
            if let Some(v) = memo.get(&n.id) {
                return *v;
            }
            let v = match holds(&n.atom) {
                Some(true) => bdd(&n.hi, holds, memo),
                Some(false) => bdd(&n.lo, holds, memo),
                None => {
                    let hi = bdd(&n.hi, holds, memo);
                    if hi.is_none() { None } else { bdd(&n.lo, holds, memo).filter(|lo| Some(*lo) == hi) }
                }
            };
            memo.insert(n.id, v);
            v
        }
        let mut nodes = HashMap::new();
        let mut memo: HashMap<*const Expr<A>, Option<bool>> =
            pins.iter().map(|(e, v)| (*e, Some(*v))).collect();
        let mut stack = vec![self.clone()];
        // Each expression is evaluated after its operands, on a stack of parts still to do.
        while let Some(p) = stack.pop() {
            let e = match &p {
                Part::Bdd(b) => {
                    bdd(b, holds, &mut nodes);
                    continue;
                }
                Part::Expr(e) => e,
            };
            let key = Arc::as_ptr(e);
            if memo.contains_key(&key) {
                continue;
            }
            let value = |q: &Part<A>, nodes: &mut HashMap<u64, Option<bool>>, memo: &HashMap<*const Expr<A>, Option<bool>>| match q {
                Part::Bdd(b) => Some(bdd(b, holds, nodes)),
                Part::Expr(x) => memo.get(&Arc::as_ptr(x)).copied(),
            };
            let operands: Vec<&Part<A>> = match &e.form {
                Form::Not(a) => vec![a],
                Form::Or(a, b) | Form::And(a, b) => vec![a, b],
            };
            let vs: Vec<Option<Option<bool>>> =
                operands.iter().map(|q| value(q, &mut nodes, &memo)).collect();
            if vs.iter().any(|v| v.is_none()) {
                stack.push(p.clone());
                for (q, v) in operands.iter().zip(&vs) {
                    if v.is_none() {
                        stack.push((*q).clone());
                    }
                }
                continue;
            }
            let vs: Vec<Option<bool>> = vs.into_iter().flatten().collect();
            let v = match &e.form {
                Form::Not(_) => vs[0].map(|v| !v),
                Form::Or(..) => match (vs[0], vs[1]) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                },
                Form::And(..) => match (vs[0], vs[1]) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                },
            };
            memo.insert(key, v);
        }
        match self {
            Part::Bdd(b) => bdd(b, holds, &mut nodes),
            Part::Expr(e) => memo[&Arc::as_ptr(e)],
        }
    }

    /// The part with each expression used more than once in it replaced by `true` when making
    /// it `false` makes the part `false` by three-valued logic, every atom unknown, and by
    /// `false` in the converse case, until no more is replaced. Every value of the part is in,
    /// or outside, such an expression, so the result holds every value of the part, and may
    /// hold more: it is empty only if the part is.
    pub(super) fn settle(&self) -> Part<A> {
        let mut p = self.clone();
        loop {
            let mut uses: HashMap<*const Expr<A>, (usize, Arc<Expr<A>>)> = HashMap::new();
            let mut stack = vec![p.clone()];
            while let Some(q) = stack.pop() {
                let Part::Expr(e) = q else { continue };
                let n = &mut uses.entry(Arc::as_ptr(&e)).or_insert((0, e.clone())).0;
                *n += 1;
                if *n > 1 {
                    continue;
                }
                match &e.form {
                    Form::Not(a) => stack.push(a.clone()),
                    Form::Or(a, b) | Form::And(a, b) => {
                        stack.push(a.clone());
                        stack.push(b.clone());
                    }
                }
            }
            let mut pins = HashMap::new();
            for (key, (n, _)) in &uses {
                if *n < 2 {
                    continue;
                }
                for v in [true, false] {
                    let mut tried = pins.clone();
                    tried.insert(*key, !v);
                    if p.eval3_pinned(&|_| None, &tried) == Some(false) {
                        pins.insert(*key, v);
                        break;
                    }
                }
            }
            if pins.is_empty() {
                return p;
            }
            p = p.substitute_all(&pins);
        }
    }

    /// The part with each expression in `pins` replaced by its value, each rebuilt once.
    fn substitute_all(&self, pins: &HashMap<*const Expr<A>, bool>) -> Part<A> {
        fn go<A: Literal>(
            p: &Part<A>,
            pins: &HashMap<*const Expr<A>, bool>,
            memo: &mut HashMap<*const Expr<A>, Part<A>>,
        ) -> Part<A> {
            let Part::Expr(e) = p else {
                return p.clone();
            };
            let key = Arc::as_ptr(e);
            if let Some(v) = pins.get(&key) {
                return Part::leaf(*v);
            }
            if let Some(r) = memo.get(&key) {
                return r.clone();
            }
            let r = match &e.form {
                Form::Not(a) => go(a, pins, memo).not(),
                Form::Or(a, b) => go(a, pins, memo).zip(&go(b, pins, memo), Op::Or),
                Form::And(a, b) => go(a, pins, memo).zip(&go(b, pins, memo), Op::And),
            };
            memo.insert(key, r.clone());
            r
        }
        go(self, pins, &mut HashMap::new())
    }

    /// The part with each atom that `fix` decides replaced by its value, each node and
    /// expression rebuilt once.
    pub(super) fn restrict(&self, fix: &impl Fn(&A) -> Option<bool>) -> Part<A> {
        fn go<A: Literal>(
            p: &Part<A>,
            fix: &impl Fn(&A) -> Option<bool>,
            nodes: &mut HashMap<u64, Bdd<A>>,
            memo: &mut HashMap<*const Expr<A>, Part<A>>,
        ) -> Part<A> {
            let e = match p {
                Part::Bdd(b) => return Part::Bdd(b.restrict(fix, nodes)),
                Part::Expr(e) => e,
            };
            if let Some(r) = memo.get(&Arc::as_ptr(e)) {
                return r.clone();
            }
            let r = match &e.form {
                Form::Not(a) => go(a, fix, nodes, memo).not(),
                Form::Or(a, b) => go(a, fix, nodes, memo).zip(&go(b, fix, nodes, memo), Op::Or),
                Form::And(a, b) => go(a, fix, nodes, memo).zip(&go(b, fix, nodes, memo), Op::And),
            };
            memo.insert(Arc::as_ptr(e), r.clone());
            r
        }
        go(self, fix, &mut HashMap::new(), &mut HashMap::new())
    }

    /// The atoms in every value of the part (`.0`) and those in none (`.1`), among the atoms
    /// in it: for a diagram, those taken or refused on every path to `true`; for an expression,
    /// each atom whose refusal, or whose taking, makes the part `false` by three-valued logic.
    pub(super) fn forced(&self) -> (Vec<A>, Vec<A>) {
        if let Part::Bdd(b) = self {
            return b.forced();
        }
        let mut atoms = std::collections::BTreeSet::new();
        self.atoms(&mut |a| {
            atoms.insert(a.clone());
            true
        });
        let (mut taken, mut refused) = (Vec::new(), Vec::new());
        for a in atoms {
            if self.eval3(&|x| (*x == a).then_some(false)) == Some(false) {
                taken.push(a);
            } else if self.eval3(&|x| (*x == a).then_some(true)) == Some(false) {
                refused.push(a);
            }
        }
        (taken, refused)
    }

    /// Whether `f` holds of every atom, each node and expression visited once.
    pub(super) fn atoms(&self, f: &mut impl FnMut(&A) -> bool) -> bool {
        fn go<A: Literal>(
            p: &Part<A>,
            seen: &mut HashSet<*const Expr<A>>,
            f: &mut impl FnMut(&A) -> bool,
        ) -> bool {
            let e = match p {
                Part::Bdd(b) => return b.atoms(f),
                Part::Expr(e) => e,
            };
            if !seen.insert(Arc::as_ptr(e)) {
                return true;
            }
            match &e.form {
                Form::Not(a) => go(a, seen, f),
                Form::Or(a, b) | Form::And(a, b) => go(a, seen, f) && go(b, seen, f),
            }
        }
        go(self, &mut HashSet::new(), f)
    }

    /// The diagram, or the connective of an expression.
    pub(super) fn view(&self) -> Result<&Bdd<A>, &Form<A>> {
        match self {
            Part::Bdd(b) => Ok(b),
            Part::Expr(e) => Err(&e.form),
        }
    }
}

impl<A: Ord> Ord for Expr<A> {
    fn cmp(&self, other: &Expr<A>) -> Ordering {
        if std::ptr::eq(self, other) {
            return Ordering::Equal;
        }
        self.digest
            .cmp(&other.digest)
            .then_with(|| self.form.cmp(&other.form))
    }
}

impl<A: Ord> PartialOrd for Expr<A> {
    fn partial_cmp(&self, other: &Expr<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Ord> PartialEq for Expr<A> {
    fn eq(&self, other: &Expr<A>) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<A: Ord> Eq for Expr<A> {}

impl<A: Ord + fmt::Debug> fmt::Debug for Expr<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.form.fmt(f)
    }
}

impl<A: Ord> Ord for Bdd<A> {
    fn cmp(&self, other: &Bdd<A>) -> Ordering {
        match (self, other) {
            (Bdd::Leaf(a), Bdd::Leaf(b)) => a.cmp(b),
            (Bdd::Leaf(_), Bdd::Node(_)) => Ordering::Less,
            (Bdd::Node(_), Bdd::Leaf(_)) => Ordering::Greater,
            (Bdd::Node(a), Bdd::Node(b)) if Arc::ptr_eq(a, b) => Ordering::Equal,
            (Bdd::Node(a), Bdd::Node(b)) => a
                .digest
                .cmp(&b.digest)
                .then_with(|| a.atom.cmp(&b.atom))
                .then_with(|| a.hi.cmp(&b.hi))
                .then_with(|| a.lo.cmp(&b.lo)),
        }
    }
}

impl<A: Ord> PartialOrd for Bdd<A> {
    fn partial_cmp(&self, other: &Bdd<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Ord> PartialEq for Bdd<A> {
    fn eq(&self, other: &Bdd<A>) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<A: Ord> Eq for Bdd<A> {}

impl<A: fmt::Debug> fmt::Debug for Bdd<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bdd::Leaf(b) => write!(f, "{b}"),
            Bdd::Node(n) => f
                .debug_tuple("Node")
                .field(&n.atom)
                .field(&n.hi)
                .field(&n.lo)
                .finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Type;
    use crate::value::Value;

    /// The tuple type of one integer, an atom independent of the others.
    fn atom(i: u64) -> Row {
        Row::new(vec![Type::lit(&Value::Int(i as i64)).unwrap()])
    }

    fn random(seed: &mut u64, depth: u32) -> Part<Row> {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let pick = *seed >> 33;
        if depth == 0 || pick.is_multiple_of(5) {
            return Part::literal(atom(pick % 6));
        }
        let (a, b) = (random(seed, depth - 1), random(seed, depth - 1));
        match pick % 3 {
            0 => a.zip(&b, Op::Or),
            1 => a.zip(&b, Op::And),
            _ => a.not(),
        }
    }

    /// The part built from `random`'s connectives as expressions, so that every form is met;
    /// an operand is at times one built before, kept in `pool`, so that expressions are shared.
    fn random_expr(seed: &mut u64, depth: u32, pool: &mut Vec<Part<Row>>) -> Part<Row> {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let pick = *seed >> 33;
        if !pool.is_empty() && pick % 7 == 3 {
            return pool[(pick / 7) as usize % pool.len()].clone();
        }
        if depth == 0 || pick.is_multiple_of(5) {
            return random(seed, 2);
        }
        let (a, b) = (
            random_expr(seed, depth - 1, pool),
            random_expr(seed, depth - 1, pool),
        );
        let p = Part::expr(match pick % 3 {
            0 => Form::Or(a, b),
            1 => Form::And(a, b),
            _ => Form::Not(a),
        });
        pool.push(p.clone());
        p
    }

    #[test]
    fn three_valued_operations_keep_the_assignments() {
        // Each set of the six atoms is one assignment, and a partial assignment fixes the
        // atoms of `known` to their membership in `fixed`. A three-valued value is the value
        // of every assignment that agrees with it; restricting keeps the value of every
        // assignment agreeing with what it fixes; settling keeps every assignment in the
        // part, and makes it empty only when the part is; an atom forced taken is in every assignment in the part, and one
        // forced refused in none.
        let (mut seed, mut exprs, mut decided, mut forced, mut settled) = (7, 0, 0, 0, 0);
        for k in 0..3000u32 {
            let p = if seed % 2 == 0 {
                random(&mut seed, 6)
            } else {
                random_expr(&mut seed, 5, &mut Vec::new())
            };
            exprs += usize::from(matches!(p, Part::Expr(_)));
            let holds = |set: u32| move |t: &Row| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i));
            let inside: Vec<u32> = (0..64).filter(|&set| p.eval(&holds(set))).collect();
            let (known, fixed) = (k % 64, (k / 64) % 64);
            let fix = |t: &Row| (0..6).find(|&i| *t == atom(i) && known & (1 << i) != 0).map(|i| fixed & (1 << i) != 0);
            let agree = |set: u32| (set ^ fixed) & known == 0;
            if let Some(v) = p.eval3(&fix) {
                decided += 1;
                assert!((0..64).filter(|&s| agree(s)).all(|s| p.eval(&holds(s)) == v), "{p:?}");
            }
            let r = p.restrict(&fix);
            let t = p.settle();
            settled += usize::from(inside.is_empty() && t.is_leaf() == Some(false));
            for set in 0..64 {
                if agree(set) {
                    assert_eq!(r.eval(&holds(set)), p.eval(&holds(set)), "{p:?} at {set:b}");
                }
                assert!(!p.eval(&holds(set)) || t.eval(&holds(set)), "{p:?} at {set:b}");
            }
            let (taken, refused) = p.forced();
            forced += taken.len() + refused.len();
            for a in &taken {
                let i = (0..6).find(|&i| *a == atom(i)).unwrap();
                assert!(inside.iter().all(|s| s & (1 << i) != 0), "{p:?} takes {i}");
            }
            for a in &refused {
                let i = (0..6).find(|&i| *a == atom(i)).unwrap();
                assert!(inside.iter().all(|s| s & (1 << i) == 0), "{p:?} refuses {i}");
            }
        }
        assert!(
            exprs > 500 && decided > 300 && forced > 1000 && settled > 100,
            "{exprs} {decided} {forced} {settled}"
        );
    }
}
