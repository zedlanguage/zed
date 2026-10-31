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
//! An expression is decided by its paths (`Part::paths`): its Shannon expansion on the
//! smallest atom at its top, each step taking the cofactors of its operands, each operand
//! once. Emptiness of these Boolean combinations is coNP-hard, so the number of paths can be
//! exponential in the atoms; the walk holds one path at a time, and no count of nodes or
//! paths stops it.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering as Atomic};

use super::{Morphism, Op, Type, mix};

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
    static TUPLES: RefCell<Table<Vec<Type>>> = const { RefCell::new(BTreeMap::new()) };
    static MORPHISMS: RefCell<Table<Morphism>> = const { RefCell::new(BTreeMap::new()) };
}

impl Literal for Vec<Type> {
    fn table<R>(f: impl FnOnce(&mut Table<Self>) -> R) -> R {
        TUPLES.with(|t| f(&mut t.borrow_mut()))
    }
    fn digest(&self) -> u64 {
        self.iter().fold(5, |h, t| mix(h, t.digest()))
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

    /// Whether `f` holds of every path of the part to `true`, as [`Bdd::walk`] gives them with
    /// `prune`, stopping at the first path where it does not; `f` must hold of a path whenever
    /// it holds of one that takes a subset of its atoms and refuses a subset of its atoms. An
    /// expression is first expanded on a subexpression it shares between two operands: it is
    /// `x & e[x := true] | !x & e[x := false]`, and the two cofactors are built again from
    /// their operands, so a part like `b & !(b | a)` is `false` at once. Each expansion leaves
    /// one fewer shared subexpression. An expression that shares none is expanded on the
    /// smallest atom at the top of any of its diagrams, its cofactors being its operands'
    /// cofactors combined again.
    pub(super) fn paths(&self, f: &mut impl FnMut(&[&A], &[&A]) -> bool) -> bool {
        fn go<A: Literal>(
            p: &Part<A>,
            pos: &mut Vec<A>,
            neg: &mut Vec<A>,
            f: &mut impl FnMut(&[&A], &[&A]) -> bool,
        ) -> bool {
            let e = match p {
                // The diagram's own walk, after the atoms taken and refused so far.
                Part::Bdd(b) => {
                    return b.walk(true, &mut |bp, bn| {
                        let ps: Vec<&A> = pos.iter().chain(bp.iter().copied()).collect();
                        let ns: Vec<&A> = neg.iter().chain(bn.iter().copied()).collect();
                        f(&ps, &ns)
                    });
                }
                Part::Expr(e) => e,
            };
            if let Some(x) = p.shared() {
                let ex = Part::Expr(x.clone());
                return [true, false].into_iter().all(|v| {
                    let rest = p.substitute(&x, v, &mut HashMap::new());
                    let side = if v { ex.clone() } else { ex.not() };
                    go(&side.zip(&rest, Op::And), pos, neg, f)
                });
            }
            let Some(a) = p.top() else {
                // An expression of leaves alone is a constant.
                let ps: Vec<&A> = pos.iter().collect();
                let ns: Vec<&A> = neg.iter().collect();
                return !Part::Expr(e.clone()).eval(&|_| false) || f(&ps, &ns);
            };
            let hi = p.cofactor(&a, true, &mut HashMap::new());
            pos.push(a.clone());
            let r = hi.is_leaf() == Some(false)
                || {
                    let ps: Vec<&A> = pos.iter().collect();
                    f(&ps, &[])
                }
                || go(&hi, pos, neg, f);
            pos.pop();
            if !r {
                return false;
            }
            let lo = p.cofactor(&a, false, &mut HashMap::new());
            let refuse = hi.is_leaf() != Some(true);
            if refuse {
                neg.push(a);
            }
            let r = go(&lo, pos, neg, f);
            if refuse {
                neg.pop();
            }
            r
        }
        go(self, &mut Vec::new(), &mut Vec::new(), f)
    }

    /// An expression that is an operand of two connectives in the part, if any: the first met
    /// from the root, so the largest.
    fn shared(&self) -> Option<Arc<Expr<A>>> {
        fn count<A: Literal>(p: &Part<A>, seen: &mut HashMap<*const Expr<A>, usize>) {
            let Part::Expr(e) = p else { return };
            let n = seen.entry(Arc::as_ptr(e)).or_insert(0);
            *n += 1;
            if *n == 1 {
                match &e.form {
                    Form::Not(a) => count(a, seen),
                    Form::Or(a, b) | Form::And(a, b) => {
                        count(a, seen);
                        count(b, seen);
                    }
                }
            }
        }
        fn find<A: Literal>(
            p: &Part<A>,
            seen: &HashMap<*const Expr<A>, usize>,
            done: &mut HashSet<*const Expr<A>>,
        ) -> Option<Arc<Expr<A>>> {
            let Part::Expr(e) = p else { return None };
            if seen[&Arc::as_ptr(e)] > 1 {
                return Some(e.clone());
            }
            if !done.insert(Arc::as_ptr(e)) {
                return None;
            }
            match &e.form {
                Form::Not(a) => find(a, seen, done),
                Form::Or(a, b) | Form::And(a, b) => {
                    find(a, seen, done).or_else(|| find(b, seen, done))
                }
            }
        }
        let mut seen = HashMap::new();
        count(self, &mut seen);
        find(self, &seen, &mut HashSet::new())
    }

    /// The part with the expression `x` replaced by the leaf `v`, each expression rebuilt once.
    fn substitute(
        &self,
        x: &Arc<Expr<A>>,
        v: bool,
        memo: &mut HashMap<*const Expr<A>, Part<A>>,
    ) -> Part<A> {
        let Part::Expr(e) = self else {
            return self.clone();
        };
        if Arc::ptr_eq(e, x) {
            return Part::leaf(v);
        }
        if let Some(r) = memo.get(&Arc::as_ptr(e)) {
            return r.clone();
        }
        let r = match &e.form {
            Form::Not(a) => a.substitute(x, v, memo).not(),
            Form::Or(a, b) => a
                .substitute(x, v, memo)
                .zip(&b.substitute(x, v, memo), Op::Or),
            Form::And(a, b) => a
                .substitute(x, v, memo)
                .zip(&b.substitute(x, v, memo), Op::And),
        };
        memo.insert(Arc::as_ptr(e), r.clone());
        r
    }

    /// The smallest atom at the top of a diagram in the part, each expression visited once.
    fn top(&self) -> Option<A> {
        fn go<A: Literal>(p: &Part<A>, seen: &mut HashSet<*const Expr<A>>, best: &mut Option<A>) {
            match p {
                Part::Bdd(Bdd::Leaf(_)) => {}
                Part::Bdd(Bdd::Node(n)) => {
                    if best.as_ref().is_none_or(|b| n.atom < *b) {
                        *best = Some(n.atom.clone());
                    }
                }
                Part::Expr(e) => {
                    if seen.insert(Arc::as_ptr(e)) {
                        match &e.form {
                            Form::Not(a) => go(a, seen, best),
                            Form::Or(a, b) | Form::And(a, b) => {
                                go(a, seen, best);
                                go(b, seen, best);
                            }
                        }
                    }
                }
            }
        }
        let mut best = None;
        go(self, &mut HashSet::new(), &mut best);
        best
    }

    /// The part with `a` taken (`v`) or refused, for `a` no larger than any atom in it, each
    /// expression rebuilt once.
    fn cofactor(&self, a: &A, v: bool, memo: &mut HashMap<*const Expr<A>, Part<A>>) -> Part<A> {
        let e = match self {
            Part::Bdd(Bdd::Node(n)) if n.atom == *a => {
                return Part::Bdd(if v { n.hi.clone() } else { n.lo.clone() });
            }
            Part::Bdd(_) => return self.clone(),
            Part::Expr(e) => e,
        };
        if let Some(r) = memo.get(&Arc::as_ptr(e)) {
            return r.clone();
        }
        let r = match &e.form {
            Form::Not(x) => x.cofactor(a, v, memo).not(),
            Form::Or(x, y) => x.cofactor(a, v, memo).zip(&y.cofactor(a, v, memo), Op::Or),
            Form::And(x, y) => x.cofactor(a, v, memo).zip(&y.cofactor(a, v, memo), Op::And),
        };
        memo.insert(Arc::as_ptr(e), r.clone());
        r
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
    use crate::value::Value;

    /// The tuple type of one integer, an atom independent of the others.
    fn atom(i: u64) -> Vec<Type> {
        vec![Type::lit(&Value::Int(i as i64)).unwrap()]
    }

    fn random(seed: &mut u64, depth: u32) -> Part<Vec<Type>> {
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
    fn random_expr(seed: &mut u64, depth: u32, pool: &mut Vec<Part<Vec<Type>>>) -> Part<Vec<Type>> {
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
    fn the_paths_of_a_part_are_its_assignments() {
        // Each set of the six atoms is one assignment. It is outside the part exactly when
        // every path excludes it: takes an atom not in the set, or refuses one in it. That
        // test holds of a path whenever it holds of a path with fewer atoms, as `paths` asks.
        let (mut seed, mut exprs, mut shared, mut found) = (7, 0, 0, 0);
        for _ in 0..3000 {
            let p = if seed % 2 == 0 {
                random(&mut seed, 6)
            } else {
                random_expr(&mut seed, 5, &mut Vec::new())
            };
            exprs += usize::from(matches!(p, Part::Expr(_)));
            shared += usize::from(p.shared().is_some());
            for set in 0..64u32 {
                let holds = |t: &Vec<Type>| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i));
                let out = p.paths(&mut |pos, neg| {
                    pos.iter().any(|a| !holds(a)) || neg.iter().any(|a| holds(a))
                });
                assert_eq!(!out, p.eval(&holds), "{p:?} at {set:b}");
                found += usize::from(!out);
            }
        }
        assert!(
            exprs > 500 && shared > 200 && found > 10_000,
            "{exprs} {shared} {found}"
        );
    }
}
