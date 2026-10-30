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
//! `2^C` nodes. A union or intersection therefore stops after [`budget`] pairs of nodes, and its
//! part is then kept as the expression (`Part::Expr`), built in constant time. An expression is
//! decided through two diagrams within the budget that bound it from below and above
//! (`Part::bounds`): a lower bound with a value shows it inhabited, and an empty upper bound
//! shows it empty.

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering as Atomic};
use std::sync::{Arc, OnceLock};

use super::{Morphism, Op, Type, mix};

#[derive(Clone)]
pub(super) enum Bdd<A> {
    Leaf(bool),
    Node(Arc<Branch<A>>),
}

thread_local! {
    static BUDGET: Cell<usize> = const { Cell::new(4096) };
}

/// The most nodes a walk over the paths of a diagram visits.
pub(super) const WALK: usize = 1 << 16;

/// The most pairs of nodes a union or intersection of two diagrams visits.
pub(super) fn budget() -> usize {
    BUDGET.with(Cell::get)
}

/// Runs `f` with the budget of a union or intersection set to `n` on this thread. Results decided meanwhile stay in the
/// thread's tables.
pub(super) fn with_budget<R>(n: usize, f: impl FnOnce() -> R) -> R {
    let old = BUDGET.with(|b| b.replace(n));
    let r = f();
    BUDGET.with(|b| b.set(old));
    r
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

    /// The union or intersection, or `None` past [`budget`] pairs of nodes.
    pub(super) fn zip(&self, other: &Bdd<A>, op: Op) -> Option<Bdd<A>> {
        self.apply(other, op, &mut HashMap::new())
    }

    fn apply(
        &self,
        other: &Bdd<A>,
        op: Op,
        memo: &mut HashMap<(u64, u64), Bdd<A>>,
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
        if memo.len() >= budget() {
            return None;
        }
        let (Bdd::Node(a), Bdd::Node(b)) = (self, other) else {
            unreachable!("both leaves were handled")
        };
        let r = match a.atom.cmp(&b.atom) {
            Ordering::Equal => Bdd::node(
                a.atom.clone(),
                a.hi.apply(&b.hi, op, memo)?,
                a.lo.apply(&b.lo, op, memo)?,
            ),
            Ordering::Less => Bdd::node(
                a.atom.clone(),
                a.hi.apply(other, op, memo)?,
                a.lo.apply(other, op, memo)?,
            ),
            Ordering::Greater => Bdd::node(
                b.atom.clone(),
                self.apply(&b.hi, op, memo)?,
                self.apply(&b.lo, op, memo)?,
            ),
        };
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
    /// it refuses, in order; `None` once `budget` nodes have been visited. Below a node whose
    /// `hi` is `true` the `lo` path does not refuse the node's atom, since `a | (!a & L)` is
    /// `a | L`, so a union of atoms is a path per atom.
    pub(super) fn paths<'a>(
        &'a self,
        budget: &mut usize,
        f: &mut impl FnMut(&[&'a A], &[&'a A]) -> bool,
    ) -> Option<bool> {
        fn go<'a, A>(
            b: &'a Bdd<A>,
            pos: &mut Vec<&'a A>,
            neg: &mut Vec<&'a A>,
            budget: &mut usize,
            f: &mut impl FnMut(&[&'a A], &[&'a A]) -> bool,
        ) -> Option<bool> {
            *budget = budget.checked_sub(1)?;
            let n = match b {
                Bdd::Leaf(false) => return Some(true),
                Bdd::Leaf(true) => return Some(f(pos, neg)),
                Bdd::Node(n) => n,
            };
            pos.push(&n.atom);
            let hi = go(&n.hi, pos, neg, budget, f);
            pos.pop();
            if hi != Some(true) {
                return hi;
            }
            let refuse = !matches!(n.hi, Bdd::Leaf(true));
            if refuse {
                neg.push(&n.atom);
            }
            let lo = go(&n.lo, pos, neg, budget, f);
            if refuse {
                neg.pop();
            }
            lo
        }
        go(self, &mut Vec::new(), &mut Vec::new(), budget, f)
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
/// would pass the budget, the connective applied to its operands.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum Part<A: Ord> {
    Bdd(Bdd<A>),
    Expr(Arc<Expr<A>>),
}

pub(super) struct Expr<A: Ord> {
    digest: u64,
    form: Form<A>,
    bounds: OnceLock<(Bdd<A>, Bdd<A>)>,
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
        Part::Expr(Arc::new(Expr {
            digest,
            form,
            bounds: OnceLock::new(),
        }))
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

    /// Two diagrams within the budget, the first within the part and the part within the
    /// second. Where a connective's bound would pass the budget, it is an operand's bound, or
    /// the empty or the whole universe.
    pub(super) fn bounds(&self) -> (Bdd<A>, Bdd<A>) {
        let e = match self {
            Part::Bdd(b) => return (b.clone(), b.clone()),
            Part::Expr(e) => e,
        };
        e.bounds
            .get_or_init(|| {
                // Past the budget, one operand's lower bound is still below a union, and one
                // operand's upper bound still above an intersection.
                let zip = |a: &Part<A>, b: &Part<A>, op: Op| {
                    let ((al, au), (bl, bu)) = (a.bounds(), b.bounds());
                    let (lo, up) = (al.zip(&bl, op), au.zip(&bu, op));
                    match op {
                        Op::Or => (lo.unwrap_or(al), up.unwrap_or(Bdd::Leaf(true))),
                        Op::And => (lo.unwrap_or(Bdd::Leaf(false)), up.unwrap_or(au)),
                    }
                };
                match &e.form {
                    Form::Not(p) => {
                        let (l, u) = p.bounds();
                        (u.not(), l.not())
                    }
                    Form::Or(a, b) => zip(a, b, Op::Or),
                    Form::And(a, b) => zip(a, b, Op::And),
                }
            })
            .clone()
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

    #[test]
    fn bounds_enclose_the_part() {
        // With a budget of one pair of nodes most connectives are kept as expressions. Each
        // set of atoms that holds is one assignment; the lower bound implies the part, which
        // implies the upper bound.
        with_budget(1, || {
            let (mut seed, mut exprs, mut loose) = (7, 0, 0);
            for _ in 0..3000 {
                let p = random(&mut seed, 6);
                let (lo, up) = p.bounds();
                exprs += usize::from(matches!(p, Part::Expr(_)));
                for set in 0..64u32 {
                    let holds =
                        |t: &Vec<Type>| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i));
                    let (l, v, u) = (lo.eval(holds), p.eval(&holds), up.eval(holds));
                    assert!(
                        !l || v,
                        "{p:?}: lower bound {lo:?} not within it at {set:b}"
                    );
                    assert!(!v || u, "{p:?}: upper bound {up:?} not above it at {set:b}");
                    loose += usize::from(l != u);
                }
            }
            assert!(exprs > 500 && loose > 1000, "{exprs} {loose}");
        });
    }
}
