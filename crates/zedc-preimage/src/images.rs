//! What a binder's summary reads in a scope, kept by input in a persistent tree with the sum of
//! each subtree, so that the summary read in a scope that differs from an earlier one at a few
//! inputs costs those inputs (items PA-let-narrow-many, PA-walk-multi).
//!
//! A binder `x` whose summary reads `k` inputs, read where tests have narrowed `h` of them,
//! holds where each input is the binding it was made over and its integers lie within those
//! it was made over, and its bounds move by each narrowed input's [`Shift`]. A chain
//! `x_k = x_(k-1) + q_k` under a test of each `q_k` reads `x_(k-1)` over all `k - 1` inputs;
//! read afresh at each binding the chain costs `Θ(d²)`, and kept here it costs `O(log k)` a
//! binding, since `x_(k-1)` read in the scope of `x_k` differs from `x_(k-2)` read in the scope
//! of `x_(k-1)` at a few inputs. The checker reads its binders' summaries here
//! (`Ck::read_image` in `zedc-check`), and [`product`](crate::product)'s walk the summaries
//! its `let`s keep (`Scope::holds`); each gives the leaf of an input in a scope.
//!
//! A test of such a binder reads the bounds of its summary's terms from a tree of the same
//! shape whose leaves are [`TermBounds`] ([`TermRead`], item PA-letpre-linear), so that the
//! test costs the inputs it narrows, each `O(log k)`, and not all `k`.

use std::fmt;
use std::sync::Arc;

use imbl::ordmap::DiffItem;
use zedc_lattice::cell::Premises;
use zedc_lattice::interval::IntervalSet;

use crate::preimage::{Shift, SummaryRead, TermBounds};

/// What a leaf of a [`Tree`] holds: a value per input with a sum, `zero` adding nothing.
pub trait Sum: Clone {
    /// The sum of no leaves.
    fn zero() -> Self;
    /// The sum of `self` and `o`.
    fn plus(&self, o: &Self) -> Self;
}

impl Sum for TermBounds {
    fn zero() -> Self {
        TermBounds::zero()
    }

    fn plus(&self, o: &Self) -> Self {
        TermBounds::plus(self, o)
    }
}

/// What one input adds, or the sum of a subtree's.
#[derive(Clone)]
pub struct Leaf {
    /// The input's shift of the summary's bounds ([`Shift`]), nothing when it fails.
    pub shift: Shift,
    /// The inputs where the summary does not hold: whose integers lie outside those it was made
    /// over, or that are another binding than it was made over.
    pub fails: usize,
    /// The premises of the inputs' products.
    pub premises: Premises,
}

impl Sum for Leaf {
    fn zero() -> Leaf {
        Leaf {
            shift: Shift::ZERO,
            fails: 0,
            premises: Premises::new(),
        }
    }

    fn plus(&self, o: &Leaf) -> Leaf {
        let mut premises = self.premises.clone();
        premises.extend(&o.premises);
        Leaf {
            shift: self.shift.plus(&o.shift),
            fails: self.fails + o.fails,
            premises,
        }
    }
}

/// A treap of the inputs, ordered by name, each node with its leaf and the sum of its
/// subtree's; a node's priority is a hash of its name, so the tree's shape depends on its
/// names alone and an update copies the `O(log h)` nodes of one path, expected.
pub type Tree<L = Leaf> = Option<Arc<Node<L>>>;

/// A node of a [`Tree`].
pub struct Node<L = Leaf> {
    key: Arc<str>,
    prio: u64,
    leaf: L,
    sum: L,
    /// The inputs of the subtree.
    size: usize,
    left: Tree<L>,
    right: Tree<L>,
}

/// The sum of every leaf of `t`.
pub fn total<L: Sum>(t: &Tree<L>) -> L {
    t.as_ref().map_or_else(L::zero, |n| n.sum.clone())
}

/// The inputs of `t`.
pub fn len<L>(t: &Tree<L>) -> usize {
    t.as_ref().map_or(0, |n| n.size)
}

/// Calls `f` on each input of `t` and its leaf in order of name, skipping each subtree whose
/// sum `want` refuses, until `f` gives `false`; gives whether it went on to the end. Visits
/// every leaf `want` takes when `want` holds of a sum whenever it holds of one of its leaves:
/// `O((m + 1) log h)` expected for the `m` leaves visited.
pub fn visit<L: Sum>(
    t: &Tree<L>,
    want: &dyn Fn(&L) -> bool,
    f: &mut dyn FnMut(&Arc<str>, &L) -> bool,
) -> bool {
    let Some(n) = t else {
        return true;
    };
    if !want(&n.sum) {
        return true;
    }
    visit(&n.left, want, f) && (!want(&n.leaf) || f(&n.key, &n.leaf)) && visit(&n.right, want, f)
}

/// `t` with `key`'s leaf set to `leaf`, or taken out at `None`. `O(log h)` expected.
fn set<L: Sum>(t: &Tree<L>, key: &Arc<str>, leaf: Option<L>) -> Tree<L> {
    let (below, above) = split(t, key);
    let above = without(above, key);
    let one = leaf.map(|l| node(key.clone(), prio(key), l, None, None));
    join(join(below, one), above)
}

fn node<L: Sum>(key: Arc<str>, prio: u64, leaf: L, left: Tree<L>, right: Tree<L>) -> Arc<Node<L>> {
    let sum = total(&left).plus(&leaf).plus(&total(&right));
    let size = len(&left) + 1 + len(&right);
    Arc::new(Node {
        key,
        prio,
        leaf,
        sum,
        size,
        left,
        right,
    })
}

/// The keys of `t` below `key`, and the others.
fn split<L: Sum>(t: &Tree<L>, key: &Arc<str>) -> (Tree<L>, Tree<L>) {
    let Some(n) = t else {
        return (None, None);
    };
    if n.key < *key {
        let (l, r) = split(&n.right, key);
        let left = node(n.key.clone(), n.prio, n.leaf.clone(), n.left.clone(), l);
        (Some(left), r)
    } else {
        let (l, r) = split(&n.left, key);
        let right = node(n.key.clone(), n.prio, n.leaf.clone(), r, n.right.clone());
        (l, Some(right))
    }
}

/// `t`, whose keys are `key` or above, without `key`, its least if it has it.
fn without<L: Sum>(t: Tree<L>, key: &Arc<str>) -> Tree<L> {
    let n = t?;
    if n.key == *key {
        return join(n.left.clone(), n.right.clone());
    }
    let left = without(n.left.clone(), key);
    Some(node(
        n.key.clone(),
        n.prio,
        n.leaf.clone(),
        left,
        n.right.clone(),
    ))
}

/// The nodes of `a`, then those of `b`, whose keys all lie above.
fn join<L: Sum>(a: Tree<L>, b: Tree<L>) -> Tree<L> {
    match (a, b) {
        (None, t) | (t, None) => t,
        (Some(a), Some(b)) => Some(if a.prio >= b.prio {
            let right = join(a.right.clone(), Some(b));
            node(a.key.clone(), a.prio, a.leaf.clone(), a.left.clone(), right)
        } else {
            let left = join(Some(a), b.left.clone());
            node(b.key.clone(), b.prio, b.leaf.clone(), left, b.right.clone())
        }),
    }
}

/// The priority of `key`: its bytes hashed by FNV-1a and mixed by splitmix64, the same in every
/// run.
fn prio(key: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in key.bytes() {
        h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
    }
    let mut z = h.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// What a summary read in one scope: the scope's names, what the caller keeps of the summary
/// and of the scope beside them (`S`), and the tree of the inputs it read there, each with its
/// leaf ([`Leaf`]). The scope gives each name a `P`, its product in the walks that read here.
pub struct Read<S, P, L = Leaf> {
    /// The scope's names.
    pub names: Names<P>,
    /// What the caller keeps of the summary and of the scope.
    pub sum: S,
    /// The inputs the summary read, each with its leaf.
    pub tree: Tree<L>,
}

/// A scope's names, each with its `P`.
pub type Names<P> = imbl::OrdMap<Arc<str>, P>;

/// The names whose entries differ between `a` and `b`, found from the persistent maps, which
/// skip the parts the two share.
pub fn changed<'a, V: PartialEq>(
    a: &'a imbl::OrdMap<Arc<str>, V>,
    b: &'a imbl::OrdMap<Arc<str>, V>,
) -> impl Iterator<Item = &'a Arc<str>> + 'a {
    a.diff(b).map(|d| match d {
        DiffItem::Add(v, _) | DiffItem::Remove(v, _) | DiffItem::Update { new: (v, _), .. } => v,
    })
}

/// The tree of what a summary reading `vars` reads in a scope of names `names`, each input `v`
/// the scope has with the leaf `leaf(v, q)` at its product `q`, from `base`, the tree of a read
/// in another scope, perhaps of another summary, by setting the leaves of the inputs
/// `changed` names: the names where the two scopes, or the two summaries, differ, each once or
/// more. `None` when those number `limit` or more, the inputs a tree made afresh would read
/// ([`fresh`]). `O(m log k)` for `m` names changed.
pub fn updated<'a, P, L: Sum>(
    base: &Tree<L>,
    changed: impl Iterator<Item = &'a Arc<str>>,
    vars: &imbl::OrdSet<Arc<str>>,
    names: &Names<P>,
    limit: usize,
    leaf: impl Fn(&Arc<str>, &P) -> L,
) -> Option<Tree<L>> {
    let mut keys = Vec::new();
    for v in changed {
        if keys.len() >= limit {
            return None;
        }
        keys.push(v);
    }
    keys.sort_unstable();
    keys.dedup();
    #[cfg(feature = "counts")]
    crate::preimage::counts::IMAGE_SETS
        .set(crate::preimage::counts::IMAGE_SETS.get() + keys.len() as u64);
    let mut tree = base.clone();
    for v in keys {
        let q = names.get(v).filter(|_| vars.contains(v));
        tree = set(&tree, v, q.map(|q| leaf(v, q)));
    }
    Some(tree)
}

/// The tree of what a summary reading `vars` reads in a scope of names `names`, made afresh
/// from the smaller of the two: `O(h log h)` for the `h` inputs the scope has.
pub fn fresh<P, L: Sum>(
    vars: &imbl::OrdSet<Arc<str>>,
    names: &Names<P>,
    leaf: impl Fn(&Arc<str>, &P) -> L,
) -> Tree<L> {
    let here: Vec<(&Arc<str>, &P)> = if vars.len() <= names.len() {
        vars.iter().filter_map(|v| names.get_key_value(v)).collect()
    } else {
        (names.iter()).filter(|(v, _)| vars.contains(*v)).collect()
    };
    #[cfg(feature = "counts")]
    crate::preimage::counts::IMAGE_SETS
        .set(crate::preimage::counts::IMAGE_SETS.get() + here.len() as u64);
    here.into_iter()
        .fold(None, |t, (v, q)| set(&t, v, Some(leaf(v, q))))
}

/// A summary's inputs as a test reads them ([`SummaryRead`]): the scope's names, of which the
/// summary reads `vars`, each with its integers (`ints`), and the tree of the bounds of the
/// summary's term of each input ([`TermBounds`]), kept like a [`Read`]'s tree.
pub struct TermRead<P> {
    /// The scope's names.
    pub names: Names<P>,
    /// The inputs the summary reads, each one of `names`.
    pub vars: imbl::OrdSet<Arc<str>>,
    /// The bounds of the summary's term of each input, over the input's integers.
    pub tree: Tree<TermBounds>,
    /// The integers of a name's product.
    pub ints: fn(&P) -> &IntervalSet,
}

impl<P> fmt::Debug for TermRead<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TermRead")
            .field("vars", &self.vars)
            .finish_non_exhaustive()
    }
}

impl<P> SummaryRead for TermRead<P> {
    fn vars(&self) -> &imbl::OrdSet<Arc<str>> {
        &self.vars
    }

    fn ints(&self, v: &str) -> Option<&IntervalSet> {
        if !self.vars.contains(v) {
            return None;
        }
        self.names.get(v).map(self.ints)
    }

    fn scope_ints(&self, v: &str) -> Option<&IntervalSet> {
        self.names.get(v).map(self.ints)
    }

    fn total(&self) -> TermBounds {
        total(&self.tree)
    }

    fn visit(&self, want: &dyn Fn(&TermBounds) -> bool, f: &mut dyn FnMut(&Arc<str>) -> bool) {
        visit(&self.tree, want, &mut |v, _| f(v));
    }
}
