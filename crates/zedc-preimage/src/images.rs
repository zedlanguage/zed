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
use zed_collections::priority::Priorities;
use zed_collections::treap;
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
/// subtree's; a node's priority is drawn at random once per run from its name, so in a run the
/// tree's shape depends on its names alone and an update copies the `O(log h)` nodes of one
/// path, expected. The generic treap of zed-collections ([`zed_collections::treap`]), whose
/// item is an [`Input`] (DRY-persistent-trees-2026-11-26).
pub type Tree<L = Leaf> = treap::Tree<Input<L>>;

/// An item of a [`Tree`]: an input's name and its leaf.
#[derive(Clone)]
pub struct Input<L = Leaf> {
    key: Arc<str>,
    leaf: L,
}

impl<L: Sum> treap::Item for Input<L> {
    type Key = Arc<str>;
    type Sum = L;

    fn key(&self) -> &Arc<str> {
        &self.key
    }

    fn priority(&self) -> u64 {
        prio(&self.key)
    }

    /// The sum of a subtree, `left + leaf + right` in key order, as the private treap this
    /// replaced made it.
    fn sum(&self, left: Option<&L>, right: Option<&L>) -> L {
        (left.map_or_else(L::zero, L::clone).plus(&self.leaf))
            .plus(&right.map_or_else(L::zero, L::clone))
    }
}

/// The sum of every leaf of `t`.
pub fn total<L: Sum>(t: &Tree<L>) -> L {
    t.as_ref().map_or_else(L::zero, |n| n.sum().clone())
}

/// The inputs of `t`.
pub fn len<L: Sum>(t: &Tree<L>) -> usize {
    treap::len(t)
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
    if !want(n.sum()) {
        return true;
    }
    let Input { key, leaf } = n.item();
    visit(n.left(), want, f) && (!want(leaf) || f(key, leaf)) && visit(n.right(), want, f)
}

/// `t` with `key`'s leaf set to `leaf`, or taken out at `None`. `O(log h)` expected: the
/// insertion and removal of the generic treap, each one walk down the search path. The private
/// treap this replaced split at the key, took the key out of the upper part and joined the
/// three again, making the search path and both joined spines anew.
fn set<L: Sum>(t: &Tree<L>, key: &Arc<str>, leaf: Option<L>) -> Tree<L> {
    match leaf {
        Some(leaf) => treap::insert(
            t,
            Input {
                key: key.clone(),
                leaf,
            },
        ),
        None => treap::remove(t, key),
    }
}

/// The priorities of the inputs' names, drawn once per run ([`zed_collections::priority`]).
static PRIORITIES: Priorities = Priorities::new(6);

/// The priority of `key`: the run's random polynomial of degree 4 at a random polynomial hash
/// of the name's bytes ([`Priorities::hash`]). Distinct names have distinct streams and tie with
/// probability at most `(S + 1)/p` a pair for names of `S` symbols; the priorities are
/// otherwise 5-wise independent and uniform, and every node's depth is `O(log h)` in
/// expectation for every set of names (Seidel and Aragon, "Randomized search trees",
/// Algorithmica 16, 1996, doi:10.1007/BF01940876, Theorem 3.3 and section 6; the full comment
/// and the proof are in module [`zed_collections::priority`]), where the fixed hash this replaces
/// had no bound for chosen names (COMPLEXITY.md K123). In a run the shape depends on the names
/// alone; it is never shown, and a subtree's sum is the same for every shape, since every
/// [`Sum::plus`] here adds exact integers and joins sets of premises.
fn prio(key: &str) -> u64 {
    PRIORITIES.hash(key)
}

/// What a summary read in one scope: the scope's names, what the caller keeps of the summary
/// and of the scope beside them (`S`), and the tree of the inputs it read there, each with its
/// leaf ([`Leaf`]). The scope's names are an `N`: a [`Names`] map, or a map that gives each
/// name's product by name (`NameProducts` in [`product`](crate::product)).
pub struct Read<S, N, L: Sum = Leaf> {
    /// The scope's names.
    pub names: N,
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
///
/// Why the tree equals the one [`fresh`] makes, so that a read gives the same answer
/// whichever read it starts from: an input not among `changed` has the same leaf here as in
/// `base`, or is in neither, provided the caller lists every name where the scopes' products,
/// the summaries' inputs or anything else the leaf reads differ (`Scope::holds` in
/// `product.rs` lists names, orders, inputs and what the summaries were made over); each
/// changed input is set to its leaf here. So the two trees hold the same keys with the same
/// leaves, and a treap's shape depends on its keys alone (priorities are hashes of the
/// names, [`Tree`]), so every subtree, and its sum, is the same. Test:
/// `l01_39_reduced_product::random::every_run_of_a_random_body_reaches_only_arms_that_hold_it`
/// (2,700 bodies against the interpreter, commit eaef33ced); it cannot catch a caller that
/// leaves out a difference its bodies never make.
pub fn updated<'a, P, L: Sum>(
    base: &Tree<L>,
    changed: impl Iterator<Item = &'a Arc<str>>,
    vars: &imbl::OrdSet<Arc<str>>,
    names: &Names<P>,
    limit: usize,
    leaf: impl Fn(&Arc<str>, &P) -> L,
) -> Option<Tree<L>> {
    updated_with(base, changed, limit, |v| {
        let q = names.get(v).filter(|_| vars.contains(v));
        q.map(|q| leaf(v, q))
    })
}

/// [`updated`] for a scope that gives each input's leaf by name: `leaf_of(v)` is the leaf of
/// the input `v`, `None` when the summary does not read it or the scope has no product of it.
/// `O(m log k)` for `m` names changed, plus `m` calls of `leaf_of`.
pub fn updated_with<'a, L: Sum>(
    base: &Tree<L>,
    changed: impl Iterator<Item = &'a Arc<str>>,
    limit: usize,
    leaf_of: impl Fn(&Arc<str>) -> Option<L>,
) -> Option<Tree<L>> {
    let mut keys = Vec::new();
    for v in changed {
        if keys.len() >= limit {
            return None;
        }
        keys.push(v);
    }
    zed_collections::sorted::sort_dedup(&mut keys);
    #[cfg(feature = "counts")]
    crate::preimage::counts::IMAGE_SETS
        .set(crate::preimage::counts::IMAGE_SETS.get() + keys.len() as u64);
    let mut tree = base.clone();
    for v in keys {
        tree = set(&tree, v, leaf_of(v));
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
    if vars.len() <= names.len() {
        let here = vars.iter().filter_map(|v| names.get_key_value(v));
        fresh_with(here.map(|(v, q)| (v, leaf(v, q))))
    } else {
        let here = (names.iter()).filter(|(v, _)| vars.contains(*v));
        fresh_with(here.map(|(v, q)| (v, leaf(v, q))))
    }
}

/// The tree of the inputs `leaves`, each with its leaf, made afresh: `O(h log h)` for `h`
/// inputs.
pub fn fresh_with<'a, L: Sum>(leaves: impl Iterator<Item = (&'a Arc<str>, L)>) -> Tree<L> {
    #[cfg(feature = "counts")]
    let mut count = 0u64;
    let tree = leaves.fold(None, |t, (v, l)| {
        #[cfg(feature = "counts")]
        {
            count += 1;
        }
        set(&t, v, Some(l))
    });
    #[cfg(feature = "counts")]
    crate::preimage::counts::IMAGE_SETS.set(crate::preimage::counts::IMAGE_SETS.get() + count);
    tree
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
