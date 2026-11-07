//! What a binder's summary reads in a scope, kept by input in a persistent tree with the sum of
//! each subtree, so that the image of the summary in a scope that differs from an earlier one
//! at a few inputs costs those inputs (item PA-let-narrow-many).
//!
//! A binder `x` read where tests have narrowed `h` of the `k` inputs its summary reads lies
//! where the summary does over them ([`Ck::with_bound_read`]): the summary must hold there
//! (each input's integers within those it was made over), its bounds move by each narrowed
//! input's [`Shift`], and the narrowing rests on the inputs' premises. A chain
//! `x_k = x_(k-1) + q_k` under a test of each `q_k` reads `x_(k-1)` over all `k - 1` narrowed
//! inputs; summed afresh at each binding the chain costs `Θ(d²)`, and kept here it costs
//! `O(log k)` a binding, since `x_(k-1)` read in the scope of `x_k` differs from `x_(k-2)` read
//! in the scope of `x_(k-1)` at `q_(k-1)` alone.
//!
//! [`Ck::with_bound_read`]: super::walk
//! [`Shift`]: zedc_preimage::preimage::Shift

use std::rc::Rc;
use std::sync::Arc;

use imbl::ordmap::DiffItem;
use zedc_lattice::cell::Premises;
use zedc_preimage::preimage::Shift;
use zedc_preimage::product::Product;

use super::arms::Summarized;

/// What one input adds, or the sum of a subtree's.
#[derive(Clone)]
pub(super) struct Leaf {
    /// The input's shift of the summary's bounds ([`Shift`]), nothing when it fails.
    pub(super) shift: Shift,
    /// The inputs whose integers lie outside those the summary was made over: where one does,
    /// the summary does not hold.
    pub(super) fails: usize,
    /// The premises of the inputs' products.
    pub(super) premises: Premises,
}

impl Leaf {
    fn empty() -> Leaf {
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
pub(super) type Tree = Option<Rc<Node>>;

pub(super) struct Node {
    key: Arc<str>,
    prio: u64,
    leaf: Leaf,
    sum: Leaf,
    left: Tree,
    right: Tree,
}

/// The sum of every leaf of `t`.
pub(super) fn total(t: &Tree) -> Leaf {
    t.as_ref().map_or_else(Leaf::empty, |n| n.sum.clone())
}

/// `t` with `key`'s leaf set to `leaf`, or taken out at `None`. `O(log h)` expected.
pub(super) fn set(t: &Tree, key: &Arc<str>, leaf: Option<Leaf>) -> Tree {
    let (below, above) = split(t, key);
    let above = without(above, key);
    let one = leaf.map(|l| node(key.clone(), prio(key), l, None, None));
    join(join(below, one), above)
}

fn node(key: Arc<str>, prio: u64, leaf: Leaf, left: Tree, right: Tree) -> Rc<Node> {
    let sum = total(&left).plus(&leaf).plus(&total(&right));
    Rc::new(Node {
        key,
        prio,
        leaf,
        sum,
        left,
        right,
    })
}

/// The keys of `t` below `key`, and the others.
fn split(t: &Tree, key: &Arc<str>) -> (Tree, Tree) {
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
fn without(t: Tree, key: &Arc<str>) -> Tree {
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
fn join(a: Tree, b: Tree) -> Tree {
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

/// What a binder's summary read in one scope: the scope's names, the summary, and the tree of
/// the inputs it read there, each with its leaf ([`Leaf`]).
pub(super) struct Read {
    pub(super) names: Names,
    pub(super) sum: Rc<Summarized>,
    pub(super) tree: Tree,
}

/// A scope's names and their products.
pub(super) type Names = imbl::OrdMap<Arc<str>, Product>;

/// What the input `v` of `sum`, of product `q` in a scope, adds there.
pub(super) fn leaf(sum: &Summarized, v: &Arc<str>, q: &Product) -> Leaf {
    // The summary holds where each input's integers lie within those it was made over
    // ([`Scope::bind_summarized`]).
    let holds = (sum.inputs.get(v)).is_some_and(|d| q.ints().is_subset(d.ints()));
    Leaf {
        shift: if holds {
            sum.summary.shift(v, q.ints())
        } else {
            Shift::ZERO
        },
        fails: usize::from(!holds),
        premises: q.premises(),
    }
}

/// The tree of what `sum` reads in a scope of names `names` ([`Read`]), from `base`, read in
/// another scope and perhaps of another summary, by setting the leaves of the inputs where the
/// two scopes' names, the two summaries' inputs ([`LetPa::changed_since`]) or their maps of
/// inputs differ: `None` when the summaries cannot be compared, or when those differences
/// number `limit` or more, the inputs a tree made afresh would read. The differences are
/// found from the persistent maps, which skip the parts the two share, so a read of `x_(k-1)`
/// from one of `x_(k-2)` in a scope with one more test costs `O(log k)`.
///
/// [`LetPa::changed_since`]: zedc_preimage::preimage::LetPa::changed_since
pub(super) fn updated(
    base: &Read,
    sum: &Rc<Summarized>,
    names: &Names,
    limit: usize,
) -> Option<Tree> {
    fn key<'a>(d: DiffItem<'a, 'a, Arc<str>, Product>) -> &'a Arc<str> {
        match d {
            DiffItem::Add(v, _) | DiffItem::Remove(v, _) | DiffItem::Update { new: (v, _), .. } => {
                v
            }
        }
    }
    let own: Box<dyn Iterator<Item = &Arc<str>>> = if Rc::ptr_eq(&base.sum, sum) {
        Box::new(std::iter::empty())
    } else {
        let terms = sum.summary.changed_since(&base.sum.summary)?;
        Box::new(terms.chain(base.sum.inputs.diff(&sum.inputs).map(key)))
    };
    let mut keys = Vec::new();
    for v in own.chain(base.names.diff(names).map(key)) {
        if keys.len() >= limit {
            return None;
        }
        keys.push(v);
    }
    keys.sort_unstable();
    keys.dedup();
    let vars = sum.summary.vars();
    let mut tree = base.tree.clone();
    for v in keys {
        let q = names.get(v).filter(|_| vars.contains(v));
        tree = set(&tree, v, q.map(|q| leaf(sum, v, q)));
    }
    Some(tree)
}
