//! Persistent ordered sets of settings, each an atom and a value, for [`Part::forced`]: treaps
//! whose union and intersection split one set at the other's root and join the halves, so `k`
//! settings meet `n` in `O(k log(n/k + 1))` expected time (Blelloch, Ferizovic and Sun, "Just
//! join for parallel ordered sets", SPAA 2016, doi:10.1145/2935764.2935768, Theorem 4 of the
//! full version, for independent
//! priorities, cited in full and quoted in module `bdd::list::treap`; for the 8-wise
//! independent priorities here, module [`zed_collections::priority`]), where adding the smaller
//! set's settings to the larger one at a time takes `O(k log n)`.
//!
//! Unlike the sets of module `set`, these nodes are kept in no table: [`Part::forced`] never asks
//! whether two sets are one node, so a table lookup per node made would be cost with no use
//! (PERF-forced-balanced-union measured the shared treaps at 3.4 times these instructions).
//! A node's priority is a function of its setting drawn at random once per run ([`priority`]),
//! ties broken by the setting's order, so in a run one set has one shape whatever order its
//! settings came in. The shape is never shown: a set is read only in order. Every walk keeps a
//! stack of its own and a set is dropped in a loop, so the stack needed does not depend on a
//! set's height.
//!
//! [`Part::forced`]: super::Part::forced

use std::cmp::Ordering;
use std::sync::Arc;

use super::set::Atom;
use zed_collections::priority::Priorities;

/// A setting: an atom and its value.
pub(super) type Key<A> = (A, bool);

/// A node: its setting, and the sets of the settings before and after it.
pub(super) struct Node<A: Atom> {
    key: Key<A>,
    prio: u64,
    len: usize,
    left: Tree<A>,
    right: Tree<A>,
}

/// A set: its root, or `None` when empty.
pub(super) type Tree<A> = Option<Arc<Node<A>>>;

/// A set is freed in a loop, a node whose last handle goes handing its children on, so a set of
/// any height is dropped on a small stack.
impl<A: Atom> Drop for Node<A> {
    fn drop(&mut self) {
        // Only children whose last handle this is are walked; the stack allocates nothing
        // until one is, and a node popped from it has no children left when it drops.
        let mut stack: Vec<Node<A>> = Vec::new();
        let free = |c: Tree<A>, stack: &mut Vec<Node<A>>| {
            if let Some(c) = c
                && let Ok(n) = Arc::try_unwrap(c)
            {
                stack.push(n);
            }
        };
        free(self.left.take(), &mut stack);
        free(self.right.take(), &mut stack);
        while let Some(mut n) = stack.pop() {
            free(n.left.take(), &mut stack);
            free(n.right.take(), &mut stack);
        }
    }
}

/// The priorities of the settings of each value, drawn once per run (module
/// [`zed_collections::priority`]): two uses, so that the two settings of one atom are two
/// independent points.
static PRIORITIES: [Priorities; 2] = [
    Priorities::eight_wise(1).fixed_in_unit_tests(cfg!(test)),
    Priorities::eight_wise(2).fixed_in_unit_tests(cfg!(test)),
];

/// The priority of `key`: the run's random polynomial of degree 7 at its atom's digest, one for
/// each value. Distinct digests take 8-wise independent uniform priorities, which bounds every
/// node's expected depth by `O(log n)` for every set of settings (Seidel and Aragon 1996,
/// doi:10.1007/BF01940876, Theorem 3.3 and section 6, cited in full and quoted in module
/// [`zed_collections::priority`]) and the work of [`combine`] by the finger bound (module
/// [`zed_collections::priority`] has both proofs), where the fixed hash this replaces had no bound
/// for chosen settings (COMPLEXITY.md K123). Atoms of one digest share a point: they tie whatever
/// the draw, and each such atom adds at most one to a depth.
fn priority<A: Atom>(key: &Key<A>) -> u64 {
    PRIORITIES[usize::from(key.1)].of(key.0.digest())
}

/// Whether node `a` stands above node `b`: the higher priority, ties broken by the setting.
fn above<A: Atom>(a: &Node<A>, b: &Node<A>) -> bool {
    (a.prio, &a.key) > (b.prio, &b.key)
}

/// The node of `key`, whose priority is `prio` ([`priority`]), over `left` and `right`. Only
/// [`from_keys`] evaluates [`priority`]; every other node made is a node of a set rebuilt with
/// other children, and takes its stored priority, so no node costs a second evaluation.
fn node_at<A: Atom>(prio: u64, key: Key<A>, left: Tree<A>, right: Tree<A>) -> Arc<Node<A>> {
    Arc::new(Node {
        prio,
        len: 1 + len(&left) + len(&right),
        key,
        left,
        right,
    })
}

/// The node `n` with the children `left` and `right`, `n` itself when they are its own.
fn remake<A: Atom>(n: &Arc<Node<A>>, left: Tree<A>, right: Tree<A>) -> Arc<Node<A>> {
    if same(&left, &n.left) && same(&right, &n.right) {
        return n.clone();
    }
    node_at(n.prio, n.key.clone(), left, right)
}

/// Whether two sets are one node (or both empty); a shortcut only, never an order.
fn same<A: Atom>(x: &Tree<A>, y: &Tree<A>) -> bool {
    match (x, y) {
        (Some(x), Some(y)) => Arc::ptr_eq(x, y),
        (None, None) => true,
        _ => false,
    }
}

/// The number of settings.
pub(super) fn len<A: Atom>(t: &Tree<A>) -> usize {
    t.as_ref().map_or(0, |n| n.len)
}

/// Whether `key` is in the set.
#[cfg(test)]
fn contains<A: Atom>(t: &Tree<A>, key: &Key<A>) -> bool {
    let mut cur = t.as_ref();
    while let Some(n) = cur {
        cur = match key.cmp(&n.key) {
            Ordering::Less => n.left.as_ref(),
            Ordering::Greater => n.right.as_ref(),
            Ordering::Equal => return true,
        };
    }
    false
}

/// The settings in order, by one walk with a stack of its own, `O(k)`.
pub(super) fn keys<A: Atom>(t: &Tree<A>) -> Vec<Key<A>> {
    let mut out = Vec::with_capacity(len(t));
    let mut stack: Vec<&Node<A>> = Vec::new();
    let mut cur = t.as_deref();
    loop {
        while let Some(n) = cur {
            stack.push(n);
            cur = n.left.as_deref();
        }
        let Some(n) = stack.pop() else { break };
        out.push(n.key.clone());
        cur = n.right.as_deref();
    }
    out
}

/// The set of `keys`, in any order, each once: sorted, then its shape found over their indices
/// as a Cartesian tree by priority made with one stack, and each node made once over its
/// children, `O(k log k)` for the sort and `O(k)` after it. The construction is
/// `zed_collections::cartesian::build` (DRY-persistent-structures), shared with
/// `bdd::set::from_sorted`; its module comment cites and quotes its sources (Vuillemin, CACM
/// 1980, for the tree; Gabow, Bentley and Tarjan, STOC 1984, section 3, for the stack) and
/// proves it. Tested by `settings::tests`, against ordered sets.
pub(super) fn from_keys<A: Atom>(mut keys: Vec<Key<A>>) -> Tree<A> {
    zed_collections::sorted::sort_dedup(&mut keys);
    let prios: Vec<u64> = keys.iter().map(priority).collect();
    zed_collections::cartesian::build(keys, &prios, |i, key, l, r| node_at(prios[i], key, l, r))
}

/// The settings of `t` before `key` and those after it, and whether `key` is in `t`: one walk
/// down from the root, the nodes passed made again on each side, `O(height)`.
fn split<A: Atom>(t: &Tree<A>, key: &Key<A>) -> (Tree<A>, bool, Tree<A>) {
    let (mut lefts, mut rights) = (Vec::new(), Vec::new());
    let mut cur = t.as_ref();
    let (mut l, mut found, mut r) = (None, false, None);
    while let Some(n) = cur {
        match n.key.cmp(key) {
            Ordering::Less => {
                lefts.push(n);
                cur = n.right.as_ref();
            }
            Ordering::Greater => {
                rights.push(n);
                cur = n.left.as_ref();
            }
            Ordering::Equal => {
                (l, found, r) = (n.left.clone(), true, n.right.clone());
                break;
            }
        }
    }
    for n in lefts.into_iter().rev() {
        l = Some(node_at(n.prio, n.key.clone(), n.left.clone(), l));
    }
    for n in rights.into_iter().rev() {
        r = Some(node_at(n.prio, n.key.clone(), r, n.right.clone()));
    }
    (l, found, r)
}

/// The settings of `a` and of `b`, every one of `a` before every one of `b`: the two merged
/// down one spine, the higher root first, `O(height)`.
fn join<A: Atom>(a: Tree<A>, b: Tree<A>) -> Tree<A> {
    let mut spine: Vec<(Arc<Node<A>>, bool)> = Vec::new();
    let (mut a, mut b) = (a, b);
    let mut bottom = loop {
        match (a, b) {
            (None, x) | (x, None) => break x,
            (Some(x), Some(y)) => {
                if above(&x, &y) {
                    a = x.right.clone();
                    b = Some(y);
                    spine.push((x, false));
                } else {
                    b = y.left.clone();
                    a = Some(x);
                    spine.push((y, true));
                }
            }
        }
    };
    for (n, left) in spine.into_iter().rev() {
        bottom = Some(if left {
            node_at(n.prio, n.key.clone(), bottom, n.right.clone())
        } else {
            node_at(n.prio, n.key.clone(), n.left.clone(), bottom)
        });
    }
    bottom
}

/// Whether [`combine`] keeps the settings in either set or only those in both.
#[derive(Clone, Copy)]
enum Op {
    Union,
    Meet,
}

/// The union or the intersection of two sets: from the roots down, the higher root kept and the
/// other set split at its setting, the two sides combined past it, and for an intersection the
/// root kept only when the other set had it. Two subtrees that are one node are their own
/// union and intersection. For `k` settings into `n`, `O(k log(n/k + 1))` expected time
/// (Blelloch, Ferizovic and Sun, Theorem 4 of the full version, splits and joins included, for
/// independent priorities, cited in full in module `bdd::list::treap`; for the 8-wise
/// independent ones of [`priority`], the finger bound of module [`zed_collections::priority`], plus
/// the settings that share a point).
fn combine<A: Atom>(x: &Tree<A>, y: &Tree<A>, op: Op) -> Tree<A> {
    /// A pair of subtrees to combine, or a node to make over the two combined last: with its
    /// setting kept, or (for an intersection whose other set lacked it) the two joined.
    enum Step<A: Atom> {
        Combine(Tree<A>, Tree<A>),
        Make(Arc<Node<A>>, bool),
    }
    let mut todo = vec![Step::Combine(x.clone(), y.clone())];
    let mut done: Vec<Tree<A>> = Vec::new();
    while let Some(step) = todo.pop() {
        let (x, y) = match step {
            Step::Make(n, kept) => {
                let r = done.pop().expect("the right side is combined");
                let l = done.pop().expect("the left side is combined");
                done.push(if kept {
                    Some(remake(&n, l, r))
                } else {
                    join(l, r)
                });
                continue;
            }
            Step::Combine(None, t) | Step::Combine(t, None) => {
                done.push(match op {
                    Op::Union => t,
                    Op::Meet => None,
                });
                continue;
            }
            Step::Combine(Some(x), Some(y)) if Arc::ptr_eq(&x, &y) => {
                done.push(Some(x));
                continue;
            }
            Step::Combine(Some(x), Some(y)) => (x, y),
        };
        let (hi, lo) = if above(&x, &y) { (x, y) } else { (y, x) };
        let (l, found, r) = split(&Some(lo), &hi.key);
        let kept = match op {
            Op::Union => true,
            Op::Meet => found,
        };
        let (hl, hr) = (hi.left.clone(), hi.right.clone());
        todo.push(Step::Make(hi, kept));
        todo.push(Step::Combine(hr, r));
        todo.push(Step::Combine(hl, l));
    }
    done.pop().expect("the two sets are combined")
}

/// The settings in either set.
pub(super) fn union<A: Atom>(x: &Tree<A>, y: &Tree<A>) -> Tree<A> {
    combine(x, y, Op::Union)
}

/// The settings in both sets.
pub(super) fn meet<A: Atom>(x: &Tree<A>, y: &Tree<A>) -> Tree<A> {
    combine(x, y, Op::Meet)
}

/// The settings in any of `sets`: the settings of all but the largest gathered, sorted and
/// made into one set ([`from_keys`]), which is then joined to the largest ([`union`]). For `R`
/// settings outside the largest set of `L`, `O(R log R + R log(L/R + 1))`.
// Complexity tradeoff (COMPLEXITY.md K32, PERF-forced-balanced-union): the naive union of `m`
// sets folds [`union`] over them, two at a time; on a balanced tree of `m` single settings
// each level of the tree joins sets of equal size, `O(m)` node copies per level and
// `O(m log m)` copies in all, where this sorts the `m` settings once (`O(m log m)` comparisons,
// no node made) and makes `m` nodes. A set much larger than the rest is never copied: it is
// the one the rest are joined to, so a chain adding one setting at a time to a shared set
// stays `O(log L)` per link.
pub(super) fn union_all<A: Atom>(sets: &[&Tree<A>]) -> Tree<A> {
    let big = (0..sets.len()).max_by_key(|&i| (len(sets[i]), std::cmp::Reverse(i)))?;
    let mut rest = Vec::new();
    for (i, t) in sets.iter().enumerate() {
        if i != big {
            rest.extend(keys(t));
        }
    }
    if rest.is_empty() {
        return sets[big].clone();
    }
    union(sets[big], &from_keys(rest))
}

/// The settings in every one of `sets` (at least one): the smallest met with each of the rest
/// in turn, stopping when nothing is left. Each step keeps at most the settings of the one
/// before, so for `m` sets the smallest of which is `s`, `O(m s log(L/s + 1))`, `L` the largest.
pub(super) fn meet_all<A: Atom>(sets: &[&Tree<A>]) -> Tree<A> {
    let small = (0..sets.len())
        .min_by_key(|&i| len(sets[i]))
        .expect("a meet of one set at least");
    let mut out = sets[small].clone();
    for (i, t) in sets.iter().enumerate() {
        if out.is_none() {
            break;
        }
        if i != small {
            out = meet(&out, t);
        }
    }
    out
}

#[cfg(test)]
mod tests;
