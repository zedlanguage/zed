//! Persistent ordered sets as treaps, each node keeping the size, the wrapping sum of the
//! weights and the union of the classes of its subtree (plan row CHECK-literal-union-cost, part
//! 2): the literals of a type (`types::Lits`) and the finite-set domain of the reduced product
//! (`zedc_lattice::lattice::FiniteSet`) share one kind of set, so a set narrowed to a range of
//! its keys keeps every subtree outside the cut and one domain's set can become another's at
//! no cost.
//!
//! Operations: membership, insertion, removal, the keys at least or at most a bound
//! ([`TreapSet::at_least`], [`TreapSet::at_most`]) and the join of two sets one before the other
//! ([`TreapSet::concat`]), each one walk down a path, `O(log n)` expected; union, intersection and
//! difference by Blelloch and Reid-Miller's join-based recursion, `O(m log(n/m + 1))` expected
//! for sets of `m <= n` keys. Sources:
//!
//! - G. E. Blelloch and M. Reid-Miller, "Fast set operations using treaps", SPAA '98, ACM,
//!   pp. 16-26, 1998, doi:10.1145/277651.277660. Crossref checked 2026-11-20; the text was not
//!   obtained, so what it says is taken from the paper below, which credits it: "Blelloch and
//!   Reid-Miller later show that similar algorithms for treaps \[7\], are optimal for work (i.e.
//!   Θ(m log(n/m + 1)))".
//! - G. E. Blelloch, D. Ferizovic and Y. Sun, "Just join for parallel ordered sets", SPAA 2016,
//!   ACM, pp. 253-264, doi:10.1145/2935764.2935768 (Crossref and the text checked 2026-11-20).
//!   Section 4: UNION, INTERSECT and DIFFERENCE split one tree at the other's root key and
//!   join the two recursive results; "For INTERSECT, JOIN2 is used instead of JOIN if the root
//!   of the first is not found in the second. For DIFFERENCE, JOIN2 is used anyway". Theorem 4:
//!   work `O(m log(n/m + 1))` for sizes `m <= n`, "in expectation for treaps". The full citation
//!   and the treap JOIN (Figure 5) are also in `types::bdd::list::treap`.
//!
//! Departures: the recursion runs on an explicit stack (`combine`), and it stops early at
//! shared subtrees and at results of an operand's size (below); neither changes the bound.
//! Tests: `every_operation_agrees_with_a_btree_set` checks the results against
//! `std::collections::BTreeSet`; no test measures the work bound, which rests on Theorem 4.
//!
//! A set is shared, never changed: an operation makes new nodes along the paths it changes and
//! shares every subtree it leaves alone. A node's priority is a function of its key drawn at
//! random once per run ([`Elem::priority`], module [`crate::priority`]), ties broken by the
//! order of the keys, so in a run the keys of a set fix its shape whatever order they came in.
//! So two sets made from one set by cuts and set operations share the subtrees where they agree,
//! and an operation on them stops at the first pair of shared subtrees (`Arc::ptr_eq`): the
//! intersection of a set with a range cut of it is the cut's path, `O(log n)`, not `O(n)`. An
//! operation whose result has the size of an operand gives that operand itself, at every level
//! of the recursion, so a result equal to an operand shares its nodes and the next operation on
//! the pair stops at once.
//!
//! Complexity tradeoff (CHECK-literal-union-cost): naive version, `imbl::OrdSet` for the
//! literals and `BTreeSet` for the finite set: a meet of two sets walks the smaller, `O(m log n)`
//! with `m` near `n` when a test narrows a union of `k` literals to half of it, and each domain
//! is rebuilt from the other's list, so `k` tests on a callee giving `k` literals cost `O(k^2)`.
//! Used: one treap for both, cuts by a path and set operations that skip shared subtrees, so each
//! test costs `O(log k)` where its sets derive from one set. Cost: three words more per node (the
//! weight, the sum and the classes) than a plain treap, and an `Arc` per key, where a B-tree
//! keeps up to 16 keys a node. Test:
//! `l01_39_reduced_product::arm_test_through_call::bench::tests_on_a_callee_of_k_literal_arms_scale`.
//!
//! The depth. Priorities are drawn by [`Priorities::eight_wise`]: the module comment of
//! [`crate::priority`] proves the expected depth `O(log n)` for keys at distinct points of the
//! draw, and the work of a join-based operation `O(m log(1 + n/m))` in expectation under 8-wise
//! independence (plan row PROOF-join-work-limited-independence). Keys at one point tie whatever
//! the draw; which keys share a point is said at each [`Elem`] implementation.
//!
//! Every walk keeps a stack of its own, and a set is dropped in a loop, so the stack needed does
//! not depend on a set's height.

use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

use crate::priority::Priorities;

/// A key of a [`TreapSet`]: ordered, with a priority drawn once per run, a weight whose
/// wrapping sum each subtree keeps, and a class whose union each subtree keeps.
pub trait Elem: Ord + Clone {
    /// The key's priority: a random function of the key, one per kind of key, drawn once per
    /// run (module [`crate::priority`]).
    fn priority(&self) -> u64;
    /// A hash of the key, equal for equal keys; a set's [`TreapSet::sum`] is the wrapping sum
    /// of its keys' weights.
    fn weight(&self) -> u64;
    /// A bit mask of the key's kind; a set's [`TreapSet::classes`] is the union of its keys'.
    fn class(&self) -> u32;
}

/// Integers tie only when equal: the point of `n` is `n` with its sign bit flipped, below `p`
/// except for the 59 integers from `2^63 - 59` up, which share their points with the 59 from
/// `i64::MIN`, so at most 118 keys tie whatever the draw (module [`crate::priority`]).
impl Elem for i64 {
    fn priority(&self) -> u64 {
        static PRIORITIES: Priorities = Priorities::eight_wise(18);
        PRIORITIES.of((*self as u64) ^ (1 << 63))
    }
    /// Fibonacci hashing: odd multiplier, so distinct integers weigh differently.
    fn weight(&self) -> u64 {
        (*self as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
    }
    fn class(&self) -> u32 {
        1
    }
}

/// A node: its key, priority and weight, and over its subtree the number of keys, the sum of
/// the weights and the union of the classes.
struct Node<T> {
    key: T,
    prio: u64,
    weight: u64,
    len: usize,
    sum: u64,
    classes: u32,
    left: Tree<T>,
    right: Tree<T>,
}

/// A tree: its root, or `None` when empty.
type Tree<T> = Option<Arc<Node<T>>>;

/// A set is freed in a loop, a node whose last handle goes handing its children on, so a set of
/// any height is dropped on a small stack (as `types::bdd::list::treap` does).
impl<T> Drop for Node<T> {
    fn drop(&mut self) {
        let mut stack: Vec<Node<T>> = Vec::new();
        let free = |c: Tree<T>, stack: &mut Vec<Node<T>>| {
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

/// A persistent ordered set of distinct keys (module comment).
pub struct TreapSet<T> {
    root: Tree<T>,
}

impl<T> Clone for TreapSet<T> {
    fn clone(&self) -> Self {
        TreapSet {
            root: self.root.clone(),
        }
    }
}

impl<T> Default for TreapSet<T> {
    fn default() -> Self {
        TreapSet { root: None }
    }
}

fn len<T>(t: &Tree<T>) -> usize {
    t.as_ref().map_or(0, |n| n.len)
}

fn sum<T>(t: &Tree<T>) -> u64 {
    t.as_ref().map_or(0, |n| n.sum)
}

fn classes<T>(t: &Tree<T>) -> u32 {
    t.as_ref().map_or(0, |n| n.classes)
}

/// Whether node `a` stands above node `b`: the higher priority, ties broken by the key.
fn above<T: Ord>(a: &Node<T>, b: &Node<T>) -> bool {
    (a.prio, &a.key) > (b.prio, &b.key)
}

/// The node `n` made again over `left` and `right`, its priority and weight kept rather than
/// computed.
fn again<T: Elem>(n: &Node<T>, left: Tree<T>, right: Tree<T>) -> Arc<Node<T>> {
    Arc::new(Node {
        key: n.key.clone(),
        prio: n.prio,
        weight: n.weight,
        len: 1 + len(&left) + len(&right),
        sum: n.weight.wrapping_add(sum(&left)).wrapping_add(sum(&right)),
        classes: n.key.class() | classes(&left) | classes(&right),
        left,
        right,
    })
}

/// A node of `key` over `left` and `right`, its priority and weight computed.
fn fresh<T: Elem>(key: T, left: Tree<T>, right: Tree<T>) -> Arc<Node<T>> {
    let (prio, weight) = (key.priority(), key.weight());
    Arc::new(Node {
        prio,
        weight,
        len: 1 + len(&left) + len(&right),
        sum: weight.wrapping_add(sum(&left)).wrapping_add(sum(&right)),
        classes: key.class() | classes(&left) | classes(&right),
        key,
        left,
        right,
    })
}

/// The path `path` from the root down, each node with the side taken from it, made again over
/// `bottom`, the new subtree where the path ends.
fn up<T: Elem>(path: Vec<(&Arc<Node<T>>, bool)>, mut bottom: Tree<T>) -> Tree<T> {
    for (n, left) in path.into_iter().rev() {
        bottom = Some(match left {
            true => again(n, bottom, n.right.clone()),
            false => again(n, n.left.clone(), bottom),
        });
    }
    bottom
}

/// The keys of `t` before `key`, whether `t` has `key`, and the keys after it: one walk down
/// from the root, the nodes passed made again on each side, `O(height)`.
fn split<T: Elem>(t: &Tree<T>, key: &T) -> (Tree<T>, bool, Tree<T>) {
    let (mut lefts, mut rights) = (Vec::new(), Vec::new());
    let mut cur = t.as_ref();
    let (mut l, mut r, mut found) = (None, None, false);
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
                (l, r, found) = (n.left.clone(), n.right.clone(), true);
                break;
            }
        }
    }
    for n in lefts.into_iter().rev() {
        l = Some(again(n, n.left.clone(), l));
    }
    for n in rights.into_iter().rev() {
        r = Some(again(n, r, n.right.clone()));
    }
    (l, found, r)
}

/// The keys of `t` on one side of `bound`: at least it (`low`), else at most it, with `bound`
/// itself. One walk down: a node on the far side is dropped with its subtree on that side, and
/// the walk goes on into its other subtree; a node kept keeps its subtree on the kept side whole
/// and takes what the rest of the walk keeps as its other child, `O(height)`. `t` itself when
/// nothing is dropped.
fn side<T: Elem>(t: &Tree<T>, bound: &T, low: bool) -> Tree<T> {
    let mut kept = Vec::new();
    let mut dropped = false;
    let mut cur = t.as_ref();
    while let Some(n) = cur {
        let out = match low {
            true => n.key < *bound,
            false => n.key > *bound,
        };
        match (out, low) {
            (true, true) => cur = n.right.as_ref(),
            (true, false) => cur = n.left.as_ref(),
            (false, true) => {
                kept.push(n);
                cur = n.left.as_ref();
            }
            (false, false) => {
                kept.push(n);
                cur = n.right.as_ref();
            }
        }
        dropped |= out;
    }
    if !dropped {
        return t.clone();
    }
    let mut bottom = None;
    for n in kept.into_iter().rev() {
        bottom = Some(match low {
            true => again(n, bottom, n.right.clone()),
            false => again(n, n.left.clone(), bottom),
        });
    }
    bottom
}

/// The keys of `a` and of `b`, every key of `a` before every key of `b`: the two merged down
/// one spine, the higher root first, `O(height)`.
fn join<T: Elem>(a: Tree<T>, b: Tree<T>) -> Tree<T> {
    let mut spine: Vec<(Arc<Node<T>>, bool)> = Vec::new();
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
        bottom = Some(match left {
            true => again(&n, bottom, n.right.clone()),
            false => again(&n, n.left.clone(), bottom),
        });
    }
    bottom
}

/// A set operation of [`combine`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    Union,
    Meet,
    Minus,
}

/// `op` on `a` and `b` without a walk, when one is empty or both are one tree.
fn at_once<T>(op: Op, a: &Tree<T>, b: &Tree<T>) -> Option<Tree<T>> {
    let same = matches!((a, b), (Some(x), Some(y)) if Arc::ptr_eq(x, y));
    match op {
        Op::Union if a.is_none() || same => Some(b.clone()),
        Op::Union if b.is_none() => Some(a.clone()),
        Op::Meet if a.is_none() || b.is_none() => Some(None),
        Op::Meet if same => Some(a.clone()),
        Op::Minus if a.is_none() || same => Some(None),
        Op::Minus if b.is_none() => Some(a.clone()),
        _ => None,
    }
}

/// `op` on `a` and `b` by Blelloch and Reid-Miller's recursion, on a stack of its own: the root
/// of higher priority is the pivot, the other tree is split at its key, the two sides are
/// combined, and the pivot's key joins them when the result has it. A pair of empty or shared
/// subtrees is answered at once ([`at_once`]), and a result of an operand's size is that operand
/// (module comment), so the walk visits only where the two trees differ.
fn combine<T: Elem>(op: Op, a: &Tree<T>, b: &Tree<T>) -> Tree<T> {
    enum Job<T> {
        Do(Tree<T>, Tree<T>),
        Make(Arc<Node<T>>, bool, Tree<T>, Tree<T>),
    }
    let mut jobs = vec![Job::Do(a.clone(), b.clone())];
    let mut done: Vec<Tree<T>> = Vec::new();
    while let Some(job) = jobs.pop() {
        match job {
            Job::Do(a, b) => {
                if let Some(t) = at_once(op, &a, &b) {
                    done.push(t);
                    continue;
                }
                let (Some(x), Some(y)) = (&a, &b) else {
                    unreachable!("`at_once` answers an empty operand")
                };
                let (x, y) = (x.clone(), y.clone());
                if above(&x, &y) {
                    // The pivot is `a`'s: each side of it meets `b`'s keys on that side.
                    let (l, found, r) = split(&b, &x.key);
                    let keep = match op {
                        Op::Union => true,
                        Op::Meet => found,
                        Op::Minus => !found,
                    };
                    let (pl, pr) = (x.left.clone(), x.right.clone());
                    jobs.push(Job::Make(x, keep, a, b));
                    jobs.push(Job::Do(pr, r));
                    jobs.push(Job::Do(pl, l));
                } else {
                    // The pivot is `b`'s: each side of `a` meets `b`'s keys on that side, `a`'s
                    // still first, since `Minus` is not symmetric.
                    let (l, found, r) = split(&a, &y.key);
                    let keep = match op {
                        Op::Union => true,
                        Op::Meet => found,
                        Op::Minus => false,
                    };
                    let (pl, pr) = (y.left.clone(), y.right.clone());
                    jobs.push(Job::Make(y, keep, a, b));
                    jobs.push(Job::Do(r, pr));
                    jobs.push(Job::Do(l, pl));
                }
            }
            Job::Make(pivot, keep, a, b) => {
                let r = done.pop().expect("the right side's result");
                let l = done.pop().expect("the left side's result");
                // The pivot stands above every key of both trees but its own, so it is the
                // root of the result when kept.
                let t = match keep {
                    true => Some(again(&pivot, l, r)),
                    false => join(l, r),
                };
                let n = len(&t);
                done.push(match op {
                    _ if n == len(&a) => a,
                    Op::Union | Op::Meet if n == len(&b) => b,
                    _ => t,
                });
            }
        }
    }
    done.pop().expect("the result")
}

impl<T: Elem> TreapSet<T> {
    /// The empty set.
    pub fn new() -> Self {
        TreapSet { root: None }
    }

    /// The number of keys, `O(1)`.
    pub fn len(&self) -> usize {
        len(&self.root)
    }

    /// Whether the set has no key, `O(1)`.
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// The wrapping sum of the keys' weights ([`Elem::weight`]), `O(1)`.
    pub fn sum(&self) -> u64 {
        sum(&self.root)
    }

    /// The union of the keys' classes ([`Elem::class`]), `O(1)`.
    pub fn classes(&self) -> u32 {
        classes(&self.root)
    }

    /// Whether the two are one tree, so equal, `O(1)`.
    pub fn ptr_eq(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }

    /// Whether the set has `key`: one walk down, `O(log n)`.
    pub fn contains(&self, key: &T) -> bool {
        let mut cur = self.root.as_deref();
        while let Some(n) = cur {
            cur = match key.cmp(&n.key) {
                Ordering::Less => n.left.as_deref(),
                Ordering::Greater => n.right.as_deref(),
                Ordering::Equal => return true,
            };
        }
        false
    }

    /// The least key, `O(log n)`.
    pub fn first(&self) -> Option<&T> {
        let mut n = self.root.as_deref()?;
        while let Some(l) = n.left.as_deref() {
            n = l;
        }
        Some(&n.key)
    }

    /// The greatest key, `O(log n)`.
    pub fn last(&self) -> Option<&T> {
        let mut n = self.root.as_deref()?;
        while let Some(r) = n.right.as_deref() {
            n = r;
        }
        Some(&n.key)
    }

    /// Adds `key`; whether it was new. One walk down while the nodes stand above the new one,
    /// then the subtree there split at the key, the path made again, `O(log n)` expected (as
    /// `types::bdd::list::treap::insert`). The set is left as it was when it has the key.
    pub fn insert(&mut self, key: T) -> bool {
        if self.contains(&key) {
            return false;
        }
        let prio = key.priority();
        let mut path = Vec::new();
        let mut cur = self.root.as_ref();
        while let Some(n) = cur
            && (n.prio, &n.key) > (prio, &key)
        {
            let left = key < n.key;
            path.push((n, left));
            cur = if left {
                n.left.as_ref()
            } else {
                n.right.as_ref()
            };
        }
        let (l, _, r) = split(&cur.cloned(), &key);
        let bottom = fresh(key, l, r);
        self.root = up(path, Some(bottom));
        true
    }

    /// Removes `key`; whether it was there. One walk down to its node, whose two subtrees are
    /// joined in its place, the path made again, `O(log n)` expected.
    pub fn remove(&mut self, key: &T) -> bool {
        let mut path = Vec::new();
        let mut cur = self.root.as_ref();
        while let Some(n) = cur {
            match key.cmp(&n.key) {
                Ordering::Equal => {
                    let root = up(path, join(n.left.clone(), n.right.clone()));
                    self.root = root;
                    return true;
                }
                Ordering::Less => {
                    path.push((n, true));
                    cur = n.left.as_ref();
                }
                Ordering::Greater => {
                    path.push((n, false));
                    cur = n.right.as_ref();
                }
            }
        }
        false
    }

    /// The keys at least `bound`, `O(log n)` expected; the set itself when it has no key below.
    pub fn at_least(&self, bound: &T) -> Self {
        TreapSet {
            root: side(&self.root, bound, true),
        }
    }

    /// The keys at most `bound`, `O(log n)` expected; the set itself when it has no key above.
    pub fn at_most(&self, bound: &T) -> Self {
        TreapSet {
            root: side(&self.root, bound, false),
        }
    }

    /// The keys of `self` and of `after`, every key of `self` below every key of `after`,
    /// `O(log n)` expected. The caller keeps the order; a set is checked in debug builds.
    pub fn concat(&self, after: &Self) -> Self {
        debug_assert!(
            match (self.last(), after.first()) {
                (Some(a), Some(b)) => a < b,
                _ => true,
            },
            "`concat` of sets out of order"
        );
        TreapSet {
            root: join(self.root.clone(), after.root.clone()),
        }
    }

    /// The keys of either set (`combine`).
    pub fn union(&self, other: &Self) -> Self {
        TreapSet {
            root: combine(Op::Union, &self.root, &other.root),
        }
    }

    /// The keys of both sets (`combine`).
    pub fn intersection(&self, other: &Self) -> Self {
        TreapSet {
            root: combine(Op::Meet, &self.root, &other.root),
        }
    }

    /// The keys of `self` not in `other` (`combine`).
    pub fn difference(&self, other: &Self) -> Self {
        TreapSet {
            root: combine(Op::Minus, &self.root, &other.root),
        }
    }

    /// Whether every key of `self` is in `other`: the difference empty (`combine`); `false` at
    /// once when `self` is larger.
    pub fn is_subset(&self, other: &Self) -> bool {
        self.len() <= other.len() && self.difference(other).is_empty()
    }

    /// Whether no key is in both: the intersection empty (`combine`).
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.intersection(other).is_empty()
    }

    /// The keys in order, by one walk with a stack of its own.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            stack: Vec::new(),
            at: self.root.as_deref(),
        }
    }
}

/// The keys of a [`TreapSet`] in order.
pub struct Iter<'a, T> {
    stack: Vec<&'a Node<T>>,
    at: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        while let Some(n) = self.at {
            self.stack.push(n);
            self.at = n.left.as_deref();
        }
        let n = self.stack.pop()?;
        self.at = n.right.as_deref();
        Some(&n.key)
    }
}

impl<'a, T: Elem> IntoIterator for &'a TreapSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// By insertion, `O(n log n)` expected.
impl<T: Elem> FromIterator<T> for TreapSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(keys: I) -> Self {
        let mut s = TreapSet::new();
        for k in keys {
            s.insert(k);
        }
        s
    }
}

/// Equal sets: one tree at once; else equal sizes and sums, and then the two trees walked
/// together, node by node, a pair of shared subtrees skipped. In a run one set of keys has one
/// shape (module comment), so two trees are equal sets exactly when they have one shape and one
/// key at each node, and the walk visits only the nodes the two do not share: two equal sets
/// made apart from one set, as `u - 1` twice from `u`, compare in `O(log n)`, not `n`
/// (LIST-xor-finite, as `imbl`'s `==` skipped shared nodes).
impl<T: Elem> PartialEq for TreapSet<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.ptr_eq(other) {
            return true;
        }
        if self.len() != other.len() || self.sum() != other.sum() {
            return false;
        }
        let mut stack = vec![(self.root.as_ref(), other.root.as_ref())];
        while let Some(pair) = stack.pop() {
            match pair {
                (None, None) => {}
                (Some(a), Some(b)) if Arc::ptr_eq(a, b) => {}
                (Some(a), Some(b)) if a.len == b.len && a.key == b.key => {
                    stack.push((a.left.as_ref(), b.left.as_ref()));
                    stack.push((a.right.as_ref(), b.right.as_ref()));
                }
                _ => return false,
            }
        }
        true
    }
}

impl<T: Elem> Eq for TreapSet<T> {}

/// The keys in order compared as sequences, as `BTreeSet` orders; one tree is equal at once.
impl<T: Elem> Ord for TreapSet<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.ptr_eq(other) {
            true => Ordering::Equal,
            false => self.iter().cmp(other.iter()),
        }
    }
}

impl<T: Elem> PartialOrd for TreapSet<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// The size and the sum of the weights, `O(1)`: equal sets hash alike.
impl<T: Elem> std::hash::Hash for TreapSet<T> {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.len().hash(h);
        self.sum().hash(h);
    }
}

impl<T: Elem + fmt::Debug> fmt::Debug for TreapSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests;
