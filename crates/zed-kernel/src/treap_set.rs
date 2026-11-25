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
//!   pp. 16-26, 1998, doi:10.1145/277651.277660. Crossref checked 2026-11-20; the paper below
//!   credits it: "Blelloch and Reid-Miller later show that similar algorithms for treaps \[7\],
//!   are optimal for work (i.e. Θ(m log(n/m + 1)))". Read 2026-11-21 (PDF, LibGen,
//!   verification only): the abstract, "For two sets of size n and m (m <= n) the algorithms
//!   run in expected O(m lg(n/m)) work", and Theorem 2.4 (sec. 2, p. 21) for union: the work
//!   is a sum of split costs, each logarithmic in the part of the larger treap between two
//!   keys of the smaller, and that sum is greatest when those parts are equal (Lemma 2.2).
//!   The `+ 1` here keeps the bound positive at `m = n`.
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
//! shares every subtree it leaves alone. The one exception is [`TreapSet::insert`], which
//! changes in place the nodes no other set holds (`Arc::make_mut`), so no other set sees it.
//! A node's priority is a function of its key drawn at random once per run
//! ([`Elem::priority`], module [`crate::priority`]), ties broken by the order of the keys,
//! so in a run the keys of a set fix its shape whatever order they came in.
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
    /// The key's seeded weight, for [`HashConsTable`]: equal for equal keys, and for two given
    /// unequal keys unequal except with probability near `2^-64` over this process's key,
    /// whatever the keys. The default, [`seeded`] of the weight, has that only when unequal
    /// keys weigh differently; a kind whose unequal keys can share a weight gives its own
    /// (`Value`'s big integers and `rat`s, whose weights are residues modulo the fixed
    /// `2^61 - 1`).
    fn seeded_weight(&self) -> u64 {
        seeded(self.weight())
    }
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

/// Names, as the variable sets of a type keep them (`zedc_types::ty::VarFacts`,
/// PERF-varfacts-held-shared-dag). The priority is the draw's hash of the text
/// ([`Priorities::hash`]), so two names tie whatever the draw only when they are one text; the
/// weight is the hash of another draw, so that it is independent of the priority.
impl Elem for Arc<str> {
    fn priority(&self) -> u64 {
        static PRIORITIES: Priorities = Priorities::eight_wise(19);
        PRIORITIES.hash(&**self)
    }
    fn weight(&self) -> u64 {
        static WEIGHTS: Priorities = Priorities::new(20);
        WEIGHTS.hash(&**self)
    }
    fn class(&self) -> u32 {
        1
    }
}

/// A node: its key, priority and weight, and over its subtree the number of keys, the sum of
/// the weights, the sum of the seeded weights ([`seeded`]) and the union of the classes. The
/// node's own seeded weight is not kept: it is `keyed` less its children's ([`own_keyed`]).
struct Node<T> {
    key: T,
    prio: u64,
    weight: u64,
    len: usize,
    sum: u64,
    keyed: u64,
    classes: u32,
    left: Tree<T>,
    right: Tree<T>,
}

/// The copy `Arc::make_mut` makes of a shared node ([`TreapSet::insert`]): the key and the
/// handles of the two subtrees, which it shares.
impl<T: Clone> Clone for Node<T> {
    fn clone(&self) -> Self {
        Node {
            key: self.key.clone(),
            left: self.left.clone(),
            right: self.right.clone(),
            ..*self
        }
    }
}

/// A tree: its root, or `None` when empty.
type Tree<T> = Option<Arc<Node<T>>>;

/// A pair of [`TreapSet::is_subset`]'s walk: a subtree of each set and the bounds of the range,
/// each `None` where the range has no bound on that side, and the greatest key of `self` below
/// every key of its subtree (`None`: no key below), for step 13.
type Pair<'a, T> = (
    Option<&'a Arc<Node<T>>>,
    Option<&'a Arc<Node<T>>>,
    Option<&'a T>,
    Option<&'a T>,
    Option<&'a T>,
);

#[cfg(test)]
thread_local! {
    /// The units of work [`TreapSet::is_subset`] has done on this thread, counted in tests only:
    /// pairs taken and moves of `p`. The test
    /// `is_subset_work_within_its_bound` holds it to the bound of the proof.
    static IS_SUBSET_WORK: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

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

fn keyed<T>(t: &Tree<T>) -> u64 {
    t.as_ref().map_or(0, |n| n.keyed)
}

/// The seeded weight of node `n` alone: its subtree's less its children's.
fn own_keyed<T>(n: &Node<T>) -> u64 {
    n.keyed
        .wrapping_sub(keyed(&n.left))
        .wrapping_sub(keyed(&n.right))
}

/// An input through SipHash under a key drawn once per process from the system's random bytes
/// (std's `RandomState`): the seeded weights of [`HashConsTable`] ([`Elem::seeded_weight`],
/// whose default input is the key's weight; for a `u64` input this is the function it was when
/// it took only weights). Complexity tradeoff: the table first keyed its
/// sets by the sum of the weights, which is public and in places linear (an `i64` weighs a
/// fixed multiple of itself, so `{i, -i}` all weigh 0, and an integer literal's weight
/// `mix(1, i)` is a bijection anyone can invert): `n` distinct sets of one sum went to one
/// bucket, scanned on each set put in, `O(n^2)` (`sharing_sets_of_one_sum_scales` and
/// `literal_types_of_one_sum_scale` in `bench.rs`, FREE2-tables-hashcons-bench). The sum
/// itself cannot be seeded: it is in the digests and order of types (`types::Parts::hashes`,
/// `cmp`), which must be the same on every run. Used: a second sum, of the weights through a
/// pseudorandom function whose key no input sees, the incremental hash of a set by addition
/// ("AdHash", Bellare and Micciancio, "A new paradigm for collision-free hashing:
/// incrementality at reduced cost", EUROCRYPT 1997, LNCS 1233, pp. 163-192,
/// doi:10.1007/3-540-69053-0_13, Crossref checked 2026-11-25). For two unequal sets, the
/// symmetric difference holds a key; when no other key of it gives the same input to the
/// random function, that key's value is independent of the others', and the two sums of the
/// function's values are equal with probability `2^-64`. The default input is the weight, and
/// a kind whose unequal keys can share a weight gives an input that tells them apart
/// ([`Elem::seeded_weight`]: `Value` gives a big integer's or `rat`'s fingerprint,
/// `crate::priority::fingerprint_primes`). So a bucket holds the sets equal to the one put in
/// and, in expectation, `O(1)` others. Where the inputs still tie (a fingerprint collision, or
/// keys of a kind whose weights tie and which gives no other input, as types of one digest,
/// plan row PERF-set-tied-digest-depth), the bucket is ordered, so a share costs `O(log b)`
/// comparisons of sets for `b` sets in the bucket, not `b` ([`HashConsTable`]). Not proved here
/// that SipHash-1-3 (std's algorithm, "subject to change" by its documentation) is such a function; it is the one std
/// uses against the same attack on its maps. Cost: 8 bytes a node and one hash per key put in
/// ([`TreapSet::insert`]); a node made again takes its own seeded weight from its old counts
/// ([`own_keyed`]). Results do not depend on the key: the table only ever gives a set an equal
/// set's tree, equal sets have one seeded sum under any key, and nothing else reads the seeded
/// sums. The table is only swept (`retain`) and counted, never listed in order; `Hash` and
/// `cmp` of a set, and the digests of types, read the unseeded sum (checked by
/// `the_trees_are_the_same_under_two_keys` in `tests.rs`, which sets `TEST_SALT`).
pub(crate) fn seeded<K: std::hash::Hash>(input: K) -> u64 {
    use std::hash::BuildHasher;
    static KEY: std::sync::OnceLock<std::hash::RandomState> = std::sync::OnceLock::new();
    let key = KEY.get_or_init(std::hash::RandomState::new);
    #[cfg(test)]
    if let Some(salt) = TEST_SALT.get() {
        return key.hash_one((salt, input));
    }
    key.hash_one(input)
}

#[cfg(test)]
thread_local! {
    /// A second key for this thread's seeded weights in tests: a thread that sets it before it
    /// makes any set hashes each weight with the salt, another function of the weight than
    /// with no salt or another salt.
    static TEST_SALT: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(None) };
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
        keyed: own_keyed(n)
            .wrapping_add(keyed(&left))
            .wrapping_add(keyed(&right)),
        classes: n.key.class() | classes(&left) | classes(&right),
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

/// The keys of `t` before `key` and after it, for a `key` that `t` lacks, as [`split`] gives
/// them; a node of the walk that `t` alone holds is moved, not made again (`Arc::make_mut`), and
/// its counts made again from its new children, bottom up.
fn split_absent<T: Elem>(mut t: Tree<T>, key: &T) -> (Tree<T>, Tree<T>) {
    // Each node of the walk with whether it goes to the left part. On a treap's insertion the
    // walk is the two spines below the new node, fewer than 2 nodes in expectation (`insert`).
    let mut walk = Vec::new();
    while let Some(mut n) = t {
        let m = Arc::make_mut(&mut n);
        let before = m.key < *key;
        // Read while both children are in place.
        let own = own_keyed(m);
        t = match before {
            true => m.right.take(),
            false => m.left.take(),
        };
        walk.push((n, before, own));
    }
    let (mut l, mut r) = (None, None);
    for (mut n, before, own) in walk.into_iter().rev() {
        // Held only here, as made unique above: `make_mut` copies nothing.
        let m = Arc::make_mut(&mut n);
        match before {
            true => m.right = l.take(),
            false => m.left = r.take(),
        }
        m.len = 1 + len(&m.left) + len(&m.right);
        m.sum = m
            .weight
            .wrapping_add(sum(&m.left))
            .wrapping_add(sum(&m.right));
        m.keyed = own
            .wrapping_add(keyed(&m.left))
            .wrapping_add(keyed(&m.right));
        m.classes = m.key.class() | classes(&m.left) | classes(&m.right);
        *(if before { &mut l } else { &mut r }) = Some(n);
    }
    (l, r)
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

    /// Whether the set has `key`, or a key that borrows as it (a name's text, `&str`, for an
    /// `Arc<str>`): one walk down, `O(log n)`.
    pub fn contains<Q: Ord + ?Sized>(&self, key: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
    {
        let mut cur = self.root.as_deref();
        while let Some(n) = cur {
            cur = match key.cmp(n.key.borrow()) {
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
    /// then the subtree there split at the key, `O(log n)` expected (as
    /// `types::bdd::list::treap::insert`). A node on the path that another set shares is made
    /// again, one this set alone holds is changed in place. The set is left as it was when it
    /// has the key.
    // Complexity tradeoff (PERF-varfacts-held-shared-dag): naive version, the path always made
    // again (`up`), as a persistent insert does: `O(log n)` new nodes and as many freed per
    // insertion even into a set no other holds, which is how a set is built one key at a time.
    // The facts of a tuple of `n` variables (`Ty::var_facts`) took 7.4M instructions at 400 and
    // 75M at 3200 (10.1 times, 10.85 under one seed), against 3.11M and 28.7M (9.23) for the
    // `imbl::OrdSet` it replaced, whose insertion changes nodes it alone holds in place
    // (`Arc::make_mut`). Used: the same, `Arc::make_mut` on each node of the path, which copies
    // a shared node and so keeps every other set as it was. Proof that the counts stay right:
    // the key is not in the set (checked first), so it lands below each node of the path, and
    // each of those gains one key, its weight and its class. The subtree below is split by
    // `split_absent`, which moves the nodes this set alone holds as well; its walk is the two
    // spines of the new node's subtrees, whose length is the number of rotations a treap's
    // insertion by rotations makes, below 2 in expectation over independent priorities (Seidel
    // and Aragon, "Randomized search trees", Algorithmica 16, 1996, pp. 464-497,
    // doi:10.1007/BF01940876, Crossref checked 2026-11-21; the abstract: "in the expected case
    // a search or an update takes logarithmic time, with the update requiring fewer than two
    // rotations"). Not proved here for the 8-wise independent draw ([`Priorities::eight_wise`]);
    // the walk is at most the depth, `O(log n)` expected under it (module [`crate::priority`]).
    // Measured after, over seeds 0 to 15: 3.74M to 3.87M and 32.0M to 34.8M, at most 9.25
    // times (8.4 times the bytes); with the path changed in place and the subtree below still
    // made again, 4.86M and 42.7M, up to 10.2 times the bytes. Given up: none of the sharing;
    // a set's nodes are still never changed while another set holds them.
    // Tests: `every_operation_agrees_with_a_btree_set`,
    // `an_insertion_leaves_every_set_sharing_its_nodes_as_it_was`.
    pub fn insert(&mut self, key: T) -> bool {
        if self.contains(&key) {
            return false;
        }
        let (prio, weight, class) = (key.priority(), key.weight(), key.class());
        let kw = key.seeded_weight();
        let mut cur = &mut self.root;
        // The test is apart from the step down so that no borrow of `cur` outlives the loop.
        while cur
            .as_ref()
            .is_some_and(|n| (n.prio, &n.key) > (prio, &key))
        {
            if let Some(n) = cur {
                let n = Arc::make_mut(n);
                n.len += 1;
                n.sum = n.sum.wrapping_add(weight);
                n.keyed = n.keyed.wrapping_add(kw);
                n.classes |= class;
                cur = if key < n.key {
                    &mut n.left
                } else {
                    &mut n.right
                };
            }
        }
        let (left, right) = split_absent(cur.take(), &key);
        *cur = Some(Arc::new(Node {
            len: 1 + len(&left) + len(&right),
            sum: weight.wrapping_add(sum(&left)).wrapping_add(sum(&right)),
            keyed: kw.wrapping_add(keyed(&left)).wrapping_add(keyed(&right)),
            classes: class | classes(&left) | classes(&right),
            key,
            prio,
            weight,
            left,
            right,
        }));
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

    /// Whether every key of `self` is in `other`: `false` at once when `self` is larger, else one
    /// walk of the two trees together that makes no node and stops at the first key of `self`
    /// missing from `other` (PROOF-kernel-treap-is-subset-cost).
    ///
    /// The walk keeps pairs `(p, q, lo, hi)`: `q` is a subtree of `other` whose keys are exactly
    /// the keys of `other` strictly between `lo` and `hi` (no bound where `None`), and `p` is a
    /// subtree of `self` holding every key of `self` in that range, and maybe keys outside it. The
    /// question at a pair is whether the keys of `p` in the range are all in `q`. A pair whose
    /// range lies wholly below `self`'s least key or above its greatest (read once, `O(h)`) holds
    /// at once. Otherwise `p` first moves down past its root while the root is outside the range,
    /// to the side of the range. Proof that each step is right, and of the cost:
    ///
    /// 1. The pairs keep their invariant. At the start `p` and `q` are the two roots, with no
    ///    bounds. Moving `p` from a root of key `<= lo` to its right child drops that root and its
    ///    left subtree, all keys `<= lo`, outside the range; the same on the right. The pushes of
    ///    steps 4 and 6 split the range at a key `z` and give each side the child of `q` on that
    ///    side, which holds exactly `other`'s keys there since `q` held exactly those of the
    ///    range; `p` keeps every key of `self` on each side, as its child on that side (step 4,
    ///    `z` the key of `p`'s root) or as `p` itself (step 6).
    /// 2. After the move, the root of `p` is the greatest key of `self` in the range by `above`
    ///    (priority, ties by key), and the root of `q` the greatest of `other`'s keys there: each
    ///    root stands above its whole subtree (heap order), the subtree holds every key of its
    ///    set in the range (step 1), and the root lies in the range. A key has one priority in a
    ///    run whichever set holds it ([`Elem::priority`]), so `above` orders the keys of both
    ///    trees alike.
    /// 3. Range wholly below the least key `m` of `self` (`hi <= m`) or above the greatest `M`
    ///    (`lo >= M`), or `p` empty: no key of `self` in the range, so the pair holds. `q` empty
    ///    and `p` not: the
    ///    root of `p` is a key of `self` in the range that `other` lacks, `false`. `p` and `q` one
    ///    node: the keys of `p` are those of `q`, so the pair holds.
    /// 4. The two roots of one key: that key is in both, and the rest of the range splits at it
    ///    into two pairs, the children on each side.
    /// 5. The root of `p` above the root of `q`: the key of `p`'s root is not in `other`, since it
    ///    lies in the range and would then be a key of `other` there above `q`'s root, against
    ///    step 2. So `false` at once, with no search of `q`.
    /// 6. The root of `q` above the root of `p`: by step 2 turned around, `q`'s key `z` is not in
    ///    `self`, so the range splits at `z` into two pairs, `p` itself with each child of `q`.
    ///
    /// Cost. Let `U` be the number of nodes of `self` that are not nodes of `other` (as `Arc`s),
    /// `D` the number of pairs that take step 6, and `h` the height of `self`.
    ///
    /// 7. A pair at step 4 that did not stop at step 3 has a root of `p` that is not a node of
    ///    `other`: were it one, it would be `other`'s only node of that key, which is `q`'s root
    ///    (in the range by step 2), and the pair would have stopped at step 3. No later range
    ///    holds that key, so these pairs are at most `U`.
    /// 8. A pair at step 6 has its `z`, a key of `other` not in `self`, which leaves every later
    ///    range; these pairs are `D`, at most the keys of `other` not in `self`. Split `D` into
    ///    `D_in`, the keys `z` between `m` and `M`, and `D_out`, those outside.
    /// 9. Step 5 happens at most once. Each pair at steps 4 or 6 pushes two pairs, so the walk
    ///    takes at most `2 (U + D) + 1` pairs, each of `O(1)` work besides the moves of `p`.
    /// 10. The moves of `p`. A node of `self` is passed only when its key is outside the range,
    ///     beyond a bound `z` that is a key of step 4 or 6. At step 4 the key is `p`'s root, so
    ///     each child of `p` lies wholly on its side of it and no move passes a node at that
    ///     bound. A key `z` of step 6 below `m` bounds a pair whose range lies below `m`, which
    ///     holds at step 3 before any move, and pairs above `z`, where every key of `self` is, so
    ///     no move passes a node at `z`; the same above `M`. A key `z` of `D_in` bounds two
    ///     chains of pairs, one on each side of it, and the moves in each follow the search path
    ///     of `z` in `self` down, passing each of its nodes at most once: at most `2h` moves.
    /// 11. Where `self` lies in `other`, `D_out <= 2 h'` and `D_in <= 2 g h'`, with `h'` the
    ///     height of `other` and `g` the number of runs of consecutive keys of `other` lying
    ///     between two keys of `self` and not in `self` (the gaps). Proof: at step 6 the range
    ///     holds a key of `self` (else `p` was empty at step 3); let `s` be the key of `self` in
    ///     the range nearest to `z` (on either side). Every key between `z` and `s` is not in
    ///     `self`, so `z` lies in the run of `other` next to `s`. `s` is in `other`, in the range,
    ///     so in `q`, whose root is `z`, so `z` is an ancestor of `s` in `other`. A run outside
    ///     `[m, M]` is next to `m` or `M` only, and a gap next to its two ends; each key `s` has
    ///     at most `h'` ancestors.
    ///
    /// Steps 10 and 11 give `O(D_in h)` moves, and without more that is reached: every key of a
    /// gap has the same search path in `self`, and each pair whose range lies in the gap walked
    /// it down to an empty subtree again (PROOF-kernel-treap-is-subset-gaps, 2026-11-21). So:
    ///
    /// 12. The walk keeps the last range it found to hold no key of `self`, `(a, b)`. A pair
    ///     whose `p` has its root outside the range (so that step 1 would move it), and whose
    ///     range lies inside `(a, b)`, holds, as at step 3, whatever the order of the pairs, since
    ///     `(a, b)` holds no key of `self` (step 13). A pair whose root is in the range makes no
    ///     move, so the check would save nothing there and is not made.
    /// 13. Each pair carries `pred`, the greatest key of `self` below every key of `p`'s subtree
    ///     (`None` at the root, none below). It stays exact: the left child of step 4 keeps its
    ///     parent's and the right child takes `x`'s key, as no key of `self` lies between `x` and
    ///     the least key of its right subtree (keys in order); step 6 keeps `p`, so `pred`; a move
    ///     right past `n` takes `n`'s key, for the same reason, and a move left keeps it. Each of
    ///     these keeps `pred <= lo`: at the root both are `None`, the right child of step 4 has
    ///     `lo` the key of `x`, step 6 only raises `lo`, and a move right passes `n <= lo`. When
    ///     `p` ends empty after its moves, no key of `self` lies between `pred` and the least key
    ///     of `self` above `p`'s subtree, which is at least `hi` (the same argument from the other
    ///     side), so `(pred, hi)` holds no key of `self` and is kept: its lower end is the key of
    ///     `self` next below the range and its upper end is `hi`, with no search.
    /// 14. Each gap costs at most `3h` moves. Let `s1 < s2` be keys of `self`
    ///     next to each other with keys of `other` between them, the gap `G`. A move passes a
    ///     node only at a bound `z` in `D_in` (step 10); let `z` be in `G`. A pair with bound `z`
    ///     lies inside `G`, or holds `s1` with its upper bound in `G`, or `s2` with its lower
    ///     bound in `G`. (a) The pairs that hold `s1` with upper bound in `G` form one chain: a
    ///     split at a key below `s1` gives one such child (the upper one), at a key in `G` one
    ///     (the lower one), at `s1` none. Along the chain each `p` starts where its parent's
    ///     ended (step 6) or at a child of it (step 4), so the chain's moves go down one path of
    ///     `self`: at most `h`. The same for `s2`. (b) A pair inside `G` pushes no pair, as its
    ///     `p` ends empty. The pairs that push none have ranges apart from one another and the
    ///     walk takes them in falling order of their ranges, as `pairs` is a stack and the upper
    ///     pair of a split is pushed last, so those inside `G` come one after another with none
    ///     of another gap between them, and no pair between them changes the kept range (step 13
    ///     changes it only at a pair whose `p` ends empty, whose range holds no key of `self`, so
    ///     lies between `s1` and `s2` when between them in order). The first that moves keeps
    ///     `(s1, hi)` (step 13), after at most `h` moves; every later one lies below that `hi`
    ///     and above `s1`, and either has `p` empty or its root outside its range (the range
    ///     holds no key of `self`), so holds at step 12 at once, or makes no move.
    ///
    /// So the work is `O(U + D + g h + h)`, `g` the number of gaps (at most `D_in`), besides the
    /// `O(h)` of `first` and `last`: at most `2 (U + D) + 1` pairs (step 9) and `3 g h` moves
    /// (step 14), which the test `is_subset_work_within_its_bound` counts. The cost of steps 12
    /// and 13 where they save nothing: `pred`, one word more on every pair, and the check of
    /// step 12 on pairs that move; measured 2026-11-21 against the walk without them, in
    /// instructions, 4% to 11% more (65 cuts of `l` keys with 64 gaps of `l`, `l = 16` and
    /// `128`; `d = 64`
    /// edits of 2^17 keys; the middle half of 2^17 keys). A search for the lower end at step 13
    /// in place of `pred` cost 31% more on the edits. Where
    /// `other` has no key outside `self` (a set and a narrowing of it, either way round), `D = 0`
    /// and the work is `O(U + h)`. Where `self` is a cut of `other` to a range (`at_least`,
    /// `at_most`, or both), `self` lies in `other` with no gap, `g = 0`, `D_out <= 2 h'`, and the
    /// cut makes new nodes only along its two paths, `U <= 2h`: `O(h + h')`, `O(log k)` expected
    /// for `k` keys (the expected height, module comment). For `self` and `other` made from one
    /// set by `d` edits, each making new nodes along one path and adding or removing at most one
    /// key, `U = O(d h)` and `D, g <= d`, so `O(d log k)` expected. For `self` a set of `g + 1`
    /// cuts of `other` joined in order, `U = O(g h)` and `D_in <= 2 g h'`, so `O(g (h + h'))`,
    /// `O(g log k)` expected. Sets not made from one another share no node and `U` is up to
    /// `|self|`. Until 2026-11-21 this was `self.difference(other).is_empty()`, which made the
    /// difference's nodes and went on past the first key missing, a split of `O(h)` and a join at
    /// each pair. Tests: `every_operation_agrees_with_a_btree_set` and
    /// `is_subset_agrees_on_sets_made_from_one_set` (correctness),
    /// `is_subset_work_within_its_bound` (the units of work against the bound, on gaps that the
    /// walk without steps 12 to 14 took past it),
    /// `bench::is_subset_scales_with_the_edits_not_the_size` and
    /// `bench::is_subset_of_joined_cuts_scales_with_the_gaps` (at n and 8n).
    pub fn is_subset(&self, other: &Self) -> bool {
        let mut work = 0;
        let held = self.subset_walk(other, &mut work);
        #[cfg(test)]
        IS_SUBSET_WORK.with(|c| c.set(c.get() + work));
        held
    }

    /// The walk of [`TreapSet::is_subset`], adding its units of work to `work`: a local count,
    /// which a build without tests drops, so that the count costs one add a unit in tests and
    /// nothing outside them.
    #[inline(always)]
    fn subset_walk(&self, other: &Self, work: &mut u64) -> bool {
        if self.len() > other.len() {
            return false;
        }
        let (Some(least), Some(greatest)) = (self.first(), self.last()) else {
            return true;
        };
        let mut pairs: Vec<Pair<'_, T>> =
            vec![(self.root.as_ref(), other.root.as_ref(), None, None, None)];
        // Step 12: the last range found to hold no key of `self`, `(a, b)` with `a` `None` where
        // it has no lower bound.
        let mut free: Option<(Option<&T>, &T)> = None;
        while let Some((mut p, q, lo, hi, mut pred)) = pairs.pop() {
            *work += 1;
            // Step 3, the range outside `[least, greatest]`.
            if hi.is_some_and(|h| h <= least) || lo.is_some_and(|l| l >= greatest) {
                continue;
            }
            let outside =
                |n: &Node<T>| lo.is_some_and(|l| n.key <= *l) || hi.is_some_and(|h| n.key >= *h);
            if p.is_some_and(|n| outside(n)) {
                // Step 12, the range inside the free range.
                if let (Some((a, b)), Some(h)) = (free, hi) {
                    let above_a = match (a, lo) {
                        (None, _) => true,
                        (Some(a), Some(l)) => l >= a,
                        (Some(_), None) => false,
                    };
                    if h <= b && above_a {
                        continue;
                    }
                }
                // Step 1: `p` moved down to its first node in the range, `pred` kept (step 13).
                while let Some(n) = p {
                    p = match (lo, hi) {
                        (Some(l), _) if n.key <= *l => {
                            pred = Some(&n.key);
                            n.right.as_ref()
                        }
                        (_, Some(h)) if n.key >= *h => n.left.as_ref(),
                        _ => break,
                    };
                    *work += 1;
                }
                // Step 13: `p` ended empty, and the free range is from the key of `self` next
                // below the range to `hi`.
                if p.is_none() {
                    if let Some(h) = hi {
                        free = Some((pred, h));
                    }
                    continue;
                }
            }
            // Step 3.
            let Some(x) = p else { continue };
            let Some(y) = q else { return false };
            if Arc::ptr_eq(x, y) {
                continue;
            }
            if x.key == y.key {
                // Step 4.
                pairs.push((x.left.as_ref(), y.left.as_ref(), lo, Some(&x.key), pred));
                pairs.push((
                    x.right.as_ref(),
                    y.right.as_ref(),
                    Some(&x.key),
                    hi,
                    Some(&x.key),
                ));
            } else if above(x, y) {
                // Step 5.
                return false;
            } else {
                // Step 6.
                pairs.push((p, y.left.as_ref(), lo, Some(&y.key), pred));
                pairs.push((p, y.right.as_ref(), Some(&y.key), hi, pred));
            }
        }
        true
    }

    /// Whether no key is in both: the intersection empty (`combine`).
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.intersection(other).is_empty()
    }

    /// The keys in order, by one walk with a stack of its own.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            stack: smallvec::SmallVec::new(),
            at: self.root.as_deref(),
        }
    }
}

/// The keys of a [`TreapSet`] in order.
///
/// Complexity tradeoff: the stack holds the nodes whose left subtree is being walked, at most
/// the height. As a `Vec` it allocated on the first key, 32 bytes or more a walk, and
/// [`Ord`] makes two walks a comparison, so a search of a bucket of `b` sets in
/// [`HashConsTable::share`] allocated `O(log b)` times: `2n` sets of two keys allocated
/// 137,048,020 and 1,363,687,412 bytes at `n` = 20,000 and 160,000 (`sharing_tied_sets_scales`,
/// b22-free2 on a Colab VM, 2026-11-25), `n log n`. Used: 16 nodes inline (136 bytes), going to
/// the heap past that. The stack's first fill is the left spine, the path to the least key, whose
/// expected length in a treap of `m` keys is `H_m` (Seidel and Aragon 1996, Theorem 4.7 (i) at
/// `l = 1`, cited at [`HashConsTable`]), at most 16 for `m` up to about `5 * 10^6`. Cost: 136
/// bytes moved with each iterator.
pub struct Iter<'a, T> {
    stack: smallvec::SmallVec<[&'a Node<T>; 16]>,
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

/// The keys in order, each cloned: one walk, `O(n)`, and a vector of the keys.
impl<T: Elem> IntoIterator for TreapSet<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> std::vec::IntoIter<T> {
        self.iter().cloned().collect::<Vec<T>>().into_iter()
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

/// A table of live sets by their sum of seeded weights (`seeded`), so that equal sets made
/// apart become one tree (plan row TYPE-hashcons): [`HashConsTable::share`] gives a set the
/// root of an equal set the table holds, or puts its own root in. Two sets made apart, as
/// `{0, 1, ..., n}` built up in two orders, then compare by [`TreapSet::ptr_eq`], `O(1)`, where
/// `==` walked every node, `O(n)`, at each comparison. A bucket holds the sets of one seeded sum
/// in their order ([`TreapSet`]'s `Ord`), so a set is found among `b` in `O(log b)` comparisons.
/// The table holds the sets' roots; a set no one else holds (its root's only handle is the
/// table's) is taken out when the table has doubled since its last sweep, `O(1)` amortized per
/// set put in.
///
/// Complexity tradeoff: the naive way, comparing equal sets made apart in full each time,
/// costs `O(n)` per comparison, `O(n k)` for `k` comparisons. Used: a search of the bucket of
/// the set's seeded sum, `O(n)` per comparison only where an equal set is alive (the walk of a
/// set built in `O(n)` already) or on a collision of the seeded sums, probability `2^-64` a pair
/// whatever the input (`seeded`), then `O(1)` per comparison. Where many unequal sets share a
/// seeded sum (keys whose seeded weights tie, `seeded`), a bucket of `b` sets is searched in
/// `O(log b)` comparisons by its order; the bucket was a list of weak handles before, `b`
/// comparisons a set put in, `O(b^2)` for `b` such sets (`sharing_tied_sets_scales` in
/// `bench.rs`). An ordered bucket needs its sets alive to compare them, so it holds strong
/// handles: a dead set's nodes stay until the next sweep, at most as many sets as were live at
/// the last one. Cost: a hash lookup per set put in, and a handle per set held.
///
/// Prior work: a treap of distinct priorities has one shape per set (Seidel and Aragon,
/// "Randomized search trees", Algorithmica 16(4/5), 464-497, 1996, doi:10.1007/BF01940876,
/// sec. 2: "the treap for X is unique: the item with largest priority becomes the root, and the
/// allotment of the remaining items to the left and right subtree is then determined by their
/// keys"), which is what makes equality a walk of two shapes (`==`) and lets one tree stand for
/// all equal sets. Sundar and Tarjan, "Unique binary search tree representations and
/// equality-testing of sets and sequences", STOC '90, 18-25, doi:10.1145/100216.100219, p. 19:
/// "Aragon and Seidel [2] give a randomized binary search tree representation of a dictionary
/// that has the unique representability property and allows dictionary operations to be
/// performed in O(log n) randomized time"; their Theorem 1 (p. 21) is why no deterministic
/// shape would do: "If the n-subsets of U are represented by binary search trees of height at
/// most d, then there is an n-subset on which an update operation requires Ω(n − 2d)
/// rotations." Both checked 2026-11-25 against the papers' text.
pub struct HashConsTable<T> {
    table: crate::digest::DigestMap<u64, std::collections::BTreeSet<TreapSet<T>>>,
    held: usize,
    swept_at: usize,
}

impl<T> Default for HashConsTable<T> {
    fn default() -> Self {
        HashConsTable {
            table: Default::default(),
            held: 0,
            swept_at: 0,
        }
    }
}

impl<T: Elem> HashConsTable<T> {
    /// `set` made one tree with an equal live set of the table, or put in the table.
    pub fn share(&mut self, set: &mut TreapSet<T>) {
        let Some(root) = &set.root else {
            return;
        };
        let bucket = self.table.entry(root.keyed).or_default();
        if let Some(other) = bucket.get(set) {
            *set = other.clone();
            return;
        }
        bucket.insert(set.clone());
        self.held += 1;
        if self.held > 2 * self.swept_at {
            // A set is dead when the table holds its root's only handle.
            self.table.retain(|_, b| {
                b.retain(|s| s.root.as_ref().is_some_and(|r| Arc::strong_count(r) > 1));
                !b.is_empty()
            });
            self.held = self
                .table
                .values()
                .map(std::collections::BTreeSet::len)
                .sum();
            self.swept_at = self.held;
        }
    }
}

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

#[cfg(test)]
mod bench;
