//! Sets of literals, each an atom and whether it is taken, as treaps whose nodes are shared: the
//! blocks of a decision list (module `list`) and the atoms of an exclusive or (`Part::xor`).
//!
//! A node's priority is drawn once per run for its literal ([`priority`]), ties broken by the
//! literal's order, so the nodes are ordered by priority with no ties and, in one run, one set
//! has one shape whatever order its literals were added in. The live nodes of a thread are kept
//! in a table by literal and children, so one set is one node: two sets are equal exactly when
//! their roots are one node, and a set built in two orders is found again. The table holds each
//! node weakly, and a node leaves it when it is dropped (step TABLE-life). An insertion or
//! removal rebuilds the path to the place it changes, `O(log n)` nodes in expectation, each
//! looked up in the table in `O(1)` expected; the walks keep stacks of their own, so a set of
//! any shape is walked on a small stack.
//!
//! The depth. The priority of a literal is the run's random polynomial `q` of degree 4, one for
//! each value of `taken`, at its point, its atom's digest modulo `p = 2^64 - 59`. Fix a set of
//! `n` literals, chosen with no knowledge of the draw (nothing the kernel computes reads a shape,
//! paragraph below). Let `T0` be the literals whose point another of the set shares: they tie
//! whatever the draw. Literals at distinct points take 5-wise independent uniform priorities, two
//! of them equal with probability `1/p`, so every node's expected depth is at most
//! `T0 + n(n - 1)/p + 2c H_n`, `c` the constant of Seidel and Aragon's Lemma 6.1 ("Randomized
//! search trees", Algorithmica 16, 1996, Lemma 4.3, Theorem 4.7 and section 6; the proof, ties
//! included, is in module [`crate::priority`]). Not proved for every program: `T0` is a function
//! of the fixed digests, and a program can name many atoms of one digest (each step of a digest,
//! `digest::step`, can be inverted in each argument), whose set is then a path whatever the draw
//! (PERF-xor-shape-free, COMPLEXITY.md K123; plan row PERF-set-tied-digest-depth).
//!
//! The shape follows the draw, so nothing printed or ordered reads it (rule
//! deterministic-checking): a set's digests are sums over its literals ([`make`]), the same for
//! every shape; the order of types compares two sets of equal digests by their literals in order
//! (`Walk::Sets` in module `types`); and the exclusive or of a set (module `xor`) is built from
//! its smallest literal and the rest, not over its tree.

use std::sync::Arc;
use std::sync::atomic::Ordering as Atomic;

use crate::priority::Priorities;
use crate::types::bucket::{self, Bucket};
use crate::types::hash::mix;

/// The atoms of sets, each kind with its thread's table of set nodes. Every atom of a diagram
/// (`bdd::Literal`) is one; the module needs no more of the atoms, so it imports nothing of the
/// diagrams that hold its sets.
pub(in crate::types) trait Atom: Ord + Clone + 'static {
    /// Runs `f` on the thread's table of set nodes.
    fn sets<R>(f: impl FnOnce(&mut SetTable<Self>) -> R) -> R;
    /// Runs `f` on the thread's table of set nodes to remove a dropped node's entry; nothing is
    /// done while the thread is ending or the table is borrowed (`bdd::Literal::untable`).
    fn unsets(f: impl FnOnce(&mut SetTable<Self>));
    /// A hash of the atom, equal for equal atoms.
    fn digest(&self) -> u64;
    fn name_digest(&self) -> u64;
    /// Drops a set node in the thread's loop of type parts (module `deep`).
    fn free_set(set: Arc<Set<Self>>);
}

/// The next node id. Cells, sets and expressions take their ids from one counter, so an id
/// names one node among them; ids key the maps of a walk, never addresses.
pub(super) static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(2);

/// A literal: an atom and whether it is taken.
pub(in crate::types) type Key<A> = (A, bool);

/// A node of a set: its literal, and the sets of the literals before and after it.
pub(in crate::types) struct Set<A: Atom> {
    /// The node's id, unique among the nodes of the process.
    pub(in crate::types) id: u64,
    /// A hash of the set's literals, equal for equal sets.
    pub(in crate::types) digest: u64,
    pub(in crate::types) name_digest: u64,
    prio: u64,
    /// The node's slot in its bucket of the table (module `bucket`).
    slot: u32,
    pub(in crate::types) key: Key<A>,
    len: usize,
    pub(in crate::types) left: Tree<A>,
    pub(in crate::types) right: Tree<A>,
}

/// A set: the root, or `None` when empty.
pub(in crate::types) type Tree<A> = Option<Arc<Set<A>>>;

/// The live nodes of a thread's sets, by the hash of the atom, whether it is taken and the
/// children's ids; nodes whose atoms differ but share a hash share a bucket, ordered by their
/// atoms (module `bucket`), and a lookup tells them apart by the atoms' order. Hashed rather than ordered by literal, since the table is
/// never read in order: a lookup in a table ordered by literal compared its key with some
/// `log N` others, each by the atoms' contents (three types read through their nodes for a
/// morphism type), which had made half the cost of a search through nested morphism types
/// (EMPTY-morphism-diff-cost).
pub(in crate::types) type SetTable<A> = std::collections::HashMap<
    Slot,
    Bucket<Set<A>>,
    std::hash::BuildHasherDefault<crate::digest::Digest>,
>;

/// The key of a node's bucket in its [`SetTable`]: the hash of its atom, whether the atom is
/// taken, and its children's ids.
type Slot = (u64, bool, u64, u64);

/// The bucket of the node of `key` over the children of ids `left` and `right`.
fn slot<A: Atom>(key: &Key<A>, left: u64, right: u64) -> Slot {
    (key.0.name_digest(), key.1, left, right)
}

/// A set node leaves its thread's table, and its children are freed in a loop (module `deep`),
/// as a diagram's cells are.
impl<A: Atom> Drop for Set<A> {
    fn drop(&mut self) {
        let k = slot(&self.key, id(self.left.as_ref()), id(self.right.as_ref()));
        A::unsets(|t: &mut SetTable<A>| {
            // The node has no entry when it was made on another thread.
            if let Some(bucket) = t.get_mut(&k) {
                bucket.leave(self.slot, self);
                if bucket.is_empty() {
                    t.remove(&k);
                }
            }
        });
        for c in [self.left.take(), self.right.take()].into_iter().flatten() {
            A::free_set(c);
        }
    }
}

/// The priorities of the literals, drawn once per run (module [`crate::priority`]): two uses, so
/// that the taken and the refused literal of one atom are two independent points.
static PRIORITIES: [Priorities; 2] = [Priorities::new(11), Priorities::new(12)];

/// The priority of `key`: the run's random polynomial of degree 4 at its atom's digest, one for
/// each value of `taken`. Distinct points take 5-wise independent uniform priorities, which
/// bounds every node's expected depth by `O(log n)` plus the literals that share a point
/// (module comment; Seidel and Aragon 1996, Theorem 3.3 and section 6; the proof is in module
/// [`crate::priority`]). Atoms whose digests are equal modulo `2^64 - 59` share a point: they
/// tie whatever the draw, and each such atom adds at most one to a depth.
// Complexity tradeoff (PERF-xor-shape-free, COMPLEXITY.md K123): the fixed hash this replaces,
// `mix(mix(13, digest), taken)`, cost two mixes and gave one shape whatever the run, but no
// bound: a program can name literals whose hashes rise in their order, and their set is a path
// (2,030 of the first 2^20 integer literals, test `chosen_literals_give_a_logarithmic_height`),
// `O(n)` per insertion. The draw costs four multiplications modulo `2^64 - 59` per new literal
// (nodes rebuilt over new children keep theirs, [`remake`]) and gives depth `O(log n)` in
// expectation plus the number of literals that share a point, for every input. Given up: the
// shape of a set follows the draw, so nothing printed or ordered reads it (`set::same` still
// does, as one draw serves the whole process). Still open: atoms of one digest tie, and a
// program can name many (plan row PERF-set-tied-digest-depth); a priority that tells them
// apart needs a random function of an atom's whole content, which no node keeps.
fn priority<A: Atom>(key: &Key<A>) -> u64 {
    PRIORITIES[usize::from(key.1)].of(key.0.digest())
}

/// Whether a node of literal `key` and priority `prio` stands above `n`.
fn above<A: Atom>(prio: u64, key: &Key<A>, n: &Set<A>) -> bool {
    (prio, key) > (n.prio, &n.key)
}

fn id<A: Atom>(t: Option<&Arc<Set<A>>>) -> u64 {
    t.map_or(0, |s| s.id)
}

/// The digest of a set, `t` its root: the sum of its literals' hashes ([`make`]), 0 when empty.
pub(super) fn digest<A: Atom>(t: Option<&Arc<Set<A>>>) -> u64 {
    t.map_or(0, |s| s.digest)
}

pub(super) fn name_digest<A: Atom>(t: Option<&Arc<Set<A>>>) -> u64 {
    t.map_or(0, |s| s.name_digest)
}

/// The digest of the set of `left`, the literal of an atom of digest `atom` taken as `taken`, and
/// `right`, from the digests of `left` and `right`: the sum of the hashes of the literals, so the
/// same for every shape of the set.
///
/// Complexity tradeoff: the digest this replaces mixed the literal with the children's digests,
/// also `O(1)` per node, but a function of the shape, which drawn priorities make a function of
/// the draw; digests order types, so the draw would reach what zedc prints. A sum is `O(1)` per
/// node from the children's sums and depends only on the literals. Given up: a sum of fixed
/// hashes has collisions a program could choose (two sets of equal sums); a collision costs only
/// a comparison of the two sets by their literals, as any collision of digests does.
///
/// Under the short-addresses build the sum is kept to its low 8 bits, as `mix` keeps every digest
/// (`address::short64`): the low 8 bits of a sum are the sum of the low 8 bits, so it is still
/// one function of the literals.
fn summed(atom: u64, taken: bool, left: u64, right: u64) -> u64 {
    crate::address::short64(
        mix(15, atom ^ u64::from(taken))
            .wrapping_add(left)
            .wrapping_add(right),
    )
}

/// The number of literals.
pub(super) fn len<A: Atom>(t: Option<&Arc<Set<A>>>) -> usize {
    t.map_or(0, |s| s.len)
}

/// The node of `key` over `left` and `right`, the one in the table if there is one.
fn make<A: Atom>(key: Key<A>, left: Tree<A>, right: Tree<A>) -> Arc<Set<A>> {
    make_at(priority(&key), key, left, right)
}

/// The node of `n`'s literal over `left` and `right`: its priority is `n`'s, not computed again.
fn remake<A: Atom>(n: &Set<A>, left: Tree<A>, right: Tree<A>) -> Arc<Set<A>> {
    make_at(n.prio, n.key.clone(), left, right)
}

/// [`make`] with the priority of `key`, `prio`, given.
fn make_at<A: Atom>(prio: u64, key: Key<A>, left: Tree<A>, right: Tree<A>) -> Arc<Set<A>> {
    let k = slot(&key, id(left.as_ref()), id(right.as_ref()));
    // No comparison or drop runs while the table is borrowed (module `bucket`); a bucket nearly
    // always holds one node at most.
    let bucket = |f: &mut dyn FnMut(&mut Bucket<Set<A>>)| A::sets(|t| f(t.entry(k).or_default()));
    let place = match bucket::find(bucket, |s| s.key.0.cmp(&key.0)) {
        Ok(s) => return s,
        Err(place) => place,
    };
    let s = Arc::new(Set {
        id: NEXT.fetch_add(1, Atomic::Relaxed),
        digest: summed(
            key.0.digest(),
            key.1,
            digest(left.as_ref()),
            digest(right.as_ref()),
        ),
        name_digest: summed(
            key.0.name_digest(),
            key.1,
            name_digest(left.as_ref()),
            name_digest(right.as_ref()),
        ),
        prio,
        slot: place.slot(),
        key,
        len: 1 + len(left.as_ref()) + len(right.as_ref()),
        left,
        right,
    });
    bucket(&mut |b| b.insert(&place, Arc::downgrade(&s)));
    s
}

/// The set of the one literal `key`.
pub(super) fn single<A: Atom>(key: Key<A>) -> Arc<Set<A>> {
    make(key, None, None)
}

/// Whether `atom` is in the set, and the literal's `taken` if so.
pub(super) fn get<A: Atom>(t: Option<&Arc<Set<A>>>, atom: &A) -> Option<bool> {
    let mut cur = t;
    while let Some(n) = cur {
        cur = match atom.cmp(&n.key.0) {
            std::cmp::Ordering::Less => n.left.as_ref(),
            std::cmp::Ordering::Greater => n.right.as_ref(),
            std::cmp::Ordering::Equal => return Some(n.key.1),
        };
    }
    None
}

/// The smallest literal.
pub(super) fn min<A: Atom>(t: &Arc<Set<A>>) -> &Key<A> {
    let mut n = t;
    while let Some(l) = &n.left {
        n = l;
    }
    &n.key
}

impl<A: Atom> Set<A> {
    /// The number of literals of the set under the node.
    pub(in crate::types) fn len(&self) -> usize {
        self.len
    }
}

/// The set split into its literals before `key` and those after; `key` is not in it.
fn split<A: Atom>(t: Option<&Arc<Set<A>>>, key: &Key<A>) -> (Tree<A>, Tree<A>) {
    let (mut lefts, mut rights) = (Vec::new(), Vec::new());
    let mut cur = t;
    while let Some(n) = cur {
        if n.key < *key {
            lefts.push(n);
            cur = n.right.as_ref();
        } else {
            rights.push(n);
            cur = n.left.as_ref();
        }
    }
    // A node whose side below is all on its side of `key` is kept as it is, with no lookup.
    let mut l: Tree<A> = None;
    for n in lefts.into_iter().rev() {
        l = Some(match id(l.as_ref()) == id(n.right.as_ref()) {
            true => n.clone(),
            false => remake(n, n.left.clone(), l),
        });
    }
    let mut r: Tree<A> = None;
    for n in rights.into_iter().rev() {
        r = Some(match id(r.as_ref()) == id(n.left.as_ref()) {
            true => n.clone(),
            false => remake(n, r, n.right.clone()),
        });
    }
    (l, r)
}

/// The set of `keys`, sorted with no atom twice, built bottom up: the shape is found first
/// over their indices, a Cartesian tree by priority made with one stack in `O(k)` (Vuillemin,
/// "A unifying look at data structures", CACM 23(4), 1980), and each node is then made once,
/// over children already made, in post-order. Priorities decide the shape, so it is the set
/// that adding the literals one at a time makes.
// Complexity tradeoff (PERF-equal-functions-forms-ratio): `k` nodes made, each looked up once in
// the table, `O(k)` after the sort; adding the literals one at a time makes `O(k log k)`, and
// joining sets of them in pairs ([`union_if_agree`]) remakes each merged set's nodes at each of
// `log k` levels, `O(k log k)` too.
pub(super) fn from_sorted<A: Atom>(keys: Vec<Key<A>>) -> Tree<A> {
    debug_assert!(
        keys.windows(2).all(|w| w[0].0 < w[1].0),
        "sorted, no atom twice"
    );
    const NONE: usize = usize::MAX;
    let n = keys.len();
    let prios: Vec<u64> = keys.iter().map(priority).collect();
    let (mut left, mut right) = (vec![NONE; n], vec![NONE; n]);
    // The right spine of the tree of the keys so far, root first: a key above the bottom of
    // the spine takes what it passes as its left subtree and hangs from what it stops at.
    let mut spine: Vec<usize> = Vec::new();
    for i in 0..n {
        let mut passed = NONE;
        while let Some(&top) = spine.last() {
            if (prios[top], &keys[top]) < (prios[i], &keys[i]) {
                passed = top;
                spine.pop();
            } else {
                break;
            }
        }
        left[i] = passed;
        if let Some(&top) = spine.last() {
            right[top] = i;
        }
        spine.push(i);
    }
    let root = *spine.first()?;
    let mut keys: Vec<Option<Key<A>>> = keys.into_iter().map(Some).collect();
    let mut made: Vec<Tree<A>> = vec![None; n];
    let mut todo = vec![(root, false)];
    while let Some((i, ready)) = todo.pop() {
        if ready {
            let l = (left[i] != NONE).then(|| made[left[i]].take()).flatten();
            let r = (right[i] != NONE).then(|| made[right[i]].take()).flatten();
            let key = keys[i].take().expect("each key made once");
            made[i] = Some(make_at(prios[i], key, l, r));
            continue;
        }
        todo.push((i, true));
        for c in [right[i], left[i]] {
            if c != NONE {
                todo.push((c, false));
            }
        }
    }
    made[root].take()
}

/// The set with the nodes of `path` rebuilt over `node`, the last of `path` its parent; each
/// entry says whether the child is the node's left.
fn rebuild<A: Atom>(path: Vec<(&Arc<Set<A>>, bool)>, mut node: Tree<A>) -> Tree<A> {
    for (n, left) in path.into_iter().rev() {
        node = Some(if left {
            remake(n, node, n.right.clone())
        } else {
            remake(n, n.left.clone(), node)
        });
    }
    node
}

/// The set with `key` added; its atom is not in the set.
pub(super) fn insert<A: Atom>(t: Option<&Arc<Set<A>>>, key: Key<A>) -> Arc<Set<A>> {
    let prio = priority(&key);
    let mut path = Vec::new();
    let mut cur = t;
    while let Some(n) = cur {
        if above(prio, &key, n) {
            break;
        }
        let left = key < n.key;
        path.push((n, left));
        cur = if left {
            n.left.as_ref()
        } else {
            n.right.as_ref()
        };
    }
    let (l, r) = split(cur, &key);
    rebuild(path, Some(make_at(prio, key, l, r))).expect("a set with a literal added has a root")
}

/// The set without `key`, which is in it.
pub(super) fn remove<A: Atom>(t: &Arc<Set<A>>, key: &Key<A>) -> Tree<A> {
    let mut path = Vec::new();
    let mut n = t;
    loop {
        let left = match key.cmp(&n.key) {
            std::cmp::Ordering::Equal => break,
            c => c.is_lt(),
        };
        path.push((n, left));
        n = (if left {
            n.left.as_ref()
        } else {
            n.right.as_ref()
        })
        .expect("the literal removed is in the set");
    }
    rebuild(path, join(n.left.as_ref(), n.right.as_ref()))
}

/// The set of the literals of `a` and of `b`, every literal of `a` before every one of `b`:
/// the two merged down one spine, the higher root of the two first.
fn join<A: Atom>(mut a: Option<&Arc<Set<A>>>, mut b: Option<&Arc<Set<A>>>) -> Tree<A> {
    let mut spine: Vec<(&Arc<Set<A>>, bool)> = Vec::new();
    let bottom = loop {
        match (a, b) {
            (None, x) | (x, None) => break x.cloned(),
            (Some(x), Some(y)) => {
                if above(x.prio, &x.key, y) {
                    spine.push((x, false));
                    a = x.right.as_ref();
                } else {
                    spine.push((y, true));
                    b = y.left.as_ref();
                }
            }
        }
    };
    rebuild(spine, bottom)
}

// Complexity tradeoff (COMPLEXITY.md K86 (1)): the naive version removes each literal that
// goes by `remove`, O(log m) each, O(r log m) for r of m literals; `split_classes` removes each
// literal once on each of its `log k` levels, so a product split into c cells cost
// O(c log² c). Used: one in-order walk, O(m) per block, nodes made only on the paths to the
// literals removed and on the joins, which makes the split O(c log c). Given up: a block
// that loses few literals still costs O(m) calls of `keep`, more than O(r log m) when r is
// below m / log m.
/// The set of the literals for which `keep`, called on each in order, is true. One walk, from
/// a stack: a subtree that loses no literal is kept as it is, a node that stays is made again
/// over its new children, and the children of one that goes are joined. So removing `r` of `m`
/// literals makes nodes only on the paths to them and on the joins, `O(m)` in all, where
/// removing them one at a time made `O(r log m)` (item SCALE-fix-kernel, COMPLEXITY.md K86).
pub(super) fn retain<A: Atom>(t: &Arc<Set<A>>, mut keep: impl FnMut(&Key<A>) -> bool) -> Tree<A> {
    /// What is left to do for a node: its left subtree, its own literal, or, with the
    /// answer of `keep`, the node over its two new subtrees.
    enum Stage {
        Left,
        Key,
        Make(bool),
    }
    let mut todo = vec![(t, Stage::Left)];
    let mut done: Vec<Tree<A>> = Vec::new();
    while let Some((n, stage)) = todo.pop() {
        match stage {
            Stage::Left => {
                todo.push((n, Stage::Key));
                match &n.left {
                    Some(l) => todo.push((l, Stage::Left)),
                    None => done.push(None),
                }
            }
            Stage::Key => {
                todo.push((n, Stage::Make(keep(&n.key))));
                match &n.right {
                    Some(r) => todo.push((r, Stage::Left)),
                    None => done.push(None),
                }
            }
            Stage::Make(kept) => {
                let r = done.pop().expect("the right subtree is walked");
                let l = done.pop().expect("the left subtree is walked");
                done.push(if !kept {
                    join(l.as_ref(), r.as_ref())
                } else if id(l.as_ref()) == id(n.left.as_ref())
                    && id(r.as_ref()) == id(n.right.as_ref())
                {
                    Some(n.clone())
                } else {
                    Some(remake(n, l, r))
                });
            }
        }
    }
    done.pop().expect("the set is walked")
}

/// The literals in order, from a stack.
pub(super) fn iter<A: Atom>(t: Option<&Arc<Set<A>>>) -> Iter<'_, A> {
    let mut it = Iter { stack: Vec::new() };
    it.descend(t);
    it
}

pub(super) struct Iter<'a, A: Atom> {
    stack: Vec<&'a Set<A>>,
}

impl<'a, A: Atom> Iter<'a, A> {
    fn descend(&mut self, mut t: Option<&'a Arc<Set<A>>>) {
        while let Some(n) = t {
            self.stack.push(n);
            t = n.left.as_ref();
        }
    }
}

impl<'a, A: Atom> Iterator for Iter<'a, A> {
    type Item = &'a Key<A>;
    fn next(&mut self) -> Option<&'a Key<A>> {
        let n = self.stack.pop()?;
        self.descend(n.right.as_ref());
        Some(&n.key)
    }
}

/// The union of two sets with no atom in common: the smaller's literals added to the larger.
pub(super) fn union<A: Atom>(x: &Arc<Set<A>>, y: &Arc<Set<A>>) -> Arc<Set<A>> {
    let (big, small) = if x.len >= y.len { (x, y) } else { (y, x) };
    let mut out = big.clone();
    for k in iter(Some(small)) {
        out = insert(Some(&out), k.clone());
    }
    out
}

/// The union of two sets, or `None` when one holds an atom with the other `taken` than the
/// other set: from the roots down, the higher root kept and the other set split at its atom,
/// past each pair of subtrees that is one node. A set has one shape in a run, so the union is the node
/// that adding the literals one at a time makes. For `k` literals into `n`, `O(k log(n/k + 1))`
/// nodes are visited in expectation, each splitting in `O(log n)`, and two sets that differ on
/// `d` paths cost only those paths; the walk keeps a stack of its own.
pub(super) fn union_if_agree<A: Atom>(x: &Arc<Set<A>>, y: &Arc<Set<A>>) -> Option<Arc<Set<A>>> {
    /// A pair of subtrees to join, or a literal to make over the two joined last.
    enum Step<A: Atom> {
        Join(Tree<A>, Tree<A>),
        Make(Arc<Set<A>>),
    }
    let mut todo = vec![Step::Join(Some(x.clone()), Some(y.clone()))];
    let mut done: Vec<Tree<A>> = Vec::new();
    while let Some(step) = todo.pop() {
        let (x, y) = match step {
            Step::Make(n) => {
                let r = done.pop().expect("the right side is joined");
                let l = done.pop().expect("the left side is joined");
                done.push(Some(remake(&n, l, r)));
                continue;
            }
            Step::Join(None, t) | Step::Join(t, None) => {
                done.push(t);
                continue;
            }
            Step::Join(Some(x), Some(y)) if x.id == y.id => {
                done.push(Some(x));
                continue;
            }
            Step::Join(Some(x), Some(y)) => (x, y),
        };
        let (hi, lo) = if above(x.prio, &x.key, &y) {
            (x, y)
        } else {
            (y, x)
        };
        let (atom, taken) = &hi.key;
        if *atom == lo.key.0 {
            // One atom at both roots: the children are joined side by side, with no split.
            if *taken != lo.key.1 {
                return None;
            }
            todo.push(Step::Make(hi.clone()));
            todo.push(Step::Join(hi.right.clone(), lo.right.clone()));
            todo.push(Step::Join(hi.left.clone(), lo.left.clone()));
            continue;
        }
        let lo = match get(Some(&lo), atom) {
            None => Some(lo),
            Some(t) if t == *taken => remove(&lo, &hi.key),
            Some(_) => return None,
        };
        let (l, r) = split(lo.as_ref(), &hi.key);
        todo.push(Step::Make(hi.clone()));
        todo.push(Step::Join(hi.right.clone(), r));
        todo.push(Step::Join(hi.left.clone(), l));
    }
    Some(
        done.pop()
            .flatten()
            .expect("the union of two sets has a root"),
    )
}

/// The literals of `x` whose atom is not in `y`, or `None` when an atom is in both, taken in
/// one and not in the other. Each node of `y` from the root down splits the part of `x` it
/// covers at its atom, after removing the literal on that atom, and the two sides are joined
/// past the node; two subtrees that are one node leave nothing. The walk keeps a stack of its
/// own. For `m <= n` literals the expected work is `O(m (1 + D))`, `D` the bound on a node's
/// expected depth in module `priority` for `N = n + m` keys (`O(log N)` when no two keys share
/// a point): there are at most `m` splits, one at each node of `y`; a split or a removal walks
/// one search path of a treap whose keys are a range of what is left of `x`, whose ancestors
/// are among those in the treap of all that is left, so `1 + D` in expectation; and a join walks
/// the facing spines of its two sides, two paths of the treap of at most `N` keys it makes.
/// Blelloch, Ferizovic and Sun ("Just join for parallel ordered sets", SPAA 2016) prove
/// `O(m log(n/m + 1))` for priorities drawn independently and identically; for the 5-wise
/// independent draw of module `priority` that is not proved, and it was measured with a
/// constant near 4 (cross-review of PERF-xor-shape-free, round 2; plan row
/// PROOF-join-work-limited-independence).
pub(super) fn difference_if_agree<A: Atom>(x: &Arc<Set<A>>, y: &Arc<Set<A>>) -> Option<Tree<A>> {
    /// A pair of subtrees whose difference is wanted, or the join of the last two differences.
    enum Step<A: Atom> {
        Minus(Tree<A>, Option<Arc<Set<A>>>),
        Join,
    }
    let mut todo = vec![Step::Minus(Some(x.clone()), Some(y.clone()))];
    let mut done: Vec<Tree<A>> = Vec::new();
    while let Some(step) = todo.pop() {
        let (x, y) = match step {
            Step::Join => {
                let r = done.pop().expect("the right side is made");
                let l = done.pop().expect("the left side is made");
                done.push(join(l.as_ref(), r.as_ref()));
                continue;
            }
            Step::Minus(None, _) => {
                done.push(None);
                continue;
            }
            Step::Minus(x, None) => {
                done.push(x);
                continue;
            }
            Step::Minus(Some(x), Some(y)) if x.id == y.id => {
                done.push(None);
                continue;
            }
            Step::Minus(Some(x), Some(y)) => (x, y),
        };
        let x = match get(Some(&x), &y.key.0) {
            None => Some(x),
            Some(t) if t == y.key.1 => remove(&x, &y.key),
            Some(_) => return None,
        };
        let (l, r) = split(x.as_ref(), &y.key);
        todo.push(Step::Join);
        todo.push(Step::Minus(r, y.right.clone()));
        todo.push(Step::Minus(l, y.left.clone()));
    }
    Some(done.pop().expect("the difference is made"))
}

/// The literals in exactly one of the two sets; an atom in both is taken alike in both (the
/// sets of exclusive ors, every atom taken). From the roots down, as [`union_if_agree`]: a
/// literal at both roots leaves, and the two sides are joined past it; otherwise the higher
/// root is kept and the other set split at its literal. Two subtrees that are one node leave
/// nothing. A set has one shape in a run, so the result is the node that adding or removing the
/// literals one at a time makes.
// Complexity tradeoff (PERF-xor-shape-free, COMPLEXITY.md K123): the naive method adds or
// removes each of the smaller set's `m` literals in the larger's `n`, `O(m log n)` expected, and
// makes `O(log n)` nodes for each literal, most of them dropped at the next. Used: the join-based
// set operation of Blelloch, Ferizovic and Sun ("Just join for parallel ordered sets", SPAA 2016),
// difference with the literals of `y` kept, and the nodes made are those of the result's changed
// paths. Proved for the draw of module `priority`: `O(m (1 + D))` expected work in all, its splits
// and joins included, `D` the bound on a node's expected depth there for `N = n + m` keys, so
// `O(m log N)` when no two keys share a point (each split, removal or join walks paths of treaps
// of at most `N` keys; cross-review of PERF-xor-shape-free, round 2, Opus §4). Blelloch,
// Ferizovic and Sun's `O(m log(n/m + 1))`, `O(n)` when `m` is near `n`, is proved for priorities
// drawn independently and identically, not for the 5-wise independent draw; measured with a
// constant near 4 under it (plan row PROOF-join-work-limited-independence). The proved bound is
// of the naive method's order, so the gain over it, in work and in nodes made, is measured, not
// proved (COMPLEXITY.md K123). For `m = 1` both make one path, and the one literal is
// added or removed directly, which the step stack would make about 17% dearer (parity, 4.55G
// against 3.89G instructions at 8,192 literals).
pub(super) fn symmetric<A: Atom>(x: &Tree<A>, y: &Tree<A>) -> Tree<A> {
    /// A pair of subtrees to take the symmetric difference of, a literal to make over the two
    /// made last, or the join of the two made last.
    enum Step<A: Atom> {
        Both(Tree<A>, Tree<A>),
        Make(Arc<Set<A>>),
        Join,
    }
    // One literal, as parity built a literal at a time takes: added or removed along one path,
    // with no stack of steps.
    for (one, other) in [(x, y), (y, x)] {
        if let (Some(k), Some(o)) = (one.as_ref().and_then(single_key), other) {
            return match get(Some(o), &k.0) {
                Some(taken) => {
                    debug_assert_eq!(taken, k.1, "an atom in both sets is taken alike");
                    remove(o, k)
                }
                None => Some(insert(Some(o), k.clone())),
            };
        }
    }
    let mut todo = vec![Step::Both(x.clone(), y.clone())];
    let mut done: Vec<Tree<A>> = Vec::new();
    while let Some(step) = todo.pop() {
        let (x, y) = match step {
            Step::Make(n) => {
                let r = done.pop().expect("the right side is made");
                let l = done.pop().expect("the left side is made");
                let kept =
                    id(l.as_ref()) == id(n.left.as_ref()) && id(r.as_ref()) == id(n.right.as_ref());
                done.push(Some(if kept { n } else { remake(&n, l, r) }));
                continue;
            }
            Step::Join => {
                let r = done.pop().expect("the right side is made");
                let l = done.pop().expect("the left side is made");
                done.push(join(l.as_ref(), r.as_ref()));
                continue;
            }
            Step::Both(None, t) | Step::Both(t, None) => {
                done.push(t);
                continue;
            }
            Step::Both(Some(x), Some(y)) if x.id == y.id => {
                done.push(None);
                continue;
            }
            Step::Both(Some(x), Some(y)) => (x, y),
        };
        let (hi, lo) = if above(x.prio, &x.key, &y) {
            (x, y)
        } else {
            (y, x)
        };
        if hi.key.0 == lo.key.0 {
            // One atom at both roots: it leaves, and the children are taken side by side.
            debug_assert_eq!(hi.key.1, lo.key.1, "an atom in both sets is taken alike");
            todo.push(Step::Join);
            todo.push(Step::Both(hi.right.clone(), lo.right.clone()));
            todo.push(Step::Both(hi.left.clone(), lo.left.clone()));
            continue;
        }
        // `hi`'s literal is not in `lo`: a literal's priority is a function of the literal, and
        // a set's root is its highest literal by (priority, literal), so had `lo` held it, `lo`'s
        // root would be at least as high as it, and so be it. So `lo` splits with nothing left
        // out, and `hi` stays over the two sides.
        debug_assert!(get(Some(&lo), &hi.key.0).is_none(), "taken alike");
        let (l, r) = split(Some(&lo), &hi.key);
        todo.push(Step::Make(hi.clone()));
        todo.push(Step::Both(hi.right.clone(), r));
        todo.push(Step::Both(hi.left.clone(), l));
    }
    done.pop().expect("the symmetric difference is made")
}

/// The one literal of a set of one.
pub(super) fn single_key<A: Atom>(t: &Arc<Set<A>>) -> Option<&Key<A>> {
    (t.len == 1).then_some(&t.key)
}

/// Whether two sets have the same literals. Equal sets made on one thread are one node, so
/// their ids agree; equal sets made on two threads are not (each thread has its table), so
/// trees of one digest are walked side by side, from a stack, past each pair of subtrees that
/// is one node. A set has one shape in a run, its priorities one draw for the process and
/// ties broken by the literals, so equal sets match node by node (item XOR-cross-thread); the
/// answer is a yes or no, the same for every draw.
// Complexity tradeoff: two equal sets made on two threads are compared in `O(k)` for their `k`
// literals at each comparison, rather than made one node by a table of the process, which
// would take a lock at each set node made on every thread; on one thread the ids decide.
pub(super) fn same<A: Atom>(x: &Arc<Set<A>>, y: &Arc<Set<A>>) -> bool {
    let mut stack = vec![(x, y)];
    while let Some((x, y)) = stack.pop() {
        if x.id == y.id {
            continue;
        }
        if x.digest != y.digest || x.len != y.len || x.key != y.key {
            return false;
        }
        for (a, b) in [(&x.left, &y.left), (&x.right, &y.right)] {
            match (a, b) {
                (Some(a), Some(b)) => stack.push((a, b)),
                (None, None) => {}
                _ => return false,
            }
        }
    }
    true
}

#[cfg(test)]
mod tests;
