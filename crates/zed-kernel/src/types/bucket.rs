//! A bucket of a thread's table of live nodes (rows and morphism types in `Shared`, set nodes in
//! `bdd::set`): the nodes whose hashes tie, held weakly in a treap ordered by their contents
//! (step TABLE-short-scan).
//!
//! A lookup compares its key with the `O(log b)` nodes on one path of the bucket's `b` nodes, in
//! expectation, and a dropped node leaves by the slot it was given, in `O(log b)` rotations and
//! no comparison. A bucket nearly always holds one node at most; it held a list that every
//! lookup read whole, which with 8-bit hashes put a chain of `n` nested tuples at `O(n³)`.
//!
//! No comparison runs while the table is borrowed, since a comparison reads types through their
//! nodes and a drop on the way takes a node out of the table: [`find`] takes each node out of
//! the bucket alone, compares it outside, and starts again from the root when the bucket
//! changed in between. A node dropped on another thread cannot reach this thread's table and
//! leaves an entry that no longer upgrades, so it cannot be compared; a lookup that meets one
//! takes it out, without comparing, and starts again. Each change to a bucket restarts a lookup
//! at most once, so the restarts cost `O(log b)` for each node taken out.

// Complexity tradeoff (COMPLEXITY.md K83): the naive bucket is a list read whole at each lookup
// and scanned for its entry at each drop, O(b) comparisons per lookup and O(b) per drop, each
// comparison as deep as the levels on which the hashes tie. Used: a treap ordered by contents,
// O(log b) comparisons per lookup and O(log b) rotations and no comparison per drop, in
// expectation; a bucket of one node keeps no slots. Given up: the bound holds only in
// expectation; slots, priorities and parent links cost memory once a second node is put in; a
// lookup restarts from the root after each change to the bucket during a comparison. Each
// comparison still reads the levels on which the hashes tie, so the `short-addresses` chain of
// n nested tuples stays about O(n² log n), which only a comparison not by contents would avoid.

use std::cmp::Ordering;
use std::sync::{Arc, Weak};

/// No node: an empty child, the parent of the root, the end of the free slots.
const NIL: u32 = u32::MAX;

/// A slot of a bucket: a node, or a free slot, whose `item` never upgrades and whose
/// `child[0]` is the next free slot.
struct Node<T> {
    item: Weak<T>,
    /// The node's priority: the treap keeps each node's above its children's.
    prio: u64,
    parent: u32,
    /// The children: `child[0]` before the node, `child[1]` after it.
    child: [u32; 2],
}

/// The nodes of one hash: none or one, without slots, as nearly every bucket in the build with
/// full hashes; or a treap of slots, once a second node is put in.
pub(in crate::types) struct Bucket<T>(Repr<T>);

enum Repr<T> {
    /// The node of slot 0, or none (an `item` that never upgrades, as made by `Weak::new`)
    /// before one is put in.
    One {
        item: Weak<T>,
        version: u32,
    },
    Tree(Box<Tree<T>>),
}

impl<T> Default for Bucket<T> {
    fn default() -> Bucket<T> {
        Bucket(Repr::One {
            item: Weak::new(),
            version: 0,
        })
    }
}

/// The nodes of a bucket, in slots, a treap over them ordered by contents.
struct Tree<T> {
    nodes: Vec<Node<T>>,
    root: u32,
    /// The first free slot.
    free: u32,
    len: usize,
    /// The number of changes so far: a lookup that finds it changed starts again, and it seeds
    /// each new node's priority.
    version: u32,
}

/// Where a lookup that found no equal node ended: the slot the new node takes, and its parent.
/// It is valid until the bucket next changes.
pub(in crate::types) struct Place {
    version: u32,
    parent: u32,
    side: usize,
    slot: u32,
}

impl Place {
    /// The slot the new node takes, for its [`Bucket::leave`] when dropped.
    pub(in crate::types) fn slot(&self) -> u32 {
        self.slot
    }
}

/// Where a lookup stands: the node it compared last, at `version` of the bucket.
struct Cursor {
    version: Option<u32>,
    node: u32,
}

/// One step of a lookup: the next node to compare, or where the path ended.
enum Step<T> {
    Visit(Arc<T>),
    End(Place),
}

/// The live node of the bucket that `cmp` finds equal, or the place for a new node.
///
/// `cmp(node)` orders a node against the key sought. `bucket(f)` runs `f` on the bucket while
/// the table is borrowed; it is called once for each node compared, and every comparison runs
/// after it returns.
pub(in crate::types) fn find<T>(
    bucket: impl Fn(&mut dyn FnMut(&mut Bucket<T>)),
    mut cmp: impl FnMut(&T) -> Ordering,
) -> Result<Arc<T>, Place> {
    let mut c = Cursor {
        version: None,
        node: NIL,
    };
    let mut went = Ordering::Equal;
    loop {
        let mut step = None;
        bucket(&mut |b| step = Some(b.step(&mut c, went)));
        match step.expect("`bucket` runs its function once") {
            Step::Visit(item) => match cmp(&item) {
                Ordering::Equal => return Ok(item),
                o => went = o,
            },
            Step::End(place) => return Err(place),
        }
    }
}

impl<T> Bucket<T> {
    /// The number of entries, those of nodes dropped on another thread included.
    #[cfg(test)]
    pub(in crate::types) fn len(&self) -> usize {
        match &self.0 {
            Repr::One { item, .. } => usize::from(!item.ptr_eq(&Weak::new())),
            Repr::Tree(t) => t.len,
        }
    }

    pub(in crate::types) fn is_empty(&self) -> bool {
        match &self.0 {
            Repr::One { item, .. } => item.ptr_eq(&Weak::new()),
            Repr::Tree(t) => t.len == 0,
        }
    }

    /// The next node of a lookup at `c`, whose last node compared `went` against the key. A
    /// node that no longer upgrades alone in a bucket is overwritten by the insertion.
    fn step(&mut self, c: &mut Cursor, went: Ordering) -> Step<T> {
        let (item, version) = match &mut self.0 {
            Repr::Tree(t) => return t.step(c, went),
            Repr::One { item, version } => (item, *version),
        };
        if c.version == Some(version) {
            // The node was compared and differs: the new one goes beside it.
            return Step::End(Place {
                version,
                parent: 0,
                side: usize::from(went == Ordering::Less),
                slot: 1,
            });
        }
        c.version = Some(version);
        c.node = 0;
        match item.upgrade() {
            Some(item) => Step::Visit(item),
            None => Step::End(Place {
                version,
                parent: NIL,
                side: 0,
                slot: 0,
            }),
        }
    }

    /// Puts `item` at `place`, which a lookup returned since the bucket last changed.
    pub(in crate::types) fn insert(&mut self, place: &Place, new: Weak<T>) {
        match &mut self.0 {
            Repr::Tree(t) => t.insert(place, new),
            Repr::One { item, version } => {
                assert_eq!(
                    place.version, *version,
                    "nothing changes the bucket between a lookup and its insertion"
                );
                if place.parent == NIL {
                    *item = new;
                    *version = version.wrapping_add(1);
                } else {
                    let mut t = Tree {
                        nodes: vec![Node {
                            item: std::mem::take(item),
                            prio: priority(version.wrapping_sub(1)),
                            parent: NIL,
                            child: [NIL; 2],
                        }],
                        root: 0,
                        free: NIL,
                        len: 1,
                        version: *version,
                    };
                    t.insert(place, new);
                    self.0 = Repr::Tree(Box::new(t));
                }
            }
        }
    }

    /// Takes out the entry of the node at `me`, given slot `slot` when made; nothing when the
    /// slot holds another node, as when the node was made on another thread or its entry was
    /// taken out after it stopped upgrading.
    pub(in crate::types) fn leave(&mut self, slot: u32, me: *const T) {
        match &mut self.0 {
            Repr::Tree(t) => t.leave(slot, me),
            Repr::One { item, version } => {
                if slot == 0 && std::ptr::eq(item.as_ptr(), me) {
                    *item = Weak::new();
                    *version = version.wrapping_add(1);
                }
            }
        }
    }
}

impl<T> Tree<T> {
    /// The next node of a lookup at `c`, whose last node compared `went` against the key; from
    /// the root when the bucket changed since. Entries that no longer upgrade are taken out on
    /// the way.
    fn step(&mut self, c: &mut Cursor, went: Ordering) -> Step<T> {
        let (mut parent, mut side) = (NIL, 0);
        let mut at = self.root;
        if c.version == Some(self.version) {
            parent = c.node;
            side = usize::from(went == Ordering::Less);
            at = self.nodes[parent as usize].child[side];
        }
        loop {
            c.version = Some(self.version);
            if at == NIL {
                let slot = match self.free {
                    NIL => {
                        u32::try_from(self.nodes.len()).expect("a bucket has fewer than 2³² slots")
                    }
                    f => f,
                };
                return Step::End(Place {
                    version: self.version,
                    parent,
                    side,
                    slot,
                });
            }
            if let Some(item) = self.nodes[at as usize].item.upgrade() {
                c.node = at;
                return Step::Visit(item);
            }
            self.remove(at);
            (parent, side, at) = (NIL, 0, self.root);
        }
    }

    /// Puts `item` at `place`.
    fn insert(&mut self, place: &Place, item: Weak<T>) {
        assert_eq!(
            place.version, self.version,
            "nothing changes the bucket between a lookup and its insertion"
        );
        let at = place.slot;
        let node = Node {
            item,
            prio: priority(self.version),
            parent: place.parent,
            child: [NIL; 2],
        };
        if at as usize == self.nodes.len() {
            self.nodes.push(node);
        } else {
            self.free = self.nodes[at as usize].child[0];
            self.nodes[at as usize] = node;
        }
        match place.parent {
            NIL => self.root = at,
            p => self.nodes[p as usize].child[place.side] = at,
        }
        loop {
            let p = self.nodes[at as usize].parent;
            if p == NIL || self.nodes[p as usize].prio >= self.nodes[at as usize].prio {
                break;
            }
            self.rotate_up(at);
        }
        self.len += 1;
        self.version = self.version.wrapping_add(1);
    }

    /// [`Bucket::leave`] in the treap.
    fn leave(&mut self, slot: u32, me: *const T) {
        if self
            .nodes
            .get(slot as usize)
            .is_some_and(|n| std::ptr::eq(n.item.as_ptr(), me))
        {
            self.remove(slot);
        }
    }

    /// Takes the node at `at` out: it is turned down below its children until it has one at
    /// most, then unlinked, and its slot freed.
    fn remove(&mut self, at: u32) {
        loop {
            let [l, r] = self.nodes[at as usize].child;
            match (l, r) {
                (NIL, only) | (only, NIL) => {
                    self.relink(at, only);
                    break;
                }
                _ if self.nodes[l as usize].prio > self.nodes[r as usize].prio => self.rotate_up(l),
                _ => self.rotate_up(r),
            }
        }
        self.nodes[at as usize] = Node {
            item: Weak::new(),
            prio: 0,
            parent: NIL,
            child: [self.free, NIL],
        };
        self.free = at;
        self.len -= 1;
        self.version = self.version.wrapping_add(1);
    }

    /// Puts `new` (or nothing) where `old` hangs from its parent.
    fn relink(&mut self, old: u32, new: u32) {
        let p = self.nodes[old as usize].parent;
        if new != NIL {
            self.nodes[new as usize].parent = p;
        }
        match p {
            NIL => self.root = new,
            p => {
                let side = usize::from(self.nodes[p as usize].child[1] == old);
                self.nodes[p as usize].child[side] = new;
            }
        }
    }

    /// Turns the node at `x` above its parent, keeping the order.
    fn rotate_up(&mut self, x: u32) {
        let p = self.nodes[x as usize].parent;
        let side = usize::from(self.nodes[p as usize].child[1] == x);
        let inner = self.nodes[x as usize].child[1 - side];
        self.relink(p, x);
        self.nodes[p as usize].child[side] = inner;
        if inner != NIL {
            self.nodes[inner as usize].parent = p;
        }
        self.nodes[x as usize].child[1 - side] = p;
        self.nodes[p as usize].parent = x;
    }
}

/// A priority from the bucket's count of changes: splitmix64, untruncated in the build with
/// short hashes, so that priorities do not follow the nodes' order and the treap's depth is
/// `O(log b)` in expectation.
fn priority(seed: u32) -> u64 {
    let mut z = u64::from(seed).wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    /// The node of `k` in `b`, made and put in when there is none.
    fn get(b: &RefCell<Bucket<u64>>, k: u64) -> Arc<u64> {
        let bucket = |f: &mut dyn FnMut(&mut Bucket<u64>)| f(&mut b.borrow_mut());
        match find(bucket, |x| x.cmp(&k)) {
            Ok(x) => x,
            Err(place) => {
                let x = Arc::new(k);
                bucket(&mut |b| b.insert(&place, Arc::downgrade(&x)));
                x
            }
        }
    }

    fn tree(b: &Bucket<u64>) -> &Tree<u64> {
        match &b.0 {
            Repr::Tree(t) => t,
            Repr::One { .. } => panic!("a bucket of two nodes or more is a treap"),
        }
    }

    /// Checks the treap: parent links, order of the live nodes, priorities, and the count of
    /// entries; returns the live keys in order.
    fn check(b: &Tree<u64>) -> Vec<u64> {
        let (mut keys, mut seen) = (Vec::new(), 0);
        let mut stack = vec![(b.root, NIL)];
        let mut order = Vec::new();
        while let Some((at, parent)) = stack.pop() {
            if at == NIL {
                continue;
            }
            let n = &b.nodes[at as usize];
            assert_eq!(n.parent, parent);
            for c in n.child {
                assert!(c == NIL || b.nodes[c as usize].prio <= n.prio);
            }
            seen += 1;
            order.push(at);
            stack.push((n.child[0], at));
            stack.push((n.child[1], at));
        }
        assert_eq!(seen, b.len);
        // In order, by an explicit walk.
        let (mut stack, mut at) = (Vec::new(), b.root);
        while at != NIL || !stack.is_empty() {
            while at != NIL {
                stack.push(at);
                at = b.nodes[at as usize].child[0];
            }
            let top = stack
                .pop()
                .expect("the loop runs while the stack or `at` holds a node");
            keys.extend(b.nodes[top as usize].item.upgrade().map(|x| *x));
            at = b.nodes[top as usize].child[1];
        }
        assert!(keys.windows(2).all(|w| w[0] < w[1]), "{keys:?}");
        keys
    }

    #[test]
    fn nodes_are_found_kept_in_order_and_leave_by_their_slots() {
        let b = RefCell::new(Bucket::default());
        // Keys in a scrambled order.
        let keys: Vec<u64> = (0..500u64).map(|i| i * 7919 % 500).collect();
        let nodes: Vec<Arc<u64>> = keys.iter().map(|&k| get(&b, k)).collect();
        assert_eq!(check(tree(&b.borrow())), (0..500).collect::<Vec<_>>());
        for (&k, x) in keys.iter().zip(&nodes) {
            assert!(Arc::ptr_eq(&get(&b, k), x));
        }
        // Dropped nodes leave by their slots, as `Shared` and set nodes do in `Drop`.
        let slots: Vec<u32> = keys
            .iter()
            .map(|&k| {
                let bucket = |f: &mut dyn FnMut(&mut Bucket<u64>)| f(&mut b.borrow_mut());
                let mut slot = None;
                bucket(&mut |b| {
                    let t = tree(b);
                    slot = (0..t.nodes.len())
                        .find(|&s| t.nodes[s].item.upgrade().is_some_and(|x| *x == k))
                });
                u32::try_from(slot.expect("every key has a node")).expect("few slots")
            })
            .collect();
        let mut kept = Vec::new();
        for ((k, x), slot) in keys.iter().zip(nodes).zip(slots) {
            if k % 3 == 0 {
                b.borrow_mut().leave(slot, Arc::as_ptr(&x));
                // Leaving twice, or by a slot another node took, does nothing.
                b.borrow_mut().leave(slot, Arc::as_ptr(&x));
            } else {
                kept.push(x);
            }
        }
        let live: Vec<u64> = (0..500).filter(|k| k % 3 != 0).collect();
        assert_eq!(check(tree(&b.borrow())), live);
        assert_eq!(b.borrow().len(), live.len());
        // Freed slots are taken again.
        let again: Vec<Arc<u64>> = (0..500)
            .filter(|k| k % 3 == 0)
            .map(|k| get(&b, k))
            .collect();
        assert_eq!(tree(&b.borrow()).nodes.len(), 500);
        assert_eq!(check(tree(&b.borrow())), (0..500).collect::<Vec<_>>());
        drop((kept, again));
    }

    #[test]
    fn entries_that_no_longer_upgrade_are_taken_out_by_the_lookups_that_meet_them() {
        // Nodes dropped without leaving, as those dropped on another thread are: their entries
        // cannot be compared, and each lookup that meets one takes it out and starts again.
        let b = RefCell::new(Bucket::default());
        let nodes: Vec<Arc<u64>> = (0..400u64).map(|i| get(&b, i * 31 % 400)).collect();
        let (kept, gone): (Vec<_>, Vec<_>) = nodes.into_iter().partition(|x| **x % 2 == 0);
        drop(gone);
        assert_eq!(b.borrow().len(), 400);
        for x in &kept {
            assert!(Arc::ptr_eq(&get(&b, **x), x));
        }
        let even: Vec<u64> = (0..400).filter(|k| k % 2 == 0).collect();
        assert_eq!(check(tree(&b.borrow())), even);
        let odd: Vec<Arc<u64>> = (0..400)
            .filter(|k| k % 2 == 1)
            .map(|k| get(&b, k))
            .collect();
        assert_eq!(check(tree(&b.borrow())), (0..400).collect::<Vec<_>>());
        assert_eq!(b.borrow().len(), 400);
        drop((kept, odd));
    }

    #[test]
    fn a_bucket_of_one_node_is_found_left_and_written_over_when_dead() {
        let b = RefCell::new(Bucket::default());
        assert!(b.borrow().is_empty());
        let x = get(&b, 5);
        assert!(Arc::ptr_eq(&get(&b, 5), &x));
        assert!(matches!(b.borrow().0, Repr::One { .. }));
        b.borrow_mut().leave(1, Arc::as_ptr(&x));
        assert_eq!(b.borrow().len(), 1);
        b.borrow_mut().leave(0, Arc::as_ptr(&x));
        assert!(b.borrow().is_empty());
        // A node dropped without leaving is written over by the next one.
        let y = get(&b, 6);
        drop(y);
        assert_eq!(b.borrow().len(), 1);
        let z = get(&b, 7);
        assert!(matches!(b.borrow().0, Repr::One { .. }));
        assert_eq!(b.borrow().len(), 1);
        // A second node makes a treap that keeps the first in slot 0.
        let w = get(&b, 3);
        assert_eq!(check(tree(&b.borrow())), vec![3, 7]);
        b.borrow_mut().leave(0, Arc::as_ptr(&z));
        assert_eq!(check(tree(&b.borrow())), vec![3]);
        drop((x, w));
    }
}
