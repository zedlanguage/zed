//! Values held while borrowed: each is put in through a shared reference and stays at its place
//! until the holder is dropped, so a walk may keep borrows into every value it has put in while
//! it puts in more. Users: the unfoldings of recursive types in zed-kernel (`Type::p_held`), and
//! the flat forms of signatures in zedc-types (`Sig::first_seen`).

use std::cell::{Cell, OnceCell};

/// The holder. Block `k` has room for `2^k` values.
// Complexity tradeoff: a put walks to the block with room, O(log n) for the `n`th; a block
// that knew the last block would refer into its own holder. The standard form, one growing
// `Vec`, puts in O(1) amortized but moves its items when it grows, which would end the
// borrows into them; a pointer to the last block would put in O(1) but make the holder
// refer into itself. Dropping drops O(log n) nested blocks, so it recurses O(log n) deep.
pub struct Held<T> {
    used: Cell<usize>,
    first: Block<T>,
}

struct Block<T> {
    slots: Box<[OnceCell<T>]>,
    next: OnceCell<Box<Block<T>>>,
}

impl<T> Block<T> {
    fn new(room: usize) -> Block<T> {
        Block {
            slots: (0..room).map(|_| OnceCell::new()).collect(),
            next: OnceCell::new(),
        }
    }
}

impl<T> Default for Held<T> {
    fn default() -> Held<T> {
        Held {
            used: Cell::new(0),
            first: Block::new(1),
        }
    }
}

impl<T> Held<T> {
    /// Holds `t` until the holder is dropped.
    pub fn put(&self, t: T) -> &T {
        let n = self.used.get() + 1;
        self.used.set(n);
        // The `n`th value goes to block `log2 n`, at `n - 2^k`.
        // Proof that the slot exists and is empty, so the `expect` below cannot fire (and
        // `set`, whose error is dropped, does not fail and leave an older value in the slot):
        // with `k = floor(log2 n)`, `2^k <= n < 2^(k + 1)`, so `0 <= n - 2^k < 2^k`, inside
        // block `k`, which has `2^k` slots (`Block::new(1 << i)` for block `i`, 1 for the
        // first). The map from `n >= 1` to `(k, n - 2^k)` is one to one, and each call takes a
        // new `n`, since `used` only rises and is read and written with no call in between:
        // `Held` holds a `Cell`, so it is not `Sync`, and nothing between the read and the
        // write runs code of the caller. So no earlier call wrote this slot. Test:
        // `tests::values_keep_their_addresses_across_block_ends_and_drop_once` (every block end
        // up to 2^12 + 1); it cannot check counts near `usize::MAX`, where `used + 1` would
        // overflow, which needs more values than memory holds.
        let k = n.ilog2();
        let mut block = &self.first;
        for i in 1..=k {
            block = block.next.get_or_init(|| Box::new(Block::new(1 << i)));
        }
        let slot = &block.slots[n - (1 << k)];
        let _ = slot.set(t);
        slot.get().expect("the slot was empty and is set")
    }
}

#[cfg(test)]
mod tests {
    use super::Held;

    #[test]
    fn values_put_in_stay_at_their_places_while_more_are_put_in() {
        let held = Held::default();
        let firsts: Vec<&String> = (0..100).map(|i| held.put(i.to_string())).collect();
        for (i, s) in firsts.iter().enumerate() {
            assert_eq!(**s, i.to_string());
        }
        assert_eq!(*held.put("last".to_string()), "last");
        assert_eq!(*firsts[0], "0");
    }

    /// Counts at and around each block's end, up to 2^12 + 1 (TEST-dry-shared-units): each
    /// value stays at the address it was put at while the later blocks are made, the `n`th
    /// value lands in block `log2 n`, and dropping the holder drops each value once. No
    /// negative control: a `Vec` that grows may or may not move its items (realloc can grow a
    /// block in place), so no faulty holder fails this check on every run.
    #[test]
    fn values_keep_their_addresses_across_block_ends_and_drop_once() {
        use std::rc::Rc;
        for count in [1usize, 2, 3, 4, 7, 8, 9, 4095, 4096, 4097] {
            let token = Rc::new(());
            let held = Held::default();
            let mut at: Vec<*const (usize, Rc<()>)> = Vec::new();
            for i in 0..count {
                let r = held.put((i, token.clone()));
                assert_eq!(r.0, i);
                at.push(r);
            }
            assert_eq!(held.used.get(), count);
            // Walk the blocks: block k holds 2^k slots, all full but the last.
            let (mut block, mut k, mut seen) = (Some(&held.first), 0, 0);
            while let Some(b) = block {
                assert_eq!(b.slots.len(), 1 << k, "count {count}: block {k}");
                for slot in b.slots.iter() {
                    if let Some(v) = slot.get() {
                        assert_eq!(std::ptr::from_ref(v), at[v.0], "count {count}: {}", v.0);
                        assert_eq!(v.0, seen, "count {count}: in order");
                        seen += 1;
                    }
                }
                (block, k) = (b.next.get().map(|n| &**n), k + 1);
            }
            assert_eq!(seen, count);
            assert_eq!(k, count.ilog2() + 1, "count {count}: blocks made");
            assert_eq!(Rc::strong_count(&token), count + 1);
            drop(held);
            assert_eq!(
                Rc::strong_count(&token),
                1,
                "count {count}: each dropped once"
            );
        }
    }
}
