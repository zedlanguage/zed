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
}
