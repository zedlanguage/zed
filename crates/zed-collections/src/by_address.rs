//! A map key that is the address of an `Arc` and holds that `Arc` (DRY-pointer-memos-keep-alive,
//! 2026-11-20): [`ByAddress`].
//!
//! A memo keyed by a bare address (`*const T`) is wrong when the value at a key is freed while
//! the memo lives: a new value made at the same address reads the old one's entry. A key that
//! holds the `Arc` keeps its value alive, so no address in the memo is freed and given to
//! another value while the memo lives. Lookups take the bare address ([`Borrow`]), so a lookup
//! costs no `Arc` clone; an insert costs one, O(1). Test:
//! `tests::a_value_made_after_one_dropped_never_reads_the_dropped_ones_entry`.
//!
//! Used by the forward memo of zedc-check `finish` (`fwd_memo`), whose keys were callees of
//! signatures made for one call and dropped after it, and by the signatures met in zedc-check
//! `read.rs` (`Seen::sigs`), which held each key's `Arc` by hand.

use std::borrow::Borrow;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// The address of an `Arc`, as a key, with the `Arc` held so the address names its value for
/// as long as the key lives. Equal and hashed by address only.
pub struct ByAddress<T> {
    at: *const T,
    held: Arc<T>,
}

impl<T> ByAddress<T> {
    /// The key of `a`, holding a clone of it.
    pub fn new(a: &Arc<T>) -> Self {
        ByAddress {
            at: Arc::as_ptr(a),
            held: a.clone(),
        }
    }

    /// The `Arc` held.
    pub fn get(&self) -> &Arc<T> {
        &self.held
    }
}

impl<T> PartialEq for ByAddress<T> {
    fn eq(&self, other: &Self) -> bool {
        self.at == other.at
    }
}

impl<T> Eq for ByAddress<T> {}

impl<T> Hash for ByAddress<T> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        // The same hash as the bare address, as `Borrow` requires.
        self.at.hash(h);
    }
}

impl<T> Borrow<*const T> for ByAddress<T> {
    fn borrow(&self) -> &*const T {
        &self.at
    }
}

#[cfg(test)]
mod tests {
    use super::ByAddress;
    use std::collections::HashMap;
    use std::sync::Arc;

    /// The key holds the first value, so a value made after the caller drops its own `Arc`
    /// cannot take that address. A bare-address memo, the negative control, is shown to reuse
    /// it: with the key not held, the allocator gives the freed block to the next value of the
    /// same size (checked here, not assumed; where it does not, that part says so and passes).
    #[test]
    fn a_value_made_after_one_dropped_never_reads_the_dropped_ones_entry() {
        let mut memo: HashMap<ByAddress<[u64; 4]>, &str> = HashMap::new();
        let first = Arc::new([1u64; 4]);
        memo.insert(ByAddress::new(&first), "first");
        let first_at = Arc::as_ptr(&first);
        drop(first);
        let second = Arc::new([2u64; 4]);
        assert_ne!(
            Arc::as_ptr(&second),
            first_at,
            "the key holds the first value"
        );
        assert_eq!(memo.get(&Arc::as_ptr(&second)), None);
        assert_eq!(memo.get(&first_at), Some(&"first"));
        let (key, _) = memo.iter().next().expect("one entry");
        assert_eq!(**key.get(), [1u64; 4]);

        // The negative control: a bare address, the value not held.
        let mut bare: HashMap<*const [u64; 4], &str> = HashMap::new();
        let third = Arc::new([3u64; 4]);
        bare.insert(Arc::as_ptr(&third), "third");
        let third_at = Arc::as_ptr(&third);
        drop(third);
        let fourth = Arc::new([4u64; 4]);
        if Arc::as_ptr(&fourth) == third_at {
            assert_eq!(
                bare.get(&Arc::as_ptr(&fourth)),
                Some(&"third"),
                "a stale hit"
            );
        }
    }

    #[test]
    fn keys_are_equal_by_address_not_by_value() {
        let (a, b) = (Arc::new(5u32), Arc::new(5u32));
        assert!(ByAddress::new(&a) == ByAddress::new(&a.clone()));
        assert!(ByAddress::new(&a) != ByAddress::new(&b));
    }
}
