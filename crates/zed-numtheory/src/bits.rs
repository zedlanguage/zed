//! The binary size of an unsigned machine integer, defined once for every crate. Moved from
//! zed-kernel's `machine_int` (DRY-num-words-2026-11-26), so that the crates below zed-kernel
//! and zed-numtheory itself can use it too.

/// The binary size of an unsigned machine integer (DRY-numeric-shared): before, 31 sites wrote
/// `BITS - leading_zeros()` (or the floor log, one less) by hand and three wrote
/// `ilog2() + !is_power_of_two()`, which panics at 0. For the floor log of a number above 0,
/// std's `ilog2` is the one routine. One copy stays written out, in `zed_graph::Lift::with_depth`:
/// zed-graph depends on no crate, and the one expression does not pay for a dependency.
pub trait BitLen: Copy {
    /// The number of binary digits: 0 for 0, and `floor(log2 x) + 1` otherwise.
    fn bit_len(self) -> u32;
    /// `ceil(log2 x)`, the least `k` with `2^k >= x`: 0 for 0 and 1, so it is total where
    /// `ilog2` panics at 0. It is `bit_len(x - 1)` for `x >= 1`, since `2^(k-1) < x <= 2^k`
    /// exactly when `2^(k-1) <= x - 1 < 2^k`.
    fn ceil_log2(self) -> u32;
}

// `#[inline]`: one or two instructions each, called from zed-kernel's and the compiler's loops
// through a dylib boundary (the reason given at `m61`).
macro_rules! bit_len {
    ($($t:ty),*) => {$(
        impl BitLen for $t {
            #[inline]
            fn bit_len(self) -> u32 {
                <$t>::BITS - self.leading_zeros()
            }
            #[inline]
            fn ceil_log2(self) -> u32 {
                if self <= 1 { 0 } else { (self - 1).bit_len() }
            }
        }
    )*};
}
bit_len!(u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;

    /// `bit_len` and `ceil_log2` against their definitions by doubling, at 0, 1, around each
    /// power of two and at `MAX`, in the narrowest and widest widths.
    #[test]
    fn bit_lengths_and_ceiling_logs_at_every_power_of_two() {
        let doubling = |x: u128| {
            (0..=128u32)
                .find(|&k| k == 128 || (1u128 << k) > x)
                .unwrap()
        };
        let ceiling = |x: u128| {
            (0..=128u32)
                .find(|&k| k == 128 || (1u128 << k) >= x)
                .unwrap()
        };
        let mut xs: Vec<u128> = vec![0, 1, 2, 3, 4, 5, u128::MAX - 1, u128::MAX];
        xs.extend((1..128).flat_map(|k| [(1u128 << k) - 1, 1u128 << k, (1u128 << k) + 1]));
        for &x in &xs {
            assert_eq!(x.bit_len(), doubling(x), "bit_len {x}");
            assert_eq!(x.ceil_log2(), ceiling(x), "ceil_log2 {x}");
            if let Ok(b) = u8::try_from(x) {
                assert_eq!(b.bit_len(), doubling(x), "bit_len {x}u8");
                assert_eq!(b.ceil_log2(), ceiling(x), "ceil_log2 {x}u8");
            }
        }
        assert_eq!(u8::MAX.bit_len(), 8);
        assert_eq!(u8::MAX.ceil_log2(), 8);
        assert_eq!(usize::MAX.ceil_log2(), usize::BITS);
    }
}
