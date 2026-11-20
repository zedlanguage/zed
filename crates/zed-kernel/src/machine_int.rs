//! Arithmetic on machine integers that needs nothing else of the crate: the binary size of an
//! unsigned integer, and the midpoints of two `i128` values with no overflow.
//!
//! This module imports nothing from the crate, so every module may import it without closing an
//! import cycle (FAIL-kernel-import-cycle-bits, 2026-11-19). These items were in `bits`, which
//! imports `num` and `value`; when `num` and `value` imported them from there, the cycles
//! bits -> num -> bits and bits -> value -> bits joined 19 files (test
//! `s_01f_import_graph::no_crate_has_an_import_cycle_but_the_known_ones`). `bits` re-exports
//! them, so the path `zed_kernel::bits::BitLen` that other crates use still works.

/// The binary size of an unsigned machine integer, defined once for every crate
/// (DRY-numeric-shared): before, 31 sites wrote `BITS - leading_zeros()` (or the floor log,
/// one less) by hand and three wrote `ilog2() + !is_power_of_two()`, which panics at 0. One
/// copy stays written out, in `zed_graph::Lift::with_depth`: zed-graph sits below zed-kernel
/// and cannot call this.
pub trait BitLen: Copy {
    /// The number of binary digits: 0 for 0, and `floor(log2 x) + 1` otherwise.
    fn bit_len(self) -> u32;
    /// `ceil(log2 x)`, the least `k` with `2^k >= x`: 0 for 0 and 1, so it is total where
    /// `ilog2` panics at 0. It is `bit_len(x - 1)` for `x >= 1`, since `2^(k-1) < x <= 2^k`
    /// exactly when `2^(k-1) <= x - 1 < 2^k`.
    fn ceil_log2(self) -> u32;
}

macro_rules! bit_len {
    ($($t:ty),*) => {$(
        impl BitLen for $t {
            fn bit_len(self) -> u32 {
                <$t>::BITS - self.leading_zeros()
            }
            fn ceil_log2(self) -> u32 {
                if self <= 1 { 0 } else { (self - 1).bit_len() }
            }
        }
    )*};
}
bit_len!(u8, u16, u32, u64, u128, usize);

/// `floor((a + b) / 2)`, for every pair with no overflow: the halves of `a` and `b` (each
/// shifted down, which floors), plus 1 when both dropped a 1 bit. A bisection over signed
/// values needs it, as `while lo < hi`, `mid` in `[lo, hi)`: std's signed `midpoint` rounds
/// toward zero, so it gives `-2` for `(-3, -2)`, the end `hi`, and such a search no longer
/// shrinks; `lo + (hi - lo) / 2` floors as this does but overflows when `hi - lo` passes
/// `i128::MAX`. For unsigned values std's `midpoint` floors, and is used.
pub fn floor_midpoint(a: i128, b: i128) -> i128 {
    (a >> 1) + (b >> 1) + (a & b & 1)
}

/// `ceil((a + b) / 2)`, for every pair with no overflow: [`floor_midpoint`] plus 1 when
/// `a + b` is odd, which is when the low bits differ. The floor is then below the greater
/// of the two, so the 1 fits. For a bisection that keeps `mid` in `(lo, hi]`, in place of
/// `hi - (hi - lo) / 2`, which overflows as `lo + (hi - lo) / 2` does.
pub fn ceil_midpoint(a: i128, b: i128) -> i128 {
    floor_midpoint(a, b) + ((a ^ b) & 1)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

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

    /// The floor of the mean against the exact sum in `BigInt`, at the ends of `i128` and
    /// around zero; and the case std's signed `midpoint` gets wrong for a bisection.
    #[test]
    fn the_floor_midpoint_is_exact_at_every_end() {
        let xs = [
            i128::MIN,
            i128::MIN + 1,
            -3,
            -2,
            -1,
            0,
            1,
            2,
            3,
            i128::MAX - 1,
            i128::MAX,
        ];
        for &a in &xs {
            for &b in &xs {
                let want =
                    num_integer::Integer::div_floor(&(BigInt::from(a) + b), &BigInt::from(2));
                assert_eq!(
                    BigInt::from(floor_midpoint(a, b)),
                    want,
                    "floor_midpoint({a}, {b})"
                );
                let up = num_integer::Integer::div_ceil(&(BigInt::from(a) + b), &BigInt::from(2));
                assert_eq!(
                    BigInt::from(ceil_midpoint(a, b)),
                    up,
                    "ceil_midpoint({a}, {b})"
                );
            }
        }
        assert_eq!(floor_midpoint(-3, -2), -3);
        assert_eq!((-3i128).midpoint(-2), -2, "std rounds toward zero");
    }
}
