//! Binary search for the border of a monotone predicate over a range of integers
//! (DRY-sorted-structures-2): [`first_true`] where the predicate is false and then true,
//! [`last_true`] where it is true and then false, and [`try_first_true`] and [`try_last_true`]
//! for a predicate that can fail, and [`gallop`], the exponential search of a slice from a
//! place (Bentley and Yao 1976, doi:10.1016/0020-0190(76)90071-5; the full comment is at fn
//! `gallop`). Each of the four binary searches asks the predicate O(log w) times for a range
//! `w` wide, never at the end of the range it already knows, and never forms a value outside
//! the range, so a search over the whole of a primitive type does not overflow.
//!
//! For a sorted slice, `<[T]>::partition_point` is the same search over its indices.

use crate::intervals::Discrete;

/// An integer type that [`first_true`] and [`last_true`] can halve. The one copy of the
/// overflow-free midpoint of two integers for every crate: `zed_kernel::machine_int` held an
/// `i128` copy (`floor_midpoint`, `ceil_midpoint`), whose callers were all binary searches and
/// now call these searches.
pub trait Midpoint: Discrete {
    /// `floor((lo + hi) / 2)`, for `lo <= hi`: at least `lo`, and less than `hi` when
    /// `lo < hi`.
    fn mid_down(lo: &Self, hi: &Self) -> Self;

    /// `ceil((lo + hi) / 2)`, for `lo <= hi`: at most `hi`, and greater than `lo` when
    /// `lo < hi`.
    fn mid_up(lo: &Self, hi: &Self) -> Self;
}

// The mean rounded down without forming `lo + hi`, which can overflow: the bits the two share,
// plus half of those they do not (`>>` on a signed type keeps the sign, so it rounds down).
// Rounded up: all the bits of either, less half of those they do not share. Hacker's Delight,
// section 2-5. std's `midpoint` is not used: on a signed type it rounds toward zero, so for
// `(-3, -2)` it gives `-2`, the end `hi`, and a search taking `mid` in `[lo, hi)` would not
// shrink.
macro_rules! midpoint_primitive {
    ($($t:ty),*) => {$(
        impl Midpoint for $t {
            #[inline]
            fn mid_down(lo: &Self, hi: &Self) -> Self {
                (lo & hi) + ((lo ^ hi) >> 1)
            }

            #[inline]
            fn mid_up(lo: &Self, hi: &Self) -> Self {
                (lo | hi) - ((lo ^ hi) >> 1)
            }
        }
    )*};
}

midpoint_primitive!(
    i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
);

/// For `zed_kernel::value`'s search over integers past `i64` (`search_beside`); the orphan rule
/// puts the impl here, beside the trait.
impl Discrete for num_bigint::BigInt {
    fn succ(&self) -> Option<Self> {
        Some(self + 1u8)
    }

    fn pred(&self) -> Option<Self> {
        Some(self - 1u8)
    }
}

// `hi - lo` is at least 0, so `/ 2`, which rounds toward zero, rounds it down.
impl Midpoint for num_bigint::BigInt {
    fn mid_down(lo: &Self, hi: &Self) -> Self {
        lo + (hi - lo) / 2u8
    }

    fn mid_up(lo: &Self, hi: &Self) -> Self {
        hi - (hi - lo) / 2u8
    }
}

/// `v + 1` for a `v` below some value of the type, so it is never `None`.
fn above<T: Discrete>(v: &T) -> T {
    v.succ().expect("a value below another has a successor")
}

/// `v - 1` for a `v` above some value of the type.
fn below<T: Discrete>(v: &T) -> T {
    v.pred().expect("a value above another has a predecessor")
}

/// The least `i` in `lo..hi` with `pred(i)`, or `hi` where there is none, for a `pred` false
/// on a prefix of `lo..hi` and true on the rest: `pred(hi)` is taken to hold and never asked.
/// `lo` itself where `lo >= hi`. At most `ceil(log2(hi - lo + 1))` questions.
pub fn first_true<T: Midpoint>(lo: T, hi: T, mut pred: impl FnMut(&T) -> bool) -> T {
    match try_first_true(lo, hi, |i| Ok::<bool, std::convert::Infallible>(pred(i))) {
        Ok(i) => i,
    }
}

/// The greatest `i` in `lo + 1..=hi` with `pred(i)`, or `lo` where there is none, for a `pred`
/// true on a prefix of `lo..=hi` and false on the rest: `pred(lo)` is taken to hold and never
/// asked. `lo` itself where `lo >= hi`. At most `ceil(log2(hi - lo + 1))` questions.
pub fn last_true<T: Midpoint>(lo: T, hi: T, mut pred: impl FnMut(&T) -> bool) -> T {
    match try_last_true(lo, hi, |i| Ok::<bool, std::convert::Infallible>(pred(i))) {
        Ok(i) => i,
    }
}

/// [`first_true`] for a `pred` that can fail: the first failure, as soon as it is met.
pub fn try_first_true<T: Midpoint, E>(
    mut lo: T,
    mut hi: T,
    mut pred: impl FnMut(&T) -> Result<bool, E>,
) -> Result<T, E> {
    while lo < hi {
        let mid = T::mid_down(&lo, &hi);
        if pred(&mid)? {
            hi = mid;
        } else {
            lo = above(&mid);
        }
    }
    Ok(lo)
}

/// [`last_true`] for a `pred` that can fail: the first failure, as soon as it is met.
pub fn try_last_true<T: Midpoint, E>(
    mut lo: T,
    mut hi: T,
    mut pred: impl FnMut(&T) -> Result<bool, E>,
) -> Result<T, E> {
    while lo < hi {
        let mid = T::mid_up(&lo, &hi);
        if pred(&mid)? {
            lo = mid;
        } else {
            hi = below(&mid);
        }
    }
    Ok(lo)
}

/// The least `i` in `from..a.len()` with `!pred(&a[i])`, or `a.len()` where there is none, for
/// a `pred` true on a prefix of `a[from..]` and false on the rest: exponential search from
/// `from` (J. L. Bentley and A. C. Yao, "An almost optimal algorithm for unbounded searching",
/// 1976), then binary search in the last step. O(log d) calls of `pred` for an answer `d` past
/// `from`, so a walk of a sorted list by many searches, each from where the last stopped, costs
/// no more than a merge.
//
// Source: J. L. Bentley and A. C. Yao, Information Processing Letters 5(3):82-87, 1976,
// doi:10.1016/0020-0190(76)90071-5; read in the preprint SLAC-PUB-1679, November 1975,
// https://www.osti.gov/servlets/purl/1318069. Section 2, Algorithm B1 (Binary Search): "the
// first stage of the algorithm determines m = ⌊lg n⌋ + 1 by successively evaluating F(2^i - 1)
// for i = 1, 2, ... until F(2^m - 1) = B", then "a standard bounded binary search on those
// 2^(m-1) elements", "so the total cost is C_B1(n) = 2⌊lg n⌋ + 1". Here the probes are at
// `from + 2^i - 1` (`lo + step`, `step` doubling), and the second stage is `partition_point`.
// Departures: the search first asks at `from` itself, so an answer of `from` costs one call;
// the slice ends, so the doubling stops at `a.len()`; and it uses B1, not the paper's B2 or
// its later algorithms, which take lg n + O(lg lg n) calls instead of 2 lg n: the merge walks
// this serves are O(log d) either way, and B1 is the simplest. Checked 2026-11-20 against
// the preprint's page 5. Test: `tests::gallop_matches_a_scan`, every start and border of
// every list up to 40 long against a scan, with at most 2⌊lg(d + 1)⌋ + 3 calls for an answer
// `d` past `from`; it does not reach lists longer than 40.
//
// `from` must be at most `a.len()`. Past it the answer `from` would lie outside `from..=a.len()`,
// the range the result is read in; a build with debug assertions panics there instead
// (TEST-dry-shared-units; `tests::gallop_from_past_the_end_panics_in_a_debug_build`).
pub fn gallop<T>(a: &[T], from: usize, mut pred: impl FnMut(&T) -> bool) -> usize {
    debug_assert!(
        from <= a.len(),
        "search::gallop from {from}, past the end {}",
        a.len()
    );
    if a.get(from).is_none_or(|x| !pred(x)) {
        return from;
    }
    // `pred` holds at `lo`.
    let (mut lo, mut step) = (from, 1);
    while lo + step < a.len() && pred(&a[lo + step]) {
        lo += step;
        step *= 2;
    }
    let hi = (lo + step + 1).min(a.len());
    lo + 1 + a[lo + 1..hi].partition_point(pred)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_integer::Integer;

    /// Every border in every range of `i8` listed, and each search's questions counted: the
    /// answer of a scan, never a question at the known end or outside the range.
    #[test]
    fn every_border_of_every_range_of_i8() {
        let all = i8::MIN..=i8::MAX;
        for (lo, hi) in [
            (i8::MIN, i8::MAX),
            (i8::MIN, i8::MIN),
            (-3, 4),
            (5, 5),
            (126, 127),
        ] {
            for t in all.clone() {
                let mut asked = 0u32;
                let got = first_true(lo, hi, |&i| {
                    assert!(lo <= i && i < hi, "{i} outside {lo}..{hi}");
                    asked += 1;
                    i >= t
                });
                let want = (lo..hi).find(|&i| i >= t).unwrap_or(hi);
                assert_eq!(got, want, "first_true {lo} {hi} {t}");
                assert!(asked <= 8, "{asked} questions");
                let got = last_true(lo, hi, |&i| {
                    assert!(lo < i && i <= hi, "{i} outside {lo}<..={hi}");
                    i <= t
                });
                let want = (lo..=hi).rev().find(|&i| i == lo || i <= t);
                assert_eq!(Some(got), want, "last_true {lo} {hi} {t}");
            }
        }
        assert_eq!(first_true(5u8, 2, |_| unreachable!()), 5);
        assert_eq!(last_true(5u8, 2, |_| unreachable!()), 5);
    }

    /// The midpoints against the exact mean in `BigInt`, at the ends of `i128` and around
    /// zero (moved from `zed_kernel::machine_int`, where the `i128` copy was), and of `u64` at
    /// its top; and the case std's signed `midpoint` gets wrong for a search.
    #[test]
    fn midpoints_are_exact_at_every_end() {
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
                let (lo, hi) = (a.min(b), a.max(b));
                let sum = BigInt::from(lo) + hi;
                let two = BigInt::from(2);
                let down = i128::mid_down(&lo, &hi);
                assert_eq!(
                    BigInt::from(down),
                    sum.div_floor(&two),
                    "mid_down({lo}, {hi})"
                );
                let up = i128::mid_up(&lo, &hi);
                assert_eq!(BigInt::from(up), sum.div_ceil(&two), "mid_up({lo}, {hi})");
                let (blo, bhi) = (BigInt::from(lo), BigInt::from(hi));
                assert_eq!(BigInt::mid_down(&blo, &bhi), sum.div_floor(&two));
                assert_eq!(BigInt::mid_up(&blo, &bhi), sum.div_ceil(&two));
            }
        }
        assert_eq!(i128::mid_down(&-3, &-2), -3);
        assert_eq!((-3i128).midpoint(-2), -2, "std rounds toward zero");
        assert_eq!(u64::mid_down(&(u64::MAX - 1), &u64::MAX), u64::MAX - 1);
        assert_eq!(u64::mid_up(&(u64::MAX - 1), &u64::MAX), u64::MAX);
    }

    /// Searches over the whole of `i128` and `u128`, and a failure passed on as soon as met.
    #[test]
    fn whole_types_and_failures() {
        let t = 12345i128 << 100;
        assert_eq!(first_true(i128::MIN, i128::MAX, |&i| i >= t), t);
        assert_eq!(last_true(i128::MIN, i128::MAX, |&i| i <= -t), -t);
        assert_eq!(
            first_true(0u128, u128::MAX, |&i| i >= u128::MAX - 1),
            u128::MAX - 1
        );
        assert_eq!(first_true(i128::MIN, i128::MAX, |_| false), i128::MAX);
        assert_eq!(last_true(i128::MIN, i128::MAX, |_| false), i128::MIN);
        let (lo, hi): (BigInt, BigInt) = (-(BigInt::from(1) << 300), BigInt::from(1) << 300);
        let t = BigInt::from(-7) << 200;
        assert_eq!(first_true(lo.clone(), hi.clone(), |i| *i >= t), t);
        assert_eq!(last_true(lo, hi, |i| *i <= t), t);
        let mut asked = 0;
        let r = try_first_true(0u32, 1000, |&i| {
            asked += 1;
            if i < 700 { Ok(false) } else { Err(i) }
        });
        assert_eq!((r, asked), (Err(750), 2));
        assert_eq!(
            try_last_true(0u32, 1000, |&i| Ok::<_, ()>(i < 700)),
            Ok(699)
        );
    }

    /// The gallop from every start to every border of every list up to 40 long, against a
    /// scan, with its questions counted. The bound on questions is Bentley and Yao's (1976,
    /// doi:10.1016/0020-0190(76)90071-5); the full comment is at fn `gallop`.
    #[test]
    fn gallop_matches_a_scan() {
        for n in 0..=40usize {
            let a: Vec<usize> = (0..n).collect();
            for from in 0..=n {
                for t in from..=n {
                    let mut asked = 0u32;
                    let got = gallop(&a, from, |&x| {
                        asked += 1;
                        x < t
                    });
                    assert_eq!(got, t, "n={n} from={from} t={t}");
                    let d = (t - from + 1) as u32;
                    assert!(asked <= 2 * d.ilog2() + 3, "{asked} questions for {d}");
                }
            }
        }
    }

    // Random searches against scans at every width, and the regressions of the copies the
    // module replaced (TEST-dry-shared-units).

    use crate::seed::Rng;

    /// The most questions a search of a range `w` wide may ask, `ceil(log2(w + 1))`, as the
    /// functions promise; `w` as `u128`, so the whole of `u64` and `i64` fits.
    fn most_questions(w: u128) -> u32 {
        (w + 1).next_power_of_two().ilog2()
    }

    /// Random borders in random ranges near the ends and the middle of `i64`, `u64`, `u16` and
    /// `usize`, by `first_true` and `last_true`, against the border itself, with the questions
    /// counted and each asked inside the range; the faulty search that asks `hi` (`mid_up` in
    /// `first_true`), caught by the question at the known end.
    #[test]
    fn random_borders_at_every_width_are_found() {
        let (mut rng, _) = Rng::fresh("random_borders_at_every_width_are_found");
        macro_rules! width {
            ($t:ty) => {{
                let picks = [<$t>::MIN, <$t>::MAX, 0, <$t>::MAX / 2];
                let mut caught = false;
                for round in 0..3000 {
                    let near = |rng: &mut Rng| {
                        let at = rng.pick(&picks);
                        let bits = rng.below(20);
                        let d = rng.below_u64(1 << bits) as $t;
                        if at == <$t>::MAX {
                            at - d
                        } else {
                            at.saturating_add(d)
                        }
                    };
                    let (x, y) = (near(&mut rng), near(&mut rng));
                    let (lo, hi) = (x.min(y), x.max(y));
                    let w = (hi as i128 - lo as i128) as u128;
                    let t = if rng.below(8) == 0 {
                        hi
                    } else {
                        near(&mut rng).clamp(lo, hi)
                    };
                    let mut asked = 0;
                    let got = first_true(lo, hi, |&i| {
                        assert!(lo <= i && i < hi, "round {round}: {i} outside {lo}..{hi}");
                        asked += 1;
                        i >= t
                    });
                    assert_eq!(got, t, "round {round}: first_true {lo} {hi} {t}");
                    assert!(asked <= most_questions(w), "round {round}: {asked} for {w}");
                    let mut asked = 0;
                    let got = last_true(lo, hi, |&i| {
                        assert!(lo < i && i <= hi, "round {round}: {i} outside {lo}<..={hi}");
                        asked += 1;
                        i <= t
                    });
                    assert_eq!(got, t, "round {round}: last_true {lo} {hi} {t}");
                    assert!(asked <= most_questions(w), "round {round}: {asked} for {w}");
                    // The control: `first_true` halving at `mid_up` asks `hi`, the end it knows,
                    // once its range is two wide; cut off at 200 questions, since where `hi`
                    // answers true it no longer shrinks.
                    let (mut l, mut h) = (lo, hi);
                    for _ in 0..200 {
                        if l >= h {
                            break;
                        }
                        let mid = <$t>::mid_up(&l, &h);
                        caught |= mid == hi;
                        if mid >= t { h = mid } else { l = mid + 1 }
                    }
                }
                assert!(
                    caught,
                    "the negative control of {} was never caught",
                    stringify!($t)
                );
            }};
        }
        width!(i64);
        width!(u64);
        width!(u16);
        width!(usize);
    }

    /// two_pins.rs `full_dark` took its peak's midpoint as `peak.0 + (peak.1 - peak.0) / 2`,
    /// which overflows `i128` where the two ends have opposite signs and are far apart
    /// (DRY-sorted-structures-2 job 4, 2b3e706f1); the shared midpoint does not.
    #[test]
    fn the_midpoint_of_ends_of_opposite_sign_does_not_overflow() {
        let old = |lo: i128, hi: i128| hi.checked_sub(lo).map(|d| lo + d / 2);
        for (lo, hi) in [(i128::MIN, i128::MAX), (i128::MIN, 1), (-1, i128::MAX)] {
            assert_eq!(old(lo, hi), None, "the old form overflows at ({lo}, {hi})");
        }
        assert_eq!(i128::mid_down(&i128::MIN, &i128::MAX), -1);
        assert_eq!(i128::mid_up(&i128::MIN, &i128::MAX), 0);
        assert_eq!(i128::mid_down(&i128::MIN, &1), i128::MIN / 2);
        // ceil((i128::MAX - 1) / 2) = ceil((2^127 - 2) / 2) = 2^126 - 1.
        assert_eq!(i128::mid_up(&-1, &i128::MAX), (1 << 126) - 1);
        // A peak at either end of the whole type is found.
        assert_eq!(first_true(i128::MIN, i128::MAX, |_| true), i128::MIN);
        assert_eq!(last_true(i128::MIN, i128::MAX, |_| true), i128::MAX);
        // The midpoints of every pair of `i8` against the exact mean, and std's signed
        // `midpoint`, rounded toward zero, would stop a search on a negative range.
        for lo in i8::MIN..=i8::MAX {
            for hi in lo..=i8::MAX {
                let sum = i16::from(lo) + i16::from(hi);
                assert_eq!(i16::from(i8::mid_down(&lo, &hi)), sum.div_euclid(2));
                assert_eq!(i16::from(i8::mid_up(&lo, &hi)), -(-sum).div_euclid(2));
            }
        }
        assert_eq!((-3i8).midpoint(-2), -2, "std's midpoint is the end hi");
    }

    /// The failure of the first question is passed on with no second question, by both.
    #[test]
    fn a_failure_is_passed_on_at_once() {
        let mut asked = 0;
        let r = try_last_true(i64::MIN, i64::MAX, |_| {
            asked += 1;
            Err::<bool, _>("no")
        });
        assert_eq!((r, asked), (Err("no"), 1));
        let r = try_first_true(3u8, 3, |_| Err::<bool, ()>(()));
        assert_eq!(r, Ok(3), "an empty range asks nothing");
    }

    /// The gallop on random sorted lists up to 5000 long, from random starts, against
    /// `partition_point`, with at most `2 floor(log2(d + 1)) + 3` questions for an answer `d`
    /// past `from`; the bound is shown to reject a linear walk, which asks `d` questions, on
    /// some draw (its negative control).
    #[test]
    fn gallop_matches_partition_point_on_long_lists() {
        let (mut rng, _) = Rng::fresh("gallop_matches_partition_point_on_long_lists");
        let mut caught = false;
        for round in 0..500 {
            let n = rng.below(5001);
            let mut a: Vec<u32> = (0..n).map(|_| rng.below(1 << 14) as u32).collect();
            a.sort_unstable();
            let from = rng.below(n + 1);
            let x = rng.below(1 << 14) as u32;
            let want = from + a[from..].partition_point(|&v| v < x);
            let mut asked = 0u32;
            let got = gallop(&a, from, |&v| {
                asked += 1;
                v < x
            });
            assert_eq!(got, want, "round {round}: n={n} from={from} x={x}");
            let d = (want - from + 1) as u32;
            assert!(asked <= 2 * d.ilog2() + 3, "round {round}: {asked} for {d}");
            // The control: a linear walk from `from` asks `d` questions, over the bound for
            // every `d` past 8.
            caught |= d > 2 * d.ilog2() + 3;
        }
        assert!(caught, "the negative control of gallop was never caught");
    }

    /// `from` past the end, in a build with debug assertions (the test builds are).
    #[test]
    fn gallop_from_past_the_end_panics_in_a_debug_build() {
        if !cfg!(debug_assertions) {
            return;
        }
        assert_eq!(gallop(&[1, 2, 3], 3, |_| true), 3);
        let p = std::panic::catch_unwind(|| gallop(&[1, 2, 3], 4, |_| true)).expect_err("panics");
        let text = p.downcast_ref::<String>().expect("a formatted message");
        assert_eq!(text, "search::gallop from 4, past the end 3");
    }
}
