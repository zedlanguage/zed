//! FAIL-pext-transfer-popcount, found by TEST-complete-reduced (author P189): `pext` lies below
//! `2^popCount(mask)` (DESIGN L1.39f), so its forward transfer bounds the result by `2^m - 1`,
//! `m` the most one digits of a mask in the mask's hull, and by the upper end of `x`; it was
//! bounded by `2^digits(mask)`. The count of the most one digits in a range is checked here
//! against the count over every member, on machine words, on wide words and across the two.

use zed_kernel::Prim;
use zedc::store::interval::{End, IntervalSet, Num, bit_word};

use super::{accepted, rejected};

#[test]
fn pext_is_below_two_to_the_pop_count_of_its_mask() {
    // The kernel transfer: a mask of 0b11010 has 3 one digits, so `pext` of any `x` is below 8.
    let all_x = IntervalSet::range(End::of(0), End::PosInf);
    assert_eq!(
        bit_word(Prim::Pext, &[all_x.clone(), IntervalSet::single(0b11010)]),
        IntervalSet::of(0, 7)
    );
    // A mask in 0 ..= 26: at most 4 one digits (15, 23), so below 16.
    assert_eq!(
        bit_word(Prim::Pext, &[all_x, IntervalSet::of(0, 0b11010)]),
        IntervalSet::of(0, 15)
    );
    // Through the surface: the bound read as the `x` of `bitReverse` fits 3 digits, not 2.
    let at = |v: u32| {
        format!(
            "f(positional a: int) = if a >= 0 && a < 2^16 {{ bitReverse(pext(a, 26), width: {v}) }} \
             else {{ 0 }};\n"
        )
    };
    assert!(accepted(&at(3)), "{}", at(3));
    let out = rejected(&at(2));
    assert!(
        out.contains("`bitReverse` takes `x` in int[0..<2^2]"),
        "{out}"
    );
}

#[test]
fn the_mask_hull_bounds_pext_by_its_most_one_digits() {
    let all_x = IntervalSet::range(End::of(0), End::PosInf);
    let pext = |lo: i64, hi: i64| bit_word(Prim::Pext, &[all_x.clone(), IntervalSet::of(lo, hi)]);
    // 16 ..= 22: 19, 21 and 22 have 3 one digits, none has 4.
    assert_eq!(pext(16, 22), IntervalSet::of(0, 7));
    // 16 ..= 23: 23 = 0b10111 has 4.
    assert_eq!(pext(16, 23), IntervalSet::of(0, 15));
    // An all-ones upper end keeps all its digits; the mask 0 gives 0.
    assert_eq!(pext(0, 31), IntervalSet::of(0, 31));
    assert_eq!(pext(0, 0), IntervalSet::of(0, 0));
    // A mask of one digit: `pext` is 0 or 1.
    assert_eq!(pext(1 << 40, 1 << 40), IntervalSet::of(0, 1));
    // The upper end of `x` still bounds it where it is lower.
    assert_eq!(
        bit_word(
            Prim::Pext,
            &[IntervalSet::of(0, 6), IntervalSet::of(0, 0b11010)]
        ),
        IntervalSet::of(0, 6)
    );
    // An unbounded mask leaves `x`'s bound.
    assert_eq!(
        bit_word(
            Prim::Pext,
            &[
                IntervalSet::of(0, 9),
                IntervalSet::range(End::of(3), End::PosInf)
            ]
        ),
        IntervalSet::of(0, 9)
    );
}

/// The most one digits of a member of `lo ..= hi`, counted over every member.
fn most_ones_counted(lo: u128, hi: u128) -> u32 {
    (lo..=hi).map(u128::count_ones).max().expect("lo <= hi")
}

#[test]
fn the_most_one_digits_of_a_range_agree_with_the_count_over_its_members() {
    // Every range in 0 ..< 2^7, on machine words.
    for lo in 0u128..128 {
        for hi in lo..128 {
            let got = Num::from(hi as i128).most_ones_from(&Num::from(lo as i128));
            assert_eq!(
                got,
                Num::from(i64::from(most_ones_counted(lo, hi))),
                "{lo} ..= {hi}"
            );
        }
    }
    // Ranges of up to 64 members at offsets past `i64` (wide words), and ranges whose lower end
    // is a machine word and whose upper end is wide.
    for base in [
        1u128 << 64,
        (1u128 << 70) - 40,
        (1u128 << 100) | 0b1011_0000,
        u128::MAX >> 2,
    ] {
        for a in 0u128..40 {
            for len in [0u128, 1, 2, 7, 23, 40, 64] {
                let (lo, hi) = (base + a, base + a + len);
                let got = Num::from(hi as i128).most_ones_from(&Num::from(lo as i128));
                assert_eq!(
                    got,
                    Num::from(i64::from(most_ones_counted(lo, hi))),
                    "{lo} ..= {hi}"
                );
            }
        }
    }
    for (lo, hi) in [
        (0u128, 1u128 << 64),
        (5, (1 << 64) + 3),
        (1 << 62, (1 << 64) - 1),
    ] {
        let got = Num::from(hi as i128).most_ones_from(&Num::from(lo as i128));
        // The upper end has the most digits, so the answer is its digits less one unless it is
        // all ones.
        let d = 128 - hi.leading_zeros();
        let want = if (hi + 1).is_power_of_two() { d } else { d - 1 };
        assert_eq!(got, Num::from(i64::from(want)), "{lo} ..= {hi}");
    }
}

#[test]
fn a_kept_mask_bounds_pext_by_its_digits() {
    // `2^200` and `2^200 - 1` are kept, not written out: the answer is that of `0 ..= hi`.
    // For `2^200 - 1` (all ones) it is its 200 digits; for `2^200`, of 201 digits and not all
    // ones, it is 200, the ones of `2^200 - 1`.
    let p = Num::pow2(&Num::from(200));
    let all_ones = &p - &Num::ONE;
    assert_eq!(p.most_ones_from(&Num::ZERO), Num::from(200));
    assert_eq!(all_ones.most_ones_from(&Num::ZERO), Num::from(200));
    // A kept lower end: the bound over `0 ..= hi`, sound though not the popCount 1 of `2^200`.
    assert_eq!(p.most_ones_from(&p), Num::from(200));
    let all_x = IntervalSet::range(End::of(0), End::PosInf);
    let below = End::Fin(&Num::pow2(&Num::from(200)) - &Num::ONE);
    assert_eq!(
        bit_word(
            Prim::Pext,
            &[all_x, IntervalSet::range(End::of(0), End::Fin(p.clone()))]
        ),
        IntervalSet::range(End::of(0), below)
    );
    // The upper end of `x` bounds it where it is lower.
    assert_eq!(
        bit_word(
            Prim::Pext,
            &[
                IntervalSet::of(0, 9),
                IntervalSet::range(End::of(0), End::Fin(p))
            ]
        ),
        IntervalSet::of(0, 9)
    );
}
