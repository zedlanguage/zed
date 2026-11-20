//! The tests of [`crate::seed`], compiled into this crate's unit tests only. The module itself is
//! compiled, by `#[path]`, into the unit tests of zedc-int, zedc-lattice, zedc-preimage,
//! zedc-presburger, zedc-solvers, zedc-types and zed-kernel too, and while this test lay inside
//! it, it ran again in each of those binaries, eight times a run, and each of their test counts
//! was one more than their own tests (TEST-seed-test-once, as TEST-scaling-module-tests-once did
//! for `crate::scaling`). The module gives this file `mix` as `pub(crate)`.

use crate::seed::{Rng, Xorshift64, mix};

#[test]
fn the_mix_is_splitmix64() {
    // The first output of SplitMix64 from the states 0 and 1 (Steele, Lea and Flood 2014,
    // doi:10.1145/2660193.2660195): the values the JDK's `SplittableRandom`, the paper's
    // generator, printed for `new SplittableRandom(0).nextLong()` and `(1)` on JDK 26,
    // 2026-11-20. Two states, so a changed constant that happens to leave one value alone fails.
    assert_eq!(mix(0), 0xe220_a839_7b1d_cdaf);
    assert_eq!(mix(1), 0x910a_2dec_8902_5cc1);
}

/// `ZED_TEST_SEED=0` must run a random test on varied cases. The xorshift64 generators this
/// generator replaced (DRY-test-helpers) had 0 as a fixed point: from the seed 0 every draw was 0.
#[test]
fn seed_zero_gives_varied_draws() {
    let mut rng = Rng::new(0);
    let words: Vec<u64> = (0..64).map(|_| rng.next_u64()).collect();
    let mut distinct = words.clone();
    zed_collections::sorted::sort_dedup(&mut distinct);
    assert_eq!(distinct.len(), 64, "{words:x?}");
    let mut rng = Rng::new(0);
    let mut seen = [false; 10];
    for _ in 0..200 {
        seen[rng.below(10)] = true;
    }
    assert!(
        seen.iter().all(|&s| s),
        "from seed 0, 200 draws below 10 missed one: {seen:?}"
    );
    // The xorshift kept for pinned streams replaces the seed 0, and keeps every other seed.
    let mut x = Xorshift64::new(0);
    let words: Vec<u64> = (0..64).map(|_| x.next_u64()).collect();
    assert!(words.iter().all(|&w| w != 0), "{words:x?}");
    let mut x = Xorshift64::new(1);
    // 1 → 0x2001 (<< 13) → 0x2041 (>> 7) → 0x4082_2041 (<< 17), as the copies drew.
    assert_eq!(x.next_u64(), 0x4082_2041);
}

/// Draws stay in their ranges, at the ends of each type too, and a shuffle is a permutation.
#[test]
fn draws_stay_in_range_and_shuffles_permute() {
    let mut rng = Rng::new(7);
    for _ in 0..1000 {
        assert!((-3..=3).contains(&rng.int(-3i64, 3)));
        assert!(rng.below(5) < 5);
        assert_eq!(rng.int(i64::MAX, i64::MAX), i64::MAX);
        assert!(
            (-(1i128 << 100)..=-(1i128 << 100) + 9)
                .contains(&rng.int_i128(-(1 << 100), -(1 << 100) + 9))
        );
    }
    // The whole of u64 and of i64: ranges of 2^64 numbers.
    assert!((0..=i128::from(u64::MAX)).contains(&rng.int_i128(0, u64::MAX.into())));
    let _ = rng.int(i64::MIN, i64::MAX);
    let mut xs: Vec<usize> = (0..100).collect();
    rng.shuffle(&mut xs);
    assert_ne!(xs, (0..100).collect::<Vec<_>>());
    xs.sort_unstable();
    assert_eq!(xs, (0..100).collect::<Vec<_>>());
}
