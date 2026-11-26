//! Tests of the hash steps and generators: values computed apart from this crate (the JDK, the
//! FNV draft's test code, a hand step of xorshift), the identities the callers rely on, and each
//! routine against an oracle written from its definition, the copies it replaced.

use super::*;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};

/// The oracle of splitmix64: Vigna's `splitmix64.c` `next`, transcribed line by line (the state
/// advanced by γ, then the three xor-shift-multiply lines on the new state).
struct VignaSplitMix(u64);

impl VignaSplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

#[test]
fn the_mix_is_splitmix64() {
    // The first output of SplitMix64 from the states 0 and 1 (Steele, Lea and Flood 2014,
    // doi:10.1145/2660193.2660195): the values the JDK's `SplittableRandom`, the paper's
    // generator, printed for `new SplittableRandom(0).nextLong()` and `(1)` on JDK 26,
    // 2026-11-20. Two states, so a changed constant that happens to leave one value alone fails.
    assert_eq!(mix(0), 0xe220_a839_7b1d_cdaf);
    assert_eq!(mix(1), 0x910a_2dec_8902_5cc1);
}

/// `step(0, x)` is SplitMix64's output for the state `x + γ` (Vigna's `splitmix64.c`: the state
/// is advanced by γ, then mixed), so the step from 0 over 0, γ, 2γ gives the reference
/// generator's first three outputs seeded with 0. The values were computed by a transcription of
/// `splitmix64.c` apart from this crate (2026-11-20, TEST-dry-shared-units); they pin the
/// constants zed-kernel's `bdd::set::tests` relies on.
#[test]
fn the_step_from_zero_is_splitmix64() {
    let outs: Vec<u64> = (0..3u64).map(|k| step(0, k.wrapping_mul(GAMMA))).collect();
    assert_eq!(
        outs,
        [
            0xe220_a839_7b1d_cdaf,
            0x6e78_9e6a_a1b9_65f4,
            0x06c4_5d18_8009_454f
        ]
    );
    let mut g = SplitMix64::new(0);
    assert_eq!(outs, [g.next_u64(), g.next_u64(), g.next_u64()]);
}

/// The step is a bijection in each argument (proof at [`finalize`]), so no two of many words give
/// one value from one `h`, and no two of many `h` from one word; and it depends on the order of
/// the words. Negative control: a step that ignores `h` (only the finalizer of `x`) gives one
/// value for every `h`, which the second check catches; an xor of the words is unordered. A fixed
/// seed: this crate is below the test seed of `tests/src/seed.rs`, and the identities hold for
/// every word, so a new draw each run adds little.
#[test]
fn the_step_is_one_to_one_in_each_argument_and_depends_on_order() {
    let mut rng = SplitMix64::new(0x5eed_57e9);
    let words: Vec<u64> = (0..20_000)
        .map(|_| rng.next_u64())
        .chain([0, 1, u64::MAX])
        .collect();
    let h = rng.next_u64();
    let distinct = |f: &dyn Fn(u64) -> u64| words.iter().map(|&w| f(w)).collect::<HashSet<_>>();
    assert_eq!(distinct(&|x| step(h, x)).len(), words.len());
    assert_eq!(distinct(&|g| step(g, h)).len(), words.len());
    let ordered = |f: &dyn Fn(u64, u64) -> u64| {
        (words.windows(2))
            .filter(|w| w[0] != w[1])
            .all(|w| f(f(0, w[0]), w[1]) != f(f(0, w[1]), w[0]))
    };
    assert!(ordered(&step));
    let ignores_h = |_: u64, x: u64| step(0, x);
    assert_eq!(distinct(&|g| ignores_h(g, h)).len(), 1);
    assert!(
        !ordered(&|g, x| step(0, x) ^ g),
        "an xor of the words is caught as unordered"
    );
}

/// `unstep` inverts `step` in its second argument, both ways round, on random words and the
/// words of all-zero and all-one bits.
#[test]
fn unstep_inverts_the_step() {
    let mut rng = SplitMix64::new(0x0757_e9a1);
    let words: Vec<u64> = (0..10_000)
        .map(|_| rng.next_u64())
        .chain([0, 1, u64::MAX])
        .collect();
    for w in words {
        for h in [rng.next_u64(), 0, u64::MAX] {
            assert_eq!(step(h, unstep(h, w)), w, "h={h:#x} z={w:#x}");
            assert_eq!(unstep(h, step(h, w)), w, "h={h:#x} x={w:#x}");
        }
    }
}

/// The generator against Vigna's transcription from many seeds, 0 and `u64::MAX` among them
/// (the state wraps), and `mix` against the same: the generator's `k`-th output from `s` is
/// `mix(s + k·γ)`.
#[test]
fn the_generator_agrees_with_vignas_splitmix64() {
    let mut seeds = SplitMix64::new(0x0dd5_eed5);
    for s in [0, 1, u64::MAX, GAMMA.wrapping_neg()]
        .into_iter()
        .chain((0..200).map(|_| seeds.next_u64()))
    {
        let (mut g, mut v) = (SplitMix64::new(s), VignaSplitMix(s));
        for k in 0..50u64 {
            let want = v.next();
            assert_eq!(g.next_u64(), want, "seed {s:#x}, draw {k}");
            assert_eq!(mix(s.wrapping_add(k.wrapping_mul(GAMMA))), want);
        }
    }
}

/// `ZED_TEST_SEED=0` must run a random test on varied cases. The xorshift64 generators this
/// generator replaced (DRY-test-helpers) had 0 as a fixed point: from the seed 0 every draw was 0.
#[test]
fn seed_zero_gives_varied_draws() {
    let mut rng = SplitMix64::new(0);
    let words: Vec<u64> = (0..64).map(|_| rng.next_u64()).collect();
    assert_eq!(words.iter().collect::<HashSet<_>>().len(), 64, "{words:x?}");
    let mut rng = SplitMix64::new(0);
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
    let mut rng = SplitMix64::new(7);
    for _ in 0..1000 {
        assert!((-3..=3).contains(&rng.int(-3i64, 3)));
        assert!(rng.below(5) < 5);
        assert_eq!(rng.int(i64::MAX, i64::MAX), i64::MAX);
        assert!(
            (-(1i128 << 100)..=-(1i128 << 100) + 9)
                .contains(&rng.int_i128(-(1 << 100), -(1 << 100) + 9))
        );
        let xs = rng.seq(&[1u8, 2, 3], 4);
        assert!(xs.len() <= 4 && xs.iter().all(|x| (1..=3).contains(x)));
    }
    // The whole of u64 and of i64: ranges of 2^64 numbers.
    assert!((0..=i128::from(u64::MAX)).contains(&rng.int_i128(0, u64::MAX.into())));
    let _ = rng.int(i64::MIN, i64::MAX);
    let mut xs: Vec<usize> = (0..100).collect();
    rng.shuffle(&mut xs);
    assert_ne!(xs, (0..100).collect::<Vec<_>>());
    xs.sort_unstable();
    assert_eq!(xs, (0..100).collect::<Vec<_>>());
    let mut one = [5];
    rng.shuffle(&mut one);
    rng.shuffle::<u8>(&mut []);
    assert_eq!(one, [5]);
}

/// The draws are the mappings the callers pinned their cases to: `below` is the output mod `n`,
/// `coin` the top bit, `shuffle` Durstenfeld's order of swaps; checked against those lines
/// written out on the oracle's outputs (the copies zed-kernel's `eval::SplitMix` and
/// `priority::seeded_words` held).
#[test]
fn the_draws_are_the_pinned_mappings() {
    for s in [0u64, 3, 0x9e37_79b9_7f4a_7c15] {
        let (mut g, mut v) = (SplitMix64::new(s), VignaSplitMix(s));
        for n in 1..200u64 {
            assert_eq!(g.below_u64(n), v.next() % n);
            assert_eq!(g.coin(), v.next() >> 63 == 1);
        }
        let mut xs: Vec<u32> = (0..37).collect();
        let mut ys = xs.clone();
        g.shuffle(&mut xs);
        for i in (1..ys.len()).rev() {
            let j = (v.next() % (i as u64 + 1)) as usize;
            ys.swap(i, j);
        }
        assert_eq!(xs, ys);
    }
}

#[test]
#[should_panic(expected = "an empty range")]
fn below_zero_panics() {
    SplitMix64::new(1).below(0);
}

#[test]
#[should_panic(expected = "more than 2^64 numbers")]
fn a_range_past_two_to_the_64_panics() {
    SplitMix64::new(1).int_i128(0, 1 << 64);
}

/// xorshift64 against the paper's `xor64` lines from many nonzero seeds, `below` as the output
/// mod `n`.
#[test]
fn xorshift_is_marsaglias_xor64() {
    let mut seeds = SplitMix64::new(0x0dd5_eed6);
    for s in [1, u64::MAX, 0x9e37_79b9_7f4a_7c15]
        .into_iter()
        .chain((0..200).map(|_| seeds.next_u64() | 1))
    {
        let (mut g, mut x) = (Xorshift64::new(s), s);
        for n in 1..60u64 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            if n % 2 == 0 {
                assert_eq!(g.next_u64(), x, "seed {s:#x}");
            } else {
                assert_eq!(g.below(n), x % n, "seed {s:#x}");
            }
        }
    }
}

/// The LCG is the copies' recurrence, written as they wrote it, from many seeds; `next_high` and
/// `below` read `>> 33`. Hand check of the first step from 0: the state becomes the increment.
#[test]
fn the_lcg_is_the_copies_recurrence() {
    assert_eq!(Lcg64::new(0).next_u64(), 1_442_695_040_888_963_407);
    let mut seeds = SplitMix64::new(0x0dd5_eed7);
    for s in [0, 1, 12345, 0x5eed, u64::MAX]
        .into_iter()
        .chain((0..200).map(|_| seeds.next_u64()))
    {
        let (mut g, mut x) = (Lcg64::new(s), s);
        for n in 1..60u64 {
            x = x
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            match n % 3 {
                0 => assert_eq!(g.next_u64(), x),
                1 => assert_eq!(g.next_high(), x >> 33),
                _ => assert_eq!(g.below(n), (x >> 33) % n),
            }
            // The state is the last state reached, and a generator from it goes on alike.
            assert_eq!(g.state(), x);
            assert_eq!(Lcg64::new(g.state()).next_u64(), g.clone().next_u64());
        }
    }
}

/// The four strings of the FNV draft's test code (section 8.3, `teststring`) and their 64-bit
/// FNV-1a hashes (`FNV64svalues`), without a terminating zero byte: by the function, by the
/// hasher, and in two blocks at every split.
#[test]
fn the_drafts_test_vectors() {
    for (text, want) in [
        (&b""[..], 0xcbf2_9ce4_8422_2325),
        (b"a", 0xaf63_dc4c_8601_ec8c),
        (b"foobar", 0x8594_4171_f739_67e8),
        (b"Hello!\x01\xFF\xED", 0xbd51_ea70_94ee_6fa1),
    ] {
        assert_eq!(fnv1a_64(text), want, "{}", text.escape_ascii());
        let mut h = Fnv1a::default();
        h.write(text);
        assert_eq!(h.finish(), want);
        for k in 0..=text.len() {
            let (a, b) = text.split_at(k);
            assert_eq!(fnv1a_64_from(fnv1a_64(a), b), want);
        }
    }
}

/// The hasher of a value is FNV-1a of the bytes its `Hash` writes, the numbers native-endian (the
/// `Hasher` defaults), against a fold over those bytes; and a `str` writes its bytes then `0xff`.
/// zedc-types' signature hash (`leaf_digest`) relies on it: its pinned values were made by a
/// hasher of exactly these steps.
#[test]
fn the_hasher_hashes_the_bytes_a_value_writes() {
    let fold = |bytes: &[u8]| {
        bytes.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, &b| {
            (h ^ b as u64).wrapping_mul(0x0000_0100_0000_01b3)
        })
    };
    let mut rng = SplitMix64::new(0x0dd5_eed8);
    for _ in 0..500 {
        let (a, b, c) = (rng.next_u64(), rng.next_u64() as u32, rng.next_u64() as u8);
        let mut h = Fnv1a::default();
        (a, b, c).hash(&mut h);
        let bytes: Vec<u8> = [&a.to_ne_bytes()[..], &b.to_ne_bytes(), &[c]].concat();
        assert_eq!(h.finish(), fold(&bytes));
    }
    let mut h = Fnv1a::default();
    "ab".hash(&mut h);
    assert_eq!(h.finish(), fold(b"ab\xff"));
}
