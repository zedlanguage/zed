//! Benchmarks of zed-bignum with the leaf sizes a program runs with (`fast::MUL_LEAF` 400 and
//! the others under `fast::SMALL_LEAVES`). zed-bignum's own unit tests and zed-kernel's, through
//! zed-bignum-small, take the small leaves, so that small inputs reach the Toom and transform
//! paths; a switch set by measurement (a leaf, the order of `fast::pow`) is measured here, in
//! another crate's tests, where `cfg(test)` is off for zed-bignum
//! (TEST-kernel-small-leaves-after-bignum-move).

mod bench {
    use std::hint::black_box;

    use num_bigint::BigUint;
    use num_traits::{One, Zero};
    use zed_bignum::fast;
    use zed_bignum::least_root::sqrt_rem_uint;

    use crate::scaling;

    /// A number of `words` words, its top word not zero, the same on every run.
    fn number(words: usize, seed: u64) -> BigUint {
        let mut g = zed_hash::SplitMix64::new(seed);
        let mut ds: Vec<u64> = (0..words).map(|_| g.next_u64()).collect();
        if let Some(top) = ds.last_mut() {
            *top |= 1 << 63;
        }
        BigUint::from_slice(
            &ds.iter()
                .flat_map(|d| [*d as u32, (d >> 32) as u32])
                .collect::<Vec<u32>>(),
        )
    }

    #[test]
    fn the_benchmarks_here_take_the_measured_leaves() {
        const { assert!(!fast::crossover::SMALL_LEAVES) };
        assert_eq!(fast::crossover::MUL_LEAF, 400);
    }

    /// PERF-sqrt-production-leaves-ratio: [`sqrt_rem_uint`] of a number of n words is O(M(n))
    /// (proof at the function); zed-bignum `bench::square_roots_scale` holds the same with the
    /// small leaves.
    ///
    /// The sizes, by the precedent of DECISION-roots-bench-regime (time where n and 8n run on
    /// one method): 2^14 and 2^17 words. Each level `j` of the recursion divides about `n /
    /// 2^(j+1)` by `n / 2^(j+2)` words, and `fast::div_rem` takes num-bigint's division up to
    /// 2048 by 1024 words and its reciprocal above, which costs 2.77 times as much one size
    /// up (6.87 million instructions at 2048 by 1024, 19.05 million at 4096 by 2048; hm1,
    /// 2026-11-26, `square_root_parts_by_size`). The cheap levels are a larger share of the
    /// work at 2^13 words than at 2^16, so the old sizes 2^13 and 2^16 took 10.716 times
    /// (38,694,839 and 414,649,981 instructions), over the limit, though each doubling costs
    /// less than the one before: 2.86, 2.71, 2.63, 2.32, 2.18 and 2.12 times from 2^10 to 2^16
    /// words, as O(M(n)) does with the transform product. At 2^14 and 2^17: 89,776,442 and
    /// 880,590,719, 9.809 times, the same on two runs (hm1, 2026-11-26). The top division of
    /// PERF-sqrt-production-leaves-ratio, on the same VM, before and after: 39,518,451 and
    /// 38,694,839 at 2^13, 416,119,461 and 414,649,981 at 2^16, 105,956,831 and 89,776,442 at
    /// 2^14, 1,198,777,803 and 880,590,719 at 2^17 (11.314 times before).
    #[test]
    fn square_roots_scale_with_the_measured_leaves() {
        let n = 1 << 14;
        let numbers = scaling::inputs(n, |m| number(m, 11));
        scaling::check_order("the square root of a number of n words", n, 1, |m| {
            let (s, r) = sqrt_rem_uint(&numbers[&m]);
            assert!(!s.is_zero() && r <= &s << 1u32);
        });
    }

    /// PERF-sqrt-production-leaves-ratio: the work of [`sqrt_rem_uint`] of `n` words and of the
    /// two products of its top level, the division of `r' 2^k + a1`, about `2k` bits, by `2s'`,
    /// about `k` bits, and the square of its quotient (`k` a quarter of the bits; the names of
    /// the proof at [`sqrt_rem_uint`]), for `n` from 2^10 to 2^16 words, printed: the
    /// sum over the levels is about twice the top level, so where the total grows faster than
    /// the product's `n log n` the top level's parts show which one does.
    #[test]
    fn square_root_parts_by_size() {
        let mut meter = scaling::Meter::new();
        // Counted here, not by a check (BENCH-self-counted-meters-processor-time).
        if scaling::ran_alone_in_a_new_process(&meter) {
            return;
        }
        for n in (10..=16).map(|j| 1usize << j) {
            let a = number(n, 11);
            let bits = a.bits();
            let k = bits.div_ceil(4);
            let (s1, r1) = sqrt_rem_uint(&(&a >> (2 * k)));
            // The top division of `sqrt_rem_uint`: `(r' B + a1) >> 1` by `s'`.
            let top = ((r1 << k) + ((&a >> k) & ((BigUint::one() << k) - 1u32))) >> 1u32;
            let den = s1;
            let q = fast::div_rem(&top, &den).0;
            let all = meter.least(|| {}, || drop(black_box(sqrt_rem_uint(&a))));
            let div = meter.least(|| {}, || drop(black_box(fast::div_rem(&top, &den))));
            let sq = meter.least(|| {}, || drop(black_box(fast::mul(&q, &q))));
            let by_num_bigint = meter.least(
                || {},
                || drop(black_box(num_integer::Integer::div_rem(&top, &den))),
            );
            let by_reciprocal = meter.least(
                || {},
                || {
                    drop(black_box(fast::crossover::div_rem_by_reciprocal(
                        &top, &den,
                    )))
                },
            );
            eprintln!(
                "sqrt n={n}: all={} top div={} ({} by {} words, num-bigint's: {}, flip {:?}) \
                 num-bigint div={} reciprocal div={} top square={} ({})",
                all.units,
                div.units,
                top.bits().div_ceil(64),
                den.bits().div_ceil(64),
                fast::crossover::div_by_num_bigint(&top, &den),
                fast::crossover::div_flip(&top, &den),
                by_num_bigint.units,
                by_reciprocal.units,
                sq.units,
                meter.unit()
            );
        }
    }

    /// BENCH-pow-mid-width-base: `b^e` for a result of about n words and bases of 1 to n/16
    /// words (by 16 words from 64 to 128, around the switch), `e` with all its bits set (the
    /// most products), by squaring right to left and left to right with [`fast::mul`], the two
    /// orders [`fast::pow`] chooses between. Prints the instructions of each; `fast::pow`'s
    /// switch (`POW_LEFT_WORDS`) goes where the ratio crosses 1.
    #[test]
    fn powers_by_width_of_the_base() {
        fn left_to_right(base: &BigUint, e: u64) -> BigUint {
            let mut m = BigUint::one();
            for i in (0..64 - e.leading_zeros()).rev() {
                m = fast::mul(&m, &m);
                if e >> i & 1 == 1 {
                    m = fast::mul(&m, base);
                }
            }
            m
        }
        fn right_to_left(base: &BigUint, mut e: u64) -> BigUint {
            let (mut b, mut r) = (base.clone(), BigUint::one());
            while e > 0 {
                if e & 1 == 1 {
                    r = fast::mul(&r, &b);
                }
                e >>= 1;
                if e > 0 {
                    b = fast::mul(&b, &b);
                }
            }
            r
        }
        let mut meter = scaling::Meter::new();
        // Counted here, not by a check (BENCH-self-counted-meters-processor-time).
        if scaling::ran_alone_in_a_new_process(&meter) {
            return;
        }
        for n in [1usize << 12, 1 << 15] {
            let mut w = 1;
            while w <= n / 16 {
                // e = 2^k - 1 with w e of about n words.
                let k = (n / w).ilog2().max(1);
                let e = (1u64 << k) - 1;
                let base = number(w, 29 + w as u64);
                let want = fast::pow(&base, e);
                assert_eq!(left_to_right(&base, e), want);
                assert_eq!(right_to_left(&base, e), want);
                let rl = meter.least(
                    || {},
                    || assert_eq!(right_to_left(&base, e).bits(), want.bits()),
                );
                let lr = meter.least(
                    || {},
                    || assert_eq!(left_to_right(&base, e).bits(), want.bits()),
                );
                eprintln!(
                    "pow n={n} base_words={w} e={e}: right_to_left instr={} left_to_right \
                     instr={} ratio={:.3} ({})",
                    rl.units,
                    lr.units,
                    lr.units as f64 / rl.units as f64,
                    meter.unit()
                );
                w = if (64..128).contains(&w) {
                    w + 16
                } else {
                    w * 2
                };
            }
        }
    }
}
