//! The benchmarks of `r4_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//!
//! The graph-coloring benchmarks scale the coloring at [`COLORS`] (8,000) without the CRT
//! that joins its witness, and measure the whole question against its coloring and its CRT
//! ([`against_its_crt`], PNCX-coloring-crt-scale). The witness is one integer built by
//! `Int::crt` from one prime modulus per vertex, O(M(N) log k) for `k` moduli of `N`
//! bits in all, with `N` about `k log k`; that grows faster than the limit of 10.5 at 8n allows
//! once the integers are wide, and no smaller witness exists in general (the product of the
//! moduli is its period). Measured 2026-11-14 with the CRT (instructions at 8n): 8.4 to 8.9 at
//! n = 32, 8.9 to 10.7 at 256, 11.8 to 14.9 at 4000, 12.3 to 13.2 at 24,000 to 80,000, most
//! of the work in big-integer multiplication; the benchmarks stayed at n = 32 until then. The
//! coloring alone, 2026-11-22 on a VM: 8.19 to 8.69 at 16,000 (CPU time).
//! The other benchmarks are sized (2026-11-14) so the 1x case takes about 0.3 to 1 s, or less
//! where building the inputs takes most of the piece, and a piece stays under 20 s.

use super::*;

#[test]
fn pncx_pure_bounds_scale() {
    let inputs = scaling::inputs(64_000, |n| pure_constraints(n, false));
    scaling::check_order("pure bounds with separate holes", 64_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

#[test]
fn pncx_pure_residues_scale() {
    let inputs = scaling::inputs(64_000, |n| pure_constraints(n, true));
    scaling::check_order(
        "pure residue constraints with separate holes",
        64_000,
        1,
        |n| {
            assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
        },
    );
}

#[test]
fn pncx_domain_membership_scale() {
    let inputs = scaling::inputs(2_048_000, |n| {
        Domain::from_pieces(
            (0..n)
                .map(|i| (Some(Int::from(3 * i as i64)), Some(Int::from(3 * i as i64))))
                .collect(),
        )
    });
    scaling::check_instructions_only(
        "membership in disjoint bound intervals",
        2_048_000,
        1,
        |n| {
            for i in 0..n {
                let yes = Some(Int::from(3 * i as i64));
                let no = Some(Int::from(3 * i as i64 + 1));
                assert!(inputs[&n].contains_span(&yes, &yes));
                assert!(!inputs[&n].contains_span(&no, &no));
            }
        },
    );
}

#[test]
fn pncx_kept_prefix_scale() {
    let inputs = scaling::inputs(32_000, prefix_formula);
    scaling::check_order("kept conjunction prefixes", 32_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

#[test]
fn pncx_connected_colors_scale() {
    let n = COLORS;
    let inputs = scaling::inputs(n, connected_color_system);
    scaling::check_order("color connected triangles by removal order", n, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_choices(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_independent_components_scale() {
    let n = COLORS;
    let inputs = scaling::inputs(n, color_system);
    scaling::check_order("color independent triangles", n, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_choices(info, allowed, clauses).is_some());
    });
    for (what, system) in [
        ("independent residue components", &inputs[&n]),
        ("connected residue components", &connected_color_system(n)),
    ] {
        let (info, allowed, clauses) = system;
        against_its_crt(what, system, || {
            // Keep the measured assertion weak so the old path's slower
            // Undecided result is caught by the cost check itself.
            assert!(!matches!(
                solve_coprime_system(&None, &None, info, allowed.clone(), clauses.clone(), true),
                RegimeOut::Empty
            ));
        });
    }
}

#[test]
fn pncx_lower_witness_scale() {
    let inputs = scaling::inputs(2_048_000, |n| {
        (2..n + 2)
            .map(|m| (Int::from(m), vec![(Int::ONE, Int::from(m - 1))]))
            .collect::<BTreeMap<_, _>>()
    });
    // This routine allocates no bytes on word-sized inputs.
    scaling::check_instructions_only(
        "one candidate from residue lower bounds",
        2_048_000,
        1,
        |n| {
            std::hint::black_box(lower_witness(&Int::from(1000003), &None, &inputs[&n], &[]));
        },
    );
}

#[test]
fn pncx_bound_merge_formula_scale() {
    let inputs = scaling::inputs(30_000, bound_merge_formula);
    scaling::check_order("bound merging in a modular formula", 30_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

#[test]
fn pncx_bound_partition_scale() {
    let inputs = scaling::inputs(1_536_000, bound_partition_input);
    scaling::check_order("partition disjoint global bounds", 1_536_000, 1, |n| {
        let (global, clauses) = &inputs[&n];
        let out = partition_into_regimes(global, clauses);
        assert_eq!(out.len(), 2 * n);
        std::hint::black_box(out);
    });
}

#[test]
fn pncx_common_factor_scale() {
    let inputs = scaling::inputs(512, shared_moduli);
    scaling::check_order("common factor with coprime cofactors", 512, 1, |n| {
        std::hint::black_box(coprime_factorization(&inputs[&n]));
    });
}

/// U1, the sparse side of `shares_a_factor`: moduli `2 p` for the first n primes `p = 1 mod 4`.
/// The cofactors are about half as dense as the odd primes, so their largest is above their
/// bits at both sizes (asserted on the inputs) and the table does not answer. Until
/// PERF-negated-chain-unsolved (negchain1, 2026-11-20) the product tree and remainder tree did,
/// O(M(B) log k): 16.105 at 512 and 4096 (load 41 to 43). Now at least `FACTOR_INPUTS` (4096)
/// word values of at most `FACTOR_BITS` (44) bits are each factored into primes
/// (`zed_numtheory::shares_a_factor_by_factoring`, proof and cost at zed-kernel
/// `num/coprime.rs` `FACTOR_BITS`), so both sizes here, 4096 and 32768 cofactors of 15 to 19
/// bits, take that path; fewer values take the trees, at most 4096 of 44 bits, a bounded size.
/// The switch itself is benched on both sides by zed-benches' `crossover factor-bits`.
/// Measured 2026-11-20 at 4096 and 32768: 23,886,782 / 204,386,090 instructions, 8.556, bytes
/// 8.0 (load 76); at 512 and 4096 (the old sizes, across the switch, so not a test of either
/// side): 6.683 (load 42). Above 8 as the primes widen from about 2^16 to 2^19 with `n`, and a
/// primality test costs O(log p) word products: 8 * 19 / 17 = 8.9 at most (inferred, not
/// profiled).
#[test]
fn pncx_common_factor_tree_side_scale() {
    let inputs = scaling::inputs(4096, |n| {
        let mut ms = BTreeSet::new();
        let mut p = 5i64;
        while ms.len() < n {
            if (3..)
                .step_by(2)
                .take_while(|d| d * d <= p)
                .all(|d| p % d != 0)
            {
                ms.insert(Int::from(2 * p));
            }
            p += 4;
        }
        let cofactors: Vec<Int> = ms.iter().map(|m| m.div_floor(&Int::from(2))).collect();
        assert!(zed_kernel::num::coprime::dense_values(&uint_leaves(&cofactors)).is_none());
        ms
    });
    scaling::check_order(
        "common factor with coprime cofactors, sparse side",
        4096,
        1,
        |n| {
            std::hint::black_box(coprime_factorization(&inputs[&n]));
        },
    );
}

/// `x = q_i (2 p_i) + 2 i` for the first `n` odd primes `p_i` ([`shared_moduli`]), through
/// `solve_modular`: every modulus shares the factor 2 and the remainders are all even, so a
/// point exists, and the moduli's coprime base is 2 and the `p_i` (from the probe
/// `pncx_shared_formula_axis` of PERF-negated-chain-unsolved).
///
/// The decision-only solver checks compatibility on the coprime bases via
/// `private_quotient_consistency`. Reconstruction is needed when a model is requested.
#[test]
fn pncx_shared_formula_scale() {
    let inputs = scaling::inputs(1024, shared_formula);
    scaling::check_order("residues over moduli sharing 2", 1024, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

/// The first n odd primes: no shared factor, and every modulus is its own base. On the table
/// side of the kernel's `shares_a_factor` at both sizes (asserted on the inputs). (The bench
/// of both its methods on both sides of their condition is zed-kernel's
/// `the_shared_factor_crossover_axis` since DRY-coprime-bases-one.)
#[test]
fn pncx_coprime_dense_scale() {
    let inputs = scaling::inputs(32_000, |n| {
        let primes = odd_primes(n);
        assert!(on_the_table_side(
            &primes.iter().cloned().collect::<Vec<_>>()
        ));
        primes
    });
    scaling::check_order(
        "coprime moduli from a table of least prime factors",
        32_000,
        1,
        |n| {
            let facs = coprime_factorization(&inputs[&n]);
            assert_eq!(facs.len(), n);
        },
    );
}

/// The fixed switches of zed-kernel's scaled remainder tree to the exact descent by the width of
/// the nodes (`trees::scaled_descend_switch`, before PERF-remainders-switch-by-cost at 128
/// words), here so that zed-kernel is built with its own multiplication constants (its own
/// tests build it with the test ones): at switch widths from 0 (the scaled remainder tree
/// to the leaves) to past every node (the exact descent from the root), on the CRT cofactor sum
/// `S mod P` over the first 2,048 / 16,384 / 131,072 odd primes and on `x = P - 1 - P / 8` over
/// word leaves, 8-word, 64-word and 512-word leaves and 2, 4, .., 2^200; prints the instructions
/// and bytes of each and holds the remainders equal at every width. The measurements of the
/// fixed switch are in COMPLEXITY.md, "PERF-crt-tree-scaled-remainder"; `trees::remainders`
/// chooses its turn by cost, measured against these by `the_remainders_take_the_cheaper_method`.
#[test]
fn the_scaled_to_exact_switch_axis() {
    use num_bigint::BigUint;
    use zed_kernel::num::{rem_uint, trees};
    let mut meter = scaling::Meter::new();
    let (mut rng, _seed) = crate::seed::Rng::fresh("scaled_to_exact_axis");
    let mut odd = |words: usize| -> BigUint {
        let digits: Vec<u32> = (0..2 * words).map(|_| rng.next_u64() as u32).collect();
        BigUint::new(digits) | BigUint::from(1u32) | (BigUint::from(1u32) << (64 * words - 1))
    };
    let primes = |k: usize| -> Vec<BigUint> {
        let mut out = Vec::with_capacity(k);
        let mut c = 3u64;
        while out.len() < k {
            if zed_numtheory::is_prime(c) {
                out.push(BigUint::from(c));
            }
            c += 2;
        }
        out
    };
    let mut families: Vec<(String, Vec<BigUint>, bool)> = [2048, 16384, 131072]
        .map(|k| (format!("cofactors of {k} odd primes"), primes(k), true))
        .into();
    families.push((
        "4096 word leaves".into(),
        (0..4096).map(|_| odd(1)).collect(),
        false,
    ));
    families.push((
        "512 leaves of 8 words".into(),
        (0..512).map(|_| odd(8)).collect(),
        false,
    ));
    families.push((
        "32 leaves of 64 words".into(),
        (0..32).map(|_| odd(64)).collect(),
        false,
    ));
    families.push((
        "256 leaves of 64 words".into(),
        (0..256).map(|_| odd(64)).collect(),
        false,
    ));
    families.push((
        "32 leaves of 512 words".into(),
        (0..32).map(|_| odd(512)).collect(),
        false,
    ));
    families.push((
        "2, 4, .., 2^200".into(),
        (1..=200u32).map(|i| BigUint::from(1u32) << i).collect(),
        false,
    ));
    for (name, leaves, cofactors) in families {
        let levels = trees::product_tree(&leaves);
        let p = trees::tree_product(&leaves, &levels).into_owned();
        let x = if cofactors {
            let ones = vec![BigUint::from(1u32); leaves.len()];
            rem_uint(&trees::linear_combination_up(ones, &leaves, &levels), &p)
        } else {
            &p - 1u32 - (&p >> 3u32)
        };
        let mut want = None;
        for w in [0u64, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 1 << 40] {
            let mut got = Vec::new();
            let m = meter.work(|| got = trees::scaled_descend_switch(&x, &p, &leaves, &levels, w));
            eprintln!(
                "scaled_to_exact {name}, P {} words, switch at {w} words: {} instructions, {} bytes",
                p.bits().div_ceil(64),
                m.units,
                m.bytes
            );
            match &want {
                None => want = Some(got),
                Some(first) => assert_eq!(first, &got, "{name}, switch at {w} words"),
            }
        }
    }
}

/// `trees::remainders` takes, within 10%, the instructions of the cheapest of the fixed methods
/// `trees::scaled_descend_switch` offers: the exact descent from the root (switch past every
/// node), the scaled tree to the leaves (switch 0) and the scaled tree down to nodes of 128
/// words, the switch measured best on most families (PERF-crt-tree-scaled-remainder). On word
/// leaves, 8-word, 64-word and 512-word leaves and 2, 4, .., 2^200, with `x` the top 1/2, 7/8
/// and all of the bits of `P`, and on the CRT cofactor sum over 2,048 odd primes. Built here, in
/// a crate that builds zed-kernel with its real multiplication constants. Before
/// PERF-remainders-switch-by-cost the switch was on the width of `x` alone (from 7/8 of `P` the
/// scaled tree), and 1,024 word leaves at 7/8 took the scaled tree at 1.5 times the descent's
/// instructions.
#[test]
fn the_remainders_take_the_cheaper_method() {
    use num_bigint::BigUint;
    use zed_kernel::num::{rem_uint, trees};
    let mut meter = scaling::Meter::new();
    let (mut rng, _seed) = crate::seed::Rng::fresh("remainders_cheaper_method");
    let mut odd = |words: usize| -> BigUint {
        let digits: Vec<u32> = (0..2 * words).map(|_| rng.next_u64() as u32).collect();
        BigUint::new(digits) | BigUint::from(1u32) | (BigUint::from(1u32) << (64 * words - 1))
    };
    let mut primes = Vec::with_capacity(2048);
    let mut c = 3u64;
    while primes.len() < 2048 {
        if zed_numtheory::is_prime(c) {
            primes.push(BigUint::from(c));
        }
        c += 2;
    }
    let families: Vec<(&str, Vec<BigUint>)> = vec![
        ("cofactors of 2048 odd primes", primes),
        ("1024 word leaves", (0..1024).map(|_| odd(1)).collect()),
        ("512 leaves of 8 words", (0..512).map(|_| odd(8)).collect()),
        ("32 leaves of 64 words", (0..32).map(|_| odd(64)).collect()),
        (
            "32 leaves of 512 words",
            (0..32).map(|_| odd(512)).collect(),
        ),
        (
            "2, 4, .., 2^200",
            (1..=200u32).map(|i| BigUint::from(1u32) << i).collect(),
        ),
    ];
    let mut worst = (0.0f64, String::new());
    let key = match meter.instructions {
        true => "instr",
        false => "work",
    };
    for (name, leaves) in families {
        let levels = trees::product_tree(&leaves);
        let p = trees::tree_product(&leaves, &levels).into_owned();
        let n = p.bits();
        let xs: Vec<(String, BigUint)> = match name.starts_with("cofactors") {
            true => {
                let ones = vec![BigUint::from(1u32); leaves.len()];
                let s = trees::linear_combination_up(ones, &leaves, &levels);
                vec![("S".into(), rem_uint(&s, &p))]
            }
            false => [(1u64, 2u64), (7, 8), (1, 1)]
                .map(|(num, den)| {
                    let x = &p >> (n - n * num / den);
                    let x = if x == p { &x - 1u32 } else { x };
                    (format!("{num}/{den}"), x)
                })
                .into(),
        };
        for (width, x) in xs {
            let mut want = Vec::new();
            let got = meter.work(|| want = trees::remainders(&x, &leaves, &levels));
            let mut best = f64::INFINITY;
            for w in [1u64 << 40, 0, 128] {
                let mut other = Vec::new();
                let m = meter
                    .work(|| other = trees::scaled_descend_switch(&x, &p, &leaves, &levels, w));
                assert_eq!(want, other, "{name} at {width}, switch at {w} words");
                best = best.min(m.units as f64);
            }
            let ratio = got.units as f64 / best;
            eprintln!(
                "remainders {name} at {width}: {key}={}, the cheapest fixed method {key}={best}, \
                 ratio {ratio:.3}",
                got.units
            );
            if ratio > worst.0 {
                worst = (ratio, format!("{name} at {width}"));
            }
        }
    }
    // The limit 1.1, from the variation measured on v5e2 (DynamoRIO, 2026-11-23,
    // PERF-remainders-switch-by-cost): at one seed every count repeats to the instruction
    // (3 runs at seed 777), so the meter adds nothing. Across 5 fresh seeds and seed 777 the
    // random families' counts move with the input (32 leaves of 512 words at 1/2: 503.1 M to
    // 525.7 M for the cheapest fixed method, 4.5 %), but `remainders` moves with it, and no
    // family's ratio moved by more than 0.002; the deterministic powers of 2 moved by at most 4
    // instructions. The worst ratio measured is 1.092 to 1.093 (2, 4, .., 2^200 at 1/1, where
    // the descent is chosen and a turn at level 2 is 5 % cheaper: the cost model counts a
    // power-of-2 node's products as dense), and 1.083 at 1/2 (the estimate's 38,700
    // instructions on a descent of 284,000), so 1.1 is 0.007 above the worst, three times the
    // variation, and below it the test would fail on the cost model's known error alone.
    // Processor time, the meter of a run not started alone with `--exact` where the hardware
    // counts no instructions (`scaling::Meter::new`), changes with load, so it is allowed
    // `scaling::TIME_ALLOWANCE` times the limit, as every check of the harness allows it
    // (measured: 1.736 on 512 leaves of 8 words at 7/8 in a run of the whole crate with 8
    // threads, 1.017 in instructions).
    let limit = match meter.instructions {
        true => 1.1,
        false => 1.1 * scaling::TIME_ALLOWANCE,
    };
    assert!(
        worst.0 <= limit,
        "remainders took {:.3} times the cheapest method's {} on {}, at most {limit}",
        worst.0,
        meter.unit,
        worst.1
    );
}

/// The intersection of n domains, each all integers but one hole. Deferred by
/// TESTS-scaling-limit-10_5 (12.2 times the bytes at 64 and 512 on cdf07ac4f, merged in a
/// balanced tree, which copied the pieces on each of its `log2 n` levels); back with row
/// PRES-scaling-10_5. `pncx_bound_merge_enumeration` and
/// `pncx_bound_merge_of_mixed_domains_matches_the_fold` check the answer.
///
/// The cost is O(n log n), proof: the clone of the input, two pieces a domain, and each
/// domain's complement, its one hole, cost O(1) a domain; the `n` holes are sorted by lower
/// end, O(n log n) compares of numbers of at most `log2(3n)` bits, one or two words;
/// `complement_spans` reads them once, O(n). The bytes are O(n): no step keeps more than the
/// `2n` pieces of the input, the `n` holes and the `n + 1` pieces of the answer. So the ratio
/// is held to that of n log n, 10.0 at 4096 (`check_n_log_n`; at 64 it is 12, past the limit
/// of 10.5 that n log n meets only from 777). Measured 7.97 times the instructions and 8.0
/// times the bytes at 4096 and 32768; the balanced tree's fold of pairs put back in its place
/// (negative control, not committed) took 63.4 times.
#[test]
fn pncx_bound_merge_scale() {
    let inputs = scaling::inputs(4096, holes);
    scaling::check_n_log_n("bound intersection of n one-hole domains", 4096, |n| {
        std::hint::black_box(intersect_domains(inputs[&n].clone()));
    });
}
