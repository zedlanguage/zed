//! The checks of `s22.rs` at `n` and `8n`: the preimage of each chain family, of remainder
//! chains and of chains over holes, each held to the order COMPLEXITY.md S22 gives. Each
//! term is built before the timing; `s22.rs` checks the same families at small sizes against
//! the interpreter and the reference preimage.

use zed_kernel::{Prim, Term};
use zed_tests::scaling;
use zedc::store::preimage::{Demand, forward_pieces, preimage};
use zedc::store::preimage_ref as before;

use crate::s22::*;

/// Runs `f` on a thread with a 256 MiB stack, deep enough for chains of thousands of terms: the
/// chains of the benchmarks here and in `bench::ref_memo` overflow a default 2 MiB stack. The
/// tests of `s22.rs` and `ref_memo.rs` run on the default stack (author P178).
pub(crate) fn on_big_stack<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    std::thread::scope(|s| {
        let thread = std::thread::Builder::new().stack_size(1 << 28);
        thread.spawn_scoped(s, f).unwrap().join().unwrap()
    })
}

#[test]
fn chain_probe_scales() {
    scales("probe", 256);
}

#[test]
fn chain_live_scales() {
    scales("live", 256);
}

/// The probe with `i` over all integers: the arm `t + 1` leaves `i64` at `i = i64::MAX`,
/// where the guard keeps `t`, so the summary checks only the values each arm keeps.
#[test]
fn chain_probe_all_scales() {
    scales("probe_all", 256);
}

/// The probe with `i` over the half-line `[-100, inf)`.
#[test]
fn chain_probe_half_scales() {
    scales("probe_half", 256);
}

/// The probe with `i` in `[-100, 2^62]`: an end of the domain plus an end of the demand met
/// with the hull passes `i64::MAX`. Until S22-WIDE `Tx::fits` turned the summary and the clip
/// off there and the transfer before ran, at about `k^2.8` (30 s at `k = 2048`); the summary
/// now holds its values in `i128`, so the clip stays on.
#[test]
fn chain_probe_wide_scales() {
    scales("probe_wide", 256);
}

/// The probe with `i` in `[-100, i64::MAX]`: the domain's end at the end of `i64`, which the
/// summary read as an infinity until S22-WIDE, and so gave up on, leaving the transfer before.
#[test]
fn chain_probe_max_scales() {
    scales("probe_max", 256);
}

#[test]
fn chain_alt_scales() {
    scales("alt", 256);
}

#[test]
fn chain_cj_scales() {
    scales("cj", 256);
}

#[test]
fn chain_eq0_scales() {
    scales("eq0", 256);
}

#[test]
fn chain_range_scales() {
    scales("range", 256);
}

#[test]
fn chain_gt_scales() {
    scales("gt", 256);
}

#[test]
fn chain_swapped_scales() {
    scales("swapped", 256);
}

#[test]
fn chain_constfirst_scales() {
    scales("constfirst", 256);
}

#[test]
fn chain_sub_scales() {
    scales("sub", 256);
}

#[test]
fn chain_twoin_scales() {
    scales("twoin", 256);
}

#[test]
fn chain_conj_scales() {
    scales("conj", 256);
}

#[test]
fn chain_conj_live_scales() {
    scales("conj_live", 256);
}

#[test]
fn chain_cross_scales() {
    scales("cross", 256);
}

#[test]
fn chain_abs_guard_scales() {
    scales("abs_guard", 256);
}

#[test]
fn chain_ne_guard_scales() {
    scales("ne_guard", 256);
}

#[test]
fn chain_pow2_scales() {
    scales("pow2", 256);
}

#[test]
fn chain_jt_scales() {
    scales("jt", 256);
}

#[test]
fn chain_jt_range_scales() {
    scales("jt_range", 256);
}

/// The chain whose else arms reflect, `j - t`, over `[-k, k]` with `tk` in `[-3, 7]`: each
/// level reflects the demands of the one above about a new constant. The summary reads `c - t`
/// since plan item S22b-rest and inverts the demand once: 10.6 times the instructions at
/// `k` = 256 and 2,048, and 8.8 and 21 ms at 256 and 512. Before, the transfer read the chain
/// level by level: 63.4 times, and 3.36 and 8.64 s at 256 and 512 (load about 85 to 110).
#[test]
fn chain_jt_range_live_scales() {
    scales("jt_range_live", 256);
}

#[test]
fn chain_five_range_live_scales() {
    scales("five_range_live", 256);
}

#[test]
fn chain_min_scales() {
    scales("min", 256);
}

/// The probe with the guard spelled `j <= i`.
#[test]
fn chain_le_scales() {
    scales("le", 256);
}

/// The probe asked `tk >= -3 && tk <= 7`: two comparisons of the shared chain under `&&`.
#[test]
fn chain_rangeand_scales() {
    scales("rangeand", 256);
}

/// The live families, `i` in `[-k, k]`: no demand merges with another.
#[test]
fn chain_alt_live_scales() {
    scales("alt_live", 256);
}

#[test]
fn chain_eq0_live_scales() {
    scales("eq0_live", 256);
}

#[test]
fn chain_range_live_scales() {
    scales("range_live", 256);
}

/// `c_j = j` over `[-k, k]`: before S22a 28.9 times the instructions at 8 and 64 (cross-review
/// xs22, VERIFY_CLAUDE.md).
#[test]
fn chain_cj_live_scales() {
    scales("cj_live", 256);
}

/// `c_j = ±j`, the sign alternating with `j`.
#[test]
fn chain_altj_scales() {
    scales("altj", 256);
}

/// `c_j = ±j` over `[-k, k]`: before S22a 216 times the instructions at 8 and 64 (cross-review
/// xs22, VERIFY_CLAUDE.md).
#[test]
fn chain_altj_live_scales() {
    scales("altj_live", 256);
}

#[test]
fn chain_ne0_scales() {
    scales("ne0", 256);
}

/// Else arm `0 - (t + 1)`, under an integer demand of two pieces on both signs.
#[test]
fn chain_neg_scales() {
    scales("neg", 256);
}

/// Else arm `-2 * t`, under an integer demand of two pieces on both signs: `tk` reaches
/// `50 * 2^k`, which passes `i128` from `k = 122`, where the summary's coefficients and values
/// become big integers (`Int`; COMPLEXITY.md S22, `mul`). From 32 to 256 the chain crosses that
/// size.
#[test]
fn chain_mul_across_i128_scales() {
    scales("mul", 32);
}

/// `mul` past `i128` at both sizes, its ends a bit longer at each level.
#[test]
fn chain_mul_scales() {
    scales("mul", 256);
}

/// The chain that leaves `i64`, with no point meeting `t_k >= 0`.
#[test]
fn chain_t3_gaps_scales() {
    scales("t3_gaps", 256);
}

#[test]
fn chain_mod7_scales() {
    scales("mod7", 256);
}

/// `cross` with every guard inside the inputs' width, so that the relation is asked at both
/// sizes (from `k = 100` on, the transfer's box is exact and the relation is not needed).
#[test]
fn chain_cross_within_its_width_scales() {
    scales("cross", 6);
}

/// `cross` from `k = 12` to `96`: at 96 the formula implies `i >= 47`, and the disjuncts
/// `i <= j - 1` for `j` up to 47 have no point. Each was refuted by its own full propagation
/// in `probe`, about `k (k - 50)` settles in all: 99.5 M and 3.98 G bytes, 40.0 times (ledger
/// LIN-probe-refute). Since then one search over the bounds those disjuncts write finds
/// `i >= 47` with `O(log k)` propagations and refutes them all: 1.00 G bytes, 10.1 times, and
/// 3.74 G instructions against 0.30 G at 12, 12.3 times.
#[test]
fn chain_cross_above_its_width_scales() {
    scales("cross", 12);
}

/// `cross_dead` (`cross` with its inputs two narrower than the chain is long) has its only
/// point outside the demand at an end, `i = k - 2` and `m = 2 - k`. The greedy search over
/// disjunctions keeps `i` where the first solution put it and fails, and the failed-literal
/// search then tests the `2k` disjuncts. It tested each with a full propagation, about `k^2.4`
/// in all (0.26, 1.40, 7.2 and 39.4 G instructions at `k` = 10, 18, 34, 66); since LIN-probe
/// it keeps without a propagation each disjunct that a point found so far meets (2.88 G at
/// `k = 66`). On `cross` from `k = 51` to `99` the `k - 50` guards `j > 50` that no input meets
/// were each still refuted by one full propagation (2.0 G at 52, was 22.9 G; 1.05 G at 48), and since
/// LIN-probe-refute by one search over their bounds (`chain_cross_above_its_width_scales`).
#[test]
fn chain_cross_dead_scales() {
    scales("cross_dead", 8);
}

/// COMPLEXITY.md S22e-quad: the `2k + 1` classes of `k` distinct remainders share one reading
/// of the chain. Each class runs the transfer from the root to the chain's top `if`, whose
/// summary in that class is read from one summary of the chain over all classes, built once.
/// Before, the whole chain was read again in each class: 58.0 times the instructions at 32
/// and 256 (200,279,152 against 11,615,272,274); now about 8.5 times.
#[test]
fn many_remainders_scales() {
    on_big_stack(|| {
        let n = 32;
        let (a, b) = (many_remainders(n), many_remainders(n * scaling::FACTOR));
        scaling::check("the preimage of the chain of k remainders", n, |k| {
            let (t, ds, d) = if k == n { &a } else { &b };
            preimage(t, ds, d);
        });
    });
}

/// COMPLEXITY.md S22e-quad: over one period the transfer over the box reads every guard on the
/// remainder exactly, and where a class's run reads a guard by itself the split by classes
/// costs one transfer of the chain per class. In both the transfer runs first, as before the
/// split was moved ahead of it. With the split run first, from 8 to 64 the `min` chain took
/// 45.3 times the instructions, from 16 to 128 the `!=` chain 45.7 times and the tests above
/// the chain 64.8 times (21.0M against 1361.2M); the transfer alone is linear in all three.
#[test]
fn remainders_read_by_each_class_keep_the_transfer_first_scales() {
    on_big_stack(|| {
        let ds = i_in(0, 1000);
        let d = Demand::Bool(true);
        let n = 8;
        let (a, b) = (min_remainders(n), min_remainders(n * scaling::FACTOR));
        scaling::check("the preimage of the min chain of k remainders", n, |k| {
            preimage(if k == n { &a } else { &b }, &ds, &d);
        });
        let n = 16;
        let (a, b) = (no_remainder_of(n), no_remainder_of(n * scaling::FACTOR));
        scaling::check("the preimage of k remainders excluded", n, |k| {
            preimage(if k == n { &a } else { &b }, &ds, &d);
        });
        let n = 16;
        let (a, b) = (above_remainders(n), above_remainders(n * scaling::FACTOR));
        scaling::check("the preimage of k tests above k remainders", n, |k| {
            preimage(if k == n { &a } else { &b }, &ds, &d);
        });
    });
}

/// COMPLEXITY.md S22e-wide: the four programs of the plan item over `[-5000, 5000]`, about ten
/// periods of 1024. On main before it, from `k` to `2k`: the `min` chain about `k^2.7` (26.6M,
/// 136.8M and 868.8M instructions at `k` = 8, 16 and 32), the tests above the chain `k^2`
/// (28.3M and 109.1M at 16 and 32), the `!=` chain 249M and 763M at 4 and 8, and the chain
/// below `i mod 1024 == 0` 1.59G and 5.16G at 4 and 8; main left all but the first inexact.
/// Now, from `k` to `8k`, 2.24M to 17.6M (`k` = 8), 6.44M to 53.7M (16), 17.3M to 20.6M (4)
/// and 85.9M to 498M (4), and all four are exact.
#[test]
fn remainders_over_many_periods_scale() {
    on_big_stack(|| {
        let ds = i_in(-5000, 5000);
        let d = Demand::Bool(true);
        let families = [
            (
                "the min chain of k remainders",
                8,
                min_remainders as fn(usize) -> Term,
            ),
            ("k tests above k remainders", 16, above_remainders),
            ("k remainders excluded", 4, no_remainder_of),
            ("k remainders below i mod 1024 == 0", 4, zero_excluded),
        ];
        for (what, n, family) in families {
            let (a, b) = (family(n), family(n * scaling::FACTOR));
            scaling::check(what, n, |k| {
                preimage(if k == n { &a } else { &b }, &ds, &d);
            });
        }
    });
}

/// COMPLEXITY.md S22-transfer-rem: the three shapes the split by remainders does not answer
/// alone (arms of an `if` reading different inputs, a test of a term that reads a remainder,
/// remainders of two inputs), each over a chain of `k` guards `x mod 3 == r` across 40
/// periods, take work of order `k` from `k` to `8k`.
#[test]
fn remainder_reads_outside_a_split_scale() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(60), Demand::Bool(true));
        for shape in [
            "arms of x and y",
            "a test of the chain",
            "remainders of two inputs",
        ] {
            let n = 8;
            let terms = scaling::inputs(n, |k| {
                remainder_shape(shape, moved_remainder_chain(1, k, "x", 3))
            });
            scaling::check(shape, n, |k| {
                preimage(&terms[&k], &ds, &d);
            });
        }
    });
}

/// COMPLEXITY.md S22-linear-rem: the linear stage on what the counted chain of `k` guards
/// `x mod 3 == j mod 3` leaves, in `c <= 2 && y mod 2 == 0` and `c <= 2 && x mod 2 == 0` over
/// `x` and `y` in `[-100000, 100000]`, does work of order `k` from `k` to `8k`. Level by
/// level, one variable for each guard read together by the solver, it took 0.66 s at
/// `k = 15` and 24.6 s at `k = 120`; written by the chain's summaries over the classes of
/// `x mod 3`, it is one variable with a case for each piece of each range of classes.
#[test]
fn remainder_chains_in_the_linear_stage_scale() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(100000), Demand::Bool(true));
        for (shape, at) in [("c <= 2 && y mod 2 == 0", 3), ("c <= 2 && x mod 2 == 0", 4)] {
            let n = 5;
            let terms = scaling::inputs(n, |k| {
                counted_shapes(counted_remainder_chain(k, 3))[at].clone()
            });
            scaling::check(shape, n, |k| {
                preimage(&terms[&k], &ds, &d);
            });
        }
    });
}

/// COMPLEXITY.md S22-case-cuts and S22-hole-summaries: the linear stage on the chain of
/// [`spread_remainder_chain`], whose cases would be `O(k^2)` cut at every other range's starts
/// or at every hole of the domain, does work of order `k` from `k` to `8k`.
#[test]
fn remainder_cases_cut_at_their_neighbors_scale() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(100000), Demand::Bool(true));
        let n = 8;
        let terms = scaling::inputs(n, |k| below_three_and_even_y(spread_remainder_chain(k)));
        scaling::check("cases of a spread remainder chain", n, |k| {
            preimage(&terms[&k], &ds, &d);
        });
    });
}

/// COMPLEXITY.md S22-hole-summaries: the linear stage on the chain of
/// [`select_remainder_chain`], whose slices would be `O(k^2)` cut at every hole of the
/// domain, does work of order `k` from `k` to `8k`.
#[test]
fn remainder_cases_sliced_by_a_test_scale() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(100000), Demand::Bool(true));
        let n = 8;
        let terms = scaling::inputs(n, |k| below_three_and_even_y(select_remainder_chain(k)));
        scaling::check("cases of a sliced remainder chain", n, |k| {
            preimage(&terms[&k], &ds, &d);
        });
    });
}

/// COMPLEXITY.md S22-fwd-holes: the forward transfer of the levels of
/// [`spread_remainder_chain`], with `64k` holes in the domain of `x`, in the second program of
/// [`counted_shapes`], makes integer sets of pieces of order `k`, from `k` to `8k`: the domain
/// of `x` is shared, not copied, and a join or a `max` keeps its operands and its bounds, so
/// no set lists the holes again where no reader asks for its pieces. Copying the holes into
/// each level's set made `O(k * H)` pieces.
#[test]
fn forward_sets_of_a_chain_share_the_holes_scale() {
    on_big_stack(|| {
        let d = Demand::Bool(true);
        let n = 8;
        let made = |k: usize| {
            let t = counted_shapes(spread_remainder_chain(k))[1].clone();
            let ds = x_with_holes(64 * k);
            forward_pieces();
            let p = preimage(&t, &ds, &d);
            assert!(p.exact, "the preimage at k = {k} is exact");
            forward_pieces()
        };
        let (small, large) = (made(n), made(scaling::FACTOR * n));
        assert!(small > 0, "the forward transfer makes sets");
        scaling::hold(
            &format!(
                "pieces of the forward sets: sizes {n} and {}",
                scaling::FACTOR * n
            ),
            "pieces",
            small,
            large,
            1,
        );
    });
}

#[test]
fn the_box_of_a_chain_over_many_holes_is_tested_in_linear_work() {
    the_box_of_a_chain_over_holes_is_tested_in_linear_work(128);
}

#[test]
fn the_box_of_a_chain_over_more_holes_is_tested_in_linear_work() {
    the_box_of_a_chain_over_holes_is_tested_in_linear_work(512);
}

/// `c - i` with `c = 4n + 3` under a demand of `2n` pieces, `n` on each side of zero, by the
/// transfer before: the reflections of the demand's pieces are all positive, so the forward
/// image of `{c} - z` caps them to the `n` pieces of one sign region of an operand and has
/// holes, and the box is exact only because the domain of `i`, the reflection itself, takes no
/// value in them (S22-exact-mislabel). The check (the reflection of the demand, the image less
/// it, and the meet with the forward image of `i`) costs `O(n log n)` at most.
#[test]
fn constant_minus_holes_scale() {
    let case = |n: usize| {
        let n = n as i64;
        let c = 4 * n + 3;
        let z = pieces(&(-n..n).map(|j| (4 * j, 4 * j + 1)).collect::<Vec<_>>());
        let reflected = (-n..n).rev().map(|j| (c - 4 * j - 1, c - 4 * j));
        let ds = over(&[("i", pieces(&reflected.collect::<Vec<_>>()))]);
        (prim(Prim::Sub, int(c), var("i")), ds, Demand::Ints(z))
    };
    let n = 256;
    let (a, b) = (case(n), case(n * scaling::FACTOR));
    on_big_stack(|| {
        for (t, ds, d) in [&a, &b] {
            let p = before::preimage(t, ds, &old(d));
            assert!(p.exact && p.domains == *ds, "{t}: {p:?}");
        }
        scaling::check("the transfer before of `c - i` with holes", n, |k| {
            let (t, ds, d) = if k == n { &a } else { &b };
            before::preimage(t, ds, &old(d));
        });
    });
}

/// The chain `t_j = if (i <= j mod 7 - 3) { t } else { (3j + 1) - t }` of `n` levels over `i`
/// in `[-20, 20]`, asked `t_n != 0`. Every level's `c - t` has holes that meet the forward
/// image of `t`, and the guards remove them, so the preimage is exact. The transfer before
/// carries the holes down as one set of doubted values and meets them with the guards' boxes
/// where `i` is read (S22-guard-exact). Measured with the whole preimage: 63 and 594 ms at 256
/// and 2,048 (9.4 times); a transfer of the holes at each level as a demand of their own, met
/// with the guards' boxes (not kept), 9.4 and 511 ms at 32 and 256 (55 times); the check before
/// (S22-exact-mislabel), which left these boxes not exact, 69 ms and 6.1 s at 8 and 64, all of
/// it in the stages after the transfer (load about 18).
#[test]
fn guarded_holes_scale() {
    let case = |n: usize| {
        let g = |j: i64| prim(Prim::Le, var("i"), int(j % 7 - 3));
        let t = chain(n, var("i"), g, |j, t| prim(Prim::Sub, int(3 * j + 1), t));
        (prim(Prim::Ne, t, int(0)), i_in(-20, 20), Demand::Bool(true))
    };
    let n = 256;
    let (a, b) = (case(n), case(n * scaling::FACTOR));
    on_big_stack(|| {
        for (t, ds, d) in [&a, &b] {
            let p = before::preimage(t, ds, &old(d));
            assert!(p.exact && !p.enumerated, "{p:?}");
            assert_eq!(first_refuted(t, ds, d, &[(&p.domains, true)]), None);
        }
        scaling::check(
            "the transfer before of a guarded chain of `c - t` with holes",
            n,
            |k| {
                let (t, ds, d) = if k == n { &a } else { &b };
                before::preimage(t, ds, &old(d));
            },
        );
    });
}

/// The chain `t_j = if (i <= j mod 7 - 3) { t } else { c - t }` of `n` levels over `i` in
/// `[-20, 20]`, asked `t_n != 0`, with the constant `c = 2`, or `c = j mod 5`. The transfer
/// before is exact but for one doubted value of `i`, the point where `t_n` may be 0, and the
/// linear stage decides that one slice of the relation: the preimage is exact, the box less
/// that point. Measured with the whole preimage before, `c = 2`: 32.8 M and 263.8 M
/// instructions at 64 and 512 (8.0 times), 5.3 MB and 42.6 MB (8.0 times), limit 13.2, load
/// 31 (item PERF-s22-const-chain). Negative control, not kept: the linear stage by the
/// projection of the relation onto `i` and the decision of its complement leaves the box
/// `[-20, 20]` inexact, and, with that check skipped, allocates 247 MB and 3.53 GB (14.3
/// times) and takes 178 ms and 3.3 s, the decision alone up to 418 G instructions at 192
/// levels. With `c = j mod 5` the preimage is exact too; its transfer is not linear in the
/// chain (COMPLEXITY.md row C48), so it is checked here at one size only.
#[test]
fn constant_guarded_chains_scale() {
    let case = |n: usize, c: fn(i64) -> i64| {
        let g = |j: i64| prim(Prim::Le, var("i"), int(j % 7 - 3));
        let t = chain(n, var("i"), g, |j, t| prim(Prim::Sub, int(c(j)), t));
        (prim(Prim::Ne, t, int(0)), i_in(-20, 20), Demand::Bool(true))
    };
    let n = 64;
    let cases = scaling::inputs(n, |m| case(m, |_| 2));
    let moving = case(n, |j| j % 5);
    on_big_stack(|| {
        for (t, ds, d) in cases.values().chain([&moving]) {
            let p = before::preimage(t, ds, &old(d));
            assert!(p.exact && !p.enumerated, "{p:?}");
            assert_eq!(first_refuted(t, ds, d, &[(&p.domains, true)]), None);
        }
        scaling::check_order(
            "the transfer and linear stage before of a guarded chain of `2 - t`",
            n,
            1,
            |k| {
                let (t, ds, d) = &cases[&k];
                before::preimage(t, ds, &old(d));
            },
        );
    });
}

/// [`scaling::check`] on the preimage of a family, its sizes built before they are timed.
fn scales(name: &'static str, n: usize) {
    on_big_stack(|| {
        let (a, b) = (family(name, n), family(name, n * scaling::FACTOR));
        scaling::check(
            &format!("the preimage of the chain family {name}"),
            n,
            |k| {
                let (t, ds, d) = if k == n { &a } else { &b };
                preimage(t, ds, d);
            },
        );
    });
}

/// COMPLEXITY.md S22-shapes-linear: whether the box of the first program of
/// [`counted_shapes`] over the levels of [`spread_remainder_chain`] is exact, with `64k` holes
/// in the domain of `x`, costs work of order `k` from 128 holes to 1024: 6.75 times the
/// instructions and 6.82 times the bytes for 8 times the holes, where probing to the end took
/// 17.4 times the bytes. The question has points, but the first search for one takes a piece
/// of `x` that the `if` of the chain cannot follow, and the probe after it
/// ([`zedc::store::presburger`]'s `has_point`) stops at its first point; probing to the end
/// found a point for each of the `32k` pieces of `x`, each at the cost of the whole formula,
/// `O(k^2)`.
///
/// Since PROJECT-canon-precision the probe runs whether or not the first search found a point,
/// and the domain of `x`, a set of values of one atom, is kept untested (`one_atom_set` in
/// `zedc_presburger`). The probe still asks one search per case of the chain, `k` in all, and
/// each search read the `64k` pieces of the domain: 9.4, 11.1 and 12.7 times (bytes, limit
/// 11.73, failed) from 128, 256 and 512 holes to 8 times as many, `O(k^2)`. Testing each piece
/// of the domain as well took 12.55 times from 128. A search now leaves the domain out and
/// looks its point up in it by binary search: 7.4, 8.3 and 9.7 times, where the probe only on
/// a failed search, which main ran, took 7.4, 8.5 and 9.2 times. The second test, at 512, is
/// the one that failed.
fn the_box_of_a_chain_over_holes_is_tested_in_linear_work(n: usize) {
    on_big_stack(|| {
        let d = Demand::Bool(true);
        let make = |holes: usize| {
            let k = holes / 64;
            let t = counted_shapes(spread_remainder_chain(k))[0].clone();
            (t, x_with_holes(holes))
        };
        let inputs = scaling::inputs(n, make);
        for (t, ds) in inputs.values() {
            assert!(
                !preimage(t, ds, &d).exact,
                "the box has points outside the preimage"
            );
        }
        scaling::check(
            "the exactness test of the box of a chain over the holes of `x`",
            n,
            |holes| {
                let (t, ds) = &inputs[&holes];
                preimage(t, ds, &d);
            },
        );
    });
}
