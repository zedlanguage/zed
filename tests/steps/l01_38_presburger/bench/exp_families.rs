//! The benchmarks of `exp_families.rs` (TEST-bench-move-l0138), run by
//! `tools/run_tests.sh --bench`. Each held by [`doubling`] runs at the sizes `k` and `8k`, the work
//! at `8k` held to that at `k`; its `k` was chosen when it ran `k`, `2k`, `4k` and `8k` twice
//! each, so that those took about 10 s (author P169).

use crate::exp_families::*;

/// The sizes `n`, `2n`, `4n` and `8n`.
const fn doubles(n: usize) -> [usize; 4] {
    [n, 2 * n, 4 * n, 8 * n]
}

/// A test that `op` on `family` costs work of order `k^power` from `k` to `8k` ([`doubling`]).
macro_rules! costs {
    ($(#[$attr:meta])* $name:ident, $family:ident, $on:expr, $op:expr, $k:expr, $power:expr) => {
        #[test]
        $(#[$attr])*
        fn $name() {
            let what = format!("{}, {}", stringify!($family), $op);
            doubling(&what, ($k, $power), |k| vec![$family(k)], $op, $on);
        }
    };
}

// The linear paths (COMPLEXITY.md S5, S31b, PRES-below-key, PRES-nest-empty).
costs!(shared_nest_decide, shared_nest, "z", 'd', 3200, 1);
costs!(shared_nest_satisfiable, shared_nest, "z", 's', 2300, 1);
costs!(shared_nest_answers, shared_nest, "z", 'a', 1700, 1);
costs!(shared_sums_decide, shared_sums, "x0", 'd', 110, 1);
costs!(shared_sums_satisfiable, shared_sums, "x0", 's', 140, 1);
costs!(shared_sums_project_each, shared_sums, "x0", 'p', 16, 1);
costs!(shared_sums_answers, shared_sums, "x0", 'a', 60, 1);
// dark_chain (PRES-dark-chain-forced-bits): its point has Θ(k²) bits, x[i] near (3/2)^i. Before,
// `decide` and `answers` fixed every x[i] at the bounds of x0 (the rounds of `Trial::holds`), so
// they paid the bits of a point they do not return: 13.93 and 11.05 times at 8n from k = 4800
// and 4600 (2026-11-21, load 21). Without the point, `forced` now eliminates the chain from its
// top (`Graph::eliminate`) and fixes nothing.
costs!(dark_chain_decide, dark_chain, "x0", 'd', 4800, 1);
costs!(dark_chain_project_each, dark_chain, "x0", 'p', 260, 1);
costs!(dark_chain_answers, dark_chain, "x0", 'a', 4600, 1);

/// `satisfiable` on dark_chain returns its point, Θ(k²) bits, so its cost is held per bit of the
/// formula and the point ([`output_sensitive`]): 13.90 times the instructions at 8n from
/// k = 5100 (2026-11-21), where the bits grew 64 times. The bound it holds, with n the rows
/// (2k + 2, each of at most two terms with coefficients 2 and 3), B the bits of the point and
/// w = 64 the bits of a word, is O(n log² n + B / w) instructions, O(m) for the m >= B bits
/// counted. The steps, from `satisfiable` to `forced::forced(f, true)` (presburger.rs, forced.rs):
/// 1. `signed`, `factored` and `Graph::of` read the formula: O(n log n) comparisons of names of
///    O(log n) characters, the passes `decide` pays too, held to order n by
///    `dark_chain_decide`.
/// 2. The first propagation forces each row. The two rows of x0 alone bound x0 to [1, 9]; each
///    other row has two variables not known, so it gives no step. `facts` fixes nothing. O(n).
/// 3. The point is asked for, so no elimination runs (`Graph::eliminate` only answers whether a
///    point exists). `Trial::holds` sets x0 to 1, its lower bound, the one variable bounded.
/// 4. By induction on i: when x[i] is known (b_i bits), the two rows on x[i] and x[i+1] have one
///    variable left, and `solve` gives x[i+1] >= ⌈3 x[i] / 2⌉ and x[i+1] <= ⌊(3 x[i] + 1) / 2⌋,
///    which meet at one value: x[i+1] is fixed and its `Known` event queued. Each row is solved
///    once (when its count of open variables falls to 1) and evaluated once (when it falls to
///    0), each time with O(1) products, sums and divisions by 2 or 3 of numbers of
///    O(b_i + b_{i+1}) bits: O(1 + b_i / w) word operations and O(1 + b_i / 8) bytes. Summed over
///    i: O(n + B / w). Then every row is true, the conjunction is true, and the trial ends.
/// 5. `Graph::point` inserts k + 1 atoms into a `BTreeMap` (O(n log n) comparisons of names) and
///    copies each value (O(B / w)), and the point is dropped after the run, O(n + B / w).
///
/// Sum: O(n log² n + B / w). Here B >= Σ_{i<=k} log2((3/2)^i) = 0.29 k(k + 1) bits and n log² n
/// = o(k²), so the count per bit of m = 8 × (the printed formula's bytes) + Σ (1 + bits of each
/// value) is O(1) on this family: the per-bit count at 8k is held to that at k with power 0,
/// under 1.3125 times. The bytes allocated follow the same steps, O(n log n + B / 8). This is no
/// bound of `satisfiable` on other families; each holds its own.
#[test]
fn dark_chain_satisfiable() {
    output_sensitive("dark_chain, s", &doubles(5100), dark_chain, 2);
}

// skew_block's `decide`, `project_each` and `answers` took 17.7 s, 22.2 s and 21.5 s at k = 550,
// 340 and 360 at load 38 (2026-11-20), and `answers` passed its limit of 23 s at load 36, so
// their sizes are halved; the work grows 2.0 to 2.1 times a doubling, so the ratio is the same
// from either start.
costs!(skew_block_decide, skew_block, "a0", 'd', 275, 1);
costs!(skew_block_satisfiable, skew_block, "a0", 's', 370, 1);
costs!(skew_block_project_each, skew_block, "a0", 'p', 170, 1);
costs!(skew_block_answers, skew_block, "a0", 'a', 180, 1);
costs!(nest_point_decide, nest_point, "x0", 'd', 2500, 1);
costs!(nest_point_satisfiable, nest_point, "x0", 's', 2600, 1);
costs!(nest_point_answers, nest_point, "x0", 'a', 1900, 1);
costs!(nest_empty_decide, nest_empty, "x0", 'd', 2800, 1);
costs!(nest_empty_satisfiable, nest_empty, "x0", 's', 3400, 1);
costs!(nest_empty_project_each, nest_empty, "x0", 'p', 16, 1);
costs!(nest_empty_answers, nest_empty, "x0", 'a', 2000, 1);
// `project_each` on a deeper nest (FAIL-nest-empty-project-each-scaling): each level of the nest
// read the atoms of every level below it in `forest_domains`, Θ(k²) in all. At k = 16 to 128 that
// cost was 10.24 times at 8n under tools/run_tests.sh and 11.38 times run directly; at 128 to
// 1024 it was 17.89 times under tools/run_tests.sh, 8.13 after the fix (COMPLEXITY.md
// PRES-exp-families). From k = 570 it was 35.2 times (2026-11-14); with each kernel equation in
// one sign (PRES-below-key-sign) it is 8.15 times (2026-11-21, PRES-growth-exp-families).
costs!(nest_empty_project_each_deep, nest_empty, "x0", 'p', 570, 1);

// `project_each` on a deeper shared_sums (PRES-growth-exp-families): 38.3 times at 8n from
// k = 590 (2026-11-14), each doubling 3.1 to 3.6 times. With each kernel equation in one sign
// (PRES-below-key-sign) it is 8.17 times from 590 to 4720 (762.98M and 6234.92M instructions,
// 2026-11-21, load 55), each doubling 2.01 times, and 8.17 times from 460 to 3680 (596.42M and
// 4870.28M, load 25), the four sizes in about 5 s.
costs!(
    shared_sums_project_each_deep,
    shared_sums,
    "x0",
    'p',
    460,
    1
);

// Subset sum is held to order k log k, one run each (k^3 log k before PRES-overlap-fast). The
// exact method of PRES-overlap-fast (module `row_sums`) answers it at every size (2026-11-13,
// rate 2048): decided in 0.48M instructions at k = 20 and 3.11M at 160 (6.5 times), where the
// solver alone refuses (114M at k = 20, 1.12G at 160; QUESTIONS.md A87); `answers` costs 5.8M
// and 48.5M (8.3 times).
costs!(subset_sum_decide, subset_sum, "y0", 'd', 200, 1);
costs!(subset_sum_satisfiable, subset_sum, "y0", 's', 200, 1);
costs!(subset_sum_answers, subset_sum, "y0", 'a', 200, 1);
// `project_each`: the method answers first (0.28M at 16, 1.68M at 128, 6.0 times), where the
// solver answered first before (54.8M at 16, 594M at 128). The weights are distinct at every
// size ([`subset_sum_untied`]): those of [`subset_sum`] repeat from i = 496, so k = 200 and 400
// were untied and 800 and 1600 tied, and only the tied sizes paid the test of their ties
// (`Renamed::by_structure` in `project_each`, PRES-project-each-naming): 12.1 times the
// instructions from 200 to 1600 (17.3M and 210.5M, against 9.9M and 73.7M on main at
// d7e7d86d0, 7.45 times).
costs!(
    subset_sum_project_each,
    subset_sum_untied,
    "y0",
    'p',
    200,
    1
);

/// A test that `op` on the window systems of seeds 0..20 costs work of order `n log n` in all,
/// from `n` to `8n`, `n` at least 12. No bound is stated for the splinter search these reach
/// (COMPLEXITY.md S5, class C in PRES-exp-audit); the growth measured is recorded in row
/// PRES-exp-families. The sizes start at 12 or more: at n = 6, 39 of 60 systems of windows of
/// three are answered, and from n = 12 on nearly all are refused (`Growth`: 58 of 60 at n = 12,
/// all from 24), so the step from 6 to 12 (3.09 times for `decide`, 3.54 for `answers`,
/// 2026-11-11) mixes two ways of answering; from 12 to 96 each doubling grew 2.1 to 2.3 times.
macro_rules! window_costs {
    ($name:ident, $width:expr, $per:expr, $op:expr, $n:expr) => {
        #[test]
        fn $name() {
            let what = format!("windows of {}, {} rows each, {}", $width, $per, $op);
            doubling(&what, ($n, 1), |n| seeds($width, $per, n), $op, "x0");
        }
    };
}

window_costs!(windows_of_three_decide, 3, 2, 'd', 180);
window_costs!(windows_of_three_satisfiable, 3, 2, 's', 150);
window_costs!(windows_of_three_project_each, 3, 2, 'p', 95);
window_costs!(windows_of_three_answers, 3, 2, 'a', 70);
window_costs!(windows_of_two_decide, 2, 3, 'd', 230);
window_costs!(windows_of_two_satisfiable, 2, 3, 's', 290);
window_costs!(windows_of_two_project_each, 2, 3, 'p', 260);
window_costs!(windows_of_two_answers, 2, 3, 'a', 220);

/// `exp_families::the_window_program_finds_the_points_of_the_box` as first written, 2.7 s
/// (2026-11-14, load 25): over 4 variables, both shapes, seeds 0 to 2, 25^4 points each.
#[test]
fn the_window_program_finds_the_points_of_the_box_over_4_variables() {
    for (width, per) in [(3, 2), (2, 3)] {
        for seed in 0..3 {
            window_program_finds_the_points_of_the_box(4, width, per, seed);
        }
    }
}

/// `exp_families::random_window_systems_are_answered_as_the_window_program_answers` as first
/// written, 0.65 s (2026-11-14, load 14): seeds 0 to 19.
#[test]
fn random_window_systems_of_seeds_0_to_19_are_answered_as_the_window_program_answers() {
    random_window_systems_answer(&(0..20).collect::<Vec<u64>>(), "seeds 0 to 19");
}
