//! The benchmarks of `exp_families.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.
//! Each runs at the sizes `k`, `2k`, `4k` and `8k`, its `k` chosen so that the four take about
//! 10 s (author P169); the work at `8k` is held to that at `k` by [`doubling`].

use crate::exp_families::*;

/// The sizes `n`, `2n`, `4n` and `8n`.
const fn doubles(n: usize) -> [usize; 4] {
    [n, 2 * n, 4 * n, 8 * n]
}

/// A test that `op` on `family` costs work of order `k^power` from `k` to `8k` ([`doubling`]),
/// the least of `runs` runs at each size.
macro_rules! costs {
    ($(#[$attr:meta])* $name:ident, $family:ident, $on:expr, $op:expr, $k:expr, $power:expr, $runs:expr) => {
        #[test]
        $(#[$attr])*
        fn $name() {
            let what = format!("{}, {}", stringify!($family), $op);
            doubling(&what, &doubles($k), $power, |k| {
                least($runs, $family, $op, $on, k)
            });
        }
    };
}

// The linear paths (COMPLEXITY.md S5, S31b, PRES-below-key, PRES-nest-empty).
costs!(shared_nest_decide, shared_nest, "z", 'd', 3200, 1, 2);
costs!(shared_nest_satisfiable, shared_nest, "z", 's', 2300, 1, 2);
costs!(shared_nest_answers, shared_nest, "z", 'a', 1700, 1, 2);
costs!(shared_sums_decide, shared_sums, "x0", 'd', 170, 1, 2);
costs!(shared_sums_satisfiable, shared_sums, "x0", 's', 140, 1, 2);
costs!(shared_sums_project_each, shared_sums, "x0", 'p', 16, 1, 2);
costs!(shared_sums_answers, shared_sums, "x0", 'a', 90, 1, 2);
costs!(dark_chain_decide, dark_chain, "x0", 'd', 16, 1, 2);
costs!(dark_chain_satisfiable, dark_chain, "x0", 's', 16, 1, 2);
costs!(dark_chain_project_each, dark_chain, "x0", 'p', 360, 1, 2);
costs!(dark_chain_answers, dark_chain, "x0", 'a', 16, 1, 2);
costs!(skew_block_decide, skew_block, "a0", 'd', 550, 1, 2);
costs!(skew_block_satisfiable, skew_block, "a0", 's', 370, 1, 2);
costs!(skew_block_project_each, skew_block, "a0", 'p', 340, 1, 2);
costs!(skew_block_answers, skew_block, "a0", 'a', 360, 1, 2);
costs!(nest_point_decide, nest_point, "x0", 'd', 2500, 1, 2);
costs!(nest_point_satisfiable, nest_point, "x0", 's', 2600, 1, 2);
costs!(nest_point_answers, nest_point, "x0", 'a', 1900, 1, 2);
costs!(nest_empty_decide, nest_empty, "x0", 'd', 2800, 1, 2);
costs!(nest_empty_satisfiable, nest_empty, "x0", 's', 3400, 1, 2);
costs!(nest_empty_project_each, nest_empty, "x0", 'p', 16, 1, 2);
costs!(nest_empty_answers, nest_empty, "x0", 'a', 2600, 1, 2);

// Subset sum is held to order k log k, one run each (k^3 log k before PRES-overlap-fast). The
// exact method of PRES-overlap-fast (module `row_sums`) answers it at every size (2026-11-13,
// rate 2048): decided in 0.48M instructions at k = 20 and 3.11M at 160 (6.5 times), where the
// solver alone refuses (114M at k = 20, 1.12G at 160; QUESTIONS.md A87); `answers` costs 5.8M
// and 48.5M (8.3 times).
costs!(subset_sum_decide, subset_sum, "y0", 'd', 200, 1, 1);
costs!(subset_sum_satisfiable, subset_sum, "y0", 's', 200, 1, 1);
costs!(subset_sum_answers, subset_sum, "y0", 'a', 200, 1, 1);
// `project_each`: the method answers first (0.28M at 16, 1.68M at 128, 6.0 times), where the
// solver answered first before (54.8M at 16, 594M at 128).
costs!(subset_sum_project_each, subset_sum, "y0", 'p', 200, 1, 1);

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
            doubling(&what, &doubles($n), 1, |n| seeds($width, $per, $op, n));
        }
    };
}

window_costs!(windows_of_three_decide, 3, 2, 'd', 180);
window_costs!(windows_of_three_satisfiable, 3, 2, 's', 200);
window_costs!(windows_of_three_project_each, 3, 2, 'p', 120);
window_costs!(windows_of_three_answers, 3, 2, 'a', 70);
window_costs!(windows_of_two_decide, 2, 3, 'd', 300);
window_costs!(windows_of_two_satisfiable, 2, 3, 's', 290);
window_costs!(windows_of_two_project_each, 2, 3, 'p', 260);
window_costs!(windows_of_two_answers, 2, 3, 'a', 280);
