//! Benchmarks of `xst::holes_model`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// Codex round 4 (`measure`): the model's work on laps, the staircase and the mixed family
/// grows near linearly from `n = 2048` to `8n` (measured here from `n = 16384`), and its answer
/// satisfies every edge with each value in its domain.
#[test]
fn scc_composition_takes_near_linear_time_on_the_families() {
    for name in ["laps", "staircase", "mixed"] {
        let inputs = scaling::inputs(16_384, |n| family(name, n));
        for sys in inputs.values() {
            let x = greatest(sys).expect("one cycle").expect("a solution");
            assert!(
                sys.edges.iter().all(|&(u, v, w)| x[v] <= x[u] + w),
                "{name}"
            );
            assert!(
                x.iter()
                    .zip(&sys.domains)
                    .all(|(&v, d)| predecessor(d, v) == Some(v)),
                "{name}"
            );
        }
        scaling::check_order(name, 16_384, 1, |n| {
            drop(greatest(&inputs[&n]));
        });
    }
}
