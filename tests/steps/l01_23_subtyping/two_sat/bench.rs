//! The benchmarks of `two_sat.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `two_sat.rs`.

use super::*;

/// The cost of deciding a shape at the variable counts `(a, b)`, the types built before the
/// runs, under the scaling limit. The input's size is that of the type: about one clause per
/// variable, each a union of tuple types of one component per variable, so of order `vars^2`,
/// and `b` about `2.83 a` gives it 8 times over, which the assert of the size ratio checks.
/// This was `scales` in `two_sat.rs`, at 45 and 128 variables (`VARS`) for every shape; each
/// benchmark below names its own counts, chosen for about 0.5 s at the smaller
/// (TEST-bench-move-l0123, author P169).
fn scales_at(name: &str, (a, b): (usize, usize)) {
    let (small, large) = (instance(name, a), instance(name, b));
    let ratio = large.2 as f64 / small.2 as f64;
    assert!((7.9..8.2).contains(&ratio), "{name}: size ratio {ratio}");
    scaling::compare(
        &format!(
            "2-CNF {name}: {a} and {b} variables, sizes {} and {}, {ratio:.2} times",
            small.2, large.2
        ),
        1,
        || decide(name, a, &small),
        || decide(name, b, &large),
    );
}

#[test]
fn a_chain_is_decided_in_the_size_of_its_type() {
    // TEST-bench-move-l0123, author P169: 45 and 128 variables before, now 500 and 1414; 1x 0.59 s
    // by `ns`, load 56.
    scales_at("chain", (500, 1414));
}

#[test]
fn an_open_chain_is_decided_in_the_size_of_its_type() {
    // TEST-bench-move-l0123, author P169: 45 and 128 variables before, now 256 and 724; 1x 0.41 s
    // by `ns`, load 56.
    scales_at("chainsat", (256, 724));
}

#[test]
fn a_parity_cycle_is_decided_in_the_size_of_its_type() {
    // TEST-bench-move-l0123, author P169: 45 and 128 variables before, now 1000 and 2828; 1x
    // 0.26 s by `ns`, load 33.
    scales_at("xorcycle", (1000, 2828));
}

/// The parity cycle at 256 and 2048 variables, held to work of order `vars^2`, the size of its
/// type: the search before item T6-2sat costs about `vars^3` here (COMPLEXITY.md K54), 512
/// times at 8 times the variables, against the limit 84 (168 by processor time), while at 8
/// times the type, as [`scales_at`] measures, it is 22.6 times, inside the limit 21 that a
/// processor-time meter allows. Control, run once (2026-11-22, Colab VM, processor time): a
/// `vars^3` busy loop in `Searching::two_sat` fails this test at 180.1 times and passes
/// [`scales_at`] at 17.9; without it this test reads 46.8. Until PERF-two-sat-parity-cycle
/// (2026-11-22) this test held the cycle to order `vars`, as if linear in the clauses, at 11
/// and 88 variables: below the size of the input, which the decision reads, since
/// `Searching::region` keeps a cell for each atom and component, `atoms * vars`. The ratio rose
/// with the size toward 64 (10.8, 14.4, 16.1 and 21.4 times the instructions from 11, 22, 32
/// and 64 variables), and it passed at 11 only through the meter heap's cost per call
/// (TEST-meter-ref-constant).
#[test]
fn a_parity_cycle_is_decided_in_time_quadratic_in_its_variables() {
    // PERF-two-sat-parity-cycle: n 256, 1x 0.013 s and 8x 0.60 s of processor time on a Colab
    // VM; the type at 8n has 2048 variables and 8.4 million components.
    let n = 256;
    let types = scaling::inputs(n, |m| instance("xorcycle", m));
    scaling::check_order("2-CNF xorcycle, by variables", n, 2, |m| {
        decide("xorcycle", m, &types[&m]);
    });
}
