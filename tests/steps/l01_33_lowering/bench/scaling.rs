//! The time of each lowering, raising and check of a graph is linear in its input: the
//! benchmarks of `scaling.rs`, whose tests lower each input at small sizes and check what the
//! larger ones were checked for.

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Family, Prim, Term, Value};
use zed_tests::deep::on_small_stack;
use zed_tests::kernel::fam;
use zed_tests::scaling;
use zed_tests::scaling::check_order;
use zedc::zir::lower::{lower, raise};

use crate::scaling::{
    calls_in_place, chain, far, lets_of_lambdas, nest, prices, push_under_ifs,
    pushes_to_many_ports, wide_match,
};

const N: usize = 4000;

#[test]
fn lowering_the_chain_scales() {
    // The lowering recurses once for each nested `let`, so the chain of 800 runs on a stack
    // large enough for a debug build.
    scaling::on_a_stack(1 << 28, || {
        let terms = scaling::inputs(100, chain);
        scaling::check("lowering a chain of functions that push", 100, |k| {
            lower(&terms[&k]).unwrap();
        })
    });
}

/// CSE keys each node by the hashes of its regions, so a nest is not canonicalized again at
/// every level above it (COMPLEXITY.md Z2, Z3).
#[test]
fn lowering_a_deep_nest_scales() {
    scaling::on_a_stack(1 << 28, || {
        let terms = scaling::inputs(100, nest);
        scaling::check("lowering a nest of `if`s", 100, |d| {
            lower(&terms[&d]).unwrap();
        })
    });
}

/// A name is found by a map, not by searching the scope (COMPLEXITY.md Z6).
#[test]
fn reading_a_name_bound_far_out_scales() {
    scaling::on_a_stack(1 << 30, || {
        let terms = scaling::inputs(2000, far);
        scaling::check("lowering lets that read the outermost name", 2000, |n| {
            lower(&terms[&n]).unwrap();
        })
    });
}

#[test]
fn lowering_lambdas_bound_by_nested_lets_scales() {
    // The ports of each `let`-bound lambda were found by reading its whole body, the lambdas
    // nested in it included.
    scaling::on_a_stack(1 << 32, || {
        // `zir::validate`, which `lower` ends with, keeps one path buffer and copies it
        // only into an error, so its bytes grow with n and not n·depth (COMPLEXITY.md Z17).
        // At depth 500 one copy of the path per node still passed; at 4000 it fails.
        let terms = scaling::inputs(4000, lets_of_lambdas);
        scaling::check("lowering let-bound lambdas nested n deep", 4000, |d| {
            lower(&terms[&d]).unwrap();
        });
    });
}

#[test]
fn lowering_many_functions_called_in_place_scales() {
    // Each such function kept a copy of the whole scope it was defined in, and its call rebuilt
    // the index of that scope.
    scaling::on_a_stack(1 << 32, || {
        let terms = scaling::inputs(2000, calls_in_place);
        scaling::check(
            "lowering n functions each called once in place",
            2000,
            |n| {
                lower(&terms[&n]).unwrap();
            },
        );
    });
}

/// The graph of `n` pushes in a row is checked in time that scales: each state edge's uses
/// are counted in a map, not by searching the edges counted before (COMPLEXITY.md Z10).
#[test]
fn checking_a_graph_of_many_pushes_scales() {
    scaling::on_a_stack(1 << 32, || {
        let graphs = scaling::inputs(N, |n| lower(&calls_in_place(n)).unwrap());
        scaling::check("checking a graph of n pushes", N, |n| {
            zedc::zir::validate::validate(&graphs[&n]).unwrap();
        });
    });
}

/// The current state of each port is found by a map, not by searching the ports used before
/// (COMPLEXITY.md Z13).
#[test]
fn lowering_pushes_to_many_ports_scales() {
    scaling::on_a_stack(1 << 32, || {
        let terms = scaling::inputs(2000, pushes_to_many_ports);
        scaling::check("lowering pushes to n ports", 2000, |n| {
            lower(&terms[&n]).unwrap();
        });
    });
}

#[test]
fn a_name_read_at_every_depth_scales() {
    // Each read carried the name through every region above it, as a new input of each.
    scaling::on_a_stack(1 << 30, || {
        // `zir::validate`, which `lower` ends with, keeps one path buffer and copies it
        // only into an error, so its bytes grow with n and not n·depth (COMPLEXITY.md Z17).
        // At depth 500 one copy of the path per node still passed; at 4000 it fails.
        let terms = scaling::inputs(4000, prices);
        scaling::check("lowering n nested reads of one name", 4000, |d| {
            lower(&terms[&d]).unwrap();
        });
    });
}

#[test]
fn lowering_and_raising_a_deep_term_is_linear_in_its_depth() {
    on_small_stack(|| {
        let terms = scaling::inputs(5_000, nest);
        check_order("lowering nested `if`s", 5_000, 1, |d| {
            lower(&terms[&d]).unwrap();
        });
        let regions = scaling::inputs(5_000, |d| lower(&terms[&d]).unwrap());
        check_order("raising nested `if` regions", 5_000, 1, |d| {
            raise(&regions[&d]).unwrap();
        });
        let terms = scaling::inputs(5_000, lets_of_lambdas);
        check_order("lowering nested let-bound lambdas", 5_000, 1, |d| {
            lower(&terms[&d]).unwrap();
        });
    });
}

#[test]
fn a_port_used_many_regions_deep_is_lowered_in_linear_time_on_a_2_mib_stack() {
    on_small_stack(|| {
        let terms = scaling::inputs(5_000, push_under_ifs);
        check_order("lowering a push under nested `if`s", 5_000, 1, |d| {
            lower(&terms[&d]).unwrap();
        });
    });
}

/// Each arm of a match is found by its index among the match's parts, once per arm; checking
/// that index by listing the parts again made a match of `n` arms cost n² (ADDR-keys, COMPLEXITY
/// K40).
#[test]
fn lowering_a_wide_match_scales() {
    let terms = scaling::inputs(N, wide_match);
    scaling::check("lowering a function over a match of n arms", N, |n| {
        lower(&terms[&n]).unwrap();
    });
}

/// `{x0: (stdin, {x1: (stdin, … stdin …)})}`, `d` families deep, each body reading standard
/// input: every read is placed outside the outermost family (row FAIL-build-port-read-in-map).
fn reads_in_nested_families(d: usize) -> Term {
    let one = || lit(Family::set([Value::Int(1)]));
    (0..d).fold(Term::Read("stdin".into()), |t, i| {
        fam(
            one(),
            &format!("x{i}"),
            prim(Prim::Tuple, vec![Term::Read("stdin".into()), t]),
        )
    })
}

/// A read inside each of d nested families finds where it goes in O(1) amortized, and the reads
/// share one node outside them, so each family takes one argument for it: linear in d, not
/// d² (`Lower::read_frame` in crates/zedc-zir/src/zir/lower.rs).
#[test]
fn reads_in_a_deep_nest_of_families_scale() {
    on_small_stack(|| {
        let terms = scaling::inputs(2_000, reads_in_nested_families);
        check_order(
            "lowering a read in each of n nested families",
            2_000,
            1,
            |d| {
                lower(&terms[&d]).unwrap();
            },
        );
    });
}
