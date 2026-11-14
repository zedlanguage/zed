//! The time of each lowering, raising and check of a graph is linear in its input: the
//! benchmarks of `scaling.rs`, whose tests lower each input at small sizes and check what the
//! larger ones were checked for.

use std::collections::BTreeMap;

use zed_kernel::Term;
use zed_tests::deep::on_small_stack;
use zed_tests::scaling;
use zed_tests::scaling::check_order;
use zedc::zir::Region;
use zedc::zir::lower::{lower, raise};

use crate::scaling::{
    calls_in_place, chain, far, lets_of_lambdas, nest, prices, push_under_ifs,
    pushes_to_many_ports, wide_match,
};

const N: usize = 4000;

/// The terms `term(m)` at `n` and `FACTOR * n`, built before the timing, so that a test times
/// the lowering alone.
fn built(n: usize, term: impl Fn(usize) -> Term) -> BTreeMap<usize, Term> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, term(m)))
        .collect()
}

#[test]
fn lowering_the_chain_scales() {
    // The lowering recurses once for each nested `let`, so the chain of 800 runs on a stack
    // large enough for a debug build.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            let terms = built(100, chain);
            scaling::check("lowering a chain of functions that push", 100, |k| {
                lower(&terms[&k]).unwrap();
            })
        })
        .unwrap()
        .join()
        .unwrap();
}

/// CSE keys each node by the hashes of its regions, so a nest is not canonicalized again at
/// every level above it (COMPLEXITY.md Z2, Z3).
#[test]
fn lowering_a_deep_nest_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            let terms = built(100, nest);
            scaling::check("lowering a nest of `if`s", 100, |d| {
                lower(&terms[&d]).unwrap();
            })
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A name is found by a map, not by searching the scope (COMPLEXITY.md Z6).
#[test]
fn reading_a_name_bound_far_out_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            let terms = built(2000, far);
            scaling::check("lowering lets that read the outermost name", 2000, |n| {
                lower(&terms[&n]).unwrap();
            })
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn lowering_lambdas_bound_by_nested_lets_scales() {
    // The ports of each `let`-bound lambda were found by reading its whole body, the lambdas
    // nested in it included.
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            // `zir::validate`, which `lower` ends with, keeps one path buffer and copies it
            // only into an error, so its bytes grow with n and not n·depth (COMPLEXITY.md Z17).
            // At depth 500 one copy of the path per node still passed; at 4000 it fails.
            let (small, large) = (
                lets_of_lambdas(4000),
                lets_of_lambdas(4000 * scaling::FACTOR),
            );
            scaling::check("lowering let-bound lambdas nested n deep", 4000, |d| {
                lower(if d == 4000 { &small } else { &large }).unwrap();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn lowering_many_functions_called_in_place_scales() {
    // Each such function kept a copy of the whole scope it was defined in, and its call rebuilt
    // the index of that scope.
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            let terms = built(2000, calls_in_place);
            scaling::check(
                "lowering n functions each called once in place",
                2000,
                |n| {
                    lower(&terms[&n]).unwrap();
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The graph of `n` pushes in a row is checked in time that scales: each state edge's uses
/// are counted in a map, not by searching the edges counted before (COMPLEXITY.md Z10).
#[test]
fn checking_a_graph_of_many_pushes_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            let graphs: std::collections::BTreeMap<usize, Region> = [N, N * scaling::FACTOR]
                .into_iter()
                .map(|n| (n, lower(&calls_in_place(n)).unwrap()))
                .collect();
            scaling::check("checking a graph of n pushes", N, |n| {
                zedc::zir::validate::validate(&graphs[&n]).unwrap();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The current state of each port is found by a map, not by searching the ports used before
/// (COMPLEXITY.md Z13).
#[test]
fn lowering_pushes_to_many_ports_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            let terms = built(2000, pushes_to_many_ports);
            scaling::check("lowering pushes to n ports", 2000, |n| {
                lower(&terms[&n]).unwrap();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_name_read_at_every_depth_scales() {
    // Each read carried the name through every region above it, as a new input of each.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            // `zir::validate`, which `lower` ends with, keeps one path buffer and copies it
            // only into an error, so its bytes grow with n and not n·depth (COMPLEXITY.md Z17).
            // At depth 500 one copy of the path per node still passed; at 4000 it fails.
            let (small, large) = (prices(4000), prices(4000 * scaling::FACTOR));
            scaling::check("lowering n nested reads of one name", 4000, |d| {
                lower(if d == 4000 { &small } else { &large }).unwrap();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn lowering_and_raising_a_deep_term_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nest(5_000), nest(40_000));
        check_order("lowering nested `if`s", 5_000, 1, |d| {
            lower(if d == 5_000 { &small } else { &large }).unwrap();
        });
        let (small, large) = (lower(&small).unwrap(), lower(&large).unwrap());
        check_order("raising nested `if` regions", 5_000, 1, |d| {
            raise(if d == 5_000 { &small } else { &large }).unwrap();
        });
        let (small, large) = (lets_of_lambdas(5_000), lets_of_lambdas(40_000));
        check_order("lowering nested let-bound lambdas", 5_000, 1, |d| {
            lower(if d == 5_000 { &small } else { &large }).unwrap();
        });
    });
}

#[test]
fn a_port_used_many_regions_deep_is_lowered_in_linear_time_on_a_2_mib_stack() {
    on_small_stack(|| {
        let small = push_under_ifs(5_000);
        let large = push_under_ifs(40_000);
        check_order("lowering a push under nested `if`s", 5_000, 1, |d| {
            lower(if d == 5_000 { &small } else { &large }).unwrap();
        });
    });
}

/// Each arm of a match is found by its index among the match's parts, once per arm; checking
/// that index by listing the parts again made a match of `n` arms cost n² (ADDR-keys, COMPLEXITY
/// K40).
#[test]
fn lowering_a_wide_match_scales() {
    let terms: std::collections::BTreeMap<usize, Term> = [N, N * scaling::FACTOR]
        .into_iter()
        .map(|n| (n, wide_match(n)))
        .collect();
    scaling::check("lowering a function over a match of n arms", N, |n| {
        lower(&terms[&n]).unwrap();
    });
}
