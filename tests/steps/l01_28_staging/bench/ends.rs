//! The form rule `stage::ends` of `ends.rs` at `k` and `8k` levels: a shared part is read
//! once, so the time grows with the term's distinct parts, not its places. Each term is built
//! before the timing; `ends.rs` checks the answers at small sizes.

use zed_kernel::term::build::var;
use zed_kernel::{Prim, Shared, Term};
use zed_tests::scaling;
use zedc::stage::ends;

use crate::ends::{
    app, arms_calling_let_functions, built_into_freed_blocks, let_functions, mixed_levels_read,
    prim, shared_and_tree_terms_read_alike, shared_arms_read, shared_arms_terms,
};

#[test]
fn a_chain_whose_if_arms_share_their_term_is_read_in_time_near_its_size() {
    // The walk read the term as a tree: 2^k steps.
    let n = 1000;
    let terms = scaling::inputs(n, shared_arms_terms);
    scaling::check("stage::ends on k levels of shared if arms", n, |k| {
        shared_arms_read(&terms[&k]);
    });
}

#[test]
fn many_let_functions_called_at_the_end_are_read_in_time_near_their_number() {
    let n = 1000;
    let terms = scaling::inputs(n, let_functions);
    scaling::check("stage::ends on k let functions called at the end", n, |k| {
        assert!(ends(&terms[&k]));
    });
}

#[test]
fn arms_that_call_different_let_functions_on_a_shared_part_are_read_in_time_near_their_size() {
    let n = 1000;
    let terms = scaling::inputs(n, arms_calling_let_functions);
    scaling::check(
        "stage::ends on k levels of arms calling let functions",
        n,
        |k| {
            assert!(ends(&terms[&k]));
        },
    );
}

/// `pj = aj(p(j-1))`, `qj = bj(q(j-1))` and `pj + qj` for every j, with the names `a1, b1,
/// a2, b2, …` read first so that their numbers interleave: each join is of two sets of j
/// names whose tries differ everywhere, and only the pair joined one level down is shared.
fn two_chains_joined(k: usize) -> Term {
    let pushed = |t: &Shared| Term::Push("out".into(), t.clone());
    let (mut p, mut q) = (Shared::new(var("n")), Shared::new(var("n")));
    let mut sums = Vec::new();
    for j in 1..=k {
        p = Shared::new(app(var(&format!("a{j}")), vec![pushed(&p)]));
        q = Shared::new(app(var(&format!("b{j}")), vec![pushed(&q)]));
        sums.push(prim(Prim::Add, vec![pushed(&p), pushed(&q)]));
    }
    let names = (1..=k)
        .flat_map(|j| [format!("a{j}"), format!("b{j}")])
        .map(|x| app(var(&x), vec![]))
        .collect();
    sums.push(prim(Prim::Add, names));
    prim(Prim::Add, sums)
}

/// Plan row STAGE-scaling-10_5, back from the deferred tests (TESTS-defer-failing,
/// 2026-11-13: 10.5 times the bytes from 1000 to 8000 on main cdf07ac4f).
#[test]
fn two_chains_of_calls_joined_at_every_level_are_read_in_time_near_their_size() {
    let n = 1000;
    let terms = scaling::inputs(n, two_chains_joined);
    scaling::check(
        "stage::ends on two chains of k calls joined at every level",
        n,
        |k| {
            assert!(ends(&terms[&k]));
        },
    );
    let freed = |x: &str| Term::Lam(vec![x.into()], Shared::new(two_chains_joined(3)));
    assert!(!ends(&freed("b2")));
    assert!(ends(&freed("b4")));
}

#[test]
fn reading_a_term_built_into_freed_blocks_scales() {
    let n = 1000;
    let terms = scaling::inputs(n, built_into_freed_blocks);
    scaling::check(
        "stage::ends on k mixed levels of shared if arms built into freed blocks",
        n,
        |k| mixed_levels_read(&terms[&k]),
    );
}

/// The few thousand random terms of plan row TESTS-random-batteries-to-size (ENDS-dag); the
/// correctness test `ends::random_shared_terms_read_as_their_trees` reads 200.
#[test]
fn three_thousand_random_shared_terms_read_as_their_trees() {
    let start = std::time::Instant::now();
    shared_and_tree_terms_read_alike(
        "three_thousand_random_shared_terms_read_as_their_trees",
        3000,
    );
    eprintln!("3000 shared terms read in {:.2?}", start.elapsed());
}
