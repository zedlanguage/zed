//! The benchmarks of step L1.37a (DESIGN.md Part G), run by `tools/run_tests.sh --bench` and
//! left out of its default run, in the full build and in the short-addresses build. Inputs are
//! built before the runs are measured. Each check they make besides the ratio is made at a small
//! size by the correctness test named in its doc.

use zed_tests::scaling::{check_order, inputs};

use super::{collide, scaling};

/// Two equal lambdas built apart: the second's key is found, and confirming it compares the
/// two bodies node by node. Small instance: `scaling::two_equal_lambdas_built_apart_are_one_
/// node`.
#[test]
fn confirming_a_key_reads_each_node_once() {
    let n = 25_000;
    let terms = inputs(n, scaling::equal_lambdas);
    check_order(
        "lowering two equal lambdas built apart, by body size",
        n,
        1,
        |k| scaling::lowers_to_one_lambda(&terms[&k]),
    );
}

/// Small instances: `scaling::sums_built_twice_apart_are_one_node_each` and
/// `collide::equal_sums_are_still_one_node`.
#[test]
fn many_equal_nodes_are_found_by_their_keys() {
    let n = 40_000;
    let terms = inputs(n, scaling::sums_twice);
    check_order("lowering n sums, each built twice apart, by n", n, 1, |k| {
        scaling::each_sum_is_one_node(&terms[&k], k);
    });
}

/// Small instance: `scaling::the_tables_of_several_definitions_pass`.
#[test]
fn numbering_the_definitions_of_a_unit_scales() {
    let n = 1_500;
    let texts = inputs(n, scaling::tables);
    check_order("checking the tables of n definitions, by n", n, 1, |k| {
        scaling::every_table_passes(&texts[&k], k);
    });
}

/// Small instances: `scaling::rows_and_morphism_types_that_tie_in_digest_are_found_and_dropped`
/// and `collide::rows_dropped_on_another_thread_leave_entries_that_lookups_pass_over`.
#[test]
fn rows_and_morphism_types_that_tie_in_digest_are_found_and_dropped_in_log_time() {
    // `n` tuple types `(aᵢ)` and morphism types `(aᵢ ⊆ dom ⊆ aᵢ) -> aᵢ` over distinct atoms,
    // each made twice, the second found in the tables, then all dropped. With
    // `short-addresses` the digests keep 8 bits. The atoms are chosen so that their digests
    // all tie, so every tuple type, every morphism type and every set node over them ties too:
    // one bucket of each table holds all n of them, and a lookup or a drop that read its whole
    // bucket would make the run quadratic. In the full build the filter keeps one name in 256
    // and each bucket holds one node.
    //
    // Atoms taken in order spread over many buckets instead, each of a fixed fraction b of n,
    // so a lookup costs about 2 ln(bn) steps of about 2,000 instructions each (815 since
    // BUCKET-cmp-cost): n log n, but with log(bn) in place of log n the ratio between n and 8n
    // exceeds the limit at every size that runs in 60 s. That input took 13.1 times the work
    // from 2,000 to 16,000 against the limit 11.2, with 5.5, 9.8 and 13.8 comparisons per lookup
    // at 2,000, 16,000 and 128,000 (SCALE-fix-37a-digest). With one bucket it took 10.3 times,
    // and 10.1 times with half the work since BUCKET-cmp-cost cut the cost of a step; a lookup
    // that compares one node in 64 of its bucket besides its path takes 43 times.
    let n = 5_000;
    let atoms = inputs(n, scaling::tied_atoms);
    check_order(
        "making n rows and n morphism types twice, then dropping them, by n",
        n,
        1,
        |k| scaling::made_twice_and_dropped(&atoms[&k]),
    );
}

/// With 8-bit digests the levels of a chain tie in digest at every depth, so building one
/// orders each new level against older ones level after level down, as ordering two chains
/// over different bases does where their digests tie. That order was a recursion, which
/// overflowed a 256 KiB stack 425 levels down (421 ran; the code before 7a79799d3, dev profile,
/// measured 2026-11-14), and a 2 MiB stack about 3,000 levels down (SHORT-stack-l01_22); it is a
/// loop with a stack of its own. Each comparison still reads the levels on which the digests
/// tie, so building the chain is quadratic in this build: the depth is the smallest round one
/// past the overflow. Small instance: `collide::types_that_tie_in_digest_level_after_level_are_
/// ordered`.
#[test]
fn types_that_tie_in_digest_level_after_level_are_ordered_on_a_small_stack() {
    const DEPTH: usize = 500;
    const STACK: usize = 256 << 10;
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(STACK);
        let run = thread.spawn_scoped(scope, || collide::chains_over_two_bases_are_ordered(DEPTH));
        run.unwrap().join().unwrap();
    });
}
