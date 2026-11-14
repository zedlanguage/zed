//! Benchmarks of `deep_let`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The arms of [`fees`] with a fee every day cost `O(d log d)`, at 4,000 and 32,000 days, on a
/// 2 MiB stack; the blocks are built before the timing. A cost of about 84 instructions for each
/// pair of bindings (a count of the names in scope at each binding; control run, not committed)
/// gives 15.7 times the work against a limit of 11.0 here, and 12.6 against 11.4 at 2,000 days,
/// but 9.5 against 12.1 at 250, where it passed (item PA-bind-cost).
#[test]
fn the_arms_of_a_deep_block_scale() {
    on_small_stack(|| {
        let terms = scaling::inputs(4_000, |d| fees(d, 1));
        let scope = ints(&["n".into()]);
        scaling::check(
            "the arms of a block of d bindings, a test in each",
            4_000,
            |d| _ = arms(&terms[&d], &scope),
        );
    });
}

/// The arms of a binding whose value is a block of `d` bindings cost `O(d log d)`, at 4,000 and
/// 32,000, on a 2 MiB stack: the walk binds each binding of the block once, and finds the arms
/// and the value in one pass (item PA-bind-cost).
#[test]
fn the_arms_of_a_binding_of_a_deep_block_scale() {
    on_small_stack(|| {
        let n = 4_000;
        let terms = scaling::inputs(n, |d| bound_to(block(d), d));
        let scope = ints(&["n".into()]);
        scaling::check("the arms of a binding of a block of d bindings", n, |d| {
            _ = arms(&terms[&d], &scope)
        });
    });
}

/// The forward transfer of a block of `d` bindings and of a sum `d` deep costs `O(d)`, at
/// 1,250 and 10,000, on a 2 MiB stack; the terms are built before the timing.
#[test]
fn the_value_of_a_deep_term_scales() {
    on_small_stack(|| {
        let n = DEEP / scaling::FACTOR;
        let scope = ints(&["n".into()]);
        for (what, make) in [
            (
                "the value of a block of d bindings",
                block as fn(usize) -> Term,
            ),
            ("the value of a sum d deep", sum),
        ] {
            let terms = scaling::inputs(n, make);
            scaling::check(what, n, |d| _ = forward(&terms[&d], &mut scope.clone()));
        }
    });
}

/// The walk of `d` blocks one after another keeps the memory of the bindings in scope, not of
/// every binding it has read: the most bytes it holds at once, and the bytes it leaves
/// allocated in the scope it was given, are the same at 1,000 and 8,000 blocks, within 4 KiB;
/// its work is `O(d log d)`. Each summary keeps its last read itself, so the read goes when
/// its binding does; when the reads were kept in a map shared by the copies of the scope,
/// keyed by each summary's number and never emptied, the walk at 8,000 held 8 times the
/// bytes at 1,000 and left them in the scope the walk was given (item PA-read-cache-free).
#[test]
fn the_walk_of_blocks_one_after_another_holds_the_bytes_of_one_block() {
    on_small_stack(|| {
        let n = 1_000;
        let terms = scaling::inputs(n, blocks_in_a_call);
        let scope = ints(&["n".into()]);
        scaling::check("the arms of d blocks in a call", n, |d| {
            _ = arms(&terms[&d], &scope)
        });
        let live =
            |d: usize| zed_alloc_count::live(|| assert!(arms(&terms[&d], &scope).is_empty())).1;
        live(n);
        let (small, large) = (live(n), live(scaling::FACTOR * n));
        eprintln!(
            "{n} blocks: peak {} bytes, left {}; {} blocks: peak {}, left {}",
            small.peak,
            small.net,
            scaling::FACTOR * n,
            large.peak,
            large.net
        );
        assert!(
            large.peak <= small.peak + 4096,
            "the walk of {} blocks held {} bytes at once, of {n} blocks {}",
            scaling::FACTOR * n,
            large.peak,
            small.peak
        );
        assert!(
            large.net <= small.net.max(0) + 4096,
            "the walk of {} blocks left {} bytes allocated, of {n} blocks {}",
            scaling::FACTOR * n,
            large.net,
            small.net
        );
    });
}
