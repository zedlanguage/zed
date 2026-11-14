//! Benchmarks of `deep_let`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`). The first three are the terms of
//! `deep_let.rs` 1,000 to 1,500 deep on a 2 MiB stack (author P178).

use super::*;

/// The default stack of a test thread.
const STACK: usize = 2 << 20;

/// How deep the terms are.
const DEEP: usize = 1_500;

/// Runs `f` on a thread with a 2 MiB stack, whatever `RUST_MIN_STACK` says.
fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .expect("a test thread")
        .join()
        .expect("the test passes on a 2 MiB stack");
}

/// The arms of [`fees`] with `DEEP` days and a fee every 100th, on a 2 MiB stack: two for
/// each fee and two for the final test, in the order written, the last fee's `2` taken only by
/// `n > DEEP`. The fee is spaced to keep the test short, not to hide a cost that grows: a
/// test costs a reduction of the scope and a copy per arm, measured at 165, 181 and 186 µs
/// with a fee on every day at 1,000, 4,000 and 12,500 days (and [`the_arms_of_a_deep_block_scale`]
/// checks that cost), and the depth of the walk is the same.
#[test]
fn a_block_of_1500_bindings_has_its_arms_on_a_2_mib_stack() {
    on_small_stack(|| {
        let every = 100;
        let a = arms(&fees(DEEP, every), &ints(&["n".into()]));
        assert_eq!(a.len(), 2 * (DEEP / every) + 2);
        let fee = &a[a.len() - 4];
        assert_eq!(fee.guard, format!("(n > {DEEP})"));
        assert!(fee.outcome);
        assert_eq!(
            fee.scope.get("n").ints().to_string(),
            format!("[{}..]", DEEP + 1)
        );
        assert!(a.iter().all(|a| a.reachable()));
    });
}

/// A binding whose value is a block of [`DEEP`] `let`s, or a sum [`DEEP`] deep: the forward
/// transfer finds its value, `DEEP + 1`, and the test after it is taken only by its true arm.
#[test]
fn a_value_nested_1500_deep_is_found_on_a_2_mib_stack() {
    on_small_stack(|| {
        let scope = ints(&["n".into()]);
        for make in [block, sum] {
            let value = make(DEEP);
            let found = forward(&value, &mut scope.clone());
            assert_eq!(found.value(), Some(&Value::Int(DEEP as i64 + 1)));
            let a = arms(&bound_to(value, DEEP), &scope);
            assert_eq!(a.len(), 2);
            assert!(a[0].reachable() && !a[1].reachable());
        }
    });
}

/// `if`s nested 1,000 deep in their first arm, on a 2 MiB stack: the `k`-th test's true arm
/// holds `n > k`, its false arm `n == k` (`n <= 1` for the first), the arms in the order
/// written (the true arms outside in, then the false arms inside out), and the value is
/// 0 or 1. (Each test costs a reduction of the scope; the depth is 1,000, two and a half times
/// the depth at which the old walk overflowed, to keep the test short.)
#[test]
fn ifs_nested_1000_deep_have_their_arms_on_a_2_mib_stack() {
    on_small_stack(|| {
        let d = 1_000;
        let a = arms(&nested_ifs(d), &ints(&["n".into()]));
        assert_eq!(a.len(), 2 * d);
        for k in [1, d / 2, d] {
            assert_eq!(
                a[k - 1].scope.get("n").ints().to_string(),
                format!("[{}..]", k + 1)
            );
            assert_eq!(
                a[2 * d - k].scope.get("n").ints().to_string(),
                if k == 1 {
                    "[..=1]".to_string()
                } else {
                    format!("[{k}..={k}]")
                }
            );
        }
        let value = forward(&nested_ifs(d), &mut ints(&["n".into()]));
        assert_eq!(value.ints().to_string(), "[0..=1]");
    });
}

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
/// 10,000 and 80,000, on a 2 MiB stack; the terms are built before the timing. (The values
/// are checked at [`DEEP`] by `a_value_nested_1500_deep_is_found_on_a_2_mib_stack`.)
#[test]
fn the_value_of_a_deep_term_scales() {
    on_small_stack(|| {
        let n = 10_000;
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
/// allocated in the scope it was given, are the same at 8,000 and 64,000 blocks, within 4 KiB;
/// its work is `O(d log d)`. Each summary keeps its last read itself, so the read goes when
/// its binding does; when the reads were kept in a map shared by the copies of the scope,
/// keyed by each summary's number and never emptied, the walk at 8,000 blocks held 8 times the
/// bytes at 1,000 and left them in the scope the walk was given (item PA-read-cache-free).
#[test]
fn the_walk_of_blocks_one_after_another_holds_the_bytes_of_one_block() {
    on_small_stack(|| {
        let n = 8_000;
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
