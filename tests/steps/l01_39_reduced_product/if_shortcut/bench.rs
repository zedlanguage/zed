//! Benchmarks of `if_shortcut`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// [`walk_chain`] at [`CHAIN`] links on a thread of [`CHAIN_STACK`] bytes. Neither the walk nor
/// the drop recurses down the chain: on a thread of [`CHAIN_STACK`] bytes (on 64 KiB it
/// overflowed at every depth tried, from the stack it takes whatever the depth), the walk
/// passed at 2,000, 10,000 and 30,000 links, so its stack does not grow with the chain, and a
/// walk that took over 66 bytes of stack a link overflows at 4,000 links. Until
/// TEST-bench-move-l0139 the chain was 100,000 links long on the test thread's stack, 9.6 s at
/// load 30; a chain this deep on a stack this small is an unusual size (author P178).
#[test]
fn a_deep_chain_of_bindings_is_walked_and_dropped() {
    std::thread::Builder::new()
        .stack_size(CHAIN_STACK)
        .spawn(|| walk_chain(CHAIN))
        .expect("a test thread")
        .join()
        .expect("the chain is walked and dropped on a 256 KiB stack");
}

/// The links of the chain of [`a_deep_chain_of_bindings_is_walked_and_dropped`], and the stack
/// it runs on.
const CHAIN: i64 = 4_000;
const CHAIN_STACK: usize = 256 << 10;

/// The walk is linear in the depth of each form of [`nest`]: blocks bound inside bound blocks
/// (a binding's summary is made when a test reads it, `product::Lazy`), `if`s with blocks in
/// their arms bound inside each other's arms (the value of an `if` is the join of its arms'
/// values without the premises of its tests, `Run::walk_value_at`), literal-armed `if`s bound
/// inside nested arms (a bottom scope's names are emptied from the last ones emptied,
/// `Scope::empty_if_bottom`), a chain of literal-armed `if`s bound one after another, and `if`s
/// nested in arms (COMPLEXITY.md row PA-walk-nest-cost). The reference reads the value of an
/// `if` whose arms are not literals by the transfer again after walking its arms, `Θ(d²)` in
/// the second form, so it is held to the others.
#[test]
fn one_pass_and_transfer_scale_on_deep_nests() {
    let scope = ints(&["x".into()]);
    for (form, what, reference) in [
        (0, "blocks bound `k` deep inside bound blocks", true),
        (
            1,
            "`if`s with blocks in their arms bound `k` deep inside each other's arms",
            false,
        ),
        (
            2,
            "literal-armed `if`s bound inside arms nested `k` deep",
            true,
        ),
        (
            3,
            "a chain of `k` literal-armed `if`s bound one after another",
            true,
        ),
        (4, "`if`s nested `k` deep in arms", true),
    ] {
        let terms = scaling::inputs(512, |k| nest(form, k as i64));
        scaling::check(&format!("the one pass over {what}"), 512, |k| {
            arms_and_value(&terms[&k], &scope);
        });
        if reference {
            scaling::check(&format!("the reference over {what}"), 512, |k| {
                arms_and_value_by_transfer(&terms[&k], &scope);
            });
        }
    }
}
