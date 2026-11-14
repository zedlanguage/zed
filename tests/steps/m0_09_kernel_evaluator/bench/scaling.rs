//! The evaluator's values at the rule of low complexity (DESIGN.md Part G): reading a family
//! once per entry, a `foldl` of unions adding one entry per step and a chain of lets reading
//! its first name each linear in their size, and a discard linear in its entries and of order
//! `d²` in the depth of a caterpillar, by the keypaths it gives. What each asserts besides its
//! ratio is checked at small sizes by `scaling::each_read_yields_the_family` and
//! `scaling::unions_lets_and_discards_give_their_values_at_small_sizes`.

use zed_kernel::Value;
use zed_tests::scaling;

use crate::scaling::{accumulate, caterpillar, keeps_all, lets, reads, run, wide};

/// `f` on a thread with a stack of `bytes`.
fn on_stack(bytes: usize, f: impl FnOnce() + Send + 'static) {
    let t = std::thread::Builder::new().stack_size(bytes).spawn(f);
    t.unwrap().join().unwrap();
}

#[test]
fn reading_a_family_once_per_entry_scales() {
    for (how, what) in ["a literal", "a variable", "a tuple"]
        .into_iter()
        .enumerate()
    {
        scaling::check(
            &format!("reading {what} once per entry, by entries"),
            2000,
            |n| {
                run(&reads(n, how));
            },
        );
    }
}

#[test]
fn a_union_adding_one_entry_per_step_scales() {
    // Each union rebuilt both families from their leaves, and the family of the `n`
    // accumulators was built from all `n²/2` of their leaves: 75 s at 8,000 steps.
    on_stack(1 << 28, || {
        scaling::check("a foldl of unions, by steps", 1000, |n| {
            run(&accumulate(n));
        });
    });
}

#[test]
fn a_name_read_past_many_bindings_scales() {
    // Each lookup walked the frames from the innermost binding out: a chain of `n` lets cost
    // `n²/2` comparisons of names.
    on_stack(1 << 29, || {
        scaling::check(
            "a chain of lets reading the first name, by lets",
            2000,
            |n| {
                assert_eq!(run(&lets(n)), Value::Int(n as i64));
            },
        )
    });
}

#[test]
fn a_discard_scales_with_its_entries_and_the_keypaths_it_gives() {
    // Each level of a discard was rebuilt from the leaves of the levels below it: a family of
    // depth `d` cost `O(L·d²)`. Now a level keeps each kept family whole. A discard gives
    // the selector the keypath of each entry, so a chain of depth `d` with a leaf beside each
    // level gives keypaths of lengths 1 to `d`, `d²` keys in all: work of order `d²`, which
    // it is allowed. Rebuilding each level from its leaves cost `d³/3`.
    on_stack(1 << 29, || {
        scaling::check("a discard of n pairs, by n", 2000, |n| keeps_all(wide(n)));
        scaling::check_order("a discard of a caterpillar, by depth", 200, 2, |d| {
            keeps_all(caterpillar(d));
        });
    });
}
