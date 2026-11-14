//! Deep programs at the rule of low complexity, each linear in its depth: a recursion, a
//! tail-recursive loop, a chain of continuations, a recursion through regions, a traced
//! recursion and a list built by recursion. Each program runs at small sizes in
//! `deep::each_benchmark_program_returns_at_small_sizes`, and far deeper in the other tests of
//! `deep.rs`.

use zed_kernel::term::build::{app, lit};
use zed_kernel::{Evaluator, World, eval};
use zed_tests::deep::{linked_list, on_main_sized_stack};
use zed_tests::scaling;

use crate::deep::{continuations, count_down, through_regions, total};

#[test]
fn nested_calls_scale_with_depth() {
    scaling::check("a recursion, by nested calls", 20_000, |n| {
        eval(&total(n as i64)).unwrap();
    });
    scaling::check("a tail-recursive loop, by iterations", 20_000, |n| {
        eval(&count_down(n as i64)).unwrap();
    });
    scaling::check("a chain of continuations, by length", 20_000, |n| {
        eval(&continuations(n as i64, |then| app(then, vec![lit(0)]))).unwrap();
    });
    scaling::check("a recursion through regions, by depth", 5_000, |n| {
        eval(&through_regions(n as i64)).unwrap();
    });
}

#[test]
fn provenance_of_a_deep_recursion_scales_with_depth() {
    scaling::check("a traced recursion, by nested calls", 2_000, |n| {
        let mut ev = Evaluator::new(World::new()).with_provenance(vec![]);
        ev.run(&total(n as i64)).unwrap();
    });
}

#[test]
fn building_a_list_scales_with_its_length() {
    // The tuple primitive copied its values, so each element copied the whole list behind it:
    // 19,990 elements took 16 s. It now keeps the values it is given.
    on_main_sized_stack(|| {
        scaling::check("a list built by recursion, by length", 10_000, |n| {
            eval(&linked_list(n as i64)).unwrap();
        });
    });
}
