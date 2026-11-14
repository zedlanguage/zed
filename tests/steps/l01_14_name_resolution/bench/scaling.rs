//! Name resolution at the rule of low complexity (DESIGN.md Part G): the benchmarks of
//! `scaling.rs`, whose tests resolve each of their programs at small sizes.

use zed_tests::scaling;

use crate::run;
use crate::scaling::{
    DEEP_SHAPES, declares_overloads, deep_resolves, nested, used, uses_resolve, uses_share_one_list,
};

#[test]
fn names_read_inside_deeply_nested_blocks_scale() {
    // A name was looked for in each open scope in turn, innermost first.
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            scaling::check("names read in blocks nested n deep", 800, |n| {
                assert!(run(&nested(n)).is_ok());
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn declaring_many_overloads_scales() {
    // Each overload's parameter types were compared with those of every one before it.
    scaling::check("k overloads of one function", 1000, declares_overloads);
}

#[test]
fn using_many_overloads_scales() {
    // Each use of `f` copied the list of all `k` overloads, so `k` uses cost `k²`.
    // The statements are built before the timing, so only resolution is measured.
    let n = 1000;
    let built = scaling::inputs(n, used);
    scaling::check_order("k overloads of one function used k times", n, 1, |k| {
        uses_resolve(&built[&k], k);
    });
    uses_share_one_list(&uses_resolve(&built[&n], n), n);
}

/// Resolves each program of `shapes` on a 2 MiB stack, 100,000 deep and 12,500 deep, and checks
/// the time is linear. Resolution recursed once per level of nesting, and overflowed this stack
/// near 10,000.
fn resolves_deep(shapes: &[&str]) {
    use zed_tests::deep::{on_small_stack, program, statements};
    let n = 12_500;
    let deep = 8 * n;
    on_small_stack(|| {
        for &shape in shapes {
            let small = statements(&program(shape, n).text);
            let large = statements(&program(shape, deep).text);
            scaling::check_order(&format!("resolving {shape}"), n, 1, |k| {
                let stmts = if k == n { &small } else { &large };
                assert!(!zedc::resolve::resolve(stmts).unwrap().binders.is_empty());
            });
            deep_resolves(shape, &zedc::resolve::resolve(&large).unwrap(), deep);
        }
    });
}

#[test]
fn sums_negations_lambdas_and_long_bodies_100000_deep_resolve_on_a_2_mib_stack() {
    resolves_deep(&DEEP_SHAPES[0..4]);
}

#[test]
fn blocks_nested_100000_deep_resolve_on_a_2_mib_stack() {
    resolves_deep(&DEEP_SHAPES[4..5]);
}

#[test]
fn else_if_chains_and_parenthesized_sums_100000_deep_resolve_on_a_2_mib_stack() {
    resolves_deep(&DEEP_SHAPES[5..7]);
}

#[test]
fn calls_and_tuples_nested_100000_deep_resolve_on_a_2_mib_stack() {
    resolves_deep(&DEEP_SHAPES[7..9]);
}
