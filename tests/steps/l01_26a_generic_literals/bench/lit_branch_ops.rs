//! Complexity tradeoff (DESIGN.md Part G): each operation is kept once as its `if` is walked,
//! read and folded once as a branch of the argument, and adopts once, O(n) in the size of the
//! nest; the call's `n + 1` values are cast once each and their singletons joined in pairs,
//! O(n log n). Joined one at a time, each union copies the type so far, O(n^2). Small
//! instances: `many_operation_branches_take_f64_at_a_parameter_or_through_a_call`.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::lit_branch_ops::{nest, products, through_a_call, tuple_calls};

/// Checks `make(m)` at `n` and `8n`.
fn checks(what: &str, n: usize, make: fn(usize) -> String) {
    scaling::on_a_thread(1 << 29, || {
        let units = scaling::inputs(n, |m| Resolved::new(&make(m)));
        scaling::check(what, n, |m| {
            units[&m].check();
        });
    });
}

#[test]
fn scaling_an_if_of_operation_branches() {
    checks(
        "checking an `if` of n operation branches at `f64`",
        250,
        nest,
    );
}

#[test]
fn scaling_a_call_of_operation_branches() {
    checks(
        "reading a call of n operation branches at `f64`",
        250,
        through_a_call,
    );
}

/// Item LIT-op-reads-call: each operator application reads its call once per arrow,
/// O(A v log v) for A arrows and v values, so n products cost O(n).
#[test]
fn scaling_products_of_calls() {
    checks(
        "reading the calls of n products `x * g(c)` at `f64`",
        1000,
        products,
    );
}

/// Item LIT-tuple-branch-ops: each tuple's components are read once, and each `if` there is
/// walked once and adopts once, O(its size), so n calls cost O(n).
#[test]
fn scaling_ifs_in_tuple_arguments() {
    checks(
        "reading the `if`s of n tuple arguments at `(f64, f64)`",
        1000,
        tuple_calls,
    );
}
