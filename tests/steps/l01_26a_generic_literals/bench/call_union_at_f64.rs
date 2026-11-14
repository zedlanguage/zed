use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::call_union_at_f64::nest;

#[test]
fn scaling() {
    // Complexity tradeoff (DESIGN.md Part G): whether an argument may be read is found by
    // one walk over the branches of its `if`s, each visited once, O(n); then the values of
    // its type outside `f64` are listed once, each is cast once, and the parts are joined in
    // pairs, as for a cast of the union, O(n log n). Listing them again for each value, or
    // walking the branches again for each, would be O(n^2). The small instance is
    // `a_call_of_many_listed_values_and_an_if_of_many_branches_are_read_at_f64`.
    scaling::on_a_thread(1 << 29, || {
        let n = 250;
        let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
        scaling::check(
            "reading a call of n listed values and an `if` of n branches at `f64`",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
