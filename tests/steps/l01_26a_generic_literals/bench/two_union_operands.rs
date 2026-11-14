use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::two_union_operands::nest;

#[test]
fn scaling() {
    // Complexity tradeoff (DESIGN.md Part G): the carrier of `f(c, x) + f(c, x)` is found from
    // the parts each operand holds whole, once per operand, and each operand's v listed values
    // are read at it once, O(v log v); the decimal literals of the inline `if` are found by
    // one walk over its branches and each adopted once, O(n log n) with the join. Checking
    // each pair of values of the two operands, as each would be alone, costs O(v²). The small
    // instance is `two_calls_of_many_listed_values_and_an_if_of_many_decimals_check`.
    scaling::on_a_thread(1 << 29, || {
        let n = 440;
        let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
        scaling::check(
            "adding two calls of n listed values beside f64, and reading an `if` of n \
             decimal literals at `rat`",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
