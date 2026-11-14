use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::lit_branches::nest;

#[test]
fn scaling() {
    // Complexity tradeoff (DESIGN.md Part G): the branches are read once, each adopts once,
    // and their singletons are joined in pairs, O(n log n); joined one at a time, each union
    // copies the type so far, O(n^2). The small instance is
    // `an_if_of_many_literal_branches_takes_f64_at_a_parameter`.
    scaling::on_a_thread(1 << 29, || {
        let n = 880;
        let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
        scaling::check("checking an `if` of n literal branches at `f64`", n, |m| {
            units[&m].check();
        });
    });
}
