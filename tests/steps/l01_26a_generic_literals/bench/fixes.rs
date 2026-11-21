use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

/// `0.5f64 ^ (3^m)`: the exponent folds to `3^m`, whose text is that power form, and no `f64`
/// equals it; its nearest `f64` is read from the value (`Rat::to_f64`, in `menu`), which past
/// the range of `f64` is found from the power's size, not its digits. The fold and the message
/// are each O(m) at most (bench `l01_29 bench::too_large::folding_a_power_of_a_huge_exponent_
/// scales`); reading the nearest by printing the value's digits first would cost O(M(m) log m).
///
/// Besides its ratio: one rejection, with no fix. Small instance:
/// `fixes::an_exponent_folded_past_f64_lists_the_nearest_whatever_its_text`.
#[test]
fn the_nearest_f64_of_a_huge_folded_exponent_scales() {
    scaling::on_a_thread(1 << 29, || {
        let n = 1 << 17;
        let units = scaling::inputs(n, |m| Resolved::new(&format!("f() = 0.5f64 ^ (3^{m});\n")));
        for (m, u) in &units {
            assert_eq!(
                u.type_errors(),
                [format!("No `f64` equals the literal `3^{m}`. [(3^{m})]")]
            );
        }
        scaling::check("the nearest f64 of `3^m` folded as an exponent", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}
