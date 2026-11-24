use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

/// `0.5f64 ^ (3^m)`: the exponent folds to `3^m`, whose text is that power form. Through the
/// arrow `f64 ^ int` (plan row POW-domains, b22-checkwalk10, 2026-11-24) it is an exact `int`
/// and is accepted; before, it was read at `f64` and refused with its nearest `f64`, read from
/// the value (`Rat::to_f64`, in `menu`). The fold is O(m) at most (bench `l01_29
/// bench::too_large::folding_a_power_of_a_huge_exponent_scales`); printing the value's digits
/// would cost O(M(m) log m).
///
/// Besides its ratio: no error. Small instance:
/// `fixes::an_exponent_folded_past_f64_lists_the_nearest_whatever_its_text`.
#[test]
fn a_huge_folded_exponent_of_an_f64_scales() {
    scaling::on_a_thread(1 << 29, || {
        let n = 1 << 17;
        let units = scaling::inputs(n, |m| Resolved::new(&format!("f() = 0.5f64 ^ (3^{m});\n")));
        for (m, u) in &units {
            assert_eq!(u.type_errors(), Vec::<String>::new(), "3^{m}");
        }
        scaling::check("`3^m` folded as the exponent of an f64", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}
