use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::spelling::{misuses, tuple};

#[test]
fn printing_the_spellings_of_many_literals_scales() {
    let n = 250;
    let texts = scaling::inputs(n, misuses);
    scaling::check("checking n misused literals and printing each", n, |m| {
        assert_eq!(type_errors(&texts[&m]).len(), m);
    });
}

#[test]
fn printing_a_tuple_of_many_literals_scales() {
    let n = 6200;
    let texts = scaling::inputs(n, tuple);
    scaling::check("checking a tuple of n literals and printing it", n, |m| {
        let errors = type_errors(&texts[&m]);
        assert!(
            errors[0].contains(&format!("{}.50r))", m - 1)),
            "{errors:?}"
        );
    });
}
