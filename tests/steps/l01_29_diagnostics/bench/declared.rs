//! The declared step of a function of `n` parameters, at `n` and `8n` (`declared.rs`).

use zed_tests::scaling;

use crate::declared::{the_declared_step_of_wide, wide};

#[test]
fn the_declared_step_of_a_function_of_many_parameters_scales() {
    let n = 4000;
    let input = scaling::inputs(n, wide);
    scaling::check(
        "the declared step of a function of n parameters",
        n,
        |size| the_declared_step_of_wide(&input[&size], size),
    );
}
