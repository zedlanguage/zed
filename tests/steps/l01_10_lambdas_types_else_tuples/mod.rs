//! Step L1.10: lambdas with a declaration's parameter list, `is` and `is not` with the type
//! expressions they test against, `else` with its atom-pattern form, and tuples.

mod bench;
mod elses;
#[cfg(feature = "spec")]
mod fences;
mod lambdas;
mod later_types;
mod literals;
mod one_tuples;
mod scaling;
mod tests_of_types;
mod tuples;

pub(crate) use zed_tests::step_helpers::l01_10_lambdas_types_else_tuples::sx;

#[track_caller]
fn check(cases: &[(&str, &str)]) {
    zed_tests::tables::check(cases, sx);
}
