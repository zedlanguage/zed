//! Step L1.10: lambdas with a declaration's parameter list, `is` and `is not` with the type
//! expressions they test against, `else` with its atom-pattern form, and tuples.

mod elses;
mod fences;
mod lambdas;
mod later_types;
mod one_tuples;
mod scaling;
mod tests_of_types;
mod tuples;

pub(crate) use zed_tests::step_helpers::l01_10_lambdas_types_else_tuples::sx;

#[track_caller]
fn check(cases: &[(&str, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = sx(text);
            (got != want).then(|| format!("{text}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
