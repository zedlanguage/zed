//! Ranges written on parameters at scale (RANGE-L1): a unit of `n` ranged parameters reads,
//! resolves and checks in time linear in `n`. The time is measured in `bench::ranges`; the unit
//! is checked small here.

/// One function of `n` ranged parameters, called once with each in its range; and `n`
/// functions of one ranged parameter each, each called once inside its range and once below
/// it. The calls below the range are the `n` errors.
pub(super) fn ranged_parameters(n: usize) -> String {
    let params: Vec<String> = (0..n)
        .map(|i| format!("x{i}: int[0..={}]", i + 9))
        .collect();
    let args: Vec<String> = (0..n).map(|i| format!("x{i}: {i}")).collect();
    let mut text = format!(
        "f({}) = x0;\na = f({});\n",
        params.join(", "),
        args.join(", ")
    );
    text.extend((0..n).map(|i| {
        format!(
            "g{i}(x: int[{i}..={}]) = x + 1;\nb{i} = g{i}(x: {i});\nc{i} = g{i}(x: {i} - 1);\n",
            i + 9
        )
    }));
    text
}

#[test]
fn ranged_parameters_give_one_error_per_call_below_the_range() {
    // A small instance of the benchmark `bench::ranges::ranged_parameters_check_in_linear_time`.
    let errors = super::type_errors(&ranged_parameters(3));
    assert_eq!(errors.len(), 3, "{errors:#?}");
    assert!(
        errors[0].starts_with("`g0` takes `x` in int[0..=9]"),
        "{}",
        errors[0]
    );
}
