//! Tables of test cases: each case is an input and the output it must give, and a table
//! reports every wrong case at once, not only the first. The one copy of the loop that the
//! parser steps each wrote (DRY-test-helpers).

/// Checks each `(text, want)` of `cases`: `f(text)` must be `want`. Panics naming every wrong
/// case, each with what it gave and what it should give.
#[track_caller]
pub fn check(cases: &[(&str, &str)], f: impl Fn(&str) -> String) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = f(text);
            (got != want).then(|| format!("{text}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// [`check`] for outputs that are lists of strings, printed as lists.
#[track_caller]
pub fn check_lists(cases: &[(&str, &[&str])], f: impl Fn(&str) -> Vec<String>) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = f(text);
            (got != want).then(|| format!("{text}\n  got  {got:?}\n  want {want:?}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
