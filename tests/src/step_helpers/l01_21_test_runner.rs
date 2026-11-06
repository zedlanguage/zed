//! Test-runner helpers of step L1.21 (tests/steps/l01_21_test_runner).

use zedc::testing::test;

/// The checks of `text`, each as `line:col: ok` or `line:col: why`.
pub fn checks(text: &str) -> Vec<String> {
    test(text)
        .into_iter()
        .map(|o| {
            let why = o.failure.unwrap_or_else(|| "ok".into());
            format!("{}:{}: {why}", o.line, o.col)
        })
        .collect()
}
