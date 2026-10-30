//! Step L1.21: the `test { }` runner. From here on a test of what a Zed program computes is
//! written in Zed: each step's `zed/` folder holds units whose tables and ✗ marks
//! `zedc test` checks. The tests here check the runner itself.

mod command;
mod fences;
mod marks;
mod tables;
mod zed;

use zedc::testing::test;

/// The checks of `text`, each as `line:col: ok` or `line:col: why`.
pub(crate) fn checks(text: &str) -> Vec<String> {
    test(text)
        .into_iter()
        .map(|o| {
            let why = o.failure.unwrap_or_else(|| "ok".into());
            format!("{}:{}: {why}", o.line, o.col)
        })
        .collect()
}
