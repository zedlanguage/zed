//! Placing diagnostics at the rule of low complexity (DESIGN.md Part G). Each diagnostic and
//! each of its steps was placed by decoding the file from its first byte, so a file of `n`
//! lines with an error on each took `O(n²)`.

use zed_tests::scaling;

use super::rejected;

/// `n` definitions, each reading a name nothing declares.
fn unresolved(n: usize) -> String {
    (0..n).map(|i| format!("f{i} = missing{i};\n")).collect()
}

#[test]
fn placing_a_diagnostic_on_every_line_scales() {
    scaling::check("placing a diagnostic on each of n lines", 500, |n| {
        let out = rejected(&unresolved(n));
        // One diagnostic per line, the last at the last line, after `f{n-1} = `.
        let last = n - 1;
        let col = format!("f{last} = ").len() + 1;
        assert_eq!(out.lines().count(), n);
        let want = format!("{n}:{col}: `missing{last}` is not defined");
        assert_eq!(out.lines().last(), Some(want.as_str()));
    });
}
