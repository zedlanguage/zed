//! A mutant is named by its definition, the node's position in it and the replacement, and
//! mutants are reported in that order, so moving declarations moves no mutant in the report.

use super::report;

/// The report without each line's `line:col: `, which moves with the text.
fn names(text: &str) -> Vec<String> {
    report(text)
        .into_iter()
        .map(|l| match l.split_once(": ") {
            Some((place, rest)) if place.contains(':') => rest.to_string(),
            _ => l,
        })
        .collect()
}

const A: &str = "isMinor(positional age) = age < 18 test { 5 -> true, 40 -> false }\n";
const B: &str = "limit = 10;\n";
const C: &str = "scale(positional x) = x * (2 + 0) test { 3 -> 6 }\n";

#[test]
fn reordering_declarations_keeps_the_report_order() {
    let first = names(&[A, B, C].concat());
    for order in [[B, C, A], [C, A, B], [C, B, A]] {
        assert_eq!(names(&order.concat()), first);
    }
    // Definitions by name: `isMinor`, `limit`, `scale`.
    let defs: Vec<&str> = first
        .iter()
        .filter_map(|l| l.split(" in `").nth(1)?.split('`').next())
        .collect();
    assert_eq!(
        defs,
        ["isMinor", "isMinor", "isMinor", "limit", "limit", "scale"]
    );
}

#[test]
fn moving_a_definition_down_changes_only_its_line() {
    let before = report(&[A, C].concat());
    let after = report(&["\n\n", A, C].concat());
    let shift = |l: &String| match l.split_once(':') {
        Some((line, rest)) if line.parse::<usize>().is_ok() => {
            format!("{}:{rest}", line.parse::<usize>().unwrap() + 2)
        }
        _ => l.clone(),
    };
    assert_eq!(after, before.iter().map(shift).collect::<Vec<_>>());
}
