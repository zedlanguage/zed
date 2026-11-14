//! FAIL-limits-steps-memory (found by TEST-complete-m0, P188, P189).
//!
//! DESIGN.md M0.11: "compile-time evaluation has no resource limit, since checking code runs
//! only when it is total by algebraic evidence and the program's static calls run under the
//! partial-evaluation budgets (sec:checking_in_zed; author, 2026-11-09)" and "The minimum is
//! 20 000 nested calls; there is no minimum of steps or of memory, since no count of either may
//! stop compile-time evaluation." The prelude unit `limits` declared `minSteps` and `minMemory`
//! too, from before that decision.

#[test]
fn the_limits_unit_names_only_the_minimum_of_nested_calls() {
    let prelude = include_str!("../../../zed/prelude/limits.zed");
    let declared: Vec<&str> = prelude
        .lines()
        .filter(|l| !l.starts_with("//") && l.contains(" = "))
        .collect();
    assert_eq!(declared, ["minNestedCalls = 20000;"]);
}
