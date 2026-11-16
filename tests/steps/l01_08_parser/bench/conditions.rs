//! Finding `<-` or `=` written in a condition takes two more parses and one scan of the unit,
//! each linear: the benchmarks of `push_or_less.rs` and `assign_in_condition.rs`, whose tests
//! report each input at small sizes.

use zed_tests::scaling::{check, inputs};
use zedc::rejection::Row;

use crate::assign_in_condition::bindings_before_a_binding;
use crate::push_or_less::{
    a_long_bad_target, bindings_before_a_bad_target, bindings_before_a_push, refusal,
    terms_before_a_push,
};

/// The time is linear in the number of statements before the condition, and in its length
/// (COMPLEXITY.md, PITFALL-push-vs-less and PITFALL-assign-in-condition).
#[test]
fn finding_a_push_or_a_binding_in_a_condition_is_linear() {
    let many = inputs(500, bindings_before_a_push);
    check("n bindings before `if x<-1 {`", 500, |n| {
        assert_eq!(refusal(&many[&n]).row, Some(Row::PushWhereLessMeant));
    });
    let long = inputs(500, terms_before_a_push);
    check("a condition of n terms ending in `x<-1`", 500, |n| {
        assert_eq!(refusal(&long[&n]).row, Some(Row::PushWhereLessMeant));
    });
    let many = inputs(500, bindings_before_a_binding);
    check("n bindings before `if x = 3 {`", 500, |n| {
        assert_eq!(refusal(&many[&n]).row, Some(Row::BindingInCondition));
    });
}

/// The time is linear in the number of statements before a push whose target cannot be pushed
/// to, and in the length of the target (COMPLEXITY.md, FAIL-pitfall-rows-statement-push-near-miss).
#[test]
fn finding_a_target_that_cannot_be_pushed_to_is_linear() {
    let many = inputs(500, bindings_before_a_bad_target);
    check(
        "n bindings before `m.stdout::bytes::len <- \"a\";`",
        500,
        |n| {
            assert_eq!(refusal(&many[&n]).row, Some(Row::PushTargetNotPushable));
        },
    );
    let long = inputs(500, a_long_bad_target);
    check(
        "a target of n fields and keys before `::bytes::len <-`",
        500,
        |n| {
            assert_eq!(refusal(&long[&n]).row, Some(Row::PushTargetNotPushable));
        },
    );
}
