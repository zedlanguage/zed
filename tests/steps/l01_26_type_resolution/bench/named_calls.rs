use zed_tests::scaling;

use super::super::named_calls::misplaced_arguments;
use super::super::scaling::resolved;

/// Item NUM-huge-div: n misplaced arguments, each in an operation and in a name read once more,
/// give their n errors and no more in linear time: an application of an argument with no value
/// asks one set of spans, once per argument.
#[test]
fn many_misplaced_arguments_in_operations_check_in_linear_time() {
    let units = resolved(640, misplaced_arguments);
    scaling::check("n misplaced arguments in operations", 640, |n| {
        assert_eq!(units[&n].check().errors.len(), 2 * n);
    });
}
