use zed_tests::scaling;

use super::super::need_free_names::compared_calls;
use super::super::scaling::resolved;

#[test]
fn calls_that_compare_a_string_entry_with_an_int_are_refused_in_linear_time() {
    // Each call meets `g`'s needs once and, refused, finds the use to name in one pass over
    // `g`'s parameters and needs, O(1) for this `g`, so n calls are O(n) in all (plan row
    // MSG-level-need-at-call-names-the-comparison). The small instance is
    // `each_call_that_compares_a_string_entry_with_an_int_names_the_comparison`.
    let n = 200;
    let units = resolved(n, compared_calls);
    let what = "n calls each comparing a String entry with an int";
    scaling::check(what, n, |k| {
        let info = units[&k].check();
        let named = (info.errors.iter())
            .filter(|e| e.message.contains("`m.any(x -> x > y)` in its body"))
            .count();
        assert_eq!(named, k, "{:?}", info.errors);
    });
}
