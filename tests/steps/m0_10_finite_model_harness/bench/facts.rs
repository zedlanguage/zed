//! Demands nested past `MIN_NESTED_CALLS`, the nesting a test thread's stack must hold, each
//! entry recording its facts at its own keypath (author P178: an unusual size is a benchmark).
//! `scaling::a_demanded_entry_has_the_facts_it_has_in_rounds` makes the same checks a few
//! levels deep.

#[test]
fn demands_nested_past_the_minimum_have_the_facts_they_have_in_rounds() {
    crate::scaling::demanded_facts(zed_kernel::eval::MIN_NESTED_CALLS + 500);
}
