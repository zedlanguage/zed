//! Many random texts (author P178: many cases are a benchmark).
//! `rejected::the_span_is_the_first_text_nfc_changes` makes the same checks on 2,000.

#[test]
fn the_span_is_the_first_text_nfc_changes_on_20000_texts() {
    let seed = zed_tests::seed::seed("the_span_is_the_first_text_nfc_changes_on_20000_texts");
    crate::rejected::spans_of_random_texts(seed, 20_000);
}
