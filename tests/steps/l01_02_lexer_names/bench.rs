//! Lexing names is of order n log n in the length of the text: many names among text beyond
//! ASCII, one long name, and the error for a long word beyond ASCII with the name it offers,
//! whether the letter beyond ASCII ends a long ASCII run, the whole word is in another script,
//! or the offer must pass n names it may not take; and the error for a long comment or string
//! that ends in a `Bidi_Control` character, with its repair (DESIGN.md Part G). The benchmarks
//! of this step, run by `tools/run_tests.sh --bench`; `scaling.rs` makes each of their checks at
//! small sizes.

use zed_tests::scaling::{check, inputs};

use super::scaling::{
    comment_ending_in_a_bidi_control, escapes_it_in_the_string, hangul_word,
    lexes_five_tokens_a_line, lexes_one_name, long_name, long_name_ending_beyond_ascii,
    names_among_text_beyond_ascii, offers_the_ascii_spelling, offers_the_first_free_suffix,
    offers_the_transliteration, removes_it_from_the_comment, string_ending_in_a_bidi_control,
    taken_names,
};

/// Checks `expect` on the text `make` builds, lexed at sizes `n` and `8n`.
fn scales(what: &str, n: usize, make: fn(usize) -> String, expect: fn(&str, usize)) {
    let texts = inputs(n, make);
    check(what, n, |m| expect(&texts[&m], m));
}

#[test]
fn many_names_among_text_beyond_ascii_scale() {
    scales(
        "lexing 5n tokens",
        2_000,
        names_among_text_beyond_ascii,
        lexes_five_tokens_a_line,
    );
}

#[test]
fn one_long_name_scales() {
    scales(
        "lexing a name of 2n letters",
        20_000,
        long_name,
        lexes_one_name,
    );
}

#[test]
fn a_long_name_ending_in_a_letter_beyond_ascii_scales() {
    scales(
        "rejecting a name of 2n letters and `é`",
        20_000,
        long_name_ending_beyond_ascii,
        offers_the_ascii_spelling,
    );
}

#[test]
fn a_long_word_in_another_script_scales() {
    scales(
        "rejecting a Hangul word of 2n letters",
        20_000,
        hangul_word,
        offers_the_transliteration,
    );
}

#[test]
fn an_offer_past_many_taken_names_scales() {
    scales(
        "offering a name past n taken names",
        2_000,
        taken_names,
        offers_the_first_free_suffix,
    );
}

#[test]
fn a_long_comment_ending_in_a_bidi_control_scales() {
    scales(
        "rejecting a comment of 2n words and U+202E",
        20_000,
        comment_ending_in_a_bidi_control,
        removes_it_from_the_comment,
    );
}

#[test]
fn a_long_string_ending_in_a_bidi_control_scales() {
    scales(
        "rejecting a string of n holes and U+202E",
        2_000,
        string_ending_in_a_bidi_control,
        escapes_it_in_the_string,
    );
}
