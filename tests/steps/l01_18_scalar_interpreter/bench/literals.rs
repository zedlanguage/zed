//! Rounding a float literal at the rule of low complexity. The inputs are built in
//! `literals.rs`, whose test `a_long_literal_rounds_by_every_digit` checks them at a small
//! size.

use std::collections::HashMap;

use zed_kernel::num::LiteralRounding;
use zed_tests::scaling::{check, check_instructions_only, check_order, inputs};
use zed_tests::step_helpers::l01_16_elaboration::elab;

/// `zed_kernel::num::literal_f64` of a decimal; every text of these benchmarks is one.
fn literal_f64(text: &str) -> Result<f64, LiteralRounding> {
    zed_kernel::num::literal_f64(text).expect("a decimal")
}

use super::super::literals::{corpus_lines, digits_above_a_tie, digits_near_one};

/// TESTS-float-text-corpus: reading the texts of a hard-case corpus, each of at most 90
/// characters, costs a bounded amount each, so n of them cost order n.
#[test]
fn reading_many_literals_of_a_hard_case_corpus_scales() {
    // It allocates nothing, and takes about 78 ns a text: 1x about 20 ms, 8x 0.16 s (Colab hm5,
    // 2026-11-22).
    let n = 1 << 18;
    let built = inputs(n, corpus_lines);
    check_instructions_only(
        "reading n float literals of a hard-case corpus",
        n,
        1,
        |m| {
            let wrong = built[&m]
                .iter()
                .filter(|&&(text, bits)| literal_bits(text) != bits)
                .count();
            assert_eq!(wrong, 0);
        },
    );
}

/// TESTS-float-text-corpus: printing a float as its shortest text (`show_f64`, Schubfach)
/// costs a bounded amount each, so n floats cost order n; no other test scales float printing.
#[test]
fn printing_many_floats_of_a_hard_case_corpus_scales() {
    // About 120 ns and 18 bytes a float: 1x about 32 ms, 8x 0.25 s (Colab hm5, 2026-11-22).
    let n = 1 << 18;
    let built = inputs(n, corpus_lines);
    check("printing n floats of a hard-case corpus", n, |m| {
        let chars: usize = built[&m]
            .iter()
            .map(|&(_, bits)| zed_kernel::num::show_f64(f64::from_bits(bits)).len())
            .sum();
        assert!(chars >= m);
    });
}

/// The `f64` encoding of the decimal `text` as IEEE 754 reads it, infinities and zeros kept.
fn literal_bits(text: &str) -> u64 {
    zed_kernel::num::read_f64_ieee(text)
        .expect("a decimal")
        .to_bits()
}

#[test]
fn elaborating_a_literal_of_n_digits_scales() {
    // About 8 ns and 5 bytes a digit: 1x about 0.27 s, 1.3 GB at 8n, 6 s in all.
    let n = 1 << 25;
    let built: HashMap<usize, String> = inputs(n, |n| format!("v = {}f64;\n", digits_near_one(n)));
    check_order("a float literal of n digits", n, 1, |n| {
        elab(&built[&n]).unwrap();
    });
}

#[test]
fn rounding_a_literal_of_n_digits_scales() {
    // The rounding alone: at 2000 digits the rest of the pipeline did about 2.6 times its
    // work, enough to hide a quadratic added to it (COMPLEXITY.md F85). It allocates nothing,
    // and takes about 0.7 ns a digit: 1x about 0.1 s. 0.6 s would take 2^30 digits, whose
    // text at 8n alone is 8 GB; the texts of 2^27 and 2^30 digits hold 1.2 GB.
    let n = 1 << 27;
    let built = inputs(n, digits_near_one);
    check_instructions_only("rounding a float literal of n digits", n, 1, |n| {
        assert!(literal_f64(&built[&n]).is_ok());
    });
}

#[test]
fn rounding_a_literal_of_n_digits_near_a_tie_scales() {
    // About 1.2 ns a digit, allocating nothing: 1x about 0.16 s; the texts of 2^27 and 2^30
    // digits hold 1.2 GB.
    let n = 1 << 27;
    let built = inputs(n, digits_above_a_tie);
    check_order(
        "rounding a float literal of n digits near a tie",
        n,
        1,
        |n| {
            assert_eq!(literal_f64(&built[&n]), Ok(1.0 + f64::EPSILON));
        },
    );
}
