//! Item K30-rest at the rule of low complexity: the copies of a joined string. Their answers are
//! checked exactly in `string_copies.rs`, by
//! `the_copies_of_a_joined_string_are_exact_when_memory_is_given` and
//! `a_joined_string_is_padded_with_no_copy_when_memory_is_short`.

use std::fmt::Write as _;

use zed_kernel::{Prim, Text};
use zed_tests::scaling::{check_order, inputs};

use super::super::string_copies::{Count, atom, halves, joined, word};

/// The work of `upper`, `lower`, `trim`, an atom's name and the display of a joined string with
/// a width is linear in its bytes.
#[test]
fn the_copies_of_a_joined_string_scale() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 46 ns a
    // byte, 1x 0.38 s, 1.0 GB at 8n; at 12 MiB the test took 16 s.
    let n = 8usize << 20;
    let strings = inputs(n, |b| {
        let a = "a".repeat(b / 2);
        let padded: Text = joined(&[" ", &a, &a, " "]);
        (halves('a', b), halves('A', b), padded)
    });
    check_order(
        "upper, lower, trim, an atom name and a display with a width of a joined string, by bytes",
        n,
        1,
        |b| {
            let (a, big_a, padded) = &strings[&b];
            word(Prim::Upper, a.clone()).expect("upper");
            word(Prim::Lower, big_a.clone()).expect("lower");
            word(Prim::Trim, padded.clone()).expect("trim");
            atom(a.clone(), vec![], vec![]).expect("an atom");
            let mut out = Count::default();
            write!(out, "{a:>20}").expect("the writer takes it");
        },
    );
}
