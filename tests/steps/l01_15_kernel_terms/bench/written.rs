//! Writing a term for a message is linear in the term: the benchmark of `written.rs`, run by
//! `tools/run_tests.sh --bench`. `written::a_short_chain_of_and_is_written_with_each_operator`
//! writes the same chains at small sizes and checks their text.

use zed_kernel::print::written;

use crate::written::{before_at, chain};

/// The text is linear in the term: `k` tests joined by `&&`, nested to the left and to the
/// right, each name renamed.
#[test]
fn written_text_scales_with_the_term() {
    zed_tests::deep::on_small_stack(|| {
        for left in [true, false] {
            let n = 2_000;
            let inputs = [n, zed_tests::scaling::FACTOR * n].map(|k| chain(k, left));
            let what = if left { "left" } else { "right" };
            zed_tests::scaling::check(&format!("written, && nested to the {what}"), n, |k| {
                let t = &inputs[usize::from(k != n)];
                std::hint::black_box(written(t, before_at, &|_| true));
            });
        }
    });
}
