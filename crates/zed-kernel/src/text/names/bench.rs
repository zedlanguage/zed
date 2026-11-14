//! The benchmark of [`Names`], run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates). It checks nothing besides the ratio; texts of many blocks
//! joined in every order are named in `tests.rs` (`texts_joined_in_any_order_have_one_name`).

use super::tests::join;
use super::*;

#[test]
fn naming_n_and_8n_nodes() {
    // A text of n blocks of LEAF bytes, joined from the left, each block different: n nodes, each
    // named once from its parts' summaries, O(n log N) dictionary steps.
    let texts = crate::scaling::inputs(5000, |n| {
        (0..n).fold(Text::from(""), |t, i| {
            let piece: String = (0..super::super::LEAF)
                .map(|j| char::from(b'a' + ((i * 7 + j * j) % 23) as u8))
                .collect();
            join(&t, &Text::from(piece))
        })
    });
    crate::scaling::check("naming a text of n blocks", 5000, |n| {
        let mut names = Names::new();
        std::hint::black_box(names.name(&texts[&n]));
    });
}
