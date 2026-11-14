//! The `cite` tool's time, linear in the citations; that they pass is checked at small sizes by
//! `cite::many_lines_of_citations_pass_at_small_sizes`.

use zed_tests::scaling::check;

use crate::cite::{CITATIONS, cites_pass, design, tree};

#[test]
fn cite_scales_with_the_number_of_citations() {
    let n = 2000;
    let texts = [CITATIONS.repeat(n), CITATIONS.repeat(8 * n)];
    let design = design("");
    let trees = texts.each_ref().map(|t| tree(&[("src/a.rs", t)]));
    check("cite, by citations", n, |m| {
        cites_pass(&design, &trees[usize::from(m != n)]);
    });
}
