use std::collections::HashMap;

use zed_tests::scaling;

use super::super::docs::doc_blocks_with_links;

#[test]
fn checking_n_doc_blocks_with_links_scales() {
    // Lexing, parsing and resolution run before timing, so only the doc check is measured.
    let inputs: HashMap<usize, _> = [1000, 8000]
        .into_iter()
        .map(|n| {
            let src = doc_blocks_with_links(n);
            let (tokens, docs) = zedc::lex::lex_with_docs(&src).unwrap();
            let tree = zedc::parse::parse(&src, &tokens, "Unit", zedc::parse::TOP).unwrap();
            let stmts = zedc::ast::unit(&src, &tokens, &tree).unwrap();
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (n, (src, tokens, docs, res))
        })
        .collect();
    scaling::check("n documented functions", 1000, |n| {
        let (src, tokens, docs, res) = &inputs[&n];
        assert!(zedc::docs::check(src, tokens, docs, res).is_empty());
    });
}
