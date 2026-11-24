use zed_tests::scaling;

use super::super::docs::doc_blocks_with_links;

#[test]
fn checking_n_doc_blocks_with_links_scales() {
    // Lexing, parsing and resolution run before timing, so only the doc check is measured;
    // each size is built only in the process that checks it (`scaling::check_inputs`;
    // FAIL-bench-first-phase-past-20s-l0126-l0129).
    let input = |n: usize| {
        let src = doc_blocks_with_links(n);
        let (tokens, docs) = zedc::lex::lex_with_docs(&src).unwrap();
        let tree = zedc::parse::parse(&src, &tokens, "Unit", zedc::parse::TOP).unwrap();
        let stmts = zedc::ast::unit(&src, &tokens, &tree).unwrap();
        let res = zedc::resolve::resolve(&stmts).unwrap();
        (src, tokens, docs, res)
    };
    scaling::check_inputs(
        "n documented functions",
        32_000,
        input,
        |(src, tokens, docs, res)| {
            assert!(zedc::docs::check(src, tokens, docs, res).is_empty());
        },
    );
}
