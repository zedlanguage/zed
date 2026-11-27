//! Every expression in the documentation's fences builds, or names the later step or layer
//! of a form inside it.

use zed_tests::fences;
use zedc::ast::expr;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

#[test]
fn every_expression_in_the_fences_builds_or_names_its_step() {
    let (mut built, mut later, mut wrong) = (0, 0, Vec::new());
    for f in fences::parsed() {
        let tokens = lex_fence(&f.text).unwrap();
        let start = if f.notation { "DocFence" } else { "Unit" };
        let tree = parse(&f.text, &tokens, start, TOP).unwrap();
        for n in 0..tree.nodes.len() {
            if tree.name(n) != "Expr" {
                continue;
            }
            match expr(&f.text, &tokens, &tree, n) {
                Ok(_) => built += 1,
                Err(e) if zed_tests::is_not_yet(&e.message) => later += 1,
                Err(e) => wrong.push(format!("{}: {e}", f.at)),
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    // 1505 and 309 at step L1.10; later steps build more. The sec:ports fence of creating and
    // removing directories (STUDY-dir-edit) brings 3496; the sec:ports fence of removing a file
    // (SPEC-file-remove) and EXAMPLES 25.1 inside `main` (SPEC-top-level-statement-fences)
    // bring 3502.
    assert!(
        built >= 1505 && built + later == 3502,
        "built {built}, later {later}"
    );
}
