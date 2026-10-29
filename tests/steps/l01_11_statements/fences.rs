//! Every block in expression position in the documentation's fences builds, or names the
//! later step or layer of a form inside it. A block in a declaration's body is built with the
//! declaration, from step L1.12.

use zed_tests::fences;
use zedc::ast::expr;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

#[test]
fn every_block_in_expression_position_builds_or_names_its_step() {
    let (mut built, mut later, mut wrong) = (0, 0, Vec::new());
    for f in fences::all() {
        let tokens = lex_fence(&f.text).unwrap();
        let start = if f.notation { "DocFence" } else { "Unit" };
        let tree = parse(&f.text, &tokens, start, TOP).unwrap();
        for (p, node) in tree.nodes.iter().enumerate() {
            if !matches!(tree.name(p), "Primary" | "Lambda" | "ElseTail") {
                continue;
            }
            for &n in &node.kids {
                if tree.name(n) != "Block" {
                    continue;
                }
                match expr(&f.text, &tokens, &tree, n) {
                    Ok(_) => built += 1,
                    Err(e) if e.message.contains(" is built from ") => later += 1,
                    Err(e) => wrong.push(format!("{}: {e}", f.at)),
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    assert_eq!((built, later), (1, 0), "built, later");
}
