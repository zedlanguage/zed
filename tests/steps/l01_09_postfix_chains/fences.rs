//! Every postfix chain in the documentation's fences builds, or names the later step or layer
//! of a form inside it.

use zed_tests::fences;
use zedc::ast::expr;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

#[test]
fn every_chain_in_the_fences_builds_or_names_its_step() {
    let (mut built, mut later, mut wrong) = (0, 0, Vec::new());
    for f in fences::all() {
        let tokens = lex_fence(&f.text).unwrap();
        let start = if f.notation { "DocFence" } else { "Unit" };
        let tree = parse(&f.text, &tokens, start, TOP).unwrap();
        for (n, node) in tree.nodes.iter().enumerate() {
            if tree.name(n) != "Postfix" || node.kids.len() < 2 {
                continue;
            }
            match expr(&f.text, &tokens, &tree, n) {
                Ok(e) => {
                    built += 1;
                    let s = e.span;
                    let first = tokens[node.start].span.start;
                    let last = tokens[node.end - 1].span.end;
                    if (s.start, s.end) != (first, last) {
                        wrong.push(format!("{}: span of {e}", f.at));
                    }
                }
                Err(e) if e.message.contains(" is built from ") => later += 1,
                Err(e) => wrong.push(format!("{}: {e}", f.at)),
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    assert_eq!((built, later), (512, 170), "built, later");
}
