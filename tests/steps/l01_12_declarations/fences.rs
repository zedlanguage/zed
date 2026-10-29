//! Every unit in the documentation's fences builds, or names the later layer of a form in it.

use zed_tests::fences;
use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

#[test]
fn every_unit_builds_or_names_its_layer() {
    let (mut built, mut later, mut wrong) = (0, 0, Vec::new());
    for f in fences::all().iter().filter(|f| !f.notation) {
        let tokens = lex_fence(&f.text).unwrap();
        let tree = parse(&f.text, &tokens, "Unit", TOP).unwrap();
        match unit(&f.text, &tokens, &tree) {
            Ok(_) => built += 1,
            Err(e) if e.message.contains(" is built from layer L") => later += 1,
            Err(e) => wrong.push(format!("{}: {e}", f.at)),
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    // 23 and 113 at step L1.12; later steps build more.
    assert!(
        built >= 23 && built + later == 136,
        "built {built}, later {later}"
    );
}
