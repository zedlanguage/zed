//! Every unit in the documentation's fences builds, or names the later layer of a form in it.

use zed_tests::fences;
use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

#[test]
fn every_unit_builds_or_names_its_layer() {
    let (mut built, mut later, mut wrong) = (0, 0, Vec::new());
    for f in fences::parsed().iter().filter(|f| !f.notation) {
        let tokens = lex_fence(&f.text).unwrap();
        let tree = parse(&f.text, &tokens, "Unit", TOP).unwrap();
        match unit(&f.text, &tokens, &tree) {
            Ok(_) => built += 1,
            Err(e) if zed_tests::is_not_yet(&e.message) => later += 1,
            Err(e) => wrong.push(format!("{}: {e}", f.at)),
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    // 23 and 113 at step L1.12; later steps build more. The sec:type_language fence of a type
    // computed from a schema file (QUESTIONS A72) is the 212th; the two sec:units fences of a
    // `local` field (QUESTIONS A80) are the 213th and 214th; the two sec:ports fences of seeded
    // random numbers and of a foreign generator (SPEC-a108-interchangeable-ops) bring 216; the
    // sec:units fence of `buildFile` (SPEC-build-read-layers) and the two sec:ffi fences of a
    // packed struct and of integer handles (SPEC-packed-align, SPEC-ffi-int-handles) bring 219;
    // the sec:ports fence of creating and removing directories (STUDY-dir-edit) brings 220; the
    // sec:ports fence of removing a file (SPEC-file-remove) brings 221.
    assert!(
        built >= 23 && built + later == 221,
        "built {built}, later {later}"
    );
}
