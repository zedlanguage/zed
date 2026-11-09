use super::run;
use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

/// Every documentation unit that builds resolves, or fails only on what a fragment leaves to
/// the text around it: a name or type it does not bind, or a rebinding the fence marks ✗; or
/// on a form of layer L2, L3, L5 or L6 that the parser builds and a later step compiles, or an
/// annotation, prelude word or prelude type of a later layer; or on an import, which a fragment read alone,
/// with no package around it, cannot follow.
#[test]
fn every_building_fence_resolves_but_for_its_free_names() {
    let (mut resolved, mut built) = (0, 0);
    for f in zed_tests::fences::all().iter().filter(|f| !f.notation) {
        let tokens = lex_fence(&f.text).unwrap();
        let tree = parse(&f.text, &tokens, "Unit", TOP).unwrap();
        if unit(&f.text, &tokens, &tree).is_err() {
            continue;
        }
        built += 1;
        match run(&f.text) {
            Ok(_) => resolved += 1,
            Err(es) => {
                for e in es {
                    let free = e.contains(" is not defined: no ");
                    let marked = e.contains("already bound") && f.text.contains('✗');
                    let later = zed_tests::is_not_yet(&e);
                    // A fragment read alone has no package around it, so it imports no unit.
                    let alone = e.contains("cannot be imported: no manifest");
                    assert!(free || marked || later || alone, "{}: {e}", f.at);
                }
            }
        }
    }
    assert!(
        built >= 23 && resolved >= 2,
        "{built} built, {resolved} resolved"
    );
}

#[test]
fn the_corpus_program_that_builds_resolves() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../zed/corpus/09-canonical-equal.zed"
    );
    let text = std::fs::read_to_string(path).unwrap();
    assert!(run(&text).is_ok());
}
