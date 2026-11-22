//! A panic in zedc is reported as a bug in zedc, not in the program (DESIGN.md
//! sec:diagnostics): what zedc expected, where in zedc it stopped, and where to report it.
//! Every message for a bug in zedc opens with one sentence and ends with one request to report
//! it at one address (plan row MSG-bug-sentence-one).

use zed_kernel::KernelError;
use zed_kernel::bug::{REPORT_TO, Stopped, opening, report};
use zedc::lex::Span;
use zedc::rejection::{VERSION, bug, bug_at, run_bug, run_bug_at};
use zedc::store::wto::SameKey;
use zedc::work::{Place, Stage};

/// The report says in plain words what happened and which declaration zedc was at work on,
/// asks for the report, and puts zedc's version, the stage, the declaration, the unit, what zedc
/// expected and zedc's own file and line in a details block after it (plan row
/// MSG-bug-report-plain, author 2026-11-09 and 2026-11-15).
#[test]
fn a_bug_names_the_declaration_in_plain_words_and_the_rest_in_details() {
    let at = Place {
        stage: Some(Stage::Elaborate),
        unit: Some("main.zed".into()),
        declaration: Some("f".into()),
    };
    assert_eq!(
        bug_at(
            "every name of a unit is resolved before it is elaborated",
            Some(("crates/zedc-elab/src/elab.rs", 120)),
            &at
        ),
        format!(
            "zedc stopped because of a bug in zedc, not in your program. zedc expected something \
             of its own to hold, and it did not, while it was at work on the declaration `f` in \
             `main.zed`.\nPlease report it at {REPORT_TO}, with the command line you ran, the \
             files it read and the details below, so that it can be repeated.\n\
             Details for the report:\n  zedc version: {VERSION}\n  stage: elaborate\n  \
             declaration: f\n  unit: main.zed\n  expected: every name of a unit is resolved \
             before it is elaborated\n  in zedc at: crates/zedc-elab/src/elab.rs, line 120"
        )
    );
}

/// Where zedc knows no place and no file and line, the report names none, and the details
/// still give the version and what zedc expected.
#[test]
fn a_bug_with_no_place_names_none() {
    let text = bug_at("something it does not describe", None, &Place::default());
    assert_eq!(
        text,
        format!(
            "zedc stopped because of a bug in zedc, not in your program. zedc expected something \
             of its own to hold, and it did not.\nPlease report it at {REPORT_TO}, with the \
             command line you ran, the files it read and the details below, so that it can be \
             repeated.\nDetails for the report:\n  zedc version: {VERSION}\n  expected: \
             something it does not describe"
        )
    );
}

/// A run's report names the declaration too and keeps the program's content address in its
/// plain part, where a record of the run names it (EXE-bug-report-address).
#[test]
fn a_run_bug_names_the_declaration_and_the_program() {
    let at = Place {
        stage: Some(Stage::Run),
        unit: None,
        declaration: Some("main".into()),
    };
    let text = run_bug_at("a wave commits once", Some(("run.rs", 9)), None, &at);
    assert!(
        text.starts_with(
            "the run stopped because of a bug in zedc, not in your program. zedc expected \
             something of its own to hold, and it did not, while it was at work on the \
             declaration `main`.\nPlease report it at "
        ) && text.ends_with(&format!(
            "Details for the report:\n  zedc version: {VERSION}\n  stage: run\n  declaration: \
             main\n  expected: a wave commits once\n  in zedc at: run.rs, line 9"
        )),
        "{text}"
    );
}

/// Checking a unit leaves the place a report names at its last top-level declaration, under
/// the stage the checker marks; the mark's end gives back the outer place.
#[test]
fn checking_a_unit_marks_each_top_level_declaration() {
    use zed_tests::step_helpers::l01_16_elaboration::checked;
    let seen = std::cell::RefCell::new(Vec::new());
    zedc::work::stage(Stage::Check, None, || {
        checked("f(positional n: int) = n + 1;\ng = f(2);\n");
        seen.borrow_mut().push(zedc::work::place());
    });
    let seen = seen.into_inner();
    assert_eq!(seen[0].declaration.as_deref(), Some("g"), "{seen:?}");
    assert_eq!(seen[0].stage, Some(Stage::Check), "{seen:?}");
}

/// Each message for a bug in zedc that a test can reach from outside its crate: zedc's report
/// of a panic, a run's report of one, the evaluator's ill-typed operation, the runtime's
/// broken invariant and the fixpoint order's two cells with one key. Each opens with the
/// shared sentence and ends with the shared request, so it says the same thing in the same
/// words wherever zedc stops. The code generator's and the lowering's messages are checked
/// in `l01_36_cranelift` and `l01_33_lowering`, where their failures are reached.
#[test]
fn every_bug_text_opens_with_one_sentence_and_names_one_address() {
    let span = Span { start: 0, end: 1 };
    let texts = [
        (Stopped::Zedc, bug("a thing", Some(("f.rs", 1)))),
        (Stopped::Run, run_bug("a thing", None, None)),
        (
            Stopped::Run,
            KernelError::Type("`!` applied to `int`".into()).to_string(),
        ),
        (Stopped::Run, zed_rt::bug("did a thing", "place 7")),
        (
            Stopped::Zedc,
            SameKey {
                name: "x".into(),
                cells: [0, 1],
                spans: [span, span],
            }
            .to_string(),
        ),
    ];
    for (who, text) in texts {
        assert!(text.starts_with(&opening(who)), "{text}");
        // The request is a line of its own: the last, or the last before the details block.
        let plain = text.split("\nDetails for the report:").next().unwrap();
        let (_, last) = plain
            .rsplit_once('\n')
            .expect("the request on a line of its own");
        assert!(
            last.starts_with(&format!("Please report it at {REPORT_TO}, with "))
                && last.ends_with(", so that it can be repeated."),
            "{text}"
        );
        assert!(!text.contains("itself"), "{text}");
    }
}

/// The address a bug is reported at is written once, in `zed_kernel::bug`: no crate defines a
/// second one.
#[test]
fn the_address_a_bug_is_reported_at_is_defined_once() {
    let crates = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../crates");
    let mut found = Vec::new();
    let mut dirs = vec![crates];
    while let Some(d) = dirs.pop() {
        for e in std::fs::read_dir(&d).expect("a readable directory") {
            let p = e.expect("an entry").path();
            if p.is_dir() {
                dirs.push(p);
            } else if p.extension().is_some_and(|x| x == "rs") {
                let text = std::fs::read_to_string(&p).expect("a readable source file");
                if text.contains("const REPORT_TO") {
                    found.push(p);
                }
            }
        }
    }
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].ends_with("zed-kernel/src/bug.rs"), "{found:?}");
}

/// The shared form itself: the opening, the body as given, and the request on its own line.
#[test]
fn the_shared_form_puts_the_request_on_its_own_line() {
    assert_eq!(
        report(Stopped::Run, "Body.", "the program's source"),
        format!(
            "the run stopped because of a bug in zedc, not in your program. Body.\nPlease report \
             it at {REPORT_TO}, with the program's source, so that it can be repeated."
        )
    );
}
