//! A panic in zedc is reported as a bug in zedc, not in the program (DESIGN.md
//! sec:diagnostics): what zedc expected, where in zedc it stopped, and where to report it.

use zedc::rejection::{REPORT_TO, bug};

#[test]
fn a_bug_names_what_zedc_expected_and_where_to_report_it() {
    assert_eq!(
        bug(
            "every name of a unit is resolved before it is elaborated",
            Some(("crates/zedc-elab/src/elab.rs", 120))
        ),
        format!(
            "zedc stopped because of a bug in zedc itself, not in your program. zedc expected \
             this to hold, and it did not: every name of a unit is resolved before it is \
             elaborated (crates/zedc-elab/src/elab.rs, line 120).\nPlease report it at \
             {REPORT_TO}, with the command line you ran and the files it read, so that it can be \
             repeated."
        )
    );
}

#[test]
fn a_bug_with_no_place_names_none() {
    let text = bug("something it does not describe", None);
    assert!(
        text.contains("it did not: something it does not describe.\nPlease report it at"),
        "{text}"
    );
}
