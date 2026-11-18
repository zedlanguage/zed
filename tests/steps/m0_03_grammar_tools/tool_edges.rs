//! Edge cases of `progress` and the fence layout: a step title cut to its length, lines that
//! only look like steps, and a documentation fence. (A spec with no table of defined words is
//! refused by the table's reader: `layer_roles`.)

use zed_tools::spec::Spec;
use zed_tools::{fence_layers, progress};

use super::{DOUBLE, design, fence, spec_dir};

/// A title over 110 characters is cut to 107 and an ellipsis; one of 110 is kept whole. A line
/// whose name has no layer number, no step number or no `.` after the name is no step.
#[test]
fn progress_cuts_a_long_title_and_skips_what_is_no_step() {
    let long = "w".repeat(120);
    let exact = "x".repeat(110);
    let spaced = format!("{} {}", "y".repeat(106), "z".repeat(10));
    let plan = format!(
        "## (sec:steps) The steps, layer by layer\n\n### L1: one\n\n\
         L1.1. {long}\nL1.2. {exact}\nL1.3. {spaced}\n\
         L.4. No layer number.\nL1.x. No step number.\nM0.5 No dot.\nM0. No number.\n\
         S.1a. A lettered step.\nQ1.1. Another letter.\n"
    );
    let (text, done, total) = progress::render(&plan, "", None).expect("a plan");
    assert_eq!((done, total), (0, 4), "{text}");
    assert!(
        text.contains(&format!("- [ ] **L1.1** {}…\n", "w".repeat(107))),
        "{text}"
    );
    assert!(
        text.contains(&format!("- [ ] **L1.2** {exact}\n")),
        "{text}"
    );
    // The cut drops the space before the ellipsis.
    assert!(
        text.contains(&format!("- [ ] **L1.3** {}…\n", "y".repeat(106))),
        "{text}"
    );
    assert!(text.contains("- [ ] **S.1a** A lettered step.\n"), "{text}");
    assert!(text.ends_with("A lettered step.\n"), "{text}");
}

/// A fence in documentation notation is laid out as such, and a program fence is not.
#[test]
fn a_documentation_fence_is_laid_out_as_notation() {
    let body = format!("{}\n{}", fence("double: int -> int"), fence(DOUBLE));
    let dir = spec_dir("lay_doc", &design(&body), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let laid = fence_layers::of_document(&dir.at("DESIGN.md"), &spec).expect("the fences lay out");
    assert_eq!(
        laid.iter().map(|f| f.notation).collect::<Vec<_>>(),
        [true, false]
    );
}
