//! Edge cases of `progress` and `sync`: a step title cut to its length, lines that only look
//! like steps, a documentation fence's copy, and a spec with no table of defined words (which
//! the layer table reader refuses first, so `sync`'s own refusal of it cannot be reached).

use std::fs;

use zed_tools::spec::Spec;
use zed_tools::{progress, sync};

use super::{design, fence, spec_dir};
use zed_tests::step_helpers::m0_03_grammar_tools::{KERNEL, zed_dir};

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

/// A fence in documentation notation is copied with that said in its header.
#[test]
fn sync_marks_the_copy_of_a_documentation_fence() {
    let body = format!("{}\n{KERNEL}", fence("double: int -> int"));
    let dir = spec_dir("sync_doc", &design(&body), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let zed = zed_dir("sync_doc_zed");
    let mut out = String::new();
    assert_eq!(
        sync::sync_into(&spec, &zed.root(), false, &mut out),
        Ok(true),
        "{out}"
    );
    let copied = fs::read_to_string(zed.at("fences/design.md")).unwrap();
    assert!(
        copied.contains(", documentation notation; section ["),
        "{copied}"
    );
}

/// A spec with no table of defined words is refused, naming the file; the layer of each fence
/// copied reads that table, so the refusal comes from that read, before `words.md` is built.
#[test]
fn sync_refuses_a_spec_with_no_table_of_defined_words() {
    let text = design(KERNEL).replace("| Layer | Annotations |", "| Level | Annotations |");
    let dir = spec_dir("sync_no_words", &text, "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let zed = zed_dir("sync_no_words_zed");
    let got = sync::sync_into(&spec, &zed.root(), false, &mut String::new());
    assert!(
        got.as_ref()
            .is_err_and(|e| e.starts_with("no table of defined words in ")
                && e.ends_with("/sync_no_words/DESIGN.md")),
        "{got:?}"
    );
}
