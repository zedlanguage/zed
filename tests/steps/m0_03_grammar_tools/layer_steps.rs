//! `layer SPEC_DIR steps` (row LAYER-steps-check): the layer audit of the plan's steps (author
//! P254) rerun by the tool. A span of a step that needs a later layer is listed, as allowed
//! when its sentence names a later layer or step or a refusal, and the run fails on a span
//! listed and not allowed.

use super::{Dir, design, spec_dir, tool};
use zed_tools::layer::{self, steps};
use zed_tools::spec::Spec;

/// A steps section of `m` L1 steps, each with a span every layer reads and a span of a later
/// layer that its sentence allows, then `extra` as one more L1 step, an S step and an L2
/// heading with an L2 step that uses the same later form.
pub(crate) fn steps_section(m: usize, extra: &str) -> String {
    let mut s = String::from("## (sec:steps) The steps\n\n### L1 — scalars\n\n");
    for i in 0..m {
        s += &format!(
            "L1.{i}. The step reads `double{i}(x: int) -> int = x * 2;`. A range \
             `x in 0..=255` is refused here and comes at L5.\n\n"
        );
    }
    s += &format!("L1.{m}. {extra}\n\nS.1. The scaffolding uses `x in 0..=255`.\n\n");
    s += "### L5 — order\n\nL5.1. Ranges: `x in 0..=255`.\n\n# (sec:next) Next\n\nL1.99. `x in 0..=255` lies outside the section.\n";
    s
}

/// The audit of [`steps_section`]`(m, "")`, as the benchmark runs it: `m` listed spans, all
/// allowed, of `2m + 1` spans (the empty L1.m step has none and the S step is not read; the
/// L5 step has one).
pub(crate) fn audits_steps(spec: &Spec, section: &str, m: usize) {
    let a = steps::audit(spec, section);
    assert_eq!(a.listed.len(), m, "{a:?}");
    assert!(a.listed.iter().all(|l| l.allowed), "{a:?}");
    assert_eq!((a.spans, a.unread, a.other_steps), (2 * m + 1, 0, 1), "{a:?}");
}

#[test]
fn the_steps_benchmark_passes_at_small_sizes() {
    let dir = spec("steps_small", "");
    let s = Spec::open(&dir.root()).expect("the spec reads");
    for m in [0, 1, 2, 9] {
        audits_steps(&s, &steps_section(m, ""), m);
    }
}

/// The spec of a test, with the table of words and the grammars of `zed/grammar`.
fn spec(name: &str, body: &str) -> Dir {
    spec_dir(name, &design(body), "")
}

#[test]
fn a_later_form_in_an_l1_step_is_listed_and_fails_the_run() {
    let dir = spec("steps_listed", &steps_section(2, "Then `x in 0..=255` is read."));
    let s = Spec::open(&dir.root()).expect("the spec reads");
    let a = steps::audit(&s, &std::fs::read_to_string(&s.design).expect("DESIGN.md"));
    let listed: Vec<_> = a
        .listed
        .iter()
        .map(|l| (l.step.as_str(), l.span.as_str(), l.allowed))
        .collect();
    assert_eq!(
        listed,
        [
            ("L1.0", "x in 0..=255", true),
            ("L1.1", "x in 0..=255", true),
            ("L1.2", "x in 0..=255", false),
        ],
        "{a:?}"
    );
    assert!(a.listed.iter().all(|l| l.layer == 1 && l.ring > 1), "{a:?}");
    // Two spans per allowed step, one in the last L1 step, one in the L5 step.
    assert_eq!((a.spans, a.unread, a.other_steps), (6, 0, 1), "{a:?}");

    let (outcome, out) = tool(layer::run, &[&dir.root(), "steps"]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("L1.2 (L1) `x in 0..=255` needs L") && out.contains("NOT ALLOWED"),
        "{out}"
    );
    assert!(out.contains("6 spans in the steps of a layer, 3 listed, 1 not allowed"), "{out}");
}

#[test]
fn steps_whose_later_forms_are_all_allowed_pass() {
    let extra = "A step that names `len` and the form `x in 0..=255` of step L5.1.";
    let dir = spec("steps_allowed", &steps_section(1, extra));
    let (outcome, out) = tool(layer::run, &[&dir.root(), "steps"]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.contains("0 not allowed"), "{out}");
}

/// Prose in backticks and fenced code: the prose is counted as unread, the fence is not read.
#[test]
fn spans_that_parse_in_no_reading_are_counted_and_fences_are_left_out() {
    let extra = "The rule `Infix` and the words `no such form (` are named.\n\n\
                 ```zed\nf(x) = x in 0..=255;\n```";
    let dir = spec("steps_unread", &steps_section(0, extra));
    let s = Spec::open(&dir.root()).expect("the spec reads");
    let a = steps::audit(&s, &std::fs::read_to_string(&s.design).expect("DESIGN.md"));
    assert!(a.listed.iter().all(|l| l.step != "L1.0"), "{a:?}");
    assert_eq!(a.unread, 1, "{a:?}");
}
