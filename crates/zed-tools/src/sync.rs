//! `sync [SPEC_DIR] [--check]` runs the checks that read the spec's prose at `SPEC_DIR`, or at
//! `ZED_SPEC_DIR` when no directory is given: the kernel grammar whose rule names no message
//! prints, the prelude laws against `docs/mathlib-study.md`, the build modes and the kinds of
//! build DESIGN.md names ([`crate::spec_checks`]), and the citations of this repository
//! ([`crate::cite`]). It fails if a check fails. It writes nothing: this repository holds no copy
//! of the spec (author P371, P375). The tests read DESIGN.md and EXAMPLES.md in place (the
//! feature `spec` of the tests crate) and run the same checks there; this command remains
//! because /home/luke/Work/wt/merge-push.sh builds it and runs `sync DIR --check`, which is
//! accepted and changes nothing.

use crate::spec_checks::{build_modes, kernel_rules, prelude_laws};
use crate::text::read_text;
use crate::{Outcome, impl_root, say};

/// The variable that names the spec checkout when no directory is given.
pub const VAR: &str = "ZED_SPEC_DIR";

/// The usage line.
const USAGE: &str = "usage: sync [SPEC_DIR] [--check]";

/// The spec checkout the tool reads: the directory among `args` (all but `--check`), or else
/// `var`, the value of [`VAR`].
pub fn spec_dir(args: &[String], var: Option<String>) -> Result<String, String> {
    let mut dirs = args.iter().filter(|a| *a != "--check");
    match (dirs.next(), dirs.next()) {
        (Some(dir), None) => Ok(dir.clone()),
        (None, None) => var
            .filter(|v| !v.is_empty())
            .ok_or_else(|| format!("{USAGE}, or set {VAR}")),
        _ => Err(USAGE.into()),
    }
}

/// The checks of the spec's prose on the text `design` of DESIGN.md, with `page` the text of
/// `docs/mathlib-study.md`: what each checks, and its failure if it fails.
pub fn prose_checks(design: &str, page: &str) -> Vec<(&'static str, Result<(), String>)> {
    vec![
        ("the kernel grammar", kernel_rules(design).map(|_| ())),
        ("the prelude laws", prelude_laws(design, page)),
        ("the build modes", build_modes(design)),
    ]
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let dir = spec_dir(args, std::env::var(VAR).ok())?;
    let design = read_text(&format!("{dir}/DESIGN.md"))?;
    let page = read_text(&format!("{}/docs/mathlib-study.md", impl_root()))?;
    let mut checks_ok = true;
    for (what, result) in prose_checks(&design, &page) {
        if let Err(e) = result {
            say!(out, "{what}: {e}");
            checks_ok = false;
        }
    }
    // A spec cite cannot read (no sec:steps) is named like a failed check, not an error that
    // hides the checks above.
    let cited_ok = crate::cite::run(&[dir], out).unwrap_or_else(|e| {
        say!(out, "the citations: {e}");
        false
    });
    Ok(checks_ok && cited_ok)
}
