//! `fences SPEC_DIR` prints the number of ```` ```zed ```` fences of `DESIGN.md` and
//! `EXAMPLES.md` and their lines.

use crate::spec::zed_fences;
use crate::{Outcome, arg, say};

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let root = arg(args, 0, "fences SPEC_DIR")?;
    let mut fences = zed_fences(&format!("{root}/DESIGN.md"))?;
    fences.extend(zed_fences(&format!("{root}/EXAMPLES.md"))?);
    let lines: usize = fences.iter().map(|f| f.text.split('\n').count()).sum();
    say!(out, "{} {lines} lines", fences.len());
    Ok(true)
}
