//! The source formatter of `zedc_syntax::format` (step L1.13), and a file as `zedc fmt` prints
//! it: in the formatter's layout, or, when the file does not load or its syntax is rejected,
//! the diagnostics `zedc run` prints for it, each with its derivation and its menu of fixes,
//! read by the same phases (`front::syntax`) and printed by the same function
//! ([`Unloaded::report`]).

pub use zedc_syntax::format::{format, format_type};

use crate::front::{self, Unloaded};
use crate::source;
use crate::work::{self, Stage};

/// The source file `bytes` in the formatter's layout; or why it was not read: its bytes are not
/// a source, or the diagnostics of the first phase of its syntax that rejects it.
pub fn formatted(bytes: &[u8]) -> Result<String, Unloaded> {
    let text = work::stage(Stage::Load, None, || source::load(bytes))
        .map_err(|e| Unloaded::Refused(e.render(bytes)))?;
    let lines = source::Lines::new(text.as_bytes());
    let (tokens, _, stmts) = front::syntax(&text, &lines).map_err(Unloaded::Rejected)?;
    Ok(format(&text, &tokens, &stmts))
}

/// The source file `bytes` in the formatter's layout, or why it was not read, as
/// [`crate::run::load`] gives it: each error at its line and column, with its derivation and
/// its menu of fixes.
pub fn format_source(bytes: &[u8]) -> Result<String, String> {
    formatted(bytes).map_err(|why| why.report(None, |_| String::new()))
}
