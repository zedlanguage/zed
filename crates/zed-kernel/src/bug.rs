//! The one text of every message for a bug in zedc (plan row MSG-bug-sentence-one, DESIGN.md
//! sec:diagnostics): the same opening sentence, the part that says what went wrong, and the
//! same request to report it at [`REPORT_TO`]. It lives in the kernel because every crate that
//! reports such a bug reaches the kernel: the runtime (`zed_rt::bug`), the code generator
//! (`zed_native`), the lowering (`zedc_zir`), the fixpoint order (`zedc_lattice::wto`), the
//! evaluator ([`crate::KernelError::Type`]) and zedc's own report of a panic
//! (`zedc_base::rejection::bug`, which re-exports [`REPORT_TO`]).

/// Where a bug in zedc is reported. Defined here only; `zedc_base::rejection` re-exports it.
pub const REPORT_TO: &str = "https://github.com/zedlanguage/zed/issues";

/// What stopped at the bug: zedc while it checked, compiled or built the program, or a run of
/// the program, under `zedc run` or in an executable `zedc build` made.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stopped {
    /// zedc itself, before any run.
    Zedc,
    /// A run of the program.
    Run,
}

impl Stopped {
    /// The words that open the message: what stopped.
    fn words(self) -> &'static str {
        match self {
            Stopped::Zedc => "zedc",
            Stopped::Run => "the run",
        }
    }
}

/// The message for a bug in zedc: the opening sentence for `who`, then `body`, one or more
/// sentences on what zedc expected and met, each ending with its period, then on a line of its
/// own the request to report it at [`REPORT_TO`] `with` what the report needs. O(length of the
/// message).
pub fn report(who: Stopped, body: &str, with: &str) -> String {
    format!(
        "{} stopped because of a bug in zedc, not in your program. {body}\n\
         Please report it at {REPORT_TO}, with {with}, so that it can be repeated.",
        who.words()
    )
}

/// `message`, a [`report`], followed by a block of the details meant for zedc's developers,
/// one `name: value` line each, indented under a line of its own (plan row
/// MSG-bug-report-plain): the reader of the message sees what happened in plain words first,
/// and the report carries the rest. O(length of the result).
pub fn with_details(message: String, details: &[(&str, String)]) -> String {
    let mut out = message;
    out.push_str("\nDetails for the report:");
    for (name, value) in details {
        out.push_str("\n  ");
        out.push_str(name);
        out.push_str(": ");
        out.push_str(value);
    }
    out
}

/// The opening sentence of every message [`report`] gives for `who`, which a test or a reader
/// of a run's output matches.
pub fn opening(who: Stopped) -> String {
    format!(
        "{} stopped because of a bug in zedc, not in your program. ",
        who.words()
    )
}
