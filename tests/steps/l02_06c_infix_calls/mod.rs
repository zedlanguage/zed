//! Step L2.6c, infix calls (DESIGN.md sec:power, tier 6; author, Q36): `a ~f~ b` is the call
//! `f(a, b)`, with the same resolution, overloads, defaults and errors, written between Range
//! and Additive and left-associative. An arithmetic operator written without parentheses in an
//! operand is rejected where the text has two readings, with both; a qualified name between the
//! tildes is rejected with the call written out; the printer writes an infix call back infix,
//! with the parentheses precedence needs and no others.
//!
//! The functions here take `int`, since structs and methods (L2.4 to L2.6) are not built yet;
//! an infix call's meaning is that of the written-out call whatever the types.

mod bench;
mod calls;
mod printing;
mod rejections;
mod scaling;

use zedc::query::Db;

/// The diagnostics of the unit `text`, each as `line:col message`, then each step as
/// `; text`, or `ok` when it is accepted.
pub(crate) fn front(text: &str) -> String {
    match &*Db::new().front(text) {
        Ok(_) => "ok".into(),
        Err(ds) => ds
            .iter()
            .map(|d| {
                let mut out = format!("{}:{} {}", d.line, d.col, d.message);
                for s in &d.steps {
                    out += &format!("; {}", s.text);
                }
                out
            })
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

/// [`front`] without the places, for comparing an infix call with the written-out call, whose
/// text is placed otherwise.
pub(crate) fn unplaced(text: &str) -> String {
    match &*Db::new().front(text) {
        Ok(_) => "ok".into(),
        Err(ds) => ds
            .iter()
            .map(|d| {
                let mut out = d.message.clone();
                for s in &d.steps {
                    out += &format!("; {}", s.text);
                }
                out
            })
            .collect::<Vec<_>>()
            .join("\n"),
    }
}
