//! The message of a run stopped by a bug in zedc, in a module of its own so that the modules
//! that report one do not import the crate root, which imports them.

/// The message of a run stopped by a broken invariant of the compiled code, which is a bug in
/// zedc and not in the program (DESIGN.md sec:diagnostics): `what` says, in the program's terms,
/// as a verb phrase, what the code zedc made for the program did that it never should, and
/// `detail` names the runtime's own place for the report, the one part of the message meant
/// for zedc's developers.
pub fn bug(what: &str, detail: &str) -> String {
    format!(
        "the program stopped because of a bug in zedc, not in the program: the code zedc \
         made for the program {what}. Please report it to the Zed developers with the \
         program's source, the input it was given, and this line: {detail}"
    )
}
