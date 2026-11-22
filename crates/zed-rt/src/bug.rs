//! The message of a run stopped by a bug in zedc, in a module of its own so that the modules
//! that report one do not import the crate root, which imports them.

/// The message of a run stopped by a broken invariant of the compiled code, which is a bug in
/// zedc and not in the program (DESIGN.md sec:diagnostics), in the words every such message
/// shares (`zed_kernel::bug`, plan row MSG-bug-sentence-one): `what` says, in the program's
/// terms, as a verb phrase, what the code zedc made for the program did that it never should,
/// and `detail` names the runtime's own place for the report, the one part of the message
/// meant for zedc's developers.
pub fn bug(what: &str, detail: &str) -> String {
    zed_kernel::bug::report(
        zed_kernel::bug::Stopped::Run,
        &format!("The code zedc made for the program {what}: {detail}."),
        "this message, the program's source and the input it was given",
    )
}
