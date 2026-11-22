//! The message of a failure of zedc's own making of machine code, in a module of its own so
//! that the modules that report one do not import the crate root, which imports them.

/// The message for a failure of zedc's own making of machine code, which is a bug in zedc and
/// never the program's fault (DESIGN.md sec:diagnostics), in the words every such message
/// shares (`zed_kernel::bug`, plan row MSG-bug-sentence-one): `detail` is the one part meant
/// for zedc's developers.
pub(crate) fn bug(detail: impl std::fmt::Display) -> String {
    zed_kernel::bug::report(
        zed_kernel::bug::Stopped::Zedc,
        &format!(
            "zedc could not make machine code for the program: {detail}. Until it is fixed, \
             `zedc run` runs the program without machine code."
        ),
        "this message and the program's source",
    )
}
