//! The message of a failure of zedc's own making of machine code, in a module of its own so
//! that the modules that report one do not import the crate root, which imports them.

/// The message for a failure of zedc's own making of machine code, which is a bug in zedc and
/// never the program's fault (DESIGN.md sec:diagnostics): `detail` is the one part meant for
/// zedc's developers.
pub(crate) fn bug(detail: impl std::fmt::Display) -> String {
    format!(
        "zedc could not make machine code for the program because of a bug in zedc, not in the \
         program. Please report it to the Zed developers with the program's source and this \
         line: {detail}. Until it is fixed, `zedc run` runs the program without machine code"
    )
}
