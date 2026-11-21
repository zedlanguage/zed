//! Step L1.27: absences and narrowing. The three absences, `#notFound`, `#none` and `#empty`,
//! are loose atoms, each its own fact: an `else` names each atom it takes, as `e else #a -> d`,
//! which handles the one it names and keeps the others (a bare `e else d` is refused, QUESTIONS
//! A113, `bare_else`), and several loose atoms from one application merge into `#errs`. The
//! atoms of a named family are data: `else` keeps them, a join keeps them protected when either
//! side protects them, a written type makes them loose, and an operator they select no arrow of
//! rejects them.

mod bare_else;
mod bench;
mod discard;
mod discard_paths;
mod edges;
mod families;
mod loose;
mod merge;
mod scaling;
