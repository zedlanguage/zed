//! Step L1.27: absences and narrowing. The three absences, `#notFound`, `#none` and `#empty`,
//! are loose atoms, each its own fact: `e else d` defaults every loose atom, the pattern form
//! `e else #a -> d` handles the one it names and keeps the others, and several loose atoms
//! from one application merge into `#errs`. The atoms of a named family are data: `else`
//! keeps them, a join keeps them protected when either side protects them, a written type
//! makes them loose, and an operator they select no arrow of rejects them.

mod families;
mod loose;
