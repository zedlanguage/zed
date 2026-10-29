//! The independent certificate checker (DESIGN.md sec:optimizer, sec:verification).
//!
//! Every rewrite the optimizer makes records `(rule, bindings, evidence used)`, and this crate
//! revalidates the chain. It is kept small and apart from `zedc` on purpose: it depends only on
//! `zed-kernel`, so a bug in the optimizer cannot also hide in the check of its output.
