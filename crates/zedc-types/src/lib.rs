//! The types of the compiler `zedc`'s checker (DESIGN.md sec:types): the checker's type, its
//! signatures and classes, its printing, and the kernel type a written type denotes. `zedc`
//! re-exports each module at its old path (`zedc::check::ty`, ...).

pub mod kernel_type;
pub mod ty;
