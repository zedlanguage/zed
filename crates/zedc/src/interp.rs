//! The definitional interpreter (DESIGN.md Part G, steps L1.18–L1.21): elaborated kernel
//! terms run by the kernel's reference evaluator, under the prelude words they read.
//!
//! Step L1.18 binds the L1 words on scalars, each to its kernel primitive; the evaluator
//! itself holds the per-region operator arrows, atom pass-through and the `#errs` merge.

use std::sync::Arc;

use zed_kernel::{Prim, Term};

/// The L1 prelude words and their primitives.
const WORDS: &[(&str, Prim)] = &[
    ("String", Prim::Show),
    ("int", Prim::CastInt),
    ("rat", Prim::CastRat),
    ("f64", Prim::CastF64),
    ("abs", Prim::Abs),
    ("len", Prim::Len),
    ("lower", Prim::Lower),
    ("upper", Prim::Upper),
    ("trim", Prim::Trim),
    ("sum", Prim::Sum),
];

/// `body` under the prelude: each word it may read bound to its primitive.
pub fn prelude(body: Term) -> Term {
    WORDS.iter().rev().fold(body, |body, (name, p)| {
        Term::Let((*name).into(), Arc::new(Term::PrimFn(*p)), Arc::new(body))
    })
}
