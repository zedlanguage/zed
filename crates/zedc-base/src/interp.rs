//! The definitional interpreter (DESIGN.md Part G, steps L1.18–L1.21): elaborated kernel
//! terms run by the kernel's reference evaluator, under the prelude words they read.
//!
//! Step L1.18 binds the L1 words on scalars, each to its kernel primitive; the evaluator
//! itself holds the per-region operator arrows, atom pass-through and the `#errs` merge.

use zed_kernel::{Prim, Shared, Term};

/// The L1 prelude words and their primitives.
const WORDS: &[(&str, Prim)] = &[
    ("String", Prim::Show),
    ("int", Prim::CastInt),
    ("rat", Prim::CastRat),
    ("f64", Prim::CastF64),
    ("abs", Prim::Abs),
    ("min", Prim::Min),
    ("max", Prim::Max),
    ("len", Prim::Len),
    ("lower", Prim::Lower),
    ("upper", Prim::Upper),
    ("trim", Prim::Trim),
    ("sum", Prim::Sum),
    ("bitAnd", Prim::BitAnd),
    ("bitOr", Prim::BitOr),
    ("bitXor", Prim::BitXor),
    ("bitNot", Prim::BitNot),
    ("shl", Prim::Shl),
    ("shr", Prim::Shr),
    ("popCount", Prim::PopCount),
    ("leadingZeros", Prim::LeadingZeros),
    ("trailingZeros", Prim::TrailingZeros),
    ("rotl", Prim::Rotl),
    ("rotr", Prim::Rotr),
    ("f64Bits", Prim::F64Bits),
    ("codePoint", Prim::CodePoint),
    ("scalar", Prim::Scalar),
    ("utf8", Prim::Utf8),
    ("fromUtf8", Prim::FromUtf8),
    ("mulHi", Prim::MulHi),
    ("bitReverse", Prim::BitReverse),
    ("byteSwap", Prim::ByteSwap),
    ("pdep", Prim::Pdep),
    ("pext", Prim::Pext),
    ("funnelShl", Prim::FunnelShl),
    ("funnelShr", Prim::FunnelShr),
];

/// Whether `name` is a prelude word.
pub fn word(name: &str) -> bool {
    WORDS.iter().any(|(w, _)| *w == name)
}

/// The primitive of the prelude word `name`, if it is one.
pub fn prim(name: &str) -> Option<Prim> {
    WORDS.iter().find(|(w, _)| *w == name).map(|&(_, p)| p)
}

/// `body` under the prelude: each word it may read bound to its primitive.
pub fn prelude(body: Term) -> Term {
    WORDS.iter().rev().fold(body, |body, (name, p)| {
        Term::Let(
            (*name).into(),
            Shared::new(Term::PrimFn(*p)),
            Shared::new(body),
        )
    })
}
