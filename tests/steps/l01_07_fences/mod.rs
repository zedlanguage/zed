//! Step L1.7: the fences of DESIGN.md and EXAMPLES.md, read from the spec in place, are lexed,
//! their ✗ marks recorded, and each commented ✗ variant has its own fixture. From here on every
//! step runs the fences of its layer.

mod doc_fences;
mod extractor;
mod keys;
mod mathlib;
mod readme;
mod scaling;
mod variants;
