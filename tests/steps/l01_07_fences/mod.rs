//! Step L1.7: the fences of DESIGN.md and EXAMPLES.md, read in place from the spec checkout
//! (feature `spec`), are lexed, their ✗ marks recorded, and each commented ✗ variant has its
//! own fixture in `zed/fences/variants/`. From here on every step runs the fences of its layer.

mod bench;
mod copies;
mod edges;
mod extractor;
mod keys;
mod mathlib;
mod readme;
mod scaling;
mod variants;
