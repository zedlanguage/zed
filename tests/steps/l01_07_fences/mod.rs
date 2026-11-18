//! Step L1.7: the fences of DESIGN.md and EXAMPLES.md, read in place from the spec checkout
//! (feature `spec`), are lexed, their ✗ marks recorded, and each commented ✗ variant has its
//! own fixture in `zed/fences/variants/`. From here on every step runs the fences of its layer.

mod bench;
mod copies;
mod edges;
mod extractor;
mod keys;
mod mathlib;
// README.md's fences are laid out with the table of words of the spec's DESIGN.md.
#[cfg(feature = "spec")]
mod readme;
mod scaling;
mod variants;
