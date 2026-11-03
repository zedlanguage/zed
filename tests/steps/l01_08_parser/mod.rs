//! Step L1.8: the parser runs the grammar of sec:grammar, copied into `zed/grammar/`, and its
//! trees are the trees of the spec's bracketing cases and the rings of the fences.

mod cases;
mod deep;
mod errors;
mod grammar_scaling;
mod grammar_shape;
mod left_recursion;
mod rings;
mod scaling;
