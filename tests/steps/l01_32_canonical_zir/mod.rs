//! Step L1.32: the M0.7 canonicalizer on ZIR, and the content address over its normal form.
//! Renaming a pattern's binders, renaming or dropping hints, reordering or repeating facets,
//! and respelling a set of integers leave the address alone; changing a value changes it. The
//! rules terminate on random graphs, each step lowering the tuple of ranks.

mod fuzz;
mod stability;

use zedc::zir::{Region, text};

/// The graph written in `src`.
pub(crate) fn graph(src: &str) -> Region {
    text::parse(src).unwrap_or_else(|e| panic!("{e}\n{src}"))
}
