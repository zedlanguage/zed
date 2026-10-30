//! Step L1.31: ZIR, the graph IR. Regions hold nodes in order; edges carry types, domains and
//! facets, or order a port's effects; the text form is flat and sorted, read back in any line
//! order, and the binary form gives back the same graph.

mod graphs;
mod items;
mod rejections;

use zedc::zir::{Region, binary, text, validate};

/// The graph in `src`, checked, after asserting that it prints back as `src`, that its lines
/// read back in reverse order, and that its binary form decodes to it.
pub(crate) fn round(src: &str) -> Region {
    let g = text::parse(src).unwrap_or_else(|e| panic!("{e}\n{src}"));
    validate(&g).unwrap_or_else(|e| panic!("{e}\n{src}"));
    assert_eq!(text::print(&g), src);
    let mut lines: Vec<&str> = src.lines().collect();
    lines[1..].reverse();
    assert_eq!(text::parse(&lines.join("\n")).as_ref(), Ok(&g));
    let bytes = binary::encode(&g);
    assert_eq!(binary::decode(&bytes).as_ref(), Ok(&g));
    g
}

/// Why the text `src` is rejected, by the reader or the validator.
pub(crate) fn rejected(src: &str) -> String {
    match text::parse(src) {
        Err(e) => e,
        Ok(g) => validate(&g).expect_err("the graph is valid"),
    }
}
