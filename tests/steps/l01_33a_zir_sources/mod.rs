//! Step L1.33a: the map between ZIR nodes and source nodes. Each node of a graph lowered with
//! sites has every parse tree node it was lowered from, named by its declaration and its path
//! there, those of the equal nodes CSE merged into it included, and each parse tree node the
//! graph nodes lowered from it; the run-time sites table is what it was.

mod bench;
mod corpus;
mod sources;

use zedc::run::Program;
use zedc::source_map::SourceMap;
use zedc::zir::Region;
use zedc::zir::lower::{Sited, lower_debug};

/// The program `src`, its graph lowered with sites, the sites and names, and the map.
pub(crate) fn mapped(src: &str) -> (Program, Region, Sited, SourceMap) {
    let p = zedc::run::load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}: {e}"));
    let (g, sited) = lower_debug(&p.term(), Some(p.sites())).unwrap();
    let map = p.source_map(&sited.sources);
    (p, g, sited, map)
}

/// A program of `m` lines after `main`'s first, each two equal sums of the line before and
/// the whole: line k is `s{k} = (s{k-1} + 1) mod 1000 + (s{k-1} + 1) mod 1000;`, whose sum and
/// remainder are each lowered to one node for its two copies.
pub(crate) fn shared_chain(m: usize) -> String {
    let mut src = "main(m: MainArgs) {\n    s0 = int(m.args[0] else #outOfBounds -> \"\") else \
                   #invalid -> 1;\n"
        .to_string();
    for k in 1..=m {
        src += &format!(
            "    s{k} = (s{} + 1) mod 1000 + (s{} + 1) mod 1000;\n",
            k - 1,
            k - 1
        );
    }
    src += &format!("    m.stdout <- String(s{m});\n}}\n");
    src
}
