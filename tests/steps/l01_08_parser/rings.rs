//! Every fence of the documentation parses, and first parses at the ring
//! the `sync` tool recorded with the spec's grammar tools: as a unit, or under the
//! documentation notation.

use zed_tests::fences;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

/// The fences that hold a range type suffix (`int[0..]`, `int[0..<n]`). The spec's grammar takes
/// the suffix at L1 (DESIGN 92ceb14, author P251), and the `sync` tool recorded their rings by it;
/// this repository's `syntax.peg` still takes it at L10, so each first parses at ring 10 here.
/// Plan row RANGE-L1 copies the spec's `syntax.peg` and `desugar.txt` and empties this list.
const RANGE_SUFFIX_AT_L10: &[&str] = &[
    "DESIGN.md [sec:failure] 2",
    "DESIGN.md [sec:constraints] 3",
    "DESIGN.md [sec:linalg] 1",
    "DESIGN.md [sec:linalg] 3",
    "DESIGN.md [sec:staging] 1",
    "DESIGN.md [sec:arenas] 2",
    "DESIGN.md [sec:ffi] 15",
    "EXAMPLES.md [10. Structs and updates] 2",
    "EXAMPLES.md [15. Trees and graphs] 4",
    "EXAMPLES.md [20. Testing, properties, and proofs] 1",
    "EXAMPLES.md [20. Testing, properties, and proofs] 3",
    "EXAMPLES.md [25. Algorithms] 7",
];

#[test]
fn every_fence_parses_first_at_its_recorded_ring() {
    let all = fences::all();
    assert_eq!(all.len(), 219);
    let mut wrong = Vec::new();
    for f in &all {
        let tokens = lex_fence(&f.text).unwrap();
        let unit = parse(&f.text, &tokens, "Unit", TOP);
        if unit.is_ok() == f.notation {
            wrong.push(format!("{}: parses as a unit: {}", f.at, unit.is_ok()));
            continue;
        }
        let start = if f.notation { "DocFence" } else { "Unit" };
        let lowest = (1..=TOP).find(|&k| parse(&f.text, &tokens, start, k).is_ok());
        let ring = if RANGE_SUFFIX_AT_L10.contains(&f.key.as_str()) {
            10
        } else {
            f.ring
        };
        if lowest != Some(ring) {
            wrong.push(format!("{}: ring {lowest:?}, recorded {}", f.at, ring));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn every_variant_fixture_parses_as_its_fence_does() {
    let all = fences::all();
    for v in fences::variants() {
        let fence = all
            .iter()
            .find(|f| f.text.lines().any(|l| l.trim() == v.of))
            .unwrap_or_else(|| panic!("no fence has the line of {}", v.name));
        let start = if fence.notation { "DocFence" } else { "Unit" };
        let tokens = lex_fence(&v.text).unwrap();
        if let Err(e) = parse(&v.text, &tokens, start, TOP) {
            panic!(
                "{} does not parse: {e} at {:?}",
                v.name,
                &v.text[e.span.start..]
            );
        }
    }
}
