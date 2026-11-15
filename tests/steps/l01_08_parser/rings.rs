//! Every fence of the documentation parses, and first parses at the ring
//! the `sync` tool recorded with the spec's grammar tools: as a unit, or under the
//! documentation notation.

use zed_tests::fences;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

/// The fences that first parse at a higher ring with this repository's `syntax.peg` than with the
/// spec's, by which the `sync` tool recorded their rings, and the ring each first parses at here.
/// The spec's grammar (34d3391) takes at L1 the range type suffix `int[0..<n]` (TypePostfix,
/// TypeSuffix, RangeLit; DESIGN 92ceb14, author P251) and, from the layer audit (23a88fd,
/// author P254), `x: T = e` (TypedBinding), the literal and `_` types (LitType, LitFactor,
/// InferType) and the `::` read (ReadSuffix), and `initial x: T = e` (InitTarget) at L6; this
/// copy takes the `::` read at L3 and the others at L10. Each entry fails the test once the
/// spec's grammar is copied, so none outlives it. Plan rows RANGE-L1 and LAYER-L1-forms build those forms;
/// whichever copies the spec's `syntax.peg` and `desugar.txt` (`sync` writes each whole) empties
/// this list.
const HELD_GRAMMAR_RINGS: &[(&str, u32)] = &[
    ("DESIGN.md [sec:failure] 1", 10),
    ("DESIGN.md [sec:failure] 2", 10),
    ("DESIGN.md [sec:codecs] 3", 3),
    ("DESIGN.md [sec:codecs] 4", 3),
    ("DESIGN.md [sec:codecs] 6", 3),
    ("DESIGN.md [sec:level_names] 2", 10),
    ("DESIGN.md [sec:level_names] 3", 10),
    ("DESIGN.md [sec:level_names] 4", 10),
    ("DESIGN.md [sec:level_names] 5", 10),
    ("DESIGN.md [sec:level_names] 8", 10),
    ("DESIGN.md [sec:constraints] 3", 10),
    ("DESIGN.md [sec:linalg] 1", 10),
    ("DESIGN.md [sec:linalg] 3", 10),
    ("DESIGN.md [sec:staging] 1", 10),
    ("DESIGN.md [sec:introspection] 1", 10),
    ("DESIGN.md [sec:symbolic] 1", 3),
    ("DESIGN.md [sec:checking_in_zed] 3", 10),
    ("DESIGN.md [sec:arenas] 2", 10),
    ("DESIGN.md [sec:ffi] 15", 10),
    ("DESIGN.md [sec:ffi] 16", 10),
    ("DESIGN.md [sec:tour_basics] 1", 10),
    ("EXAMPLES.md [2. Bindings and values] 1", 10),
    ("EXAMPLES.md [3. Numbers] 1", 10),
    ("EXAMPLES.md [3. Numbers] 2", 10),
    ("EXAMPLES.md [4. Strings] 1", 3),
    ("EXAMPLES.md [4. Strings] 2", 3),
    ("EXAMPLES.md [10. Structs and updates] 2", 10),
    ("EXAMPLES.md [15. Trees and graphs] 3", 10),
    ("EXAMPLES.md [15. Trees and graphs] 4", 10),
    ("EXAMPLES.md [16. Generics and interfaces] 1", 10),
    ("EXAMPLES.md [18. Files, stores, and the world] 1", 3),
    ("EXAMPLES.md [18. Files, stores, and the world] 7", 3),
    ("EXAMPLES.md [20. Testing, properties, and proofs] 1", 10),
    ("EXAMPLES.md [20. Testing, properties, and proofs] 3", 10),
    ("EXAMPLES.md [21. Domains] 2", 10),
    ("EXAMPLES.md [24. Small programs] 4", 3),
    ("EXAMPLES.md [25. Algorithms] 7", 10),
];

#[test]
fn every_fence_parses_first_at_its_recorded_ring() {
    let all = fences::all();
    assert_eq!(all.len(), 220);
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
        let ring = HELD_GRAMMAR_RINGS
            .iter()
            .find(|(key, _)| *key == f.key)
            .map_or(f.ring, |&(_, ring)| ring);
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
