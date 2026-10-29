//! Every fence of the documentation parses, and first parses at the ring `sync.py` recorded
//! with the spec's grammar tools: as a unit, or under the documentation notation.

use zed_tests::fences;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

#[test]
fn every_fence_parses_first_at_its_recorded_ring() {
    let all = fences::all();
    assert_eq!(all.len(), 149);
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
        if lowest != Some(f.ring) {
            wrong.push(format!("{}: ring {lowest:?}, recorded {}", f.at, f.ring));
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
