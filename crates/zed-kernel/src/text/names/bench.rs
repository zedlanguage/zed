//! The benchmark of [`Names`], run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates). It checks nothing besides the ratio; texts of many blocks
//! joined in every order are named in `tests.rs` (`texts_joined_in_any_order_have_one_name`).

use super::tests::{doubled, join};
use super::*;

#[test]
fn naming_n_and_8n_nodes() {
    // A text of n blocks of LEAF bytes, joined from the left, each block different: n nodes, each
    // named once from its parts' summaries, O(n log N) dictionary steps.
    let texts = crate::scaling::inputs(5000, |n| {
        (0..n).fold(Text::from(""), |t, i| {
            let piece: String = (0..super::super::LEAF)
                .map(|j| char::from(b'a' + ((i * 7 + j * j) % 23) as u8))
                .collect();
            join(&t, &Text::from(piece))
        })
    });
    crate::scaling::check("naming a text of n blocks", 5000, |n| {
        let mut names = Names::new();
        std::hint::black_box(names.name(&texts[&n]));
    });
}

#[test]
fn naming_a_doubled_text_costs_a_few_times_building_it() {
    // Row PERF-names-doubled-join-cost: a 5-byte text joined to itself 60 times is a tree of
    // 2866 nodes (each join makes a new node at each level of the finger tree), but only 160
    // distinct joins of two texts: a deep tree shares its digits with the trees below it, and
    // equal texts have one name. Naming each node by folding its parts cost 40 000 to 79 000
    // instructions a node, 31 to 63 times building the tree; with the joins found by the
    // names of their two texts (`Names::joins`), 2.2 to 4.0 times (instruction counts, the
    // probe of 2026-11-28 in the running log).
    let mut m = crate::scaling::Meter::new();
    for base in ["s0001", "abcab"] {
        let mut t = Text::from("");
        let build = m.work(|| t = doubled(base, 60));
        let mut names = Names::new();
        let name = m.work(|| {
            std::hint::black_box(names.name(&t));
        });
        let ratio = name.units as f64 / build.units.max(1) as f64;
        eprintln!(
            "naming {base} doubled 60 times: {} {} to build, {} to name, {ratio:.2} times",
            build.units,
            m.unit(),
            name.units
        );
        assert!(
            ratio < 8.0,
            "naming {base} doubled 60 times costs {ratio:.2} times building it"
        );
    }
}

#[test]
fn naming_n_and_8n_doubled_texts() {
    // n texts, each a different 5-byte text joined to itself 40 times, named through one
    // dictionary: no two share a join, so the work is linear in n, each text's distinct joins
    // kept in `Names::joins`. No base has two equal neighbors, so that none is a run, which
    // names in far fewer steps and would make the small size cheaper than the rest.
    let base = |i: usize| -> String {
        let d = |k: usize, from: u8| char::from(from + (i / 7usize.pow(k as u32) % 7) as u8);
        [d(0, b'a'), d(1, b'h'), d(2, b'p'), 'x', 'y']
            .iter()
            .collect()
    };
    let texts = crate::scaling::inputs(4, |n| {
        (0..n).map(|i| doubled(&base(i), 40)).collect::<Vec<_>>()
    });
    crate::scaling::check("naming n doubled texts", 4, |n| {
        let mut names = Names::new();
        for t in &texts[&n] {
            std::hint::black_box(names.name(t));
        }
    });
}
