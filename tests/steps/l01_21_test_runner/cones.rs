//! The definitions a row reads: those its terms name, and those they name in turn.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::Term;
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::elab::{Cones, Unit};
use zedc::stage::free;

use crate::l01_16_elaboration::elab;

/// The cone by one backward pass over the unit, each definition after those it uses.
fn by_scan(unit: &Unit, roots: &[&Term]) -> Vec<usize> {
    let mut reach: BTreeSet<Arc<str>> = roots.iter().flat_map(|t| free(t)).collect();
    let mut out = Vec::new();
    for (i, d) in unit.defs.iter().enumerate().rev() {
        if reach.contains(&d.kernel) {
            reach.extend(free(&d.term));
            out.push(i);
        }
    }
    out.reverse();
    out
}

#[test]
fn the_cone_is_the_definitions_a_scan_of_the_unit_reaches() {
    let mut rng = Rng::new(0x121c);
    for _ in 0..RANDOM_INSTANCES / 8 {
        let n = 1 + rng.below(8);
        // Each `ci` names some of the constants before it.
        let text: String = (0..n)
            .map(|i| {
                let uses: Vec<String> = (0..i)
                    .filter(|_| rng.below(3) == 0)
                    .map(|j| format!("c{j}"))
                    .collect();
                format!(
                    "c{i} = 1 + {};\n",
                    ["0".to_string()]
                        .iter()
                        .chain(&uses)
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(" + ")
                )
            })
            .collect();
        let unit = elab(&text).unwrap();
        let cones = Cones::new(&unit);
        for _ in 0..4 {
            let root = unit.defs[rng.below(unit.defs.len())].term.clone();
            let other = unit.defs[rng.below(unit.defs.len())].term.clone();
            for roots in [vec![&root], vec![&root, &other], vec![]] {
                assert_eq!(cones.reach(&roots), by_scan(&unit, &roots), "{text}");
            }
        }
    }
}

#[test]
fn a_term_is_closed_over_its_cone_alone_in_the_units_order() {
    let unit = elab("a = 1;\nb = a + 1;\nc = 5;\nd = b + a;\n").unwrap();
    let d = unit.defs.iter().find(|d| &*d.name == "d").unwrap();
    let closed = Cones::new(&unit).close(Term::Var(d.kernel.clone()));
    let mut lets = Vec::new();
    let mut t = &closed;
    while let Term::Let(x, _, body) = t {
        lets.push(x.to_string());
        t = body;
    }
    let kernel = |n: &str| {
        unit.defs
            .iter()
            .find(|d| &*d.name == n)
            .unwrap()
            .kernel
            .to_string()
    };
    assert_eq!(lets, [kernel("a"), kernel("b"), kernel("d")]);
    assert_eq!(unit.close(Term::Var(d.kernel.clone())), closed);
}
