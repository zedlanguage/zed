//! The map on the corpus and the step units (DESIGN.md step L1.33a): every span the lowering
//! gives a node is a source node's, so each node with a site has a source; the nodes with none
//! are counted and printed by kind.

use std::collections::BTreeMap;

use zed_tests::oracle;
use zedc::suppress::Suppress;
use zedc::zir::lower::lower_debug;
use zedc::zir::{Region, op_name};

/// The op name of each node of `g`, by node number in preorder.
fn ops(g: &Region) -> Vec<&'static str> {
    let mut out = Vec::new();
    let mut todo = vec![g.nodes.iter()];
    while let Some(top) = todo.last_mut() {
        let Some(n) = top.next() else {
            todo.pop();
            continue;
        };
        out.push(op_name(&n.op));
        todo.extend(n.regions.iter().rev().map(|r| r.nodes.iter()));
    }
    out
}

#[test]
fn every_node_of_a_corpus_program_with_a_site_has_a_source() {
    let (mut mapped, mut nodes, mut unsourced) = (0, 0, 0);
    let mut by_op: BTreeMap<&str, usize> = BTreeMap::new();
    let mut skipped: Vec<String> = Vec::new();
    // The corpus begins at L3, so at this layer no corpus program loads (the oracle's
    // `every_enabled_corpus_program_agrees_and_writes_its_output` counts 0 enabled); the step
    // units are mapped with it, and each program that does not load or lower is listed.
    let programs = oracle::corpus().into_iter().map(|(p, _)| p);
    for path in programs.chain(oracle::step_units()) {
        let file = path.to_str().expect("a program path is UTF-8");
        let name = path.display();
        let (mut suppress, _) = Suppress::take(&[]).expect("no words to take");
        let mut warnings: Vec<u8> = Vec::new();
        let p = match zedc::run::load_file(file, &[], &mut suppress, &mut warnings) {
            Ok(p) => p,
            Err((_, e)) => {
                skipped.push(format!("{name}: does not load: {e}"));
                continue;
            }
        };
        let (g, sited) = match lower_debug(&p.term(), Some(p.sites())) {
            Ok(x) => x,
            Err(e) => {
                skipped.push(format!("{name}: does not lower: {e}"));
                continue;
            }
        };
        let map = p.source_map(&sited.sources);
        assert_eq!(map.missed(), 0, "{name}: a span no source node has");
        let ops = ops(&g);
        assert_eq!(ops.len(), sited.sites.len(), "{name}");
        for (x, site) in sited.sites.iter().enumerate() {
            let sources = map.sources(x);
            assert_eq!(site.is_some(), !sources.is_empty(), "{name}: node {x}");
            for s in &sources {
                assert!(map.zir_of(s).contains(&x), "{name}: node {x}, {s:?}");
            }
            if sources.is_empty() {
                unsourced += 1;
                *by_op.entry(ops[x]).or_default() += 1;
            }
        }
        nodes += ops.len();
        mapped += 1;
    }
    eprintln!(
        "{mapped} programs mapped, {nodes} nodes, {unsourced} with no source: {by_op:?}; \
         {} skipped",
        skipped.len()
    );
    assert!(mapped > 0, "{}", skipped.join("\n"));
}
