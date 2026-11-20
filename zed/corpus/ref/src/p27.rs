//! 27 parent chains: root and depth per node, nodes in code-point order. A chain that returns to
//! a node has no root: it is an error.

use std::collections::{BTreeMap, HashMap, HashSet};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let mut par: BTreeMap<&str, &str> = BTreeMap::new();
    for l in lines {
        let w: Vec<&str> = l.split(' ').collect();
        let &[c, p] = &w[..] else {
            return Err(format!("not \"child parent\": {l}"));
        };
        par.entry(c).or_insert(p); // group then first: the first line for a child wins
    }
    // Complexity tradeoff (COMPLEXITY.md REF-p27-hashed-walk): `par` stays ordered, for the
    // nodes in code-point order, but the walk looks nodes up only by name, so it reads `parent` and
    // `known`, hashed. Each node joins `known` once, on the one walk that first reaches it, so
    // the walks take n steps and 3n lookups in all for n nodes: O(n) expected after the O(n log n)
    // building of `par`. Through the ordered maps the same 3n lookups cost O(n log n), and their
    // comparisons per lookup grow with the B-tree's height in whole levels, not with ln n: 19.7
    // at 10,000 nodes and 30.0 at 80,000 on one chain, 1.52 times where ln n grows 1.23 times,
    // which held `parent_chain_of_one_long_chain` at 10.15 times the work for 8 times the nodes.
    let parent: HashMap<&str, &str> = par.iter().map(|(&c, &p)| (c, p)).collect();
    // Each node's root and depth, so a walk stops at the first node an earlier walk reached.
    let mut known: HashMap<&str, (&str, usize)> = HashMap::with_capacity(par.len());
    for &v in par.keys() {
        let (mut path, mut on_path) = (Vec::new(), HashSet::new());
        let mut r = v;
        let (root, mut d) = loop {
            if let Some(&found) = known.get(r) {
                break found;
            }
            let Some(&up) = parent.get(r).filter(|p| **p != "-") else {
                break (r, 0);
            };
            if !on_path.insert(r) {
                return Err(format!("the chain of {v} has a cycle"));
            }
            path.push(r);
            r = up;
        };
        for &node in path.iter().rev() {
            d += 1;
            known.insert(node, (root, d));
        }
        say!(out, "{v} {root} {d}");
    }
    Ok(())
}
