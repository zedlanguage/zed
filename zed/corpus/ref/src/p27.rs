//! 27 parent chains: root and depth per node, nodes in code-point order. A chain that returns to
//! a node has no root: it is an error.

use std::collections::{BTreeMap, HashSet};

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
    // Each node's root and depth, so a walk stops at the first node an earlier walk reached.
    let mut known: BTreeMap<&str, (&str, usize)> = BTreeMap::new();
    for &v in par.keys() {
        let (mut path, mut on_path) = (Vec::new(), HashSet::new());
        let mut r = v;
        let (root, mut d) = loop {
            if let Some(&found) = known.get(r) {
                break found;
            }
            let Some(&up) = par.get(r).filter(|p| **p != "-") else {
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
