//! 13 connectivity by a classic union-find (path halving, union by size): the reference the
//! library's certified path must agree with. Node count is max node id on an edge + 1; a queried
//! node outside that range is alone. A negative node id counts from the end (-1 is node count -
//! 1); below -node count it is an error.

use std::collections::HashSet;

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

use crate::zedrt::{at, parse_int};

struct Nodes {
    count: BigInt,
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl Nodes {
    fn index(&self, x: &BigInt) -> Result<usize, String> {
        let i = if x.is_negative() {
            x + &self.count
        } else {
            x.clone()
        };
        if i.is_negative() || i >= self.count {
            return Err(format!("node {x} is out of range"));
        }
        Ok(i.to_usize().expect("below the node count"))
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    /// The root of `x`, or `x` itself for a node above the range.
    fn root(&mut self, x: &BigInt) -> Result<(bool, BigInt), String> {
        if *x < self.count {
            let i = self.index(x)?;
            Ok((false, self.find(i).into()))
        } else {
            Ok((true, x.clone()))
        }
    }
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let (mut edges, mut qs) = (Vec::new(), Vec::new());
    for l in lines {
        let w: Vec<&str> = l.split(' ').collect();
        if w[0] == "?" {
            qs.push((parse_int(at(&w, 1)?)?, parse_int(at(&w, 2)?)?));
        } else {
            edges.push((parse_int(w[0])?, parse_int(at(&w, 1)?)?));
        }
    }
    let top = edges.iter().flat_map(|e| [&e.0, &e.1]).max().cloned();
    let count: BigInt = top.unwrap_or(BigInt::from(-1)).max(BigInt::from(-1)) + 1;
    let n = count.to_usize().ok_or("too many nodes")?;
    let mut nodes = Nodes {
        count,
        parent: (0..n).collect(),
        size: vec![1; n],
    };
    for (a, b) in &edges {
        let (ia, ib) = (nodes.index(a)?, nodes.index(b)?);
        let (mut ra, mut rb) = (nodes.find(ia), nodes.find(ib));
        if ra != rb {
            if nodes.size[ra] < nodes.size[rb] {
                (ra, rb) = (rb, ra);
            }
            nodes.parent[rb] = ra;
            nodes.size[ra] += nodes.size[rb];
        }
    }
    for (a, b) in &qs {
        let same = nodes.root(a)? == nodes.root(b)?;
        say!(out, "{a} {b} {}", if same { "yes" } else { "no" });
    }
    let roots: HashSet<usize> = (0..n).map(|v| nodes.find(v)).collect();
    say!(out, "components {}", roots.len());
    Ok(())
}
