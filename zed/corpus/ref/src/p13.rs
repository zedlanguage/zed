//! 13 connectivity by a classic union-find (path halving, union by size): the reference the
//! library's certified path must agree with. Node count is max node number on an edge + 1; a
//! queried node above that range is alone. A negative node number counts from the end (-1 is node
//! count - 1); below -node count it is an error. Only nodes on edges are stored, so memory follows
//! the input and not the size of its numbers; every other node is alone.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_traits::Signed;

use crate::zedrt::{at, parse_int};

/// The stored nodes: a number's slot in `slots`, and each slot's parent and component size.
#[derive(Default)]
struct Nodes {
    slots: HashMap<BigInt, usize>,
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl Nodes {
    /// The slot of node `v`, made on first sight.
    fn slot(&mut self, v: BigInt) -> usize {
        let next = self.parent.len();
        let slot = *self.slots.entry(v).or_insert(next);
        if slot == next {
            self.parent.push(next);
            self.size.push(1);
        }
        slot
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    /// Whether the nodes `a` and `b`, in the range or above it, are connected.
    fn same(&mut self, a: &BigInt, b: &BigInt) -> bool {
        match (self.slots.get(a), self.slots.get(b)) {
            (Some(&x), Some(&y)) => self.find(x) == self.find(y),
            _ => a == b,
        }
    }
}

/// The node a negative number counts back to from `count`, or `None` when `x` names itself.
fn from_end(x: &BigInt, count: &BigInt) -> Result<Option<BigInt>, String> {
    if !x.is_negative() {
        return Ok(None);
    }
    let v = x + count;
    if v.is_negative() {
        return Err(format!("node {x} is out of range"));
    }
    Ok(Some(v))
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
    let mut nodes = Nodes::default();
    let mut merges = 0usize;
    for (a, b) in edges {
        let (a, b) = (
            from_end(&a, &count)?.unwrap_or(a),
            from_end(&b, &count)?.unwrap_or(b),
        );
        let (ia, ib) = (nodes.slot(a), nodes.slot(b));
        let (mut ra, mut rb) = (nodes.find(ia), nodes.find(ib));
        if ra != rb {
            if nodes.size[ra] < nodes.size[rb] {
                (ra, rb) = (rb, ra);
            }
            nodes.parent[rb] = ra;
            nodes.size[ra] += nodes.size[rb];
            merges += 1;
        }
    }
    for (a, b) in &qs {
        let (na, nb) = (from_end(a, &count)?, from_end(b, &count)?);
        let same = nodes.same(na.as_ref().unwrap_or(a), nb.as_ref().unwrap_or(b));
        say!(out, "{a} {b} {}", if same { "yes" } else { "no" });
    }
    // Each merge joins two components of the `count` nodes that started alone.
    say!(out, "components {}", count - merges);
    Ok(())
}
