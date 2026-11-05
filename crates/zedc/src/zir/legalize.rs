//! Legalization (DESIGN.md sec:ir, "Legalization"): one pass on ZIR, run after lowering and
//! before planning, that rewrites the operations a back end declares it does not lower into
//! simpler ZIR, so each rewrite is written once and not once per back end. Each back end
//! declares its set as a constant, never by the program's size; the counting machine's is
//! [`crate::zir::memory::EXPANSIONS`] and the Cranelift back end's is `zed_native::EXPANSIONS`.
//!
//! Every expansion gives the same value as the operation it replaces:
//!
//! - [`Expansion::Derived`] puts a derived node's certificate, which is the node's kernel
//!   definition, in the node's place, its arguments read from the node's inputs and its
//!   results standing for the node's outputs.
//! - [`Expansion::Gt`] rewrites an applied `a > b` as `b < a`, and [`Expansion::Ge`] rewrites
//!   `a >= b` as `b <= a`; the kernel's order is antisymmetric on every pair it orders and its
//!   IEEE 754 comparisons are too, so the value and every failure value are the same. A
//!   primitive with no inputs, a function value, is not rewritten.
//!
//! An expansion that yields another expandable operation is expanded too: a certificate is
//! legalized before it is put in its node's place, so a `>` inside it is rewritten.
//!
//! The pass walks the graph once, from a stack of regions on the heap, and moves every node it
//! keeps, so its cost is linear in the graph's size and its depth is limited by memory alone.

use std::mem;
use std::sync::Arc;

use zed_kernel::term::Prim;

use super::{Node, Op, Region, RegionKind, Src};

/// An operation a back end may ask to have expanded.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expansion {
    /// A derived node (`group`, `rank`, `scan`, `join`), replaced by its certificate.
    Derived,
    /// An applied `prim >`, rewritten as `prim <` on its inputs swapped.
    Gt,
    /// An applied `prim >=`, rewritten as `prim <=` on its inputs swapped.
    Ge,
}

impl Expansion {
    /// The expansion's name, as an error message writes it.
    pub fn name(self) -> &'static str {
        match self {
            Expansion::Derived => "derived",
            Expansion::Gt => "gt",
            Expansion::Ge => "ge",
        }
    }

    fn bit(self) -> u8 {
        1 << self as u8
    }
}

/// A set of expansions, as a back end declares it.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Expansions(u8);

impl Expansions {
    /// The set of `xs`.
    pub const fn of(xs: &[Expansion]) -> Expansions {
        let mut bits = 0;
        let mut i = 0;
        while i < xs.len() {
            bits |= 1 << xs[i] as u8;
            i += 1;
        }
        Expansions(bits)
    }

    /// Whether the set holds `x`.
    pub fn contains(self, x: Expansion) -> bool {
        self.0 & x.bit() != 0
    }
}

/// `g` with the expansions in `want` applied, at every depth.
pub fn legalize(g: Region, want: Expansions) -> Region {
    let mut stack = vec![Frame::new(g)];
    loop {
        let top = stack
            .last_mut()
            .expect("the outermost region is on the stack");
        if let Some(open) = &mut top.open {
            if let Some(r) = open.todo.next() {
                // Lowering gives every region its own `Arc`, so this moves the region.
                // Complexity tradeoff: a region a graph shares is copied and legalized once per
                // use, so the cost is the graph's size read as a tree, which is what validation
                // and planning already pay (COMPLEXITY.md Z20, PLAN-shared-regions); a memo by
                // address is banned.
                stack.push(Frame::new(Arc::unwrap_or_clone(r)));
                continue;
            }
            let open = top.open.take().expect("an open node");
            top.finish(open.node, open.done, want);
            continue;
        }
        match top.left.next() {
            Some(mut node) if !node.regions.is_empty() => {
                let todo = mem::take(&mut node.regions).into_iter();
                top.open = Some(Open {
                    node,
                    todo,
                    done: Vec::new(),
                });
            }
            Some(node) => top.finish(node, Vec::new(), want),
            None => {
                let done = stack.pop().expect("the frame just read").region();
                match stack.last_mut() {
                    Some(up) => up.open.as_mut().expect("an open node").done.push(done),
                    None => return done,
                }
            }
        }
    }
}

/// A region being legalized.
struct Frame {
    kind: RegionKind,
    args: Vec<super::Edge>,
    results: Vec<Src>,
    /// The nodes not yet read.
    left: std::vec::IntoIter<Node>,
    /// The nodes kept.
    nodes: Vec<Node>,
    /// For each node read, where each of its outputs now comes from.
    outs: Vec<Vec<Src>>,
    /// The node whose regions are being legalized.
    open: Option<Open>,
}

/// A node whose regions are being legalized: those not yet started, and those done.
struct Open {
    node: Node,
    todo: std::vec::IntoIter<Arc<Region>>,
    done: Vec<Region>,
}

impl Frame {
    fn new(mut r: Region) -> Frame {
        Frame {
            kind: r.kind,
            args: mem::take(&mut r.args),
            results: mem::take(&mut r.results),
            left: mem::take(&mut r.nodes).into_iter(),
            nodes: Vec::new(),
            outs: Vec::new(),
            open: None,
        }
    }

    /// Where `s`, read in this region, now comes from.
    fn src(&self, s: Src) -> Src {
        match s {
            Src::Out(n, p) => self.outs[n][p].clone(),
            s => s,
        }
    }

    /// Keeps `node`, whose regions are `regions` legalized, or what it expands to.
    fn finish(&mut self, mut node: Node, regions: Vec<Region>, want: Expansions) {
        node.inputs = mem::take(&mut node.inputs)
            .into_iter()
            .map(|s| self.src(s))
            .collect();
        if want.contains(Expansion::Derived) && matches!(node.op, Op::Derived(_)) {
            let [certificate] = <[Region; 1]>::try_from(regions)
                .unwrap_or_else(|_| unreachable!("validation gives a derived node one region"));
            let outs = self.inline(certificate, &node.inputs);
            self.outs.push(outs);
            return;
        }
        if let Op::Prim(p) = node.op
            && node.inputs.len() == 2
        {
            let swapped = match p {
                Prim::Gt if want.contains(Expansion::Gt) => Some(Prim::Lt),
                Prim::Ge if want.contains(Expansion::Ge) => Some(Prim::Le),
                _ => None,
            };
            if let Some(q) = swapped {
                node.op = Op::Prim(q);
                node.inputs.swap(0, 1);
            }
        }
        node.regions = regions.into_iter().map(Arc::new).collect();
        let at = self.nodes.len();
        self.outs
            .push((0..node.outputs.len()).map(|p| Src::Out(at, p)).collect());
        self.nodes.push(node);
    }

    /// Puts `certificate`'s nodes in this region, its argument `j` read from `inputs[j]`;
    /// gives where its results now come from. A certificate holds no derived node, so its
    /// nodes keep their order and node `n` of it is node `base + n` here.
    fn inline(&mut self, mut certificate: Region, inputs: &[Src]) -> Vec<Src> {
        let base = self.nodes.len();
        let at = |s: Src| match s {
            Src::Arg(j) => inputs[j].clone(),
            Src::Out(n, p) => Src::Out(base + n, p),
            s => s,
        };
        for mut n in mem::take(&mut certificate.nodes) {
            n.inputs = mem::take(&mut n.inputs).into_iter().map(at).collect();
            self.nodes.push(n);
        }
        mem::take(&mut certificate.results)
            .into_iter()
            .map(at)
            .collect()
    }

    /// The legalized region.
    fn region(mut self) -> Region {
        let results = mem::take(&mut self.results)
            .into_iter()
            .map(|s| self.src(s))
            .collect();
        Region {
            kind: self.kind,
            args: self.args,
            nodes: self.nodes,
            results,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zir::text::parse;

    const BOTH: Expansions = Expansions::of(&[Expansion::Gt, Expansion::Ge]);

    #[test]
    fn the_set_holds_what_it_was_made_of() {
        assert!(BOTH.contains(Expansion::Gt) && BOTH.contains(Expansion::Ge));
        assert!(!BOTH.contains(Expansion::Derived));
        assert!(!Expansions::default().contains(Expansion::Gt));
    }

    #[test]
    fn an_empty_set_changes_nothing() {
        let g = parse("zir 1\nr region function (int; int)\nr.0 prim > (r^0, r^1) -> (bool)\nr results (r.0^0)\n")
            .unwrap();
        assert_eq!(legalize(g.clone(), Expansions::default()), g);
    }
}
