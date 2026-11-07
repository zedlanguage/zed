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
//! A refusal names the operator and its operands as the program wrote them (DESIGN.md sec:ir,
//! "Legalization"): the pass returns a [`Legalized`] graph, which records each node it swapped,
//! and a back end that hands a node to the kernel raises a swapped node as the written operator
//! on its inputs in written order ([`crate::zir::lower::raise_node`]). A back end takes a
//! [`Legalized`] graph, so a graph that was not legalized cannot reach its code generator.
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

/// A graph legalized for a back end: the graph, and the nodes the pass swapped.
///
/// Nodes are named by their number in preorder: a region's nodes in order, each followed at
/// once by the nodes of its regions, in order, at every depth; the root region's first node is
/// number 0.
#[derive(Clone, Debug)]
pub struct Legalized {
    graph: Arc<Region>,
    swapped: Arc<Swapped>,
    nodes: usize,
}

impl Legalized {
    /// The legalized graph.
    pub fn graph(&self) -> &Arc<Region> {
        &self.graph
    }

    /// The nodes the pass rewrote as their converse (`a > b` as `b < a`).
    pub fn swapped(&self) -> &Arc<Swapped> {
        &self.swapped
    }

    /// The number of nodes in the graph, at every depth.
    pub fn nodes(&self) -> usize {
        self.nodes
    }
}

/// A set of node numbers (see [`Legalized`]), one bit each.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Swapped(Vec<u64>);

impl Swapped {
    /// Whether node `n` was swapped.
    pub fn contains(&self, n: usize) -> bool {
        self.0.get(n / 64).is_some_and(|w| w >> (n % 64) & 1 == 1)
    }

    fn insert(&mut self, n: usize) {
        let i = n / 64;
        if self.0.len() <= i {
            self.0.resize(i + 1, 0);
        }
        self.0[i] |= 1 << (n % 64);
    }
}

/// The operator the program wrote for a swapped node of operator `p`.
pub fn written(p: Prim) -> Prim {
    match p {
        Prim::Lt => Prim::Gt,
        Prim::Le => Prim::Ge,
        p => unreachable!("legalization swaps only `>` and `>=`, never `{p:?}`"),
    }
}

/// The number of nodes in `regions`, at every depth.
pub fn nodes_in(regions: &[Arc<Region>]) -> usize {
    let mut stack: Vec<&Region> = regions.iter().map(|r| &**r).collect();
    let mut n = 0;
    while let Some(r) = stack.pop() {
        n += r.nodes.len();
        for node in &r.nodes {
            stack.extend(node.regions.iter().map(|r| &**r));
        }
    }
    n
}

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
pub fn legalize(g: Region, want: Expansions) -> Legalized {
    let mut stack = vec![Frame::new(g)];
    // The next node kept gets this number; nodes are kept in preorder (see [`Legalized`]).
    // An expanded derived node is not kept: its certificate's nodes take its place and its
    // numbers.
    let mut next = 0;
    let mut swapped = Swapped::default();
    loop {
        let top = stack
            .last_mut()
            .expect("the outermost region is on the stack");
        if let Some(open) = &mut top.open {
            if let Some(r) = open.todo.next() {
                // Lowering gives every region its own `Arc`, so this moves the region.
                // Complexity tradeoff: a region a graph shares is copied and legalized once per
                // use, so the cost is the graph's size read as a tree, which is what validation
                // and planning already pay (COMPLEXITY.md Z25, PLAN-shared-regions); a memo by
                // address is banned.
                stack.push(Frame::new(Arc::unwrap_or_clone(r)));
                continue;
            }
            let open = top.open.take().expect("an open node");
            top.finish(open.node, open.done, want, (open.number, &mut swapped));
            continue;
        }
        match top.left.next() {
            Some(mut node) if !node.regions.is_empty() => {
                let number = next;
                if !expands(&node, want) {
                    next += 1;
                }
                let todo = mem::take(&mut node.regions).into_iter();
                top.open = Some(Open {
                    node,
                    number,
                    todo,
                    done: Vec::new(),
                });
            }
            Some(node) => {
                top.finish(node, Vec::new(), want, (next, &mut swapped));
                next += 1;
            }
            None => {
                let done = stack.pop().expect("the frame just read").region();
                match stack.last_mut() {
                    Some(up) => up.open.as_mut().expect("an open node").done.push(done),
                    None => {
                        return Legalized {
                            graph: Arc::new(done),
                            swapped: Arc::new(swapped),
                            nodes: next,
                        };
                    }
                }
            }
        }
    }
}

/// Whether `node` is replaced by what it expands to under `want`, and so not kept.
fn expands(node: &Node, want: Expansions) -> bool {
    want.contains(Expansion::Derived) && matches!(node.op, Op::Derived(_))
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
    /// The node's number; unused when the node expands.
    number: usize,
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

    /// Keeps `node`, whose regions are `regions` legalized, or what it expands to; `number` is
    /// the node's number, recorded in `swapped` if the node is swapped.
    fn finish(
        &mut self,
        mut node: Node,
        regions: Vec<Region>,
        want: Expansions,
        (number, swapped): (usize, &mut Swapped),
    ) {
        node.inputs = mem::take(&mut node.inputs)
            .into_iter()
            .map(|s| self.src(s))
            .collect();
        if expands(&node, want) {
            let [certificate] = <[Region; 1]>::try_from(regions)
                .unwrap_or_else(|_| unreachable!("validation gives a derived node one region"));
            let outs = self.inline(certificate, &node.inputs);
            self.outs.push(outs);
            return;
        }
        if let Op::Prim(p) = node.op
            && node.inputs.len() == 2
        {
            let converse = match p {
                Prim::Gt if want.contains(Expansion::Gt) => Some(Prim::Lt),
                Prim::Ge if want.contains(Expansion::Ge) => Some(Prim::Le),
                _ => None,
            };
            if let Some(q) = converse {
                node.op = Op::Prim(q);
                node.inputs.swap(0, 1);
                swapped.insert(number);
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
        let l = legalize(g.clone(), Expansions::default());
        assert_eq!(**l.graph(), g);
        assert_eq!(**l.swapped(), Swapped::default());
        assert_eq!(l.nodes(), 1);
    }

    #[test]
    fn swapped_nodes_are_named_by_their_number_in_preorder() {
        // Node 0 is the lambda, 1 and 2 are in its body, 3 is the `if`, 4 is in its first
        // arm and 5 in its second, 6 follows the `if`.
        let g = parse(
            "zir 1\n\
             r region function (int)\n\
             r.0 lambda () -> ((-> int bool))\n\
             r.0/0 region function (int)\n\
             r.0/0.0 prim < (r.0/0^0, 18) -> (bool)\n\
             r.0/0.1 prim >= (r.0/0^0, 18) -> (bool)\n\
             r.0/0 results (r.0/0.1^0)\n\
             r.1 if (true) -> (bool)\n\
             r.1/0 region match ()\n\
             r.1/0.0 prim > (7, 3) -> (bool)\n\
             r.1/0 results (r.1/0.0^0)\n\
             r.1/1 region match ()\n\
             r.1/1.0 prim <= (7, 3) -> (bool)\n\
             r.1/1 results (r.1/1.0^0)\n\
             r.2 prim > (r^0, 1) -> (bool)\n\
             r results (r.2^0)\n",
        )
        .unwrap();
        let l = legalize(g.clone(), BOTH);
        assert_eq!(l.nodes(), 7);
        let swapped: Vec<usize> = (0..8).filter(|&n| l.swapped().contains(n)).collect();
        assert_eq!(swapped, [2, 4, 6]);
        assert_eq!(nodes_in(std::slice::from_ref(l.graph())), 7);
    }

    #[test]
    fn the_converse_of_a_swapped_operator_is_the_one_written() {
        assert_eq!(written(Prim::Lt), Prim::Gt);
        assert_eq!(written(Prim::Le), Prim::Ge);
    }
}
