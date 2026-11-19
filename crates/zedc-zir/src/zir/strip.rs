//! The two forms of a module (DESIGN.md sec:kernel, "Facts carried, and the stripped form",
//! author decision P202): the full form keeps every fact the compiler stored, so a consumer may
//! re-check each before it trusts the code; the stripped form keeps only what running needs.
//!
//! What running needs, read off the readers of the graph (study `docs/zir-facts-study.md`): the
//! structure (regions, nodes, inputs, results), each operation and its attributes that change a
//! value (a fold's depth and identity input, a fix's instance, a guard's position, a port, a
//! primitive, the patterns of a match, which test types), whether an edge is a value or a port's
//! state, and the constants. Stripping drops, and so a stripped module cannot be re-checked
//! ([`recheck`]):
//!
//! - every value edge's type, domain and facets, hints included: the edge becomes `_`. No pass
//!   after lowering reads them but the native back end's NaN test (`zed_native::tables`,
//!   `may_be_nan`), which treats `_` as "may be NaN" and so tests at run time what a known
//!   type would let it skip;
//! - the evidence of a `fold` and a `fix`, which becomes empty ("nothing known"); the evaluator
//!   and the native back end never read it.
//!
//! One edge keeps a type: a region argument that a constant capture feeds keeps the type of
//! the constant, which the validator requires of every capture ([`super::validate`]) and which
//! the constant itself gives, so it is no derived fact. A `reindex` keeps its witness: the
//! graph has no form for an unknown witness, the witness is one name, and the evaluator checks
//! the collision rule on every run whatever the witness (`zed_kernel::term::Witness`).

use std::collections::HashMap;
use std::fmt::Write;
use std::mem;
use std::sync::Arc;

use zed_kernel::term::Evidence;
use zed_kernel::types::Type;

use super::validate::{shape, validate};
use super::{Edge, Node, Op, Region, Src, text};

/// The form of a serialized module.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Form {
    /// Every fact stored, as the compiler wrote it.
    Full,
    /// Only what running needs ([`strip`]).
    Stripped,
}

/// Why [`recheck`] refuses a stripped module.
pub const STRIPPED_REFUSED: &str = "the module is stripped: it keeps only what running needs and \
                                    none of the facts the compiler derived, so its facts cannot \
                                    be re-checked. Repair: re-check the full module it was \
                                    stripped from";

/// The re-check a consumer runs before it trusts a module of form `form`: a stripped module is
/// refused, since it holds no facts to check; a full one has its structure validated
/// ([`validate`]). The facts on its edges and the evidence of its folds are not yet proved again
/// here: the checker derives types, bounds and blocking on the source and does not yet store
/// them on the graph, so there is nothing of them to re-prove (plan row ZIR-checker-facts).
pub fn recheck(g: &Region, form: Form) -> Result<(), String> {
    match form {
        Form::Stripped => Err(STRIPPED_REFUSED.into()),
        Form::Full => validate(g),
    }
}

/// An edge with its facts dropped: a value edge becomes `_`, a state edge stays.
fn bare(e: &Edge) -> Edge {
    match e {
        Edge::State(p) => Edge::State(p.clone()),
        Edge::Value(_) => Edge::value(Type::top()),
    }
}

/// An operation with its evidence dropped. Every case is listed, so an operation added with a
/// fact of its own is stripped by choice, not kept by a catch-all.
fn bare_op(op: &Op) -> Op {
    match op {
        Op::Fold {
            depth, identity, ..
        } => Op::Fold {
            depth: *depth,
            identity: *identity,
            ev: Evidence::new(),
        },
        Op::Fix { lattice, .. } => Op::Fix {
            lattice: *lattice,
            ev: Evidence::new(),
        },
        Op::Reindex(_)
        | Op::Discard
        | Op::Gen(_)
        | Op::Read(_)
        | Op::Push(_)
        | Op::Fam
        | Op::Derived(_)
        | Op::Prim(_)
        | Op::Apply
        | Op::Lambda
        | Op::If
        | Op::Match(_)
        | Op::Rec
        | Op::Wave => op.clone(),
    }
}

/// The arguments of region `j` of node `n`, stripped: each `_` or a state, but an argument a
/// constant capture feeds, which keeps the constant's type; and the text of those kept, which
/// tells apart two strippings of one shared region whose users capture different constants.
fn sub_args(n: &Node, j: usize, sub: &Region) -> (Vec<Edge>, String) {
    let mut args: Vec<Edge> = sub.args.iter().map(bare).collect();
    let mut kept = String::new();
    // A node whose shape is wrong has no captures to keep; the validator reports it.
    if let Ok(s) = shape(n)
        && let Some(&(_, lead, _)) = s.regions.get(j)
    {
        for (i, c) in n.inputs.iter().skip(s.fixed).enumerate() {
            if let Src::Const(_) = c
                && let Some(a) = args.get_mut(lead + i)
            {
                *a = sub.edge(c);
                let _ = write!(kept, "{} {};", lead + i, text::edge(a));
            }
        }
    }
    (args, kept)
}

/// The stripped form of the graph rooted at `root`, which runs to the same values: the same
/// regions, nodes, inputs and results, each value edge `_` and each evidence record empty (the
/// module documentation lists what is kept). A region shared by several nodes is stripped once
/// for each set of constants its users capture, so sharing is kept.
///
/// The walk keeps one frame per open region on the heap, so a graph of any depth strips on a
/// small stack. Complexity tradeoff: each distinct pair of a shared region and its constant
/// captures is stripped once, so the cost is O(size) of the graph as the binary form counts it,
/// not of its tree, which sharing can make exponentially larger; the naive recursive copy costs
/// the tree's size and the machine stack's depth. The key of the memo is the region's address
/// and the text of its kept arguments, empty for nearly every region. Tests:
/// `l01_31_zir::stripped`.
pub fn strip(root: &Region) -> Region {
    /// A region being rebuilt: its source, its memo key (none for the root), its stripped
    /// arguments, the nodes rebuilt so far, and the regions rebuilt so far of the next node.
    struct Frame<'a> {
        src: &'a Region,
        key: Option<(usize, String)>,
        args: Vec<Edge>,
        nodes: Vec<Node>,
        regions: Vec<Arc<Region>>,
    }
    fn frame(src: &Region, key: Option<(usize, String)>, args: Vec<Edge>) -> Frame<'_> {
        Frame {
            src,
            key,
            args,
            nodes: Vec::with_capacity(src.nodes.len()),
            regions: Vec::new(),
        }
    }
    let mut memo: HashMap<(usize, String), Arc<Region>> = HashMap::new();
    let mut stack = vec![frame(root, None, root.args.iter().map(bare).collect())];
    loop {
        let f = stack
            .last_mut()
            .expect("the root's frame is the last one closed");
        let src = f.src;
        let Some(n) = src.nodes.get(f.nodes.len()) else {
            let f = stack.pop().expect("a frame is open");
            let r = Region {
                kind: src.kind,
                args: f.args,
                nodes: f.nodes,
                results: src.results.clone(),
            };
            let Some(parent) = stack.last_mut() else {
                return r;
            };
            let r = Arc::new(r);
            if let Some(key) = f.key {
                memo.insert(key, r.clone());
            }
            parent.regions.push(r);
            continue;
        };
        let j = f.regions.len();
        let Some(sub) = n.regions.get(j) else {
            let regions = mem::take(&mut f.regions);
            f.nodes.push(Node {
                op: bare_op(&n.op),
                inputs: n.inputs.clone(),
                outputs: n.outputs.iter().map(bare).collect(),
                regions,
            });
            continue;
        };
        let (args, kept) = sub_args(n, j, sub);
        let key = (Arc::as_ptr(sub) as usize, kept);
        match memo.get(&key) {
            Some(r) => f.regions.push(r.clone()),
            None => stack.push(frame(sub, Some(key), args)),
        }
    }
}
