//! ZIR, the intermediate representation (step L1.31; DESIGN.md sec:ir): an acyclic
//! hierarchical graph of the RVSDG family. A [`Region`] holds nodes in topological order; a
//! [`Node`] is an operation, and the region nodes hold regions of their own. Edges are typed:
//! a value edge carries a type, a domain and facets, and a state edge orders the effects on
//! one port. Constants and types live on edges, so a node is an opcode and its attributes.
//!
//! The node inventory is the kernel's seven generators, the four derived nodes, each carrying
//! its kernel definition as a certificate region, the scalar primitives, and the region nodes:
//!
//! | node | inputs | regions | outputs |
//! |---|---|---|---|
//! | `reindex` | family, key map, value map | | family |
//! | `discard` | family, selector | | family |
//! | `fold` | family, operator, the identity when it has one | | value |
//! | `fix lattice` | bottom, join, captures | loop: iterate, captures → next | value |
//! | `fix definedness` | domain, captures | loop: `this`, key, captures → entry | family |
//! | `gen` | generation 0, captures | loop: step, loop: guard (frame, captures → one) | family |
//! | `port read` | state | | value, state |
//! | `port push` | state, value | | acknowledgment, state |
//! | `fam` | domain, captures | function: key, captures → entry | family |
//! | `group`, `rank`, `scan`, `join` | any | function: the certificate | any |
//! | `prim` | the primitive's arguments, or none | | value, or the primitive as a function |
//! | `apply` | function, arguments | | value |
//! | `lambda` | captures | function: parameters, captures → value | function |
//! | `if` | condition, captures | match: then, match: else | any |
//! | `match` | scrutinee, captures | match per arm: the arm's bindings, captures | any |
//! | `rec` | captures | rec: the functions, captures → the functions | the functions |
//! | `wave` | captures | port: captures → outputs | any |
//!
//! Where DESIGN.md does not say, step L1.31 decides:
//!
//! - **Regions are isolated**, as in the RVSDG: a node reads its own region's arguments,
//!   earlier nodes' outputs and constants, never an enclosing region's edges. A value from
//!   outside enters as a capture, an input appended after the node's fixed inputs and
//!   received as the matching argument after the region's own, with the same edge type.
//! - **State edges are linear**: each is used exactly once in its region, by a node or as a
//!   result, so the effects on a port are totally ordered. A state edge enters only a match
//!   or port region, or the function region of a `lambda`, which takes one state argument
//!   for each port its body uses, after its parameters, and returns the states after its
//!   value; an `apply` passes the states in after its arguments and has them as outputs after
//!   the value (a `gen` step with an effect waits for the scheduler of step L4).
//! - **A certificate is kernel-only**: a derived node's region holds no derived node, at any
//!   depth, so its definition bottoms out in the generators. Its arguments are the node's
//!   inputs and its results the node's outputs.
//! - The validator checks structure: references, arities, region kinds, edge kinds, capture
//!   types and linearity. Whether a value edge's type fits its consumer is the checker's
//!   question, already answered for the kernel term the graph is lowered from (step L1.33).

pub mod binary;
pub mod canon;
pub mod legalize;
pub mod lower;
pub mod memory;
pub mod text;
pub mod validate;

use std::mem;
use std::sync::Arc;

use zed_kernel::term::{Evidence, GuardPos, Pattern, Prim, Witness};
use zed_kernel::types::Type;
use zed_kernel::value::Value;

use crate::canon::{Domain, Facet};
use zedc_lattice::interval::IntervalSet;

/// The kind of a region (DESIGN.md sec:ir, "Shape").
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RegionKind {
    /// The body of a function, a family's entries, or a certificate.
    Function,
    /// An arm of an `if` or a `match`.
    Match,
    /// The step or guard of a recurrence or generation.
    Loop,
    /// Mutually recursive functions.
    Rec,
    /// A wave over ports.
    Port,
}

/// An edge's type: a value's type, domain and facets, or the state of a port.
#[derive(Clone, PartialEq, Debug)]
pub enum Edge {
    /// A value.
    Value(ValueEdge),
    /// The ordering of the effects on the named port.
    State(Arc<str>),
}

/// What a value edge carries.
#[derive(Clone, PartialEq, Debug)]
pub struct ValueEdge {
    /// The value's type.
    pub ty: Type,
    /// The integer facts.
    pub domain: Domain,
    /// The other facts.
    pub facets: Vec<Facet>,
}

/// The domain that admits every integer.
pub fn any_domain() -> Domain {
    Domain::ints(IntervalSet::top())
}

impl Edge {
    /// A value edge of type `ty`, with no facts.
    pub fn value(ty: Type) -> Edge {
        Edge::Value(ValueEdge {
            ty,
            domain: any_domain(),
            facets: Vec::new(),
        })
    }

    /// Whether the edge is a state edge.
    pub fn is_state(&self) -> bool {
        matches!(self, Edge::State(_))
    }
}

/// Where a node's input, or a region's result, comes from.
#[derive(Clone, PartialEq, Debug)]
pub enum Src {
    /// Argument `i` of the region.
    Arg(usize),
    /// Output `port` of node `node` of the region, an earlier node.
    Out(usize, usize),
    /// A constant.
    Const(Value),
}

/// One of the four derived nodes the planner matches.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Derived {
    /// Grouping by a key.
    Group,
    /// Ranking along an order.
    Rank,
    /// A prefix fold.
    Scan,
    /// A join of two families.
    Join,
}

/// A node's operation and its attributes.
#[derive(Clone, PartialEq, Debug)]
pub enum Op {
    /// `reindex`, with its injectivity evidence.
    Reindex(Witness),
    /// `discard`.
    Discard,
    /// `fold` over `depth` levels, with an identity input or not, and its evidence.
    Fold {
        /// The number of key levels of the family.
        depth: usize,
        /// Whether the third input is the identity.
        identity: bool,
        /// The evidence for the operator.
        ev: Evidence,
    },
    /// `fix`, a lattice ascent or the definedness instance, with its evidence.
    Fix {
        /// Whether it is a lattice ascent, whose second input is the join.
        lattice: bool,
        /// The evidence for the step.
        ev: Evidence,
    },
    /// `gen`, testing its guard before or after each step.
    Gen(GuardPos),
    /// `port read` of the named port.
    Read(Arc<str>),
    /// `port push` to the named port.
    Push(Arc<str>),
    /// `fam`.
    Fam,
    /// A derived node.
    Derived(Derived),
    /// A primitive, applied to its arguments; with no inputs, a primitive of fixed arity is
    /// itself, as a function value (step L1.33), which the kernel tells apart from a lambda
    /// that calls it (a fold of `+` itself sums exactly).
    Prim(Prim),
    /// A call.
    Apply,
    /// A function.
    Lambda,
    /// A two-armed branch.
    If,
    /// A match, one region per pattern.
    Match(Vec<Pattern>),
    /// Mutual recursion.
    Rec,
    /// A wave.
    Wave,
}

/// A node.
#[derive(Clone, PartialEq, Debug)]
pub struct Node {
    /// The operation.
    pub op: Op,
    /// The inputs, fixed ones first, then captures.
    pub inputs: Vec<Src>,
    /// The outputs' edge types.
    pub outputs: Vec<Edge>,
    /// The regions, for a region node or a derived node, shared: a copy of a node copies its
    /// own fields and not what lies below it, so a pass may hold a node of any depth.
    pub regions: Vec<Arc<Region>>,
}

/// A region. Its drop, its comparison and its `Debug` keep their own stack on the heap, so a
/// graph's depth is limited by the machine's memory alone.
#[derive(Clone)]
pub struct Region {
    /// The kind.
    pub kind: RegionKind,
    /// The arguments' edge types.
    pub args: Vec<Edge>,
    /// The nodes, each after every node it reads.
    pub nodes: Vec<Node>,
    /// The results.
    pub results: Vec<Src>,
}

impl std::fmt::Debug for Region {
    /// Writes, in both the `{:?}` and `{:#?}` forms, the one line a derived `Debug` writes for
    /// `{:?}`, from a stack of regions to open and the text that closes each, so a graph of any
    /// depth prints on a small stack. `Node`'s derived `Debug` calls this for its regions.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Todo<'a> {
            Region(&'a Region),
            Node(&'a Node),
            Results(&'a Region),
            Text(&'static str),
        }
        let mut todo = vec![Todo::Region(self)];
        while let Some(t) = todo.pop() {
            match t {
                Todo::Text(s) => f.write_str(s)?,
                Todo::Results(r) => write!(f, "], results: {:?} }}", r.results)?,
                Todo::Region(r) => {
                    write!(
                        f,
                        "Region {{ kind: {:?}, args: {:?}, nodes: [",
                        r.kind, r.args
                    )?;
                    todo.push(Todo::Results(r));
                    for (i, n) in r.nodes.iter().enumerate().rev() {
                        todo.push(Todo::Node(n));
                        if i > 0 {
                            todo.push(Todo::Text(", "));
                        }
                    }
                }
                Todo::Node(n) => {
                    write!(
                        f,
                        "Node {{ op: {:?}, inputs: {:?}, outputs: {:?}, regions: [",
                        n.op, n.inputs, n.outputs
                    )?;
                    todo.push(Todo::Text("] }"));
                    for (i, r) in n.regions.iter().enumerate().rev() {
                        todo.push(Todo::Region(r));
                        if i > 0 {
                            todo.push(Todo::Text(", "));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

impl Drop for Region {
    /// Frees the regions below this one in a loop: each uniquely held region is emptied of its
    /// nodes' regions before it is freed, so no drop reaches below the next level.
    fn drop(&mut self) {
        let mut below: Vec<Arc<Region>> = self
            .nodes
            .iter_mut()
            .flat_map(|n| mem::take(&mut n.regions))
            .collect();
        while let Some(r) = below.pop() {
            if let Some(mut r) = Arc::into_inner(r) {
                below.extend(r.nodes.iter_mut().flat_map(|n| mem::take(&mut n.regions)));
            }
        }
    }
}

impl PartialEq for Region {
    /// Compares two graphs level by level, from a stack of region pairs; a pair of regions
    /// shared by both sides is equal without being read.
    fn eq(&self, other: &Region) -> bool {
        let mut pairs: Vec<(&Region, &Region)> = vec![(self, other)];
        while let Some((a, b)) = pairs.pop() {
            if a.kind != b.kind
                || a.args != b.args
                || a.results != b.results
                || a.nodes.len() != b.nodes.len()
            {
                return false;
            }
            for (m, n) in a.nodes.iter().zip(&b.nodes) {
                if m.op != n.op
                    || m.inputs != n.inputs
                    || m.outputs != n.outputs
                    || m.regions.len() != n.regions.len()
                {
                    return false;
                }
                let subs = m.regions.iter().zip(&n.regions);
                pairs.extend(
                    subs.filter(|(x, y)| !Arc::ptr_eq(x, y))
                        .map(|(x, y)| (&**x, &**y)),
                );
            }
        }
        true
    }
}

/// The number of names pattern `p` binds.
pub fn binds(p: &Pattern) -> usize {
    let mut count = 0;
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(_) => count += 1,
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps),
            Pattern::Fields(_, fs) => todo.extend(fs.iter().map(|(_, p)| p)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
    count
}

impl Region {
    /// The edge type of `src` in this region, which must be valid there.
    pub fn edge(&self, src: &Src) -> Edge {
        match src {
            Src::Arg(i) => self.args[*i].clone(),
            Src::Out(n, p) => self.nodes[*n].outputs[*p].clone(),
            Src::Const(v) => Edge::value(Type::lit(v).unwrap_or_else(Type::top)),
        }
    }
}

/// The name of an operation, as the text form writes it first.
pub fn op_name(op: &Op) -> &'static str {
    match op {
        Op::Reindex(_) => "reindex",
        Op::Discard => "discard",
        Op::Fold { .. } => "fold",
        Op::Fix { .. } => "fix",
        Op::Gen(_) => "gen",
        Op::Read(_) | Op::Push(_) => "port",
        Op::Fam => "fam",
        Op::Derived(Derived::Group) => "group",
        Op::Derived(Derived::Rank) => "rank",
        Op::Derived(Derived::Scan) => "scan",
        Op::Derived(Derived::Join) => "join",
        Op::Prim(_) => "prim",
        Op::Apply => "apply",
        Op::Lambda => "lambda",
        Op::If => "if",
        Op::Match(_) => "match",
        Op::Rec => "rec",
        Op::Wave => "wave",
    }
}

/// The name of a region kind, as the text form writes it.
pub fn kind_name(k: RegionKind) -> &'static str {
    match k {
        RegionKind::Function => "function",
        RegionKind::Match => "match",
        RegionKind::Loop => "loop",
        RegionKind::Rec => "rec",
        RegionKind::Port => "port",
    }
}
