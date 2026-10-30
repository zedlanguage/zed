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
//! | `prim` | the primitive's arguments | | value |
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
//!   or port region (a `gen` step with an effect waits for the scheduler of step L4).
//! - **A certificate is kernel-only**: a derived node's region holds no derived node, at any
//!   depth, so its definition bottoms out in the generators. Its arguments are the node's
//!   inputs and its results the node's outputs.
//! - The validator checks structure: references, arities, region kinds, edge kinds, capture
//!   types and linearity. Whether a value edge's type fits its consumer is the checker's
//!   question, already answered for the kernel term the graph is lowered from (step L1.33).

pub mod binary;
pub mod canon;
pub mod text;

use std::sync::Arc;

use zed_kernel::term::{Evidence, GuardPos, Pattern, Prim, Witness};
use zed_kernel::types::Type;
use zed_kernel::value::Value;

use crate::canon::{Domain, Facet};
use crate::store::interval::IntervalSet;

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
    /// A primitive.
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
    /// The regions, for a region node or a derived node.
    pub regions: Vec<Region>,
}

/// A region.
#[derive(Clone, PartialEq, Debug)]
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

/// The number of names pattern `p` binds, in preorder.
pub fn binds(p: &Pattern) -> usize {
    match p {
        Pattern::Bind(_) => 1,
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter().map(binds).sum(),
        Pattern::Fields(_, fs) => fs.iter().map(|(_, p)| binds(p)).sum(),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => 0,
    }
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

/// What a node's operation requires of it.
struct Shape {
    /// The inputs before the captures.
    fixed: usize,
    /// Whether the number of inputs must be exactly `fixed`.
    exact: bool,
    /// The number of outputs, when it is fixed.
    outputs: Option<usize>,
    /// Each region's kind, number of arguments before the captures, and number of results.
    regions: Vec<(RegionKind, usize, usize)>,
}

fn shape(n: &Node) -> Result<Shape, String> {
    let ins = n.inputs.len();
    let outs = n.outputs.len();
    let leaf = |fixed| Shape {
        fixed,
        exact: true,
        outputs: Some(1),
        regions: Vec::new(),
    };
    let captures = |fixed, outputs, regions| Shape {
        fixed,
        exact: false,
        outputs,
        regions,
    };
    Ok(match &n.op {
        Op::Reindex(_) => leaf(3),
        Op::Discard => leaf(2),
        Op::Fold {
            depth, identity, ..
        } => {
            if *depth == 0 {
                return Err("`fold` has depth 0, and a family has at least 1 level".into());
            }
            leaf(2 + *identity as usize)
        }
        Op::Fix { lattice: true, .. } => captures(2, Some(1), vec![(RegionKind::Loop, 1, 1)]),
        Op::Fix { lattice: false, .. } => captures(1, Some(1), vec![(RegionKind::Loop, 2, 1)]),
        Op::Gen(_) => captures(
            1,
            Some(1),
            vec![(RegionKind::Loop, 1, 1), (RegionKind::Loop, 1, 1)],
        ),
        Op::Read(_) | Op::Push(_) => Shape {
            outputs: Some(2),
            ..leaf(if matches!(n.op, Op::Read(_)) { 1 } else { 2 })
        },
        Op::Fam => captures(1, Some(1), vec![(RegionKind::Function, 1, 1)]),
        Op::Derived(_) => {
            if ins == 0 || outs == 0 {
                return Err("a derived node has at least one input and one output".into());
            }
            captures(0, None, vec![(RegionKind::Function, 0, outs)])
        }
        Op::Prim(p) => match p.arity() {
            Some(k) => leaf(k),
            None => captures(0, Some(1), Vec::new()),
        },
        Op::Apply => {
            if ins == 0 {
                return Err("`apply` has no function input".into());
            }
            captures(1, Some(1), Vec::new())
        }
        Op::Lambda => {
            let params = n
                .regions
                .first()
                .map_or(0, |r| r.args.len().saturating_sub(ins));
            captures(0, Some(1), vec![(RegionKind::Function, params, 1)])
        }
        Op::If => captures(
            1,
            None,
            vec![(RegionKind::Match, 0, outs), (RegionKind::Match, 0, outs)],
        ),
        Op::Match(ps) => {
            if ps.is_empty() {
                return Err("`match` has no arm".into());
            }
            let arms = ps.iter().map(|p| (RegionKind::Match, binds(p), outs));
            captures(1, None, arms.collect())
        }
        Op::Rec => {
            if outs == 0 {
                return Err("`rec` defines no function".into());
            }
            captures(0, None, vec![(RegionKind::Rec, outs, outs)])
        }
        Op::Wave => captures(0, None, vec![(RegionKind::Port, 0, outs)]),
    })
}

/// How a message names an operation: its name, with the primitive or the port.
fn title(op: &Op) -> String {
    match op {
        Op::Prim(p) => format!("prim {}", text::spell(*p)),
        Op::Read(port) => format!("port read {port}"),
        Op::Push(port) => format!("port push {port}"),
        op => op_name(op).into(),
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

/// Checks the structure of the graph rooted at `root`. The error names the node or region at
/// fault by its path in the text form (`r.2/0.1`) and says what is wrong.
pub fn validate(root: &Region) -> Result<(), String> {
    region(root, "r", false)
}

fn region(r: &Region, path: &str, in_certificate: bool) -> Result<(), String> {
    if !matches!(r.kind, RegionKind::Match | RegionKind::Port)
        && let Some(i) = r.args.iter().position(Edge::is_state)
    {
        return Err(format!(
            "{path}^{i}: a state edge cannot enter a {} region",
            kind_name(r.kind)
        ));
    }
    // How many times each state edge of the region is used.
    let mut uses: Vec<(String, usize)> = Vec::new();
    let mut count = |r: &Region, src: &Src, name: String| {
        if r.edge(src).is_state() {
            match uses.iter_mut().find(|(n, _)| *n == name) {
                Some(u) => u.1 += 1,
                None => uses.push((name, 1)),
            }
        }
    };
    for (k, n) in r.nodes.iter().enumerate() {
        let at = format!("{path}.{k}");
        for (i, src) in n.inputs.iter().enumerate() {
            source(r, src, k, path).map_err(|e| format!("{at}: input {i}: {e}"))?;
            count(r, src, src_name(src, path));
        }
        node(r, n, &at, in_certificate)?;
    }
    for (i, src) in r.results.iter().enumerate() {
        source(r, src, r.nodes.len(), path).map_err(|e| format!("{path}: result {i}: {e}"))?;
        count(r, src, src_name(src, path));
    }
    if let Some((name, n)) = uses.iter().find(|(_, n)| *n > 1) {
        return Err(format!(
            "{name}: a state edge is used {n} times, and each is used exactly once"
        ));
    }
    let mut made: Vec<String> = Vec::new();
    for (i, a) in r.args.iter().enumerate() {
        if a.is_state() {
            made.push(format!("{path}^{i}"));
        }
    }
    for (k, n) in r.nodes.iter().enumerate() {
        for (p, e) in n.outputs.iter().enumerate() {
            if e.is_state() {
                made.push(format!("{path}.{k}^{p}"));
            }
        }
    }
    if let Some(name) = made.iter().find(|m| !uses.iter().any(|(n, _)| n == *m)) {
        return Err(format!(
            "{name}: a state edge is never used, and each is used exactly once"
        ));
    }
    Ok(())
}

/// `n` of `thing`, with the plural when `n` is not 1: `1 input`, `2 inputs`.
fn several(n: usize, thing: &str) -> String {
    match n {
        1 => format!("1 {thing}"),
        n => format!("{n} {thing}s"),
    }
}

/// `1 is` or `n are`.
fn written(n: usize) -> String {
    match n {
        1 => "1 is".into(),
        n => format!("{n} are"),
    }
}

/// The text form of `src` in the region at `path`.
fn src_name(src: &Src, path: &str) -> String {
    match src {
        Src::Arg(i) => format!("{path}^{i}"),
        Src::Out(n, p) => format!("{path}.{n}^{p}"),
        Src::Const(v) => v.to_string(),
    }
}

/// Checks that `src` names an argument of `r` or an output of a node before node `before`.
fn source(r: &Region, src: &Src, before: usize, path: &str) -> Result<(), String> {
    match *src {
        Src::Arg(i) if i >= r.args.len() => Err(format!(
            "{path}^{i}: the region has {}, numbered from 0",
            several(r.args.len(), "argument")
        )),
        Src::Out(n, _) if n >= before => Err(format!(
            "{path}.{n}: a node reads only nodes before it, and this is node {before}"
        )),
        Src::Out(n, p) if p >= r.nodes[n].outputs.len() => Err(format!(
            "{path}.{n}^{p}: node {path}.{n} (`{}`) has {}, numbered from 0",
            title(&r.nodes[n].op),
            several(r.nodes[n].outputs.len(), "output")
        )),
        _ => Ok(()),
    }
}

fn node(r: &Region, n: &Node, at: &str, in_certificate: bool) -> Result<(), String> {
    let name = title(&n.op);
    if in_certificate && matches!(n.op, Op::Derived(_)) {
        return Err(format!(
            "{at}: `{name}` in a certificate, which holds only kernel nodes"
        ));
    }
    let s = shape(n).map_err(|e| format!("{at}: {e}"))?;
    let ins = n.inputs.len();
    if ins < s.fixed || (s.exact && ins != s.fixed) {
        let more = if s.exact { "" } else { " or more" };
        return Err(format!(
            "{at}: `{name}` takes {}{more}, and has {ins}",
            several(s.fixed, "input")
        ));
    }
    if let Some(k) = s.outputs
        && n.outputs.len() != k
    {
        return Err(format!(
            "{at}: `{name}` has {}, and {} written",
            several(k, "output"),
            written(n.outputs.len())
        ));
    }
    if n.regions.len() != s.regions.len() {
        return Err(format!(
            "{at}: `{name}` has {}, and {} written",
            several(s.regions.len(), "region"),
            written(n.regions.len())
        ));
    }
    edges(r, n, at)?;
    let captures = &n.inputs[s.fixed..];
    for (j, (sub, &(kind, lead, results))) in n.regions.iter().zip(&s.regions).enumerate() {
        let sp = format!("{at}/{j}");
        if sub.kind != kind {
            return Err(format!(
                "{sp}: region {j} of `{name}` must be a {} region, and is written `{}`",
                kind_name(kind),
                kind_name(sub.kind)
            ));
        }
        if sub.args.len() != lead + captures.len() {
            let why = match &n.op {
                Op::Match(ps) => format!(
                    " (the pattern `{}` binds {})",
                    text::pattern(&ps[j]),
                    several(lead, "name")
                ),
                _ => String::new(),
            };
            return Err(format!(
                "{sp}: the region takes {} from the node{why} and {}, {} in all, and has {}",
                several(lead, "argument"),
                several(captures.len(), "capture"),
                lead + captures.len(),
                sub.args.len()
            ));
        }
        for (i, c) in captures.iter().enumerate() {
            let (want, got) = (r.edge(c), &sub.args[lead + i]);
            if want != *got {
                return Err(format!(
                    "{sp}^{}: capture {i} is {}, and the argument is {}",
                    lead + i,
                    text::edge(&want),
                    text::edge(got)
                ));
            }
        }
        if sub.results.len() != results {
            return Err(format!(
                "{sp}: the region must have {}, and {} written",
                several(results, "result"),
                written(sub.results.len())
            ));
        }
        region(sub, &sp, in_certificate || matches!(n.op, Op::Derived(_)))?;
        // A region's results stand for the node's outputs, kind for kind.
        if s.outputs.is_none() {
            for (i, (res, out)) in sub.results.iter().zip(&n.outputs).enumerate() {
                let got = sub.edge(res);
                if got.is_state() != out.is_state() || (out.is_state() && got != *out) {
                    return Err(format!(
                        "{sp}: result {i} is {}, and output {i} is {}",
                        text::edge(&got),
                        text::edge(out)
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Checks which of a node's inputs and outputs are state edges.
fn edges(r: &Region, n: &Node, at: &str) -> Result<(), String> {
    let name = title(&n.op);
    let state_in = |i: usize, port: &Arc<str>| -> Result<(), String> {
        match r.edge(&n.inputs[i]) {
            Edge::State(p) if p == *port => Ok(()),
            e => Err(format!(
                "{at}: input {i} of `{name}` is {}, and must be `state {port}`",
                text::edge(&e)
            )),
        }
    };
    match &n.op {
        Op::Read(port) | Op::Push(port) => {
            state_in(0, port)?;
            if let Some(i) = (1..n.inputs.len()).find(|&i| r.edge(&n.inputs[i]).is_state()) {
                return Err(format!("{at}: input {i} of `{name}` is a state edge"));
            }
            if n.outputs[0].is_state() || n.outputs[1] != Edge::State(port.clone()) {
                return Err(format!(
                    "{at}: `{name}` has outputs (a value; state {port}), and has ({}; {})",
                    text::edge(&n.outputs[0]),
                    text::edge(&n.outputs[1])
                ));
            }
        }
        op => {
            // State may pass through the region nodes that thread it; elsewhere edges carry
            // values.
            let threads = matches!(op, Op::If | Op::Match(_) | Op::Wave);
            let fixed = shape(n).map_or(0, |s| s.fixed);
            for (i, src) in n.inputs.iter().enumerate() {
                if r.edge(src).is_state() && !(threads && i >= fixed) {
                    return Err(format!("{at}: input {i} of `{name}` is a state edge"));
                }
            }
            if !threads && let Some(p) = n.outputs.iter().position(Edge::is_state) {
                return Err(format!("{at}: output {p} of `{name}` is a state edge"));
            }
        }
    }
    Ok(())
}
