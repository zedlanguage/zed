//! The validator of the graph (step L1.31): it checks the structure the module documentation
//! of `super` lists, and names the node or region at fault by its path in the text form.

use std::collections::HashMap;
use std::fmt::Write;
use std::sync::Arc;

use super::text;
use super::{Edge, Node, Op, Region, RegionKind, Src, binds, kind_name, op_name};

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
            Some(_) if ins == 0 => leaf(0),
            Some(k) => leaf(k),
            None => captures(0, Some(1), Vec::new()),
        },
        Op::Apply => {
            if ins == 0 {
                return Err("`apply` has no function input".into());
            }
            captures(1, None, Vec::new())
        }
        Op::Lambda => {
            let (params, states) = n.regions.first().map_or((0, 0), |r| {
                let lead = r.args.len().saturating_sub(ins);
                (lead, r.args[..lead].iter().filter(|a| a.is_state()).count())
            });
            captures(0, Some(1), vec![(RegionKind::Function, params, 1 + states)])
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
        Op::Prim(p) => format!("prim {}", p.printed()),
        Op::Read(port) => format!("port read {port}"),
        Op::Push(port) => format!("port push {port}"),
        op => op_name(op).into(),
    }
}

/// Checks the structure of the graph rooted at `root`. The error names the node or region at
/// fault by its path in the text form (`r.2/0.1`) and says what is wrong.
///
/// The walk keeps one frame per open region on the heap, and one path buffer that grows by a
/// step on the way down and shrinks on the way up, so a check costs O(size) at any depth and a
/// path is copied only into an error.
pub fn validate(root: &Region) -> Result<(), String> {
    let mut path = String::from("r");
    enter(root, &path, false)?;
    let mut stack = vec![Visit::new(root, false, path.len())];
    while let Some(top) = stack.last_mut() {
        let r = top.r;
        if let Some((s, at)) = &top.open {
            let n = &r.nodes[top.k];
            let j = top.j;
            if j == n.regions.len() {
                path.truncate(top.base);
                top.open = None;
                top.k += 1;
                continue;
            }
            path.truncate(*at);
            write!(path, "/{j}").expect("writing to a String does not fail");
            let sub = &*n.regions[j];
            before(r, n, s, j, &path)?;
            enter(sub, &path, matches!(n.op, Op::Lambda))?;
            let in_certificate = top.in_certificate || matches!(n.op, Op::Derived(_));
            stack.push(Visit::new(sub, in_certificate, path.len()));
        } else if top.k < r.nodes.len() {
            let (k, n) = (top.k, &r.nodes[top.k]);
            let base = &path[..top.base];
            for (i, src) in n.inputs.iter().enumerate() {
                source(r, src, k, base).map_err(|e| format!("{base}.{k}: input {i}: {e}"))?;
                top.count(src);
            }
            write!(path, ".{k}").expect("writing to a String does not fail");
            let s = node(r, n, &path, top.in_certificate)?;
            top.j = 0;
            top.open = Some((s, path.len()));
        } else {
            let done = stack.pop().expect("the loop holds the top frame");
            path.truncate(done.base);
            let sub = done.r;
            done.close(&path)?;
            if let Some(up) = stack.last_mut() {
                let (s, _) = up
                    .open
                    .as_ref()
                    .expect("a child frame has an open node above it");
                after(&up.r.nodes[up.k], s, sub, &path)?;
                up.j += 1;
            }
        }
    }
    Ok(())
}

/// A state edge of a region, by where it starts: argument `i` is `(None, i)`, and output `p`
/// of node `n` is `(Some(n), p)`.
type Use = (Option<usize>, usize);

/// The text form of a state edge of the region at `path`.
fn use_name((n, p): Use, path: &str) -> String {
    match n {
        None => format!("{path}^{p}"),
        Some(n) => format!("{path}.{n}^{p}"),
    }
}

/// A region the walk of [`validate`] is inside.
struct Visit<'a> {
    r: &'a Region,
    in_certificate: bool,
    /// The length of the region's path in the walk's buffer.
    base: usize,
    /// The node being checked or next to be checked.
    k: usize,
    /// While node `k`'s regions are walked: its shape and the length of its path.
    open: Option<(Shape, usize)>,
    /// The next region of node `k` to walk.
    j: usize,
    /// How many times each state edge of the region is used.
    uses: HashMap<Use, usize>,
    /// The state edges in order of first use.
    order: Vec<Use>,
}

impl<'a> Visit<'a> {
    fn new(r: &'a Region, in_certificate: bool, base: usize) -> Visit<'a> {
        Visit {
            r,
            in_certificate,
            base,
            k: 0,
            open: None,
            j: 0,
            uses: HashMap::new(),
            order: Vec::new(),
        }
    }

    /// Counts a use of `src` when it is a state edge.
    fn count(&mut self, src: &Src) {
        let key = match *src {
            Src::Arg(i) => (None, i),
            Src::Out(n, p) => (Some(n), p),
            Src::Const(_) => return,
        };
        if self.r.edge(src).is_state() {
            let n = self.uses.entry(key).or_default();
            if *n == 0 {
                self.order.push(key);
            }
            *n += 1;
        }
    }

    /// Checks the region's results, and that each state edge is used exactly once, after its
    /// nodes. `path` is the region's.
    fn close(mut self, path: &str) -> Result<(), String> {
        let r = self.r;
        for (i, src) in r.results.iter().enumerate() {
            source(r, src, r.nodes.len(), path).map_err(|e| format!("{path}: result {i}: {e}"))?;
            self.count(src);
        }
        if let Some((key, n)) = self
            .order
            .iter()
            .map(|m| (*m, self.uses[m]))
            .find(|(_, n)| *n > 1)
        {
            return Err(format!(
                "{}: a state edge is used {n} times, and each is used exactly once",
                use_name(key, path)
            ));
        }
        let args = r.args.iter().enumerate().map(|(i, a)| ((None, i), a));
        let outs = r.nodes.iter().enumerate().flat_map(|(k, n)| {
            n.outputs
                .iter()
                .enumerate()
                .map(move |(p, e)| ((Some(k), p), e))
        });
        if let Some((key, _)) = args
            .chain(outs)
            .find(|(key, e)| e.is_state() && !self.uses.contains_key(key))
        {
            return Err(format!(
                "{}: a state edge is never used, and each is used exactly once",
                use_name(key, path)
            ));
        }
        Ok(())
    }
}

/// Checks the arguments of region `r` at `path` on entry. `of_lambda` when `r` is the region
/// of a `lambda` node, whose state arguments are the ports its body uses.
fn enter(r: &Region, path: &str, of_lambda: bool) -> Result<(), String> {
    if !matches!(r.kind, RegionKind::Match | RegionKind::Port)
        && !of_lambda
        && let Some(i) = r.args.iter().position(Edge::is_state)
    {
        return Err(format!(
            "{path}^{i}: a state edge cannot enter a {} region",
            kind_name(r.kind)
        ));
    }
    if of_lambda {
        let states: Vec<&Edge> = r.args.iter().filter(|a| a.is_state()).collect();
        let back: Vec<Edge> = r.results.iter().skip(1).map(|s| r.edge(s)).collect();
        if r.results.first().is_some_and(|s| r.edge(s).is_state())
            || back.len() != states.len()
            || back.iter().zip(&states).any(|(b, a)| b != *a)
        {
            return Err(format!(
                "{path}: a lambda's region returns its value and then the state of each port it \
                 takes, in the order of its arguments ({}), and returns ({})",
                states
                    .iter()
                    .map(|e| text::edge(e))
                    .collect::<Vec<_>>()
                    .join(", "),
                r.results
                    .iter()
                    .map(|s| text::edge(&r.edge(s)))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
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

/// Checks node `n` of region `r` at `at`, before its regions, and returns its shape.
fn node(r: &Region, n: &Node, at: &str, in_certificate: bool) -> Result<Shape, String> {
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
    Ok(s)
}

/// Checks region `j` of node `n` of region `r`, at `sp`, against the node before the walk
/// enters it.
fn before(r: &Region, n: &Node, s: &Shape, j: usize, sp: &str) -> Result<(), String> {
    let name = title(&n.op);
    let sub = &n.regions[j];
    let (kind, lead, results) = s.regions[j];
    let captures = &n.inputs[s.fixed..];
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
    Ok(())
}

/// Checks region `sub` of node `n`, at `sp`, against the node's outputs after the
/// walk leaves it: a region's results stand for the node's outputs, kind for kind.
fn after(n: &Node, s: &Shape, sub: &Region, sp: &str) -> Result<(), String> {
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
        Op::Apply => {
            let ins: Vec<Edge> = n.inputs.iter().map(|s| r.edge(s)).collect();
            let first = ins.iter().position(Edge::is_state).unwrap_or(ins.len());
            if first == 0 {
                return Err(format!(
                    "{at}: input 0 of `{name}`, the function, is a state edge"
                ));
            }
            if let Some(i) = (first..ins.len()).find(|&i| !ins[i].is_state()) {
                return Err(format!(
                    "{at}: input {i} of `{name}` is a value after a state edge, and the states \
                     come after the arguments"
                ));
            }
            let outs = &n.outputs;
            if outs.first().is_none_or(Edge::is_state) || outs[1..] != ins[first..] {
                return Err(format!(
                    "{at}: `{name}` has outputs (a value; {}), the states it takes, and has ({})",
                    ins[first..]
                        .iter()
                        .map(text::edge)
                        .collect::<Vec<_>>()
                        .join("; "),
                    outs.iter().map(text::edge).collect::<Vec<_>>().join("; ")
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
