//! What the generated code and the runtime hooks share about one graph: each node the
//! counting machine runs, numbered, with its plan; each lambda; the constants; the
//! primitives used as values; the lookup ports.

use std::collections::HashMap;

use zed_kernel::{Prim, Value};
use zedc::zir::memory::{Mode, Plan};
use zedc::zir::{Node, Op, Region, RegionKind, Src};

use zed_rt::Word;

/// One node of a planned region.
pub(crate) struct NodeInfo {
    /// The node.
    pub node: Node,
    /// The node alone in a region whose arguments are its inputs, for the kernel.
    pub alone: Region,
    /// Where it is (`r.3/0.1`), for messages.
    pub path: String,
    /// How it takes each input.
    pub modes: Vec<Mode>,
    /// For an `if` or a `match`: how each arm holds its arguments.
    pub arms: Vec<Vec<Mode>>,
    /// For a lambda: its index among the lambdas.
    pub lambda: Option<usize>,
    /// For an `apply` the plan resolves: the callee's lambda.
    pub callee: Option<usize>,
    /// An error the node raises when it runs, known before it runs.
    pub error: Option<String>,
}

/// One lambda: its node, the path of its body, its parameters and how the body holds them.
pub(crate) struct LambdaInfo {
    /// The lambda node's number.
    pub node: usize,
    /// The body's path.
    pub path: String,
    /// The number of parameters, before the captures.
    pub params: usize,
    /// How the body holds each parameter.
    pub modes: Vec<Mode>,
}

/// The tables of one graph.
pub(crate) struct Tables {
    /// The nodes, in the order the generator visits them.
    pub nodes: Vec<NodeInfo>,
    /// Each node's number by its path.
    pub ids: HashMap<String, usize>,
    /// The lambdas.
    pub lambdas: Vec<LambdaInfo>,
    /// The constants that are not scalars, which the heap holds uncounted.
    pub consts: Vec<Value>,
    /// The primitives used as values.
    pub prims: Vec<Prim>,
    /// The lookup ports.
    pub ports: Vec<std::sync::Arc<str>>,
    /// Whether a `match` fuses its release.
    pub fuse: bool,
}

impl Tables {
    /// The tables of graph `g` under `plan`.
    pub fn new(g: &Region, plan: &Plan) -> Result<Tables, String> {
        let mut t = Tables {
            nodes: Vec::new(),
            ids: HashMap::new(),
            lambdas: Vec::new(),
            consts: Vec::new(),
            prims: Vec::new(),
            ports: Vec::new(),
            fuse: plan.fuse,
        };
        t.visit(g, "r", plan)?;
        // An `apply` may call a lambda the generator visits after it.
        for id in 0..t.nodes.len() {
            t.resolve(id, plan)?;
        }
        Ok(t)
    }

    fn visit(&mut self, r: &Region, path: &str, plan: &Plan) -> Result<(), String> {
        let rp = plan.regions.get(path).ok_or_else(|| {
            format!("native: region `{path}` has no plan; only the root, lambda bodies and arms do")
        })?;
        for s in &r.results {
            self.constant(s);
        }
        for (k, node) in r.nodes.iter().enumerate() {
            let at = format!("{path}.{k}");
            let id = self.nodes.len();
            self.ids.insert(at.clone(), id);
            for s in &node.inputs {
                self.constant(s);
            }
            let mut n = node.clone();
            n.inputs = (0..n.inputs.len()).map(Src::Arg).collect();
            self.nodes.push(NodeInfo {
                node: node.clone(),
                alone: Region {
                    kind: RegionKind::Function,
                    args: Vec::new(),
                    nodes: vec![n],
                    results: vec![Src::Out(0, 0)],
                },
                path: at.clone(),
                modes: rp.nodes[k].modes.clone(),
                arms: Vec::new(),
                lambda: None,
                callee: None,
                error: None,
            });
            match &node.op {
                Op::Prim(p) if node.inputs.is_empty() && p.arity().is_some() => {
                    if !self.prims.contains(p) {
                        self.prims.push(*p);
                    }
                }
                Op::Read(p) => {
                    if !self.ports.contains(p) {
                        self.ports.push(p.clone());
                    }
                }
                Op::Lambda => {
                    let body = format!("{at}/0");
                    let params = node.regions[0].args.len() - node.inputs.len();
                    let modes = plan
                        .regions
                        .get(&body)
                        .ok_or_else(|| format!("native: lambda body `{body}` has no plan"))?
                        .args[..params]
                        .to_vec();
                    self.nodes[id].lambda = Some(self.lambdas.len());
                    self.lambdas.push(LambdaInfo {
                        node: id,
                        path: body.clone(),
                        params,
                        modes,
                    });
                    self.visit(&node.regions[0], &body, plan)?;
                }
                Op::If | Op::Match(_) => {
                    for (i, arm) in node.regions.iter().enumerate() {
                        let p = format!("{at}/{i}");
                        let modes = plan
                            .regions
                            .get(&p)
                            .ok_or_else(|| format!("native: arm `{p}` has no plan"))?
                            .args
                            .clone();
                        self.nodes[id].arms.push(modes);
                        self.visit(arm, &p, plan)?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Resolves node `id`'s callee, when it is an `apply` the plan resolves, and records the
    /// error a call raises that passes borrowed what the callee consumes.
    fn resolve(&mut self, id: usize, plan: &Plan) -> Result<(), String> {
        let ni = &self.nodes[id];
        if ni.node.op != Op::Apply {
            return Ok(());
        }
        let (parent, k) = ni.path.rsplit_once('.').expect("a node path");
        let np = &plan.regions[parent].nodes[k.parse::<usize>().expect("a node index")];
        let Some(want) = &np.callee else {
            return Ok(());
        };
        let li = self
            .lambdas
            .iter()
            .position(|l| l.path == *want)
            .ok_or_else(|| format!("native: {}: the plan calls `{want}`, no lambda", ni.path))?;
        let l = &self.lambdas[li];
        let mut error = None;
        if l.params + 1 == ni.node.inputs.len() {
            for i in 0..l.params {
                if ni.modes[1 + i] == Mode::Borrowed && l.modes[i] == Mode::Owned {
                    error = Some(format!(
                        "memory: {}: argument {i} is passed borrowed to `{want}`, which consumes it",
                        ni.path
                    ));
                    break;
                }
            }
        }
        self.nodes[id].callee = Some(li);
        self.nodes[id].error = error;
        Ok(())
    }

    fn constant(&mut self, s: &Src) {
        if let Src::Const(v) = s
            && Word::scalar(v).is_none()
            && !self.consts.contains(v)
        {
            self.consts.push(v.clone());
        }
    }

    /// The index of non-scalar constant `v`.
    pub fn const_index(&self, v: &Value) -> usize {
        self.consts
            .iter()
            .position(|c| c == v)
            .unwrap_or_else(|| panic!("constant {v:?} is not in the table {:?}", self.consts))
    }
}
