//! What the generated code and the runtime hooks share about one graph: each node the
//! counting machine runs, numbered, with its plan; each lambda; the constants; the
//! primitives used as values; the lookup ports.
//!
//! The tables share the graph: a node is its region and its index there, so entering a node
//! costs a reference count however much lies below it. Where a node is (`r.3/0.1`) is worked
//! out for a message, from the links up, and is not kept: a path is as long as its depth.

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::sync::Arc;

use zed_kernel::{Prim, Value};
use zedc::zir::legalize::{Legalized, Swapped, nodes_in};
use zedc::zir::memory::{Mode, Plan, RegionPlan};
use zedc::zir::{Node, Op, Region, Src};

use zed_rt::Word;

/// One node of a planned region.
pub(crate) struct NodeInfo {
    /// The graph's region that holds the node.
    region: Arc<Region>,
    /// The number of that region in [`Tables::regions`].
    pub at: usize,
    /// The node's index in that region.
    pub k: usize,
    /// How it takes each input.
    pub modes: Vec<Mode>,
    /// For an `if` or a `match`: how each arm holds its arguments.
    pub arms: Vec<Vec<Mode>>,
    /// For a lambda, an `if` or a `match`: the numbers of its regions.
    pub subs: Vec<usize>,
    /// For a lambda: its index among the lambdas.
    pub lambda: Option<usize>,
    /// For an `apply` the plan resolves: the callee's lambda.
    pub callee: Option<usize>,
    /// An error the node raises when it runs, known before it runs.
    pub error: Option<String>,
    /// The node's number in the legalized graph, in preorder over every region at every depth
    /// (`zedc::zir::legalize::Legalized`): what tells the kernel whether it was swapped.
    pub number: usize,
}

impl NodeInfo {
    /// The node.
    pub fn node(&self) -> &Node {
        &self.region.nodes[self.k]
    }
}

/// One planned region: the root, a lambda's body or an arm.
pub(crate) struct RegionInfo {
    /// The graph's region.
    pub region: Arc<Region>,
    /// The node that holds it and its index among that node's regions; the root has none.
    up: Option<(usize, usize)>,
    /// The numbers of its nodes.
    pub ids: Vec<usize>,
}

/// One lambda: its node, the number of its body, its parameters and how the body holds them.
pub(crate) struct LambdaInfo {
    /// The lambda node's number.
    pub node: usize,
    /// The body's number among the regions.
    pub body: usize,
    /// The number of parameters, before the captures.
    pub params: usize,
    /// How the body holds each parameter.
    pub modes: Vec<Mode>,
}

/// The tables of one graph.
pub(crate) struct Tables {
    /// The nodes, in preorder.
    pub nodes: Vec<NodeInfo>,
    /// The planned regions; the root is the first.
    pub regions: Vec<RegionInfo>,
    /// The lambdas.
    pub lambdas: Vec<LambdaInfo>,
    /// The constants that are not scalars, which the heap holds uncounted.
    pub consts: Vec<Value>,
    /// The primitives used as values.
    pub prims: Vec<Prim>,
    /// The lookup ports.
    pub ports: Vec<Arc<str>>,
    /// Each lookup port's index among the ports.
    pub port_at: HashMap<Arc<str>, usize>,
    /// Each constant's index among the constants.
    const_at: BTreeMap<Value, usize>,
    /// Whether a `match` fuses its release.
    pub fuse: bool,
    /// The nodes legalization swapped, by number.
    pub swapped: Arc<Swapped>,
}

/// A region being numbered. Regions nest as deep as the term, so the regions in progress are
/// on a stack, each with its next node.
struct Visit<'g> {
    /// Its number.
    at: usize,
    /// The region.
    region: &'g Arc<Region>,
    /// Its index in [`Plan::regions`].
    pat: usize,
    /// The next node.
    k: usize,
}

impl Tables {
    /// The tables of graph `g` under `plan`, and each region's plan by its number.
    pub fn new<'p>(g: &Legalized, plan: &'p Plan) -> Result<(Tables, Vec<&'p RegionPlan>), String> {
        let mut t = Tables {
            nodes: Vec::new(),
            regions: Vec::new(),
            lambdas: Vec::new(),
            consts: Vec::new(),
            prims: Vec::new(),
            ports: Vec::new(),
            port_at: HashMap::new(),
            const_at: BTreeMap::new(),
            fuse: plan.fuse,
            swapped: g.swapped().clone(),
        };
        let mut plans = Vec::new();
        let mut lambda_at = vec![None; plan.regions.len()];
        let numbered = t.visit(g.graph(), plan, &mut plans, &mut lambda_at)?;
        debug_assert_eq!(
            numbered,
            g.nodes(),
            "native numbers the nodes as legalization does"
        );
        // An `apply` may call a lambda the generator visits after it.
        for id in 0..t.nodes.len() {
            t.resolve(id, plan, &plans, &lambda_at)?;
        }
        Ok((t, plans))
    }

    /// Numbers the nodes of `g` and its planned regions in preorder, and gives each its number
    /// among all the nodes of `g`, those of regions it does not plan included; returns how many
    /// nodes `g` holds.
    fn visit<'p>(
        &mut self,
        g: &Arc<Region>,
        plan: &'p Plan,
        plans: &mut Vec<&'p RegionPlan>,
        lambda_at: &mut [Option<usize>],
    ) -> Result<usize, String> {
        let rp = plan.regions.first().ok_or_else(|| {
            crate::bug("region `r` has no plan; only the root, lambda bodies and arms do")
        })?;
        plans.push(rp);
        self.regions.push(RegionInfo {
            region: g.clone(),
            up: None,
            ids: Vec::new(),
        });
        let mut stack = vec![Visit {
            at: 0,
            region: g,
            pat: 0,
            k: 0,
        }];
        let mut number = 0;
        while let Some(v) = stack.last_mut() {
            if v.k == 0 {
                for s in &v.region.results {
                    self.constant(s);
                }
            }
            if v.k == v.region.nodes.len() {
                stack.pop();
                continue;
            }
            let (at, region, pat, k) = (v.at, v.region, v.pat, v.k);
            v.k += 1;
            let node = &region.nodes[k];
            let id = self.nodes.len();
            self.regions[at].ids.push(id);
            for s in &node.inputs {
                self.constant(s);
            }
            let mut info = NodeInfo {
                region: region.clone(),
                at,
                k,
                modes: plans[at].nodes[k].modes.clone(),
                arms: Vec::new(),
                subs: Vec::new(),
                lambda: None,
                callee: None,
                error: None,
                number,
            };
            number += 1;
            match &node.op {
                Op::Prim(p) if node.inputs.is_empty() && p.arity().is_some() => {
                    if !self.prims.contains(p) {
                        self.prims.push(*p);
                    }
                }
                Op::Read(p) => {
                    if !self.port_at.contains_key(p) {
                        self.port_at.insert(p.clone(), self.ports.len());
                        self.ports.push(p.clone());
                    }
                }
                Op::Lambda | Op::If | Op::Match(_) => {
                    // The first region is numbered first, so it is last on the stack.
                    let first = stack.len();
                    for (i, r) in node.regions.iter().enumerate() {
                        let sub = plan.regions[pat].nodes[k].regions.get(i).copied();
                        let sub = sub.ok_or_else(|| {
                            let what = match node.op {
                                Op::Lambda => "lambda body",
                                _ => "arm",
                            };
                            crate::bug(format_args!(
                                "{what} `{}.{k}/{i}` has no plan",
                                plan.path(pat)
                            ))
                        })?;
                        let rp = &plan.regions[sub];
                        let at = self.regions.len();
                        info.subs.push(at);
                        plans.push(rp);
                        self.regions.push(RegionInfo {
                            region: r.clone(),
                            up: Some((id, i)),
                            ids: Vec::new(),
                        });
                        stack.push(Visit {
                            at,
                            region: r,
                            pat: sub,
                            k: 0,
                        });
                        if matches!(node.op, Op::Lambda) {
                            let params = r.args.len() - node.inputs.len();
                            lambda_at[sub] = Some(self.lambdas.len());
                            info.lambda = Some(self.lambdas.len());
                            self.lambdas.push(LambdaInfo {
                                node: id,
                                body: at,
                                params,
                                modes: rp.args[..params].to_vec(),
                            });
                            break;
                        }
                        info.arms.push(rp.args.clone());
                    }
                    stack[first..].reverse();
                }
                // A `fam`, `fix` or `gen` body is not planned: the kernel runs the node whole.
                _ => number += nodes_in(&node.regions),
            }
            self.nodes.push(info);
        }
        Ok(number)
    }

    /// Resolves node `id`'s callee, when it is an `apply` the plan resolves, and records the
    /// error a call raises that passes borrowed what the callee consumes.
    fn resolve(
        &mut self,
        id: usize,
        plan: &Plan,
        plans: &[&RegionPlan],
        lambda_at: &[Option<usize>],
    ) -> Result<(), String> {
        let ni = &self.nodes[id];
        let node = ni.node();
        if node.op != Op::Apply {
            return Ok(());
        }
        let Some(want) = plans[ni.at].nodes[ni.k].callee else {
            return Ok(());
        };
        let li = lambda_at.get(want).copied().flatten().ok_or_else(|| {
            crate::bug(format_args!(
                "{}: the plan calls `{}`, no lambda",
                self.path(id),
                plan.path(want)
            ))
        })?;
        let l = &self.lambdas[li];
        let mut error = None;
        if l.params + 1 == node.inputs.len() {
            for i in 0..l.params {
                if ni.modes[1 + i] == Mode::Borrowed && l.modes[i] == Mode::Owned {
                    error = Some(format!(
                        "{}: argument {i} is passed borrowed to `{}`, which consumes it",
                        self.path(id),
                        plan.path(want)
                    ));
                    break;
                }
            }
        }
        self.nodes[id].callee = Some(li);
        self.nodes[id].error = error;
        Ok(())
    }

    /// Where node `id` is (`r.3/0.1`), for a message.
    pub fn path(&self, id: usize) -> String {
        let mut steps = vec![(self.nodes[id].k, None)];
        let mut at = self.nodes[id].at;
        while let Some((up, i)) = self.regions[at].up {
            let ni = &self.nodes[up];
            steps.push((ni.k, Some(i)));
            at = ni.at;
        }
        let mut path = String::from("r");
        for (k, i) in steps.into_iter().rev() {
            write!(path, ".{k}").expect("a write to a string");
            if let Some(i) = i {
                write!(path, "/{i}").expect("a write to a string");
            }
        }
        path
    }

    /// Where region `at` is (`r.3/0`), for a message.
    pub fn region_path(&self, at: usize) -> String {
        match self.regions[at].up {
            None => "r".into(),
            Some((up, i)) => format!("{}/{i}", self.path(up)),
        }
    }

    fn constant(&mut self, s: &Src) {
        if let Src::Const(v) = s
            && Word::scalar(v).is_none()
            && !self.const_at.contains_key(v)
        {
            self.const_at.insert(v.clone(), self.consts.len());
            self.consts.push(v.clone());
        }
    }

    /// The index of non-scalar constant `v`.
    pub fn const_index(&self, v: &Value) -> usize {
        *self
            .const_at
            .get(v)
            .unwrap_or_else(|| panic!("constant {v:?} is not in the table {:?}", self.consts))
    }
}
