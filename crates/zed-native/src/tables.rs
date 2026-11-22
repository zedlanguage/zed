//! What the generated code and the runtime hooks share about one graph: each node the
//! counting machine runs, numbered, with its plan; each lambda; the constants; the
//! primitives used as values; the lookup ports.
//!
//! The tables share the graph: a node is its region and its index there, so entering a node
//! costs a reference count however much lies below it. Where a node is (`r.3/0.1`) is worked
//! out for a message, from the links up, and is not kept: a path is as long as its depth.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::sync::Arc;

use zed_collections::index::to_u32;
use zed_kernel::{Prim, Value};
use zedc::zir::legalize::{Legalized, Swapped, nodes_in};
use zedc::zir::memory::{Mode, Plan, RegionPlan};
use zedc::zir::{Edge, Node, Op, Region, Src};
use zedc_lattice::float_kinds::Kinds;

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
    /// For a `place` whose table is a literal of the form the kernel reads: the index of its
    /// parameter list in [`Tables::placings`].
    pub placing: Option<u32>,
    /// For a `callNamed` whose shape is a literal of the form the kernel reads: the shape.
    pub named: Option<Box<NamedShape>>,
    /// The kinds of float each of the node's first two inputs may be, read from the graph by
    /// [`Tables::kinds_of`] (FLOAT-class-zir); what float `^` reads to leave out its NaN test
    /// (`codegen.rs`, fn `pow`). Two, since no primitive the rules cover takes more.
    pub kinds: [Kinds; 2],
    /// The kinds of float the node's first output may be: by [`Kinds::transfer`] for a
    /// primitive, every kind otherwise, less the NaN when the output's edge type excludes it.
    pub out: Kinds,
}

/// The parameter list a `place` node gives the closure it makes (DESIGN.md
/// sec:values_morphisms, "The function called places the arguments"), read once from the
/// literal table `(n, names, places, defaulted)` the elaborator wrote, as the kernel's
/// `placing` reads it at each call.
pub(crate) struct Placing {
    /// The literal table, for the kernel term of a closure that carries it.
    pub table: Value,
    /// The number of parameters.
    pub n: usize,
    /// The parameter names, strictly increasing.
    pub names: Vec<Value>,
    /// Each name's rank among all the names of the program ([`Tables::rank_names`]).
    pub ranks: Vec<u32>,
    /// For each name, the parameter it names; no two names name one parameter.
    pub places: Vec<usize>,
    /// For each parameter, whether the function fills it with a default when a call leaves
    /// it out.
    pub defaulted: Vec<bool>,
    /// The number of defaulted parameters.
    pub defaults: usize,
    /// Whether the node is given the function that fills the defaults, its third input.
    pub fill: bool,
}

/// The shape `(k, names, at[, opt])` of a `callNamed` node, read once from its literal, as
/// the kernel's `placing` reads it: the node's inputs after the shape and the function are `k`
/// positional arguments, one argument for each name, and the flags.
pub(crate) struct NamedShape {
    /// The number of positional arguments.
    pub k: usize,
    /// The argument names, strictly increasing.
    pub names: Vec<Value>,
    /// Each name's rank among all the names of the program ([`Tables::rank_names`]).
    pub ranks: Vec<u32>,
    /// For each name, its argument's index after the positional ones.
    pub at: Vec<usize>,
    /// For each name, the index among the flags of the flag that leaves its argument out, if
    /// any.
    pub opt: Vec<Option<usize>>,
    /// Whether some argument has a flag: then which arguments the call passes changes from
    /// one run of it to the next.
    pub flagged: bool,
}

impl Placing {
    /// The list `table` gives, or none when it is not of the form the elaborator writes; the
    /// kernel then runs the node and gives the error.
    fn read(table: &Value, fill: bool) -> Option<Placing> {
        let Value::Tuple(xs) = table else { return None };
        let [
            Value::Int(n),
            Value::Tuple(names),
            Value::Tuple(places),
            Value::Tuple(defaulted),
        ] = xs.as_slice()
        else {
            return None;
        };
        let n = usize::try_from(*n).ok()?;
        let places = places.iter().map(index).collect::<Option<Vec<_>>>()?;
        let defaulted = (defaulted.iter())
            .map(|d| match d {
                Value::Bool(b) => Some(*b),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let mut named = vec![false; n];
        for &p in &places {
            if std::mem::replace(named.get_mut(p)?, true) {
                return None;
            }
        }
        let ok = places.len() == names.len()
            && defaulted.len() == n
            && names.windows(2).all(|w| w[0] < w[1]);
        ok.then(|| Placing {
            table: table.clone(),
            n,
            names: names.to_vec(),
            ranks: Vec::new(),
            places,
            defaults: defaulted.iter().filter(|d| **d).count(),
            defaulted,
            fill,
        })
    }
}

impl NamedShape {
    /// The shape `shape` gives for a node of `inputs` inputs, or none when it is not of the
    /// form the elaborator writes; the kernel then runs the node and gives the error.
    fn read(shape: &Value, inputs: usize) -> Option<NamedShape> {
        let Value::Tuple(xs) = shape else { return None };
        let (k, names, at, opt) = match xs.as_slice() {
            [k, Value::Tuple(names), Value::Tuple(at)] => (k, names, at, None),
            [k, Value::Tuple(names), Value::Tuple(at), Value::Tuple(opt)] => {
                (k, names, at, Some(opt))
            }
            _ => return None,
        };
        let k = index(k)?;
        let at = at.iter().map(index).collect::<Option<Vec<_>>>()?;
        // As the kernel reads `opt`: a non-negative integer is a flag's index, anything else
        // none.
        let opt: Vec<Option<usize>> = match opt {
            Some(o) => o.iter().map(index).collect(),
            None => vec![None; names.len()],
        };
        let flags = opt.iter().flatten().count();
        let mut taken = vec![false; names.len()];
        for &a in &at {
            if std::mem::replace(taken.get_mut(a)?, true) {
                return None;
            }
        }
        let ok = at.len() == names.len()
            && opt.len() == names.len()
            && inputs == 2 + k + names.len() + flags
            && names.windows(2).all(|w| w[0] < w[1]);
        ok.then(|| NamedShape {
            k,
            names: names.to_vec(),
            ranks: Vec::new(),
            at,
            flagged: opt.iter().any(Option::is_some),
            opt,
        })
    }
}

/// `v` as an index: a non-negative integer.
fn index(v: &Value) -> Option<usize> {
    match v {
        Value::Int(i) => usize::try_from(*i).ok(),
        _ => None,
    }
}

impl NodeInfo {
    /// The node.
    pub fn node(&self) -> &Node {
        &self.region.nodes[self.k]
    }
}

/// Whether the edge's type excludes the NaN, as an earlier pass may have written it; lowering
/// types every edge `_`, which holds it (ZIR-checker-facts is the row that will write the
/// checker's types). A state edge holds no value.
fn excludes_nan(edge: &Edge) -> bool {
    match edge {
        Edge::Value(e) => !e.ty.contains(&Value::float(f64::NAN)),
        Edge::State(_) => true,
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
    // Complexity tradeoff: this was a `BTreeMap`, each insert O(log c) byte compares, and two
    // string constants that agree on a long prefix compare in time of that prefix: the
    // constants of a program doubling a string 63 times, `s61` and `s62`, took minutes to put
    // in order when the executable started (item BUILD-doubling-60s). A hash map costs one
    // digest of each constant, a string's from its tree's distinct nodes (`Value`'s `Hash`),
    // and a compare only of constants of equal digest, which are equal or collide. Order was
    // never read; `consts` keeps the order of first use. Test
    // `l01_36a_executables/doubling.rs`.
    // Complexity tradeoff (COMPLEXITY.md F223b, F223e): keyed by the value under `==`, which an
    // executable needs: it builds this table again from the decoded program (`exe::start`),
    // where every family and tuple constant is a copy of its own, so a key by the built value's
    // id, tried first, numbered the entries of a built program otherwise than its executable and
    // failed `l01_36a_executables::port_in_family`. When `Value`'s hash read only a family's
    // number of entries, the n one-entry lists of n `[x] ++ a` fell in one bucket and each insert
    // and lookup compared them all, O(n^2) compares, 43 times the instructions at 8n (plan row
    // PERF-list-concat-native); a key that also hashed the first and last entry (`ConstKey`,
    // F223b) left the n families of one count and the same ends (`[0, i, 0]` for each i) in one
    // bucket. A family now hashes by all its entries, kept as sums (PERF-family-hash-count-only,
    // F223e), O(1) for a family built once, so the value is the key: one digest and O(1)
    // expected compares a constant. Tests
    // `tests::equal_constants_share_one_entry_and_others_do_not`, and in
    // `l03_15a_fp_ops_run::bench`, `constants_of_families_of_one_size_and_ends_scale` and
    // `a_native_right_nested_chain_of_concatenations_runs_in_n_log_n`.
    const_at: HashMap<Value, usize>,
    /// Whether a `match` fuses its release.
    pub fuse: bool,
    /// The nodes legalization swapped, by number.
    pub swapped: Arc<Swapped>,
    /// The parameter list of each `place` node that has one ([`NodeInfo::placing`]).
    pub placings: Vec<Placing>,
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
            const_at: HashMap::new(),
            fuse: plan.fuse,
            swapped: g.swapped().clone(),
            placings: Vec::new(),
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
        t.rank_names();
        Ok((t, plans))
    }

    /// Gives each name of a parameter list and of a call's shape its rank among all of them,
    /// so that a call by name compares two ranks where it would compare two names.
    // Complexity tradeoff: the merge of a placed call compared the names as values
    // (`Value::cmp`, a text compare each) at every call run; ranks saved about 120
    // instructions per argument at p = 320
    // (`a_placed_call_costs_about_a_direct_call_in_native_code`, row CALL-callee-places-native).
    // Here the N names of the program are sorted once, O(N log N) compares,
    // and each is ranked by a binary search, O(N log N); a call then compares integers, O(1)
    // each. Equal names get one rank, and ranks keep the names' order, so every merge takes
    // the same steps as it would on the names.
    fn rank_names(&mut self) {
        let shapes = self.nodes.iter().filter_map(|n| n.named.as_deref());
        let mut all: Vec<&Value> = (self.placings.iter().flat_map(|p| &p.names))
            .chain(shapes.flat_map(|s| &s.names))
            .collect();
        all.sort_unstable();
        all.dedup_by(|a, b| (*a).cmp(*b) == std::cmp::Ordering::Equal);
        let rank = |v: &Value| {
            all.binary_search_by(|x| (*x).cmp(v))
                .expect("every name is ranked") as u32
        };
        let placings: Vec<Vec<u32>> = (self.placings.iter())
            .map(|p| p.names.iter().map(rank).collect())
            .collect();
        let shapes: Vec<Option<Vec<u32>>> = (self.nodes.iter())
            .map(|n| {
                n.named
                    .as_deref()
                    .map(|s| s.names.iter().map(rank).collect())
            })
            .collect();
        for (p, r) in self.placings.iter_mut().zip(placings) {
            p.ranks = r;
        }
        for (n, r) in self.nodes.iter_mut().zip(shapes) {
            if let (Some(s), Some(r)) = (n.named.as_deref_mut(), r) {
                s.ranks = r;
            }
        }
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
            crate::bug::bug("region `r` has no plan; only the root, lambda bodies and arms do")
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
            let mut kinds = [Kinds::ALL; 2];
            for (i, s) in node.inputs.iter().take(2).enumerate() {
                kinds[i] = self.kinds_of(at, region, s);
            }
            let out = match node.outputs.first() {
                Some(e) if excludes_nan(e) => Kinds::ALL.minus(Kinds::NAN),
                _ => Kinds::ALL,
            };
            let out = match &node.op {
                Op::Prim(p) if node.inputs.len() <= 2 => {
                    let ins = &kinds[..node.inputs.len()];
                    // The edge rule and the transfer each hold, so their meet does.
                    Kinds::transfer(*p, ins).and(out)
                }
                _ => out,
            };
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
                placing: None,
                named: None,
                kinds,
                out,
            };
            number += 1;
            match (&node.op, node.inputs.first()) {
                (Op::Prim(Prim::Place), Some(Src::Const(table)))
                    if matches!(node.inputs.len(), 2 | 3) =>
                {
                    if let Some(p) = Placing::read(table, node.inputs.len() == 3) {
                        info.placing = Some(to_u32(self.placings.len(), "placings"));
                        self.placings.push(p);
                    }
                }
                (Op::Prim(Prim::CallNamed), Some(Src::Const(shape))) if node.inputs.len() >= 2 => {
                    info.named = NamedShape::read(shape, node.inputs.len()).map(Box::new);
                }
                _ => {}
            }
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
                            crate::bug::bug(format_args!(
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
            crate::bug::bug(format_args!(
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

    /// The numbers of parameters of the lambdas, each once, when a call by name may place its
    /// arguments in native code: some `place` and some `callNamed` have literals of the form
    /// the kernel reads. Each gets a function that calls a body of that many parameters on
    /// the words of a buffer ([`Tables::trampoline`]); none when no call is placed so.
    pub fn arities(&self) -> Vec<usize> {
        if self.placings.is_empty() || self.nodes.iter().all(|n| n.named.is_none()) {
            return Vec::new();
        }
        let mut a: Vec<usize> = self.lambdas.iter().map(|l| l.params).collect();
        zed_collections::sorted::sort_dedup(&mut a);
        a
    }

    /// The index among the registered entries of the body of lambda `i`, which takes each
    /// parameter as the lambda's [`LambdaInfo::modes`] say: after the lambdas' entries, and
    /// registered only when [`Tables::arities`] has some.
    pub fn body(&self, i: usize) -> usize {
        self.lambdas.len() + i
    }

    /// For each lambda, whether a call by name may go to its placed entry
    /// ([`Tables::placed`]): its number of parameters is the length of a parameter list with
    /// no fill and the number of arguments of a call by name with no flag, as `hooks::rt_direct`
    /// asks. Only these get a placed entry, a second copy of the body. None when
    /// [`Tables::arities`] has none.
    // Complexity tradeoff: a placed entry is a second copy of the lambda's body, O(size of the
    // body) more to compile: the program of
    // `a_placed_call_costs_about_a_direct_call_in_native_code` at one call, with two functions of
    // 320 parameters, took 489M instructions against 433M with none (row
    // CALL-callee-places-native). A placed entry for every lambda would copy every body; this test
    // is O(L + P + N) for L lambdas, P lists and N nodes, by two sets.
    pub fn placeable(&self) -> Vec<bool> {
        if self.arities().is_empty() {
            return Vec::new();
        }
        let lists: HashSet<usize> = (self.placings.iter())
            .filter(|p| !p.fill)
            .map(|p| p.n)
            .collect();
        let calls: HashSet<usize> = (self.nodes.iter())
            .filter_map(|n| n.named.as_deref())
            .filter(|sh| !sh.flagged)
            .map(|sh| sh.k + sh.names.len())
            .collect();
        (self.lambdas.iter())
            .map(|l| lists.contains(&l.params) && calls.contains(&l.params))
            .collect()
    }

    /// The index among the registered entries of the placed entry of lambda `i`, which reads
    /// each parameter among the arguments of a call by name at the offsets of a merge
    /// (`hooks::rt_direct`): after the lambdas' bodies, and registered only when
    /// [`Tables::arities`] has some.
    pub fn placed(&self, i: usize) -> usize {
        2 * self.lambdas.len() + i
    }

    /// The index among the registered entries of the function that calls a body of `arity`
    /// parameters on a buffer: after the placed entries.
    pub fn trampoline(&self, arity: usize) -> usize {
        3 * self.lambdas.len() + arity
    }

    /// The number of registered entries: the lambdas', and when [`Tables::arities`] has some,
    /// their bodies' and those of the arities.
    pub fn entry_count(&self) -> usize {
        self.arities()
            .last()
            .map_or(self.lambdas.len(), |&a| self.trampoline(a) + 1)
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

    /// The kinds of float input `s` of a node of region `at` (the graph's `region`) may be: a
    /// constant's own kind; the first output of a node before it in the region, the kinds
    /// [`Tables::visit`] found for it, which it numbered first; any other output and an
    /// argument every kind. Either less the NaN when its edge's type excludes it. The checker's
    /// classes of a parameter are not in the graph, so an argument stays every kind until row
    /// ZIR-checker-facts writes them on the edges, which this then reads. O(1).
    fn kinds_of(&self, at: usize, region: &Region, s: &Src) -> Kinds {
        let (k, edge) = match s {
            Src::Const(v) => return Kinds::of(v),
            Src::Arg(a) => (Kinds::ALL, &region.args[*a]),
            Src::Out(n, p) => {
                let ids = &self.regions[at].ids;
                let k = match (p, ids.get(*n)) {
                    (0, Some(&id)) => self.nodes.get(id).map_or(Kinds::ALL, |i| i.out),
                    _ => Kinds::ALL,
                };
                (k, &region.nodes[*n].outputs[*p])
            }
        };
        if excludes_nan(edge) {
            k.minus(Kinds::NAN)
        } else {
            k
        }
    }

    fn constant(&mut self, s: &Src) {
        if let Src::Const(v) = s
            && Word::scalar(v).is_none()
        {
            let n = self.consts.len();
            if let Entry::Vacant(e) = self.const_at.entry(v.clone()) {
                e.insert(n);
                self.consts.push(v.clone());
            }
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

#[cfg(test)]
mod tests {
    use zed_kernel::term::build::{lam, lit, prim, var};
    use zed_kernel::{Family, Rat};
    use zedc::zir::lower::lower;
    use zedc::zir::memory::plan;

    use super::*;

    /// `{k -> v, 1 -> 1}`.
    fn with_one(k: Value, v: Value) -> Value {
        Value::Family(Family::of([(k, v), (Value::Int(1), Value::Int(1))]))
    }

    /// Plan row PERF-value-key-sites-bench: the table of constants keeps one entry per value
    /// under `==` ([`Tables::constant`], [`Tables::const_index`]), whatever form each was built
    /// in, and one per value that differs. Each group below is one value: 0..9 as a range, a map
    /// and a list made by `++`; 3/4 as `3 / 4` and read as `75e-2`; 10^19 as a key from
    /// its digits and from a decimal exponent; a nested list and its `++` form. Apart from them:
    /// `0.0` and `-0.0` as an entry's value, which `1 / x` tells apart, and `[0, i, 0]` for three
    /// `i`, of one count and the same end entries.
    #[test]
    fn equal_constants_share_one_entry_and_others_do_not() {
        let fam = Value::Family;
        let half = |at: i64| Family::of((0..5_i64).map(|i| (i, i + at)));
        let whole = |s: &str| Rat::decimal(s).expect("memory").expect("a decimal");
        let quarters = (whole("3").div(&whole("4")).expect("memory")).expect("4 is not 0");
        let decimal = whole("75e-2");
        let digits = Value::int_text(&format!("1{}", "0".repeat(19)), 10)
            .expect("memory")
            .expect("digits");
        let exponent = Value::integer(whole("1e19"));
        let inner = Family::of([(0_i64, 1_i64), (1, 2)]);
        let joined = Family::of([(0_i64, 1_i64)])
            .concat(&Family::of([(0_i64, 2_i64)]))
            .expect("lists join");
        let mut groups = vec![
            vec![
                fam(Family::range(0, 9)),
                fam(Family::of((0..10_i64).map(|i| (i, i)))),
                fam(half(0).concat(&half(5)).expect("lists join")),
            ],
            vec![
                with_one(Value::Int(0), Value::rat(quarters)),
                with_one(Value::Int(0), Value::rat(decimal)),
            ],
            vec![
                with_one(digits, Value::Int(1)),
                with_one(exponent, Value::Int(1)),
            ],
            vec![
                with_one(Value::Int(0), fam(inner)),
                with_one(Value::Int(0), fam(joined)),
            ],
            vec![with_one(Value::Int(0), Value::float(0.0))],
            vec![with_one(Value::Int(0), Value::float(-0.0))],
        ];
        groups.extend((0..3_i64).map(|i| vec![fam(Family::of([(0_i64, 0), (1, i), (2, 0)]))]));
        // `(x) -> (x, c_1, …, c_k)`: the parameter keeps the tuple from being one constant.
        let items = std::iter::once(var("x"));
        let items = items.chain(groups.iter().flatten().map(|v| lit(v.clone())));
        let term = lam(&["x"], prim(Prim::Tuple, items.collect()));
        let g = crate::legal::legalize(lower(&term).expect("the term lowers"));
        let (t, _) = Tables::new(&g, &plan(g.graph(), false)).expect("the tables");
        assert_eq!(t.consts.len(), groups.len(), "{:?}", t.consts);
        let mut at = Vec::new();
        for g in &groups {
            let first = t.const_index(&g[0]);
            for v in g {
                assert_eq!(t.const_index(v), first, "{v}");
            }
            assert!(!at.contains(&first), "{} shares an entry", g[0]);
            at.push(first);
        }
    }
}
