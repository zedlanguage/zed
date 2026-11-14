//! The ints the tests around an expression allow it: the scope of the reduced product
//! ([`zedc_preimage::product`]) at each arm of an `if`, at the second side of `&&` and `||`
//! and in each case of a condition. A bit word's operand (L1.39a) and the exponent of `^`
//! (L1.17) are read through it, so `if n >= 0 { popCount(n) }` is accepted (DESIGN.md L1.39:
//! a test narrows a scope).
//!
//! Each condition the walk meets makes two nodes, the scopes where it holds and where it does
//! not, built from the node it is checked under; `!` swaps them, the second side of `a && b` is
//! checked under `a`'s holding node, so `a && b` holds at `b`'s, and fails at the join of the
//! two failing nodes, and `||` is the same with the outcomes swapped. A node's scope is
//! computed the first time a read under it needs it, from its parent's, which the memo keeps,
//! so a nest of `k` tests or a chain of `k` sides of `&&` costs `k` narrowings, each the size
//! of one test and of the projections its change makes due, and a program with no read under a
//! test computes none. A narrowing is not always the size of its test: see the tradeoff at
//! [`Ck::compute`](super::Ck::compute).
//!
//! A name bound in an arm, `k = n - 1`, is read as its value in the scope of the node it was
//! bound under, once for the binder.
//!
//! Complexity tradeoff: a test or operand is translated only through literals, names, integer
//! and boolean operators, `if`, and calls of definitions whose bodies are of that kind
//! ([`Ck::callable`](super::Ck::callable)), kept as applications that the preimage reads
//! through; any other subexpression (another call, a field, an `is` test) is an opaque int of
//! its own span, and a call read as an operand is any value of its type, so
//! `if f(n) >= 0 { popCount(f(n)) }` is rejected, the two calls being different atoms, and
//! an `is` test narrows only through `Facts`. Why: the translation is one pass per root,
//! memoized by span, with no structural equality of subterms, which is what would make two
//! equal calls one atom. Trigger: a test on a call or field that the operand repeats. Test:
//! `l01_39a_bit_words::narrowing::a_test_on_a_call_the_operand_repeats_is_rejected_and_its_named_value_accepted`.
//! COMPLEXITY.md row C26. A complete solution names the repeated value
//! (`m = f(n); if m >= 0 { popCount(m) }` works today), or hash-conses the translated terms
//! so equal calls are one atom.
//! Naive version: subterms compared by structure to find equal calls, O(size of the subterm)
//! per pair; used: one pass per root, memoized by span, O(1) per node; hash-consing would make
//! equal calls one atom at O(1) expected per node (inferred).

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::rc::Rc;
use std::sync::Arc;

use imbl::ordmap::DiffItem;
use zed_kernel::types::Type as KType;
use zed_kernel::{Prim, Shared, Term};

use zedc_lattice::cell::Premises;
use zedc_lattice::interval::IntervalSet;
use zedc_preimage::preimage::LetPa;
use zedc_preimage::product::{Product, Scope};
use zedc_syntax::ast::{BinaryOp, Expr};
use zedc_syntax::lex::Span;

/// One node: a scope the walk is in, or was.
pub(super) enum Node<'a> {
    /// No test decides here.
    Root,
    /// The scope of `parent` where `test` gave `outcome`.
    Assume {
        parent: usize,
        test: &'a Expr,
        outcome: bool,
        /// The products of the names of the test, from their types where it is checked.
        fresh: Rc<Vec<(Arc<str>, Product)>>,
    },
    /// Either of two scopes: the join of their cases.
    Join(usize, usize),
}

/// An expression as a kernel term the reduced product reads, and the names in it bound by a
/// `name = value` binder, whose values the scope is told of before it is read.
pub(super) struct Translated {
    pub(super) term: Term,
    pub(super) binders: Vec<usize>,
    /// The names of binders in it, in the scope, with the binders.
    pub(super) vars: Vec<(Arc<str>, usize)>,
    /// The definitions it calls whose calls it keeps as calls ([`Called`]), by binder.
    pub(super) calls: Vec<usize>,
    /// Whether some part of it is a name of its own, by its span: a part the term does not
    /// follow.
    pub(super) opaque: bool,
}

/// What a term is read for (`Ck::term_for` in walk.rs): an expression has one term for each.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) enum Reading {
    /// The condition of an `if`, narrowed where it holds and where it fails, read at each
    /// scope it narrows. An `if` in it is a name of its own, and a call is kept as a call only
    /// where the test narrows through it, on its spine; a call elsewhere is a name of its own.
    Test,
    /// An operand read where the walk is, for its values. An `if` and a call in it are names
    /// of their own: `forward` does not enter a call, so its values are any value either way,
    /// and a check whether the operand may be 0 (`Scope::zero_reached`) does not read the body.
    Operand,
    /// The body of a definition whose calls are kept ([`Called`]) or the value of a binder:
    /// read once, where it is defined or bound, and through the name at each use. An `if`
    /// and every call it can keep are translated.
    Defined,
}

/// A definition of the unit, `f(positional x) = e` or `f = x -> e`, whose calls a term keeps
/// as calls, `App(Var(f), args)`, with `f` bound in the scope that reads the term to its
/// lambda, so that a test on a call is narrowed through it (DESIGN.md step L1.39, "an arm
/// whose test calls a definition of the unit is narrowed through the call (step L1.25)";
/// [`Scope::close`](zedc_preimage::product::Scope)). Its body reads its parameters and the
/// definitions of this kind it calls, and nothing else, so each call is its body at its own
/// arguments.
pub(super) struct Called {
    /// Its name in the scope.
    pub(super) name: Arc<str>,
    /// The number of its parameters.
    pub(super) arity: usize,
    /// Its value, `Lam(params, body)`.
    pub(super) lambda: Shared,
    /// The definitions of this kind its body calls, by binder.
    pub(super) calls: Vec<usize>,
}

/// The piecewise-affine summary of a binder's value over the inputs it reads
/// ([`zedc_preimage::preimage::let_summary`]), made once for the binder and bound with the name
/// in each scope told of it ([`Scope::bind_summarized`]), so that a test of the name narrows the
/// input: `m >= 3` after `m = n + 3` narrows `n` to `int[0..]`.
pub(super) struct Summarized {
    pub(super) summary: LetPa,
    /// The inputs the summary reads and their products where the summary was made: what a
    /// scope with no product of an input is told of it. A persistent map, so that a binder
    /// takes the largest map of the binders it reads and adds the others' to it.
    pub(super) inputs: imbl::OrdMap<Arc<str>, Product>,
    /// The binder read by the value whose summary has the most inputs, if any: the one whose
    /// map `inputs` was made from, and whose read ([`images::Read`](zedc_preimage::images::Read)) a
    /// read of this one starts from.
    pub(super) widest: Option<usize>,
}

/// For one node, each name to the nearest node at or above it where a search of the tests
/// that read that name continues: a test that reads the name. An `Assume` maps its names to
/// itself; a `Join` the names its two sides map differently, found by the maps' difference as
/// [`Scope::join`] finds its names.
#[derive(Clone)]
struct Chains {
    read: imbl::OrdMap<Arc<str>, usize>,
}

/// A name's product in a node's scope, as a lookup compares them ([`Arms::lookup`]).
#[derive(PartialEq)]
enum Held {
    /// The scope is unreachable.
    Bottom,
    /// The scope has no product of the name.
    Absent,
    /// The name's product, settled ([`Scope::settled`]).
    Is(Box<Product>),
}

/// Each node and name looked up, with what [`Arms::lookup`] found.
type Found = HashMap<(usize, Arc<str>), Option<usize>>;

/// What a scope or a binder's product waits on.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Item {
    Scope(usize),
    Bound(usize),
}

/// The nodes of the walk, the scopes computed of them and the nodes the walk is in.
pub(super) struct Arms<'a> {
    pub(super) nodes: Vec<Node<'a>>,
    /// Each node's scope, once a read has needed it.
    pub(super) scopes: Vec<Option<Scope>>,
    /// For each `Assume` whose scope is computed, the scope its test narrowed: its parent's,
    /// told of the names of the test and the values of the binders it reads.
    pub(super) before: Vec<Option<Scope>>,
    /// For each node, the number of `Assume` nodes from it up to the first `Join` or the
    /// root, and a node on that way to jump to ([`Arms::add`]).
    depth: Vec<usize>,
    jump: Vec<usize>,
    /// Each name looked up under a node, with the nearest test at or above it that changed
    /// the name's product, or the join whose two sides differ there ([`Arms::lookup`]).
    found: RefCell<Found>,
    /// For each node, once a rejection under it has needed it, the chain a search of the
    /// tests that read a name follows ([`Chains`]).
    chains: Vec<Option<Chains>>,
    /// For each test a rejection found had changed a name it does not read, the search of
    /// the relation that carried the change ([`Carried`]).
    carried: HashMap<usize, Carried>,
    /// The nodes the walk is in, innermost last.
    active: Vec<usize>,
    /// The node each binder was bound under, when it is not the root.
    pub(super) bound_at: HashMap<usize, usize>,
    /// The type of each binder bound to a value of scalars and atoms.
    pub(super) bound_ty: HashMap<usize, KType>,
    /// Each binder's value in the scope of its node, once a read has needed it.
    pub(super) bound: HashMap<usize, Product>,
    /// The terms of the expressions read so far, by span and what each is read for.
    pub(super) terms: HashMap<(Span, Reading), Rc<Translated>>,
    /// The scope name of each binder a term has read.
    pub(super) names: HashMap<usize, Arc<str>>,
    /// The summary of each binder's value, once a scope has been told of the binder
    /// ([`Summarized`]); none when its value has no summary over one input.
    pub(super) summaries: HashMap<usize, Option<Rc<Summarized>>>,
    /// What [`Ck::ints_here`](super::Ck::ints_here) gave of each expression read in the scope
    /// of each node, by the expression's span and the node.
    pub(super) here_ints: HashMap<(Span, usize), IntervalSet>,
    /// What [`Ck::ints_here`](super::Ck::ints_here) read of each expression from its parts, by
    /// span and node.
    pub(super) part_ints: HashMap<(Span, usize), IntervalSet>,
    /// For each binder a term has called, the definition its calls are kept as ([`Called`]),
    /// or none when they are not; none also while its body is being translated, so a call
    /// of it within its own body stays a name of its own.
    pub(super) called: HashMap<usize, Option<Rc<Called>>>,
    /// Each node's scope with parameters of no declared type read as of type int, by the
    /// parameters' binders, in order, and the node, once a need on their ints has read it
    /// ([`Ck::ints_as_int`](super::Ck::ints_as_int)).
    pub(super) int_scopes: HashMap<Vec<usize>, HashMap<usize, Scope>>,
}

impl<'a> Arms<'a> {
    pub(super) fn new() -> Self {
        Arms {
            nodes: vec![Node::Root],
            scopes: vec![None],
            before: vec![None],
            depth: vec![0],
            jump: vec![0],
            found: RefCell::new(HashMap::new()),
            chains: vec![None],
            carried: HashMap::new(),
            active: Vec::new(),
            bound_at: HashMap::new(),
            bound_ty: HashMap::new(),
            bound: HashMap::new(),
            terms: HashMap::new(),
            names: HashMap::new(),
            summaries: HashMap::new(),
            here_ints: HashMap::new(),
            part_ints: HashMap::new(),
            called: HashMap::new(),
            int_scopes: HashMap::new(),
        }
    }

    /// The node the walk is in.
    pub(super) fn here(&self) -> usize {
        self.active.last().copied().unwrap_or(0)
    }

    /// Adds node `n`, with its depth and jump: a `Join` is depth 0 and jumps to itself; an
    /// `Assume` under `p` is one deeper than `p` and jumps to where `p`'s jump jumps, when the
    /// two jumps below it are of one length, else to `p`. So a jump goes up `2^j - 1` nodes
    /// for some `j`, and a search up a chain of `d` tests takes O(log d) jumps and steps
    /// (Myers 1983, the skew-binary jump pointers).
    fn add(&mut self, n: Node<'a>) -> usize {
        let k = self.nodes.len();
        let (depth, jump) = match &n {
            Node::Assume { parent, .. } => {
                let (p, j) = (*parent, self.jump[*parent]);
                let jump =
                    if self.depth[p] - self.depth[j] == self.depth[j] - self.depth[self.jump[j]] {
                        self.jump[j]
                    } else {
                        p
                    };
                (self.depth[p] + 1, jump)
            }
            _ => (0, k),
        };
        self.nodes.push(n);
        self.scopes.push(None);
        self.before.push(None);
        self.depth.push(depth);
        self.jump.push(jump);
        self.chains.push(None);
        k
    }

    /// The two nodes of the condition `test` checked here: where it holds and where it fails.
    pub(super) fn test(
        &mut self,
        test: &'a Expr,
        fresh: Vec<(Arc<str>, Product)>,
    ) -> (usize, usize) {
        let parent = self.here();
        let fresh = Rc::new(fresh);
        let yes = self.add(Node::Assume {
            parent,
            test,
            outcome: true,
            fresh: fresh.clone(),
        });
        let no = self.add(Node::Assume {
            parent,
            test,
            outcome: false,
            fresh,
        });
        (yes, no)
    }

    /// The node where the walk is in `a` or in `b`.
    pub(super) fn join(&mut self, a: usize, b: usize) -> usize {
        if a == b {
            return a;
        }
        self.add(Node::Join(a, b))
    }

    /// The walk enters node `n`.
    pub(super) fn enter(&mut self, n: usize) {
        self.active.push(n);
    }

    /// The walk leaves the node it entered last.
    pub(super) fn leave(&mut self) {
        self.active.pop();
    }

    /// The binder `id` is bound here, to a value of the scalars and atoms `plain` when its type
    /// holds nothing else.
    pub(super) fn bind(&mut self, id: usize, plain: Option<KType>) {
        let here = self.here();
        if here != 0 {
            self.bound_at.insert(id, here);
        }
        if let Some(t) = plain {
            self.bound_ty.insert(id, t);
        }
    }

    /// The tests that bear on a read of `starts`, each a name with the node it is read under,
    /// innermost first, with the outcome each gave and whether it gave it in one case of a join
    /// only. A test is listed when it changed the product of a name looked up
    /// ([`Arms::lookup`]); then, unless the test alone gives the name that product
    /// ([`Arms::explains`]), the lookup goes on above it, from its parent, for each name of the
    /// test. A test that reads a name and leaves its product as it was is passed over: under
    /// `n >= 0`, the tests `ai >= n - 3` change no product of `n`, so a rejection on `ai` lists
    /// its own test and `n >= 0`. A test that changed a name it does not read, which the
    /// scope's relation carried it to, also brings in the tests of one shortest path of the
    /// relation from that name to a name the test reads ([`Carried`]), one that gives the name
    /// its product where the first found does not ([`Carried::others`]), and for each name of
    /// those tests the lookup from the carrying test ([`Arms::push_names`]): `a == b`, `b == c`,
    /// then `c >= -2` for a read of `a`; under `a0 >= n + m`, then `n >= -1`, then `m >= -1`, a
    /// read of `a0` lists all three, and under `m >= n` above the sum, a read after `n >= -1`
    /// lists the sum, `m >= n` and `n >= -1`. Under `ai >= n` for each `i`, then `n >= -1`, a
    /// read of `a0` lists `a0 >= n` and `n >= -1`, not the other tests on `n`; the lookup stops
    /// there when the test and its path alone give the name its product ([`Arms::explains`]),
    /// so weaker tests `n >= -2`, … around them are not listed. Nor is the name looked up above
    /// a carrying test whose path gives it its product from the other names' products there:
    /// under the sum and `n >= -1`, the tests `m >= -3`, `m >= -2`, `m >= -1` each move `a0`;
    /// `m >= -3` is not listed. Nor is `m >= -2`: the carrying test's own names are looked up
    /// from the test itself, which carried the product it gave them, and `m >= -1` alone gives
    /// `m` that product; so too `n - m <= 2` above them, which carried `n >= -1` to `m` but not
    /// the product `m` has where `m >= -1` is. Each step is a lookup of O(log d) scopes
    /// for a chain of `d` tests, kept for later rejections, each item is visited once, and the
    /// search of each carrying test is kept and resumed, so the cost is that of the tests
    /// listed and their names, and of each relation searched once, not of the tests the walk
    /// is in.
    pub(super) fn deciding(&mut self, starts: Vec<(Arc<str>, usize)>) -> Vec<(Span, bool, bool)> {
        for (_, s) in &starts {
            self.settle_chains(*s);
        }
        // Each node listed, with whether every way it was reached passed through a join.
        let mut listed: HashMap<usize, bool> = HashMap::new();
        // A node to look at, the name looked up and whether a join was passed.
        type At = (usize, Arc<str>, bool);
        let mut visited: HashSet<At> = HashSet::new();
        let mut stack: Vec<At> = Vec::new();
        for (x, s) in starts {
            if let Some(k) = self.lookup(s, &x) {
                stack.push((k, x, false));
            }
        }
        while let Some(at) = stack.pop() {
            if !visited.insert(at.clone()) {
                continue;
            }
            let (k, x, case) = at;
            match &self.nodes[k] {
                Node::Root => {}
                Node::Assume { parent, fresh, .. } => {
                    let all = listed.entry(k).or_insert(case);
                    *all &= case;
                    if self.explains(k, &[], &x, false) {
                        continue;
                    }
                    if fresh.iter().any(|(y, _)| *y == x) {
                        self.push_names(k, *parent, case, &mut stack);
                        continue;
                    }
                    let search = self
                        .carried
                        .entry(k)
                        .or_insert_with(|| Carried::new(*parent, fresh));
                    let first = search.path(&self.nodes, &self.chains, &x);
                    // The first shortest path that gives `x` its product with the test, else
                    // the first found; the others are searched only when that one does not.
                    let mut explained = match self.explains(k, &first, &x, false) {
                        true => Some(first.clone()),
                        false => self
                            .carried
                            .get_mut(&k)
                            .expect("searched above")
                            .others(&self.nodes, &self.chains, &x)
                            .into_iter()
                            .find(|path| self.explains(k, path, &x, false)),
                    };
                    // Else the first path, if it gives `x` its product from the other names'
                    // products here; else the longer paths that give it with the test.
                    let given = explained.is_none() && self.explains(k, &first, &x, true);
                    if explained.is_none() && !given {
                        self.carried
                            .get_mut(&k)
                            .expect("searched above")
                            .drain(&self.nodes, &self.chains);
                        explained = self.longer(k, &x);
                    }
                    let path = explained.clone().unwrap_or(first);
                    for &(q, joined) in &path {
                        let case = case || joined;
                        let all = listed.entry(q).or_insert(case);
                        *all &= case;
                    }
                    // The test and its path alone give `x` its product: no test above bears.
                    if explained.is_some() {
                        continue;
                    }
                    // The relation carried the products the test gave its names: each is
                    // looked up from the test itself, which answers with the test where it
                    // changed the name, and that test alone often gives the name its product:
                    // under `m >= -2`, `m >= -1` carries to `a0` by `a0 >= n + m` with `m`
                    // int[-1..], which `m >= -1` alone gives, so `m >= -2` is not listed.
                    self.push_names(k, k, case, &mut stack);
                    // The path gives `x` its product from the other names' products here:
                    // `x`'s product above is not used.
                    if !given && let Some(q) = self.lookup(*parent, &x) {
                        stack.push((q, x.clone(), case));
                    }
                    for &(q, joined) in &path {
                        self.push_names(q, k, case || joined, &mut stack);
                    }
                }
                Node::Join(a, b) => {
                    for side in [*b, *a] {
                        if let Some(q) = self.lookup(side, &x) {
                            stack.push((q, x.clone(), true));
                        }
                    }
                }
            }
        }
        let mut out: Vec<(usize, bool)> = listed.into_iter().collect();
        out.sort_unstable_by_key(|a| std::cmp::Reverse(a.0));
        out.into_iter()
            .map(|(k, case)| match &self.nodes[k] {
                Node::Assume { test, outcome, .. } => (test.span, *outcome, case),
                _ => unreachable!("only a test is listed"),
            })
            .collect()
    }

    /// Whether the test of node `k`, with the tests `path` of a path of the relation that
    /// carried it to `x` ([`Carried::path`]), alone, on their names as their types give them,
    /// gives `x` the product it has at `k`: then no test above `k` bears on `x` there, as under
    /// `n >= 0`, `n >= 1` the second gives `n` int[1..] alone, and under `ai >= n`, then
    /// `n >= -2`, `n >= -1`, the last with `ai >= n` gives `ai` int[-1..]. The tests are narrowed
    /// once more, together, on a scope of their names, which costs the size of the tests. With
    /// `given`, the names other than `x` have the products they have at `k` instead: then the
    /// tests give `x` its product from those of the other names, which their own lookups
    /// explain, and `x`'s product above `k` is not used.
    fn explains(&self, k: usize, path: &[(usize, bool)], x: &Arc<str>, given: bool) -> bool {
        let Some(at) = &self.scopes[k] else {
            return false;
        };
        let mut names: BTreeMap<Arc<str>, Product> = BTreeMap::new();
        let mut sides: Vec<(Term, bool)> = Vec::with_capacity(path.len() + 1);
        for q in path.iter().map(|&(q, _)| q).chain([k]) {
            let Node::Assume {
                test,
                outcome,
                fresh,
                ..
            } = &self.nodes[q]
            else {
                return false;
            };
            let Some(t) = self.terms.get(&(test.span, Reading::Test)) else {
                return false;
            };
            for (y, p) in fresh.iter() {
                names
                    .entry(y.clone())
                    .or_insert_with(|| match given && y != x {
                        true => at.settled(y),
                        false => p.clone(),
                    });
            }
            sides.push((t.term.clone(), *outcome));
        }
        let (test, outcome) = match sides.len() {
            1 => sides.pop().expect("one side"),
            _ => {
                let side = |(t, o): (Term, bool)| match o {
                    true => t,
                    false => Term::Prim(Prim::Not, vec![t]),
                };
                let all = sides
                    .into_iter()
                    .map(side)
                    .reduce(|a, b| Term::Prim(Prim::And, vec![a, b]));
                (all.expect("two sides or more"), true)
            }
        };
        let alone = Scope::new(names);
        let alone = alone.assume_case(&test, outcome, &Premises::new());
        alone.get(x) == at.settled(x)
    }

    /// The tests of the longer paths that give `x`, with the test of node `k`, its product
    /// there, when no shortest path does. Each test reading `x` and each other name of it as far
    /// from the carrying test as `x` or farther is a step, followed back by
    /// [`Carried::around`], which does not pass `x`; the steps are taken shortest first. Under
    /// `x <= n + 100`, `y >= n`, `x >= y`, then `n >= -1`, the first test reaches `x` from `n`
    /// and gives it no bound; `y >= n` then `x >= y` give it int[-1..]. The tests of the first
    /// steps together are narrowed at O(log s) prefixes of the `s` steps, halving, to the first
    /// step whose prefix gives `x` its product; that step's path, if it gives it alone, else
    /// the prefix. Each prefix is the union of its paths, each name followed back once, so the
    /// cost is O(log s) times that of the relation. One narrowing of all the steps would tell
    /// only that together they bound `x`, and would name every test reading `x`, as each
    /// `x <= y + i` beside `x >= y`; one narrowing for each step costs `s` times the length of a
    /// path, `k²` for `k` steps on paths of length `k`.
    fn longer(&self, k: usize, x: &Arc<str>) -> Option<Vec<(usize, bool)>> {
        let search = &self.carried[&k];
        let Node::Assume { fresh, .. } = &self.nodes[k] else {
            return None;
        };
        let &far = search.depth.get(x)?;
        let around = search.around(fresh, x);
        let mut steps: Vec<(usize, usize, &Arc<str>, bool)> = search
            .readers
            .get(x)
            .into_iter()
            .flatten()
            .flat_map(|q| {
                search.from[q]
                    .iter()
                    .map(move |(y, joined)| (*q, y, *joined))
            })
            .filter_map(|(q, y, joined)| match around.get(y) {
                Some(&(_, d)) if y != x && d >= far => Some((d, q, y, joined)),
                _ => None,
            })
            .collect();
        steps.sort_by_key(|s| s.0);
        // The tests of the paths of `steps`, each test once, each name followed back once.
        let paths = |steps: &[(usize, usize, &Arc<str>, bool)]| {
            let mut tests: HashSet<usize> = HashSet::new();
            let mut names: HashSet<&Arc<str>> = HashSet::new();
            let mut out = Vec::new();
            for &(_, q, y, joined) in steps {
                if tests.insert(q) {
                    out.push((q, joined));
                }
                let mut at = y;
                while names.insert(at) {
                    let Some(&(Some((q, from, joined)), _)) = around.get(at) else {
                        break;
                    };
                    if tests.insert(q) {
                        out.push((q, joined));
                    }
                    at = from;
                }
            }
            out
        };
        let mut found = paths(&steps);
        if steps.is_empty() || !self.explains(k, &found, x, false) {
            return None;
        }
        // The prefix of `hi` steps gives `x` its product, that of `lo` does not: none does
        // alone, as the lookup that searched for paths found.
        let (mut lo, mut hi) = (0, steps.len());
        while hi - lo > 1 {
            let mid = lo + (hi - lo) / 2;
            let prefix = paths(&steps[..mid]);
            match self.explains(k, &prefix, x, false) {
                true => (hi, found) = (mid, prefix),
                false => lo = mid,
            }
        }
        let one = paths(&steps[hi - 1..hi]);
        Some(match self.explains(k, &one, x, false) {
            true => one,
            false => found,
        })
    }

    /// Computes [`Arms::chains`] of `n` and of every node it is computed from, each once, on an
    /// explicit stack; the memo is the visited set.
    fn settle_chains(&mut self, n: usize) {
        let mut stack = vec![(n, false)];
        while let Some((k, ready)) = stack.pop() {
            if self.chains[k].is_some() {
                continue;
            }
            if !ready {
                stack.push((k, true));
                let from = match &self.nodes[k] {
                    Node::Root => [None, None],
                    Node::Assume { parent, .. } => [Some(*parent), None],
                    Node::Join(a, b) => [Some(*a), Some(*b)],
                };
                for d in from.into_iter().flatten() {
                    if self.chains[d].is_none() {
                        stack.push((d, false));
                    }
                }
                continue;
            }
            let settled = |d: usize| self.chains[d].as_ref().expect("settled first");
            let chains = match &self.nodes[k] {
                Node::Root => Chains {
                    read: imbl::OrdMap::new(),
                },
                Node::Assume { parent, fresh, .. } => {
                    let mut c = settled(*parent).clone();
                    for (x, _) in fresh.iter() {
                        c.read.insert(x.clone(), k);
                    }
                    c
                }
                Node::Join(a, b) => Chains {
                    read: joined(&settled(*a).read, &settled(*b).read, k),
                },
            };
            self.chains[k] = Some(chains);
        }
    }

    /// Pushes, for each name of the test of node `q`, the nearest test at or above `from` that
    /// changed its product ([`Arms::lookup`]). `from` is where `q`'s names were read: `q`'s own
    /// parent, or, for a carrying test and each test on its path, the carrying test itself,
    /// since the relation carried the change with the products the names have there. Under
    /// `a0 >= n + m`, then `n >= -1`, then `m >= -1`, the last carries to `a0` by the sum, with
    /// the product of `n` from the test below the sum; under `m >= n`, `a0 >= n + m`, then
    /// `n >= -1`, the test on `n` carries to `a0` by the sum, with the product it gave `m` by
    /// `m >= n`, so the lookup of `m` answers with the test on `n` and lists its path to `m`.
    fn push_names(
        &self,
        q: usize,
        from: usize,
        case: bool,
        stack: &mut Vec<(usize, Arc<str>, bool)>,
    ) {
        if let Node::Assume { fresh, .. } = &self.nodes[q] {
            for (y, _) in fresh.iter() {
                if let Some(r) = self.lookup(from, y) {
                    stack.push((r, y.clone(), case));
                }
            }
        }
    }

    /// The node a lookup of `x` under `s` answers with: the nearest test at or above `s` that
    /// changed `x`'s product ([`Arms::changes`]), where a join whose two sides answer
    /// differently answers itself; none at the root. Each answer is kept, so a node and a name
    /// are looked up once over all rejections, and the joins above are looked up on an
    /// explicit stack.
    ///
    /// Up a chain of tests, the products of a name only narrow, and a test changes a name only
    /// where its product differs from its parent's, so the search goes by the jumps of
    /// [`Arms::add`] to the highest node of the chain where `x`'s product is as at `s`
    /// ([`Arms::step`]): O(log d) settled products for a chain of `d` tests. So `k` tests on a
    /// hub of `k` spokes, each moving every leaf, cost no list of the leaves each changed,
    /// where a list per test costs `k²`.
    fn lookup(&self, s: usize, x: &Arc<str>) -> Option<usize> {
        let key = |n: usize| (n, x.clone());
        let known = |n: usize| self.found.borrow().get(&key(n)).copied();
        if let Some(r) = known(s) {
            return r;
        }
        let mut steps: HashMap<usize, Step> = HashMap::new();
        let mut stack = vec![s];
        while let Some(&n) = stack.last() {
            if known(n).is_some() {
                stack.pop();
                continue;
            }
            let step = *steps.entry(n).or_insert_with(|| self.step(n, x));
            let answer = match step {
                Step::Done(r) => Some(r),
                Step::Via(m) => {
                    let r = known(m);
                    if r.is_none() {
                        stack.push(m);
                    }
                    r
                }
                Step::Join(a, b) => match (known(a), known(b)) {
                    (Some(la), Some(lb)) => Some(if la == lb { la } else { Some(n) }),
                    (ka, kb) => {
                        if ka.is_none() {
                            stack.push(a);
                        }
                        if kb.is_none() {
                            stack.push(b);
                        }
                        None
                    }
                },
            };
            if let Some(r) = answer {
                self.found.borrow_mut().insert(key(n), r);
                stack.pop();
            }
        }
        known(s).expect("looked up")
    }

    /// One step of a lookup of `x` under node `n` ([`Arms::lookup`]). At a test, the highest
    /// node `u` of its chain where `x`'s product is as at `n`, found by jumps: the products
    /// only narrow up the chain, so they are as at `n` from `n` up to `u` and not above, and
    /// no test strictly below `u` changed `x`. Then `u` answers if its test changed `x`, and
    /// the lookup goes on from its parent if not. A scope no read computed is taken to change
    /// every name of its test.
    fn step(&self, n: usize, x: &Arc<str>) -> Step {
        let up = |k: usize| match &self.nodes[k] {
            Node::Assume { parent, .. } => *parent,
            _ => unreachable!("a node of depth 1 or more is a test"),
        };
        match &self.nodes[n] {
            Node::Root => Step::Done(None),
            Node::Join(a, b) => Step::Join(*a, *b),
            Node::Assume { parent, fresh, .. } => {
                let Some(here) = self.held(n, x) else {
                    return match fresh.iter().any(|(y, _)| y == x) {
                        true => Step::Done(Some(n)),
                        false => Step::Via(*parent),
                    };
                };
                let same = |k: usize| self.held(k, x).as_ref() == Some(&here);
                let mut u = n;
                while self.depth[u] > 0 {
                    let (j, p) = (self.jump[u], up(u));
                    if j != p && same(j) {
                        u = j;
                    } else if same(p) {
                        u = p;
                    } else {
                        break;
                    }
                }
                match &self.nodes[u] {
                    Node::Assume { parent, .. } => match self.changes(u, x) {
                        true => Step::Done(Some(u)),
                        false => Step::Via(*parent),
                    },
                    Node::Root => Step::Done(None),
                    Node::Join(..) => Step::Via(u),
                }
            }
        }
    }

    /// `x`'s product in the scope of node `k`, if a read computed it.
    fn held(&self, k: usize, x: &Arc<str>) -> Option<Held> {
        self.scopes[k].as_ref().map(|s| held_in(s, x))
    }

    /// Whether the test of node `k`, whose scope is computed, changed `x`'s product: `x`'s
    /// product differs in the scope the test narrowed and in its own; a test that made a
    /// reachable scope unreachable changed each name it reads, and one under an unreachable
    /// scope none.
    fn changes(&self, k: usize, x: &Arc<str>) -> bool {
        let Node::Assume { fresh, .. } = &self.nodes[k] else {
            return false;
        };
        match (&self.before[k], &self.scopes[k]) {
            (Some(p), Some(s)) if !p.bottom && !s.bottom => held_in(p, x) != held_in(s, x),
            (Some(p), Some(_)) if p.bottom => false,
            _ => fresh.iter().any(|(y, _)| y == x),
        }
    }
}

/// A step of [`Arms::lookup`].
#[derive(Clone, Copy)]
enum Step {
    /// The answer.
    Done(Option<usize>),
    /// The answer is that of this node.
    Via(usize),
    /// The answer is that of the two sides if they agree, else the join itself.
    Join(usize, usize),
}

/// `x`'s product in scope `s`, settled.
fn held_in(s: &Scope, x: &Arc<str>) -> Held {
    if s.bottom {
        Held::Bottom
    } else if s.names.contains_key(x) {
        Held::Is(Box::new(s.settled(x)))
    } else {
        Held::Absent
    }
}

/// A step of [`Carried`]'s search: the test that reached a name, the name it was reached
/// from and whether a join was passed.
type Reached = (usize, Arc<str>, bool);

/// [`Carried::around`]: each name reached, with the test that reached it, the name that test
/// was reached from and whether a join was passed (none for a start), and its distance.
type Around<'s> = HashMap<&'s Arc<str>, (Option<(usize, &'s Arc<str>, bool)>, usize)>;

/// For a test that changed names it does not read, which the scope's relation carried its
/// change to, a breadth-first search of the relation above it: from the names the test reads,
/// over the tests above it, each test joining the names it reads. Each name the search reached
/// keeps the test it was reached by and the name that test was reached from, so a lookup of a
/// name follows these back to the test and lists one shortest path. The search goes only as
/// far as a lookup needs, and later lookups resume it, so over all lookups each test above is
/// expanded once for each name it reads. A name reached again by another test from a name
/// as far from the carrying test keeps that test too, as a last step of another shortest
/// path ([`Carried::others`]).
struct Carried {
    /// Where the tests above are looked up from: the carrying test's parent.
    above: usize,
    /// Each name reached: `None` for a name the carrying test reads, else the test that
    /// reached it, the name that test was reached from and whether a join was passed.
    via: HashMap<Arc<str>, Option<Reached>>,
    /// Each name reached, with its distance in tests from the names the carrying test reads.
    depth: HashMap<Arc<str>, usize>,
    /// Each name reached by more than one test at its distance: the tests after the first, in
    /// the order reached, as in `via`.
    also: HashMap<Arc<str>, Vec<Reached>>,
    /// The names reached and not yet expanded, in the order reached.
    queue: VecDeque<(Arc<str>, bool)>,
    /// The tests whose names have been reached.
    expanded: HashSet<usize>,
    /// Each name expanded, with the tests above that read it, in the order reached.
    readers: HashMap<Arc<str>, Vec<usize>>,
    /// Each test reached, with each name it was reached from and whether a join was passed.
    from: HashMap<usize, Vec<(Arc<str>, bool)>>,
}

impl Carried {
    fn new(above: usize, fresh: &[(Arc<str>, Product)]) -> Self {
        Carried {
            above,
            via: fresh.iter().map(|(y, _)| (y.clone(), None)).collect(),
            depth: fresh.iter().map(|(y, _)| (y.clone(), 0)).collect(),
            also: HashMap::new(),
            queue: fresh.iter().map(|(y, _)| (y.clone(), false)).collect(),
            expanded: HashSet::new(),
            readers: HashMap::new(),
            from: HashMap::new(),
        }
    }

    /// The tests of one shortest path of the relation from `x` to a name the carrying test
    /// reads, nearest `x` first, each with whether a join was passed to reach it; none when
    /// the relation does not reach `x`.
    fn path(
        &mut self,
        nodes: &[Node<'_>],
        chains: &[Option<Chains>],
        x: &Arc<str>,
    ) -> Vec<(usize, bool)> {
        while !self.via.contains_key(x) {
            let Some((y, joined)) = self.queue.pop_front() else {
                return Vec::new();
            };
            self.expand(nodes, chains, &y, joined);
        }
        self.back(x)
    }

    /// The other shortest paths from `x` that [`Carried::path`] did not take, one for each
    /// other test that reached `x` ([`Carried::also`]), each followed back as `path` is. Under
    /// `m >= n`, `a0 >= n + m`, then `n >= -1`, the sum and the link each reach `m` from `n`;
    /// the sum is found first, and only the link gives `m` its product. Called after
    /// `path(x)`; the names as near as those `x` was reached from are expanded first, so every
    /// test reaching `x` at its distance is kept.
    fn others(
        &mut self,
        nodes: &[Node<'_>],
        chains: &[Option<Chains>],
        x: &Arc<str>,
    ) -> Vec<Vec<(usize, bool)>> {
        let Some(&far) = self.depth.get(x) else {
            return Vec::new();
        };
        while let Some((y, joined)) = self
            .queue
            .front()
            .filter(|(y, _)| self.depth[y] < far)
            .cloned()
        {
            self.queue.pop_front();
            self.expand(nodes, chains, &y, joined);
        }
        let Some(steps) = self.also.get(x) else {
            return Vec::new();
        };
        steps
            .iter()
            .map(|(q, from, joined)| {
                let mut out = vec![(*q, *joined)];
                out.extend(self.back(from));
                out
            })
            .collect()
    }

    /// Expands every name reached and not yet expanded: after it, [`Carried::readers`] and
    /// [`Carried::from`] hold the whole relation above, each test with all its names.
    fn drain(&mut self, nodes: &[Node<'_>], chains: &[Option<Chains>]) {
        while let Some((y, joined)) = self.queue.pop_front() {
            self.expand(nodes, chains, &y, joined);
        }
    }

    /// A breadth-first search of the whole relation above, from the names `starts` the
    /// carrying test reads, that does not go on from `x`: each name reached, with the test that
    /// reached it, the name that test was reached from and whether a join was passed (none for
    /// a start), and its distance. A path back from a name never passes `x`, as the search's
    /// own paths may: under `x >= y3`, `x <= y3 + 1`, `y3` is reached from `x` by the second.
    /// Each test is visited once, from the first of its names reached, so the cost is that of
    /// the relation. Called after [`Carried::drain`].
    fn around<'s>(&'s self, starts: &'s [(Arc<str>, Product)], x: &Arc<str>) -> Around<'s> {
        let mut out: Around<'s> = HashMap::new();
        let mut queue: VecDeque<&Arc<str>> = VecDeque::new();
        for (y, _) in starts {
            out.insert(y, (None, 0));
            queue.push_back(y);
        }
        let mut tests: HashSet<usize> = HashSet::new();
        while let Some(y) = queue.pop_front() {
            if y == x {
                continue;
            }
            let far = out[y].1 + 1;
            for &q in self.readers.get(y).into_iter().flatten() {
                if !tests.insert(q) {
                    continue;
                }
                let names = &self.from[&q];
                let joined = names.iter().any(|(z, joined)| z == y && *joined);
                for (z, _) in names {
                    if !out.contains_key(z) {
                        out.insert(z, (Some((q, y, joined)), far));
                        queue.push_back(z);
                    }
                }
            }
        }
        out
    }

    /// The tests from `x` back to a name the carrying test reads, by the first test that
    /// reached each name.
    fn back(&self, x: &Arc<str>) -> Vec<(usize, bool)> {
        let mut out = Vec::new();
        let mut at = x;
        while let Some(Some((q, from, joined))) = self.via.get(at) {
            out.push((*q, *joined));
            at = from;
        }
        out
    }

    /// Reaches the names of each test above that reads `y`, following `y`'s chain of readers
    /// through both sides of each join, each node once.
    fn expand(
        &mut self,
        nodes: &[Node<'_>],
        chains: &[Option<Chains>],
        y: &Arc<str>,
        joined: bool,
    ) {
        let read = |n: usize| {
            chains[n]
                .as_ref()
                .expect("an ancestor of a settled node is settled")
                .read
                .get(y)
                .copied()
        };
        let far = self.depth[y] + 1;
        let mut seen = HashSet::new();
        let mut stack: Vec<(usize, bool)> =
            read(self.above).map(|q| (q, joined)).into_iter().collect();
        while let Some((k, case)) = stack.pop() {
            if !seen.insert(k) {
                continue;
            }
            match &nodes[k] {
                Node::Root => {}
                Node::Assume { parent, fresh, .. } => {
                    self.readers.entry(y.clone()).or_default().push(k);
                    self.from.entry(k).or_default().push((y.clone(), case));
                    if self.expanded.insert(k) {
                        for (z, _) in fresh.iter() {
                            match self.depth.get(z) {
                                None => {
                                    self.via.insert(z.clone(), Some((k, y.clone(), case)));
                                    self.depth.insert(z.clone(), far);
                                    self.queue.push_back((z.clone(), case));
                                }
                                Some(&d) if d == far => {
                                    let step = (k, y.clone(), case);
                                    self.also.entry(z.clone()).or_default().push(step);
                                }
                                Some(_) => {}
                            }
                        }
                    }
                    stack.extend(read(*parent).map(|q| (q, case)));
                }
                Node::Join(a, b) => {
                    for side in [*b, *a] {
                        stack.extend(read(side).map(|q| (q, true)));
                    }
                }
            }
        }
    }
}

/// The chain of a join `k` of two nodes whose chains are `a` and `b`: `a`'s, with each name the
/// two map differently mapped to `k`.
fn joined(
    a: &imbl::OrdMap<Arc<str>, usize>,
    b: &imbl::OrdMap<Arc<str>, usize>,
    k: usize,
) -> imbl::OrdMap<Arc<str>, usize> {
    let mut m = a.clone();
    for d in a.diff(b) {
        let x = match d {
            DiffItem::Add(x, _) | DiffItem::Remove(x, _) => x,
            DiffItem::Update { old: (x, _), .. } => x,
        };
        m.insert(x.clone(), k);
    }
    m
}

/// The kernel primitive of the operator `o` of the text, for the operators a test is read by.
pub(super) fn prim_of(o: BinaryOp) -> Option<Prim> {
    Some(match o {
        BinaryOp::Add => Prim::Add,
        BinaryOp::Sub => Prim::Sub,
        BinaryOp::Mul => Prim::Mul,
        BinaryOp::IntDiv => Prim::IntDiv,
        BinaryOp::Mod => Prim::Mod,
        BinaryOp::Eq => Prim::Eq,
        BinaryOp::Ne => Prim::Ne,
        BinaryOp::Lt => Prim::Lt,
        BinaryOp::Le => Prim::Le,
        BinaryOp::Gt => Prim::Gt,
        BinaryOp::Ge => Prim::Ge,
        BinaryOp::And => Prim::And,
        BinaryOp::Or => Prim::Or,
        BinaryOp::Div | BinaryOp::Pow | BinaryOp::Concat => return None,
    })
}

/// The name of binder `id` in the scope: its text and its number, so two binders of one name
/// are two names, and a shadowing name says nothing of the one it shadows.
pub(super) fn var(name: &str, id: usize) -> Arc<str> {
    format!("{name}@{id}").into()
}
