//! The layout record (item LAYOUT-measure, `zed/compiler/MLIR.md` section Layout): the bytes
//! the compiler's four representations take on a real unit, per node, measured by the counting
//! allocator. The bytes of a structure are those its drop frees ([`zed_alloc_count::live`]), so
//! what a structure shares with another one that outlives it (an `Arc<str>` name the elaborator
//! copied out of the syntax tree, say) is not counted in it.

use std::cell::Cell;
use std::collections::HashSet;
use std::sync::Arc;

use zed_alloc_count::live;
use zed_kernel::term::{Pattern as KPattern, Shared};
use zed_kernel::{Evaluator, Term};
use zedc::ast::{Blocks, Expr, ExprKind, Stmt, expr_kids, stmts_exprs};
use zedc::zir::Region;
use zedc::zir::lower::lower;
use zedc::zir::memory::plan;

/// The nodes of one representation and the bytes they take.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct Stage {
    /// The nodes counted.
    pub nodes: usize,
    /// The bytes their structure frees when dropped.
    pub bytes: u64,
}

impl Stage {
    fn add(&mut self, s: Stage) {
        self.nodes += s.nodes;
        self.bytes += s.bytes;
    }

    /// Bytes per node, rounded down; none for no nodes.
    pub fn per_node(&self) -> Option<u64> {
        (self.nodes > 0).then(|| self.bytes / self.nodes as u64)
    }
}

/// What the native runs of a unit's closed terms allocate.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct Native {
    /// Closed terms run.
    pub runs: u64,
    /// Heap cells allocated, summed over the runs.
    pub cells: u64,
    /// The largest number of cells live at once in any one run.
    pub peak: u64,
}

/// The record of one unit, or of several summed.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct Record {
    /// Units measured.
    pub units: usize,
    /// The syntax tree: its expressions and statements, and the bytes of the whole tree (its
    /// types and patterns included).
    pub ast: Stage,
    /// The elaborated unit: its distinct kernel terms, and the bytes of the whole unit.
    pub term: Stage,
    /// The ZIR graphs of the closed terms the tables run: their nodes, and the graphs' bytes.
    pub zir: Stage,
    /// The native runs of the same terms.
    pub native: Native,
}

impl Record {
    /// Adds the record `r` to this one; the peak is the larger of the two.
    pub fn add(&mut self, r: &Record) {
        self.units += r.units;
        self.ast.add(r.ast);
        self.term.add(r.term);
        self.zir.add(r.zir);
        self.native.runs += r.native.runs;
        self.native.cells += r.native.cells;
        self.native.peak = self.native.peak.max(r.native.peak);
    }
}

/// The bytes `x` frees when dropped.
fn bytes_of<T>(x: T) -> u64 {
    let ((), l) = live(|| drop(x));
    // A drop frees; it allocates only scratch it frees again, so the net is never above zero.
    assert!(l.net <= 0, "a drop that leaves {} bytes allocated", l.net);
    l.net.unsigned_abs()
}

/// The record of the unit `text`, or the diagnostics of the front end when it refuses it (a
/// rejection unit). The tables run natively, each closed term lowered to ZIR, legalized, planned
/// and run.
pub fn record(text: &str) -> Result<Record, String> {
    // The front end the test runner uses; its cache goes with `db`, so the result is held once.
    let front = zedc::query::Db::new().front(text);
    let front = Arc::try_unwrap(front).unwrap_or_else(|_| unreachable!("the cache was dropped"));
    let (stmts, unit, _) = front.map_err(|ds| format!("{ds:?}"))?;
    let term = Stage {
        nodes: term_nodes(&unit),
        bytes: bytes_of(unit),
    };
    let ast = Stage {
        nodes: ast_nodes(&stmts),
        bytes: bytes_of(stmts),
    };
    let (zir, native) = (Cell::new(Stage::default()), Cell::new(Native::default()));
    let through = |t: &Term, ev: &mut Evaluator| {
        let g = lower(t)?;
        let mut z = zir.get();
        z.add(Stage {
            nodes: zir_nodes(&g),
            bytes: bytes_of(g),
        });
        zir.set(z);
        let g = zed_native::legalize(lower(t)?);
        let p = plan(g.graph(), true);
        let o = zed_native::run(&g, &p, ev)?;
        let mut n = native.get();
        n.runs += 1;
        n.cells += o.stats.allocations;
        n.peak = n.peak.max(o.stats.peak);
        native.set(n);
        Ok(o.value)
    };
    zedc::testing::test_through(text, &through);
    Ok(Record {
        units: 1,
        ast,
        term,
        zir: zir.get(),
        native: native.get(),
    })
}

/// The expressions and statements of `stmts`, counted with a work list, so a tree of any depth
/// is counted on the heap. The children are those `zedc::ast`'s drop walks; an expression in a
/// pattern or a type is part of that pattern or type and not counted. The children are listed
/// by `zedc::ast`'s own walkers, [`stmts_exprs`] and [`expr_kids`], which a test there holds to
/// the drop walk; this file kept a copy of both until row DRY-ast-walkers. A statement a `local`
/// or an annotation wraps is part of its wrapper and not counted again, as before.
pub fn ast_nodes(stmts: &[Stmt]) -> usize {
    let mut n = stmts.len();
    let mut exprs: Vec<&Expr> = Vec::new();
    stmts_exprs(stmts, &mut |e| exprs.push(e));
    while let Some(e) = exprs.pop() {
        n += 1;
        if let ExprKind::Block(ss) = &e.kind {
            n += ss.len();
        }
        expr_kids(&e.kind, Blocks::Enter, &mut |x| exprs.push(x));
    }
    n
}

/// The distinct kernel terms of `unit`: those of its definitions and its tests. A shared term
/// is counted once, by its id, so a graph of shared terms is counted in time linear in its
/// distinct nodes; a term held inline (an argument, a match arm) is its own node.
pub fn term_nodes(unit: &zedc::elab::Unit) -> usize {
    let mut seen: HashSet<u64> = HashSet::new();
    let mut work: Vec<&Term> = Vec::new();
    for d in &unit.defs {
        visit(&d.term, &mut seen, &mut work);
    }
    for t in unit.tests.iter() {
        work.push(&t.check);
        work.extend(&t.args);
        work.push(&t.want);
    }
    let mut n = 0;
    while let Some(t) = work.pop() {
        n += 1;
        let (shared, inline): (Vec<&Shared>, &[Term]) = match t {
            Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => (vec![], &[]),
            Term::Lam(_, b) | Term::Push(_, b) => (vec![b], &[]),
            Term::App(f, args) => (vec![f], args),
            Term::Prim(_, args) => (vec![], args),
            Term::Let(_, a, b)
            | Term::Discard { family: a, sel: b }
            | Term::Fam {
                domain: a, body: b, ..
            }
            | Term::Fix {
                init: a, step: b, ..
            } => (vec![a, b], &[]),
            Term::If(a, b, c)
            | Term::Reindex {
                family: a,
                kf: b,
                vf: c,
                ..
            }
            | Term::Gen {
                init: a,
                step: b,
                guard: c,
                ..
            } => (vec![a, b, c], &[]),
            Term::Fold {
                family,
                op,
                identity,
                ..
            } => {
                let mut v = vec![family, op];
                v.extend(identity);
                (v, &[])
            }
            Term::Match(of, arms) => {
                work.extend(arms.iter().map(|(_, t): &(KPattern, Term)| t));
                (vec![of], &[])
            }
        };
        for s in shared {
            visit(s, &mut seen, &mut work);
        }
        work.extend(inline);
    }
    n
}

/// Puts the term `s` holds on `work` the first time its id is seen.
fn visit<'a>(s: &'a Shared, seen: &mut HashSet<u64>, work: &mut Vec<&'a Term>) {
    if seen.insert(s.id()) {
        work.push(s);
    }
}

/// The nodes of the ZIR graph `g`, its nested regions' included. Lowering never shares a region
/// between nodes (COMPLEXITY.md Z25), so the regions form a tree and each is walked once.
pub fn zir_nodes(g: &Region) -> usize {
    let mut n = g.nodes.len();
    let mut work: Vec<&Arc<Region>> = g.nodes.iter().flat_map(|x| &x.regions).collect();
    while let Some(r) = work.pop() {
        n += r.nodes.len();
        work.extend(r.nodes.iter().flat_map(|x| &x.regions));
    }
    n
}

/// The syntax tree of the unit `text`, or the first error that stops it.
pub fn syntax(text: &str) -> Result<Vec<Stmt>, String> {
    let tokens = zedc::lex::lex_fence(text).map_err(|e| format!("lex: {e:?}"))?;
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP)
        .map_err(|e| format!("parse: {e:?}"))?;
    zedc::ast::unit(text, &tokens, &tree).map_err(|e| format!("syntax: {e:?}"))
}

/// The syntax-tree stage of the unit `text` alone, for a unit whose later stages are not built
/// yet (a struct declaration, compiled from step L2.4).
pub fn ast_stage(text: &str) -> Result<Stage, String> {
    let stmts = syntax(text)?;
    Ok(Stage {
        nodes: ast_nodes(&stmts),
        bytes: bytes_of(stmts),
    })
}
