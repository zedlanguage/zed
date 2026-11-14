//! The counting machine and the native code against the size of the program (the rule of low
//! complexity, DESIGN.md Part G): an atom of many named fields, many lookup ports,
//! many constants, many lambdas and one value used many times each run in time near linear in
//! their number (COMPLEXITY.md Z14); so do the runtime heap's match of a deep constant, many
//! matches of one, and the value of cells that share their parts (COMPLEXITY.md R3). The
//! measurements at two sizes are in `bench/scaling.rs`; the tests here are their small instances
//! and the deep programs on a small stack.

use std::mem::ManuallyDrop;
use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Lookup, Pattern, Prim, Term, Value, World};
use zed_rt::{Heap, Obj, Paths, Word};
use zed_tests::deep::{in_tuple, nested};
use zedc::zir::memory;

use super::planned;

/// A lookup port whose every key holds the same value.
#[derive(Debug)]
struct Same(Value);

impl Lookup for Same {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(self.0.clone())
    }
}

/// Lookup ports `p0`, `p1`, … `p{n-1}`.
pub(crate) fn world(n: usize) -> World {
    let mut w = World::new();
    for i in 0..n {
        let p: Arc<dyn Lookup> = Arc::new(Same(Value::Int(i as i64)));
        w.sources.insert(format!("p{i}"), p);
    }
    w
}

/// `t` run by the counting machine and natively in `w`: both values, printed, which agree.
pub(crate) fn both(t: &Term, w: &World) -> String {
    let (g, p) = planned(t);
    let (v, _) = memory::run(g.graph(), &p, &mut Evaluator::new(w.clone()))
        .unwrap_or_else(|e| panic!("{t}: {e}"));
    let o = zed_native::run(&g, &p, &mut Evaluator::new(w.clone()))
        .unwrap_or_else(|e| panic!("{t}: {e}"));
    assert_eq!(o.value, v);
    v.to_string()
}

/// `#a(f{n-1}: "x{n-1}" ++ "", …, f0: "x0" ++ "")`, the names given last first, matched by a
/// pattern that binds every field, and the binders made a tuple.
pub(crate) fn fields(n: usize) -> Term {
    let name = |i: usize| format!("f{i:05}");
    let names = Value::Tuple((0..n).rev().map(|i| Value::str(&name(i))).collect());
    let mut ins = vec![lit("a"), lit(names)];
    ins.extend(
        (0..n)
            .rev()
            .map(|i| zed_tests::step_helpers::l01_34_memory::cat(&format!("x{i}"), "")),
    );
    let p = Pattern::Fields(
        "a".into(),
        (0..n)
            .map(|i| (name(i).into(), Pattern::Bind(format!("v{i}").into())))
            .collect(),
    );
    let body = prim(Prim::Tuple, (0..n).map(|i| var(&format!("v{i}"))).collect());
    Term::Match(Shared::new(prim(Prim::Atom, ins)), vec![(p, body)])
}

/// `(p0(0), p1(0), …)`: `n` lookup ports, each read once.
pub(crate) fn ports(n: usize) -> Term {
    prim(
        Prim::Tuple,
        (0..n)
            .map(|i| app(Term::Read(format!("p{i}").into()), vec![lit(0i64)]))
            .collect(),
    )
}

/// `("s0", "s1", …)`: a tuple of `n` constant strings.
pub(crate) fn consts(n: usize) -> Term {
    prim(
        Prim::Tuple,
        (0..n).map(|i| lit(format!("s{i}").as_str())).collect(),
    )
}

/// `f0 = (x) -> x ++ "0"; …; (f0("a"), f1("a"), …)`: `n` lambdas, each called once.
pub(crate) fn lambdas(n: usize) -> Term {
    let calls = prim(
        Prim::Tuple,
        (0..n)
            .map(|i| app(var(&format!("f{i}")), vec![lit("a")]))
            .collect(),
    );
    (0..n).rev().fold(calls, |b, i| {
        let f = lam(
            &["x"],
            prim(Prim::Concat, vec![var("x"), lit(format!("{i}").as_str())]),
        );
        let_(&format!("f{i}"), f, b)
    })
}

/// `x = "a" ++ "b"; (x, x, …)`: one cell used `n` times by one node.
pub(crate) fn dups(n: usize) -> Term {
    let_(
        "x",
        zed_tests::step_helpers::l01_34_memory::cat("a", "b"),
        prim(Prim::Tuple, (0..n).map(|_| var("x")).collect()),
    )
}

#[test]
fn small_programs_agree() {
    let w = world(3);
    assert_eq!(both(&fields(3), &w), r#"("x0", "x1", "x2")"#);
    assert_eq!(both(&consts(3), &w), r#"("s0", "s1", "s2")"#);
    assert_eq!(both(&lambdas(3), &w), r#"("a0", "a1", "a2")"#);
    assert_eq!(both(&dups(3), &w), r#"("ab", "ab", "ab")"#);
    assert_eq!(both(&ports(3), &w), "(0, 1, 2)");
}

/// `t` run by the counting machine and natively: both values and both counts agree.
fn counted(t: &Term) -> String {
    counted_in(t, World::new())
}

/// [`counted`], with the ports of `w`.
pub(crate) fn counted_in(t: &Term, w: World) -> String {
    let (g, p) = planned(t);
    let (v, s) = memory::run(g.graph(), &p, &mut Evaluator::new(w.clone()))
        .unwrap_or_else(|e| panic!("{t}: {e}"));
    let o = zed_native::run(&g, &p, &mut Evaluator::new(w)).unwrap_or_else(|e| panic!("{t}: {e}"));
    assert_eq!(o.value, v);
    let native = (o.stats.increments, o.stats.decrements, o.stats.allocations);
    assert_eq!(native, (s.increments, s.decrements, s.allocations), "{t}");
    v.to_string()
}

/// A rate table: `x = d * 1; if x < 0 then "t0" else if x < 1 then "t1" else …`, `d` tests in
/// a chain, each in the other's `else`, ending at `"top"`, with `x` given by `at`.
pub(crate) fn tiers(d: usize, at: i64) -> Term {
    let chain = (0..d).rev().fold(lit("top"), |rest, i| {
        let c = prim(Prim::Lt, vec![var("x"), lit(i as i64)]);
        if_(c, lit(format!("t{i}").as_str()), rest)
    });
    let_("x", prim(Prim::Mul, vec![lit(at), lit(1i64)]), chain)
}

/// `if i < d then (y = (…) + 1; y) else i`, `d` deep through the first arms: each level holds
/// a node after its arm, so the arm's parent frame has work left when the arm ends.
pub(crate) fn nest(d: usize) -> Term {
    (0..d).fold(lit(0i64), |t, i| {
        let y = format!("y{i}");
        if_(
            prim(Prim::Lt, vec![lit(i as i64), lit(d as i64)]),
            let_(&y, prim(Prim::Add, vec![t, lit(1i64)]), var(&y)),
            lit(i as i64),
        )
    })
}

/// A decoder of `d` cases: `match x { 0 -> "c0", _ -> match x { 1 -> "c1", _ -> … } }`.
pub(crate) fn cases(d: usize, at: i64) -> Term {
    let chain = (0..d).rev().fold(lit("none"), |rest, i| {
        let hit = (
            Pattern::Lit(Value::Int(i as i64)),
            lit(format!("c{i}").as_str()),
        );
        Term::Match(Shared::new(var("x")), vec![hit, (Pattern::Wild, rest)])
    });
    let_("x", prim(Prim::Mul, vec![lit(at), lit(1i64)]), chain)
}

/// A curried sum: `(a0) -> (a1) -> … -> a0 + a{d-1}`, applied to `1, 2, …`, one at a time.
pub(crate) fn curried(d: usize) -> Term {
    let last = format!("a{}", d - 1);
    let sum = prim(Prim::Add, vec![var("a0"), var(&last)]);
    let f = (0..d).rev().fold(sum, |b, i| lam(&[&format!("a{i}")], b));
    (0..d).fold(f, |f, i| app(f, vec![lit(i as i64 + 1)]))
}

/// Runs `f` with a stack that holds the recursive passes of a term thousands deep: lowering,
/// planning and the drop of a graph.
pub(crate) fn on_big_stack(f: impl FnOnce() + Send) {
    on_stack(1 << 30, f)
}

#[test]
fn a_rate_table_gives_each_tier() {
    assert_eq!(counted(&tiers(3, -1)), r#""t0""#);
    assert_eq!(counted(&tiers(3, 1)), r#""t2""#);
    assert_eq!(counted(&tiers(3, 7)), r#""top""#);
}

#[test]
fn a_decoder_gives_each_case() {
    assert_eq!(counted(&cases(3, 0)), r#""c0""#);
    assert_eq!(counted(&cases(3, 2)), r#""c2""#);
    assert_eq!(counted(&cases(3, 9)), r#""none""#);
}

#[test]
fn a_node_after_an_arm_sees_the_arm_result() {
    assert_eq!(counted(&nest(1)), "1");
    assert_eq!(counted(&nest(5)), "5");
}

#[test]
fn a_curried_sum_runs() {
    assert_eq!(counted(&curried(1)), "2");
    assert_eq!(counted(&curried(4)), "5");
}

/// `s = "ab" ++ "c"`, wrapped around `body`.
fn with_cell(body: Term) -> Term {
    let_("s", prim(Prim::Concat, vec![lit("ab"), lit("c")]), body)
}

#[test]
fn a_computed_condition_is_released_as_the_machine_releases_it() {
    let same = prim(Prim::Eq, vec![var("s"), lit("abc")]);
    // The condition is a fresh bool, and the cell it was computed from is used by one arm.
    let one_arm = with_cell(if_(same.clone(), var("s"), lit("no")));
    assert_eq!(counted(&one_arm), r#""abc""#);
    // The condition is used by an arm as well, so it is not released at the test.
    let kept = let_("c", same.clone(), if_(var("c"), var("c"), lit(false)));
    assert_eq!(counted(&with_cell(kept)), "true");
    // The condition is used again after the `if`.
    let after = let_(
        "c",
        same,
        prim(
            Prim::Tuple,
            vec![if_(var("c"), lit(1i64), lit(2i64)), var("c")],
        ),
    );
    assert_eq!(counted(&with_cell(after)), "(1, true)");
}

#[test]
fn a_condition_that_is_a_cell_fails_as_the_machine_fails() {
    // The condition is a string, so the kernel decides, and it gives a failure value.
    let t = with_cell(if_(var("s"), lit(1i64), lit(2i64)));
    let once = with_cell(prim(Prim::Tuple, vec![if_(var("s"), lit(1i64), lit(2i64))]));
    for t in [t, once] {
        let (g, p) = planned(&t);
        let machine = memory::run(g.graph(), &p, &mut Evaluator::new(World::new()));
        let native = zed_native::run(&g, &p, &mut Evaluator::new(World::new()));
        match (machine, native) {
            (Ok((v, s)), Ok(o)) => {
                assert_eq!(o.value, v);
                assert_eq!(o.stats.decrements, s.decrements);
            }
            (Err(a), Err(b)) => assert_eq!(a, b),
            (a, b) => panic!("the machine gave {a:?}, the native run {b:?}"),
        }
    }
}

/// Runs `f` on a thread with a stack of `bytes`.
fn on_stack(bytes: usize, f: impl FnOnce() + Send) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(bytes)
            .spawn_scoped(s, f)
            .unwrap()
            .join()
            .unwrap()
    })
}

/// The depth of the terms below: above the depths at which the recursive code generator
/// (before commit d5e160e51) overflowed a thread of 128 KiB, measured by bisection on each
/// term: 107 for the rate table and the decoder, 106 for the nested `if`s.
const DEEP: usize = 200;

/// A rate table [`DEEP`] tiers long, read in the middle, and the tier it gives.
fn deep_rate_table() -> (Term, String) {
    let at = DEEP as i64 / 2;
    (tiers(DEEP, at), format!(r#""t{}""#, DEEP / 2 + 1))
}

/// A decoder of [`DEEP`] cases, given the last, and the case it gives.
fn deep_decoder() -> (Term, String) {
    (cases(DEEP, DEEP as i64 - 1), format!(r#""c{}""#, DEEP - 1))
}

/// [`DEEP`] `if`s nested through the first arm, and the value they give.
fn deep_ifs() -> (Term, String) {
    (nest(DEEP), DEEP.to_string())
}

/// Code generation keeps the regions in progress on its own stacks: `t` compiles to an object
/// file on a stack of 128 KiB. This and [`runs_as_the_machine_does`] are separate tests, each
/// compiling the term once, so that each stays well under 60 s under load.
fn compiles_on_a_small_stack(t: Term) {
    on_big_stack(|| {
        let (g, p) = planned(&t);
        on_stack(1 << 17, || {
            assert!(!zed_native::object(&g, &p).unwrap().is_empty());
        });
    });
}

/// `t` run natively gives `want`, the machine's value, with the machine's count of releases.
/// The code runs on a larger stack than [`compiles_on_a_small_stack`]'s, since one function's
/// frame holds a slot for each of its words.
fn runs_as_the_machine_does((t, want): (Term, String)) {
    on_big_stack(|| {
        let (g, p) = planned(&t);
        let (v, s) = memory::run(g.graph(), &p, &mut Evaluator::new(World::new())).unwrap();
        assert_eq!(v.to_string(), want);
        on_stack(1 << 24, || {
            let o = zed_native::run(&g, &p, &mut Evaluator::new(World::new())).unwrap();
            assert_eq!(o.value, v);
            assert_eq!(o.stats.decrements, s.decrements);
        });
    });
}

#[test]
fn a_rate_table_hundreds_deep_compiles_on_a_small_stack() {
    compiles_on_a_small_stack(deep_rate_table().0);
}

#[test]
fn a_rate_table_hundreds_deep_runs_as_the_machine_does() {
    runs_as_the_machine_does(deep_rate_table());
}

#[test]
fn a_decoder_hundreds_deep_compiles_on_a_small_stack() {
    compiles_on_a_small_stack(deep_decoder().0);
}

#[test]
fn a_decoder_hundreds_deep_runs_as_the_machine_does() {
    runs_as_the_machine_does(deep_decoder());
}

#[test]
fn ifs_hundreds_deep_compile_on_a_small_stack() {
    compiles_on_a_small_stack(deep_ifs().0);
}

#[test]
fn ifs_hundreds_deep_run_as_the_machine_does() {
    runs_as_the_machine_does(deep_ifs());
}

/// Paths are worked out for a message only, and the message is the one a path string gives.
#[test]
fn a_wrong_plan_deep_in_the_term_names_the_path() {
    let t = with_cell(if_(
        lit(true),
        if_(lit(true), var("s"), lit("no")),
        lit("no"),
    ));
    let (g, mut p) = planned(&t);
    let arm = "r.1/0.0/0";
    // The node holding the arm loses the plans of its arms.
    let at = p.find(arm).expect("the arm's plan");
    let (up, k, _) = p.regions[at].up.expect("an arm is under a node");
    p.regions[up].nodes[k].regions.clear();
    let e = zed_native::object(&g, &p).unwrap_err();
    assert!(
        e.starts_with("zedc could not make machine code for the program because of a bug in zedc")
            && e.contains(&format!("this line: arm `{arm}` has no plan.")),
        "{e}"
    );
}

/// A heap holding a shipping rate table `depth` deep as a constant, its word, and the pattern
/// `(_, (_, … last))` that reads to its end, never dropped: a pattern drops by recursion.
pub(crate) fn rate_table(depth: usize) -> (Heap, Word, ManuallyDrop<Pattern>) {
    let mut h = Heap::new();
    let w = h.uncounted(nested(in_tuple, depth, Value::Int(0)));
    let p = (0..depth).fold(Pattern::Bind("last".into()), |p, _| {
        Pattern::Tuple(vec![Pattern::Wild, p])
    });
    (h, w, ManuallyDrop::new(p))
}

/// Matches `p` against `w` and checks the end of the table is bound.
pub(crate) fn read_to_the_end(h: &mut Heap, p: &Pattern, w: Word) {
    let mut out = Vec::new();
    assert!(h.matches(p, w, &mut Paths::default(), &mut out).unwrap());
    assert_eq!(out[0].0, Word::int(0));
}

/// A heap holding a summary paired with itself `depth` times: `depth + 1` cells, `2^depth`
/// paths from the top.
pub(crate) fn paired(depth: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let mut w = h.fresh(&Value::str("total 12")).unwrap();
    for _ in 0..depth {
        h.inc(w).unwrap();
        w = h.alloc(Obj::Tuple(vec![w, w].into()));
    }
    (h, w)
}

/// A heap holding an invoice of `depth` lines, `("line 0", ("line 1", … "total"))`, and the
/// pattern `(l0, (l1, … total))` that binds every line: a binder at each level, the one at
/// level `k` at a path of `k + 1` parts. The pattern is never dropped: a pattern drops by
/// recursion.
pub(crate) fn invoice(depth: usize) -> (Heap, Word, ManuallyDrop<Pattern>) {
    let mut h = Heap::new();
    let v = (0..depth).rev().fold(Value::str("total"), |rest, k| {
        Value::tuple(vec![Value::str(&format!("line {k}")), rest])
    });
    let w = h.fresh(&v).unwrap();
    let p = (0..depth).fold(Pattern::Bind("total".into()), |p, k| {
        Pattern::Tuple(vec![Pattern::Bind(format!("l{k}").into()), p])
    });
    (h, w, ManuallyDrop::new(p))
}

/// Matches an invoice against its pattern: the heap, the scrutinee, its paths and binders.
pub(crate) fn matched_invoice(depth: usize) -> (Heap, Word, Paths, Vec<(Word, usize)>) {
    let (mut h, w, p) = invoice(depth);
    let (mut paths, mut out) = (Paths::default(), Vec::new());
    assert!(h.matches(&p, w, &mut paths, &mut out).unwrap());
    (h, w, paths, out)
}

/// The spine cell `level` levels below the top of an invoice.
fn spine(h: &Heap, w: Word, level: usize) -> Word {
    (0..level).fold(w, |c, _| match h.obj(c).unwrap() {
        Some(Obj::Tuple(xs)) => xs[1],
        _ => panic!("an invoice line"),
    })
}

#[test]
fn each_line_of_an_invoice_binds_at_its_own_path() {
    let (mut h, _, paths, out) = matched_invoice(4);
    let got: Vec<_> = out
        .iter()
        .map(|&(x, node)| (h.value(x).unwrap(), paths.path(node)))
        .collect();
    let want: Vec<_> = (0..4)
        .map(|k| {
            (
                Value::str(&format!("line {k}")),
                [vec![1; k], vec![0]].concat(),
            )
        })
        .chain([(Value::str("total"), vec![1; 4])])
        .collect();
    assert_eq!(got, want);
}

#[test]
fn a_pattern_with_no_binder_releases_the_whole_invoice() {
    let (mut h, w, _) = invoice(4);
    let p = (0..4).fold(Pattern::Wild, |p, _| Pattern::Tuple(vec![Pattern::Wild, p]));
    let (mut paths, mut out) = (Paths::default(), Vec::new());
    assert!(h.matches(&p, w, &mut paths, &mut out).unwrap());
    assert!(out.is_empty());
    h.release(w, &paths, &[]).unwrap();
    assert_eq!((h.live(), h.stats.increments), (0, 0));
}

/// Every set of kept lines of an invoice 4 deep, with the scrutinee held once or a spine cell
/// held twice: the fused release leaves each kept line live with a reference for its binder,
/// and the counts it writes are those the paths of the kept lines give: a cell held once is
/// freed with no write, and a shared one gives each kept line below it one reference and
/// loses one.
#[test]
fn a_fused_release_keeps_exactly_the_kept_lines() {
    const DEPTH: usize = 4;
    for held in [None, Some(0), Some(1), Some(3)] {
        for set in 0..1u32 << (DEPTH + 1) {
            let (mut h, w, paths, out) = matched_invoice(DEPTH);
            let other = held.map(|level| spine(&h, w, level));
            if let Some(c) = other {
                h.inc(c).unwrap();
            }
            let (writes, frees) = (h.stats.increments, h.stats.frees);
            let kept: Vec<usize> = (0..=DEPTH).filter(|b| set >> b & 1 == 1).collect();
            let nodes: Vec<usize> = kept.iter().map(|&b| out[b].1).collect();
            h.release(w, &paths, &nodes).unwrap();
            // Line `b` is below the shared cell when the cell is above its level.
            let below = |b: usize| held.is_some_and(|level| level <= b);
            let shared_kept = kept.iter().filter(|&&b| below(b)).count() as u64;
            let freed_spine = held.unwrap_or(DEPTH) as u64;
            let freed_lines = (0..freed_spine as usize)
                .filter(|b| set >> b & 1 == 0)
                .count() as u64;
            let last = u64::from(held.is_none() && set >> DEPTH & 1 == 0);
            let what = format!("held {held:?}, kept {kept:?}");
            assert_eq!(h.stats.increments - writes, shared_kept, "{what}");
            assert_eq!(
                h.stats.frees - frees,
                freed_spine + freed_lines + last,
                "{what}"
            );
            for &b in &kept {
                let x = out[b].0;
                let want = match b {
                    DEPTH => Value::str("total"),
                    b => Value::str(&format!("line {b}")),
                };
                assert_eq!(h.value(x).unwrap(), want, "{what}");
                h.dec(x).unwrap();
            }
            if let Some(c) = other {
                h.dec(c).unwrap();
            }
            assert_eq!(h.live(), 0, "{what}");
        }
    }
}

/// `#cons(n-1, #cons(…, #cons(0, #nil)))`: a list of `n` atoms, each built on the one before.
pub(crate) fn list(n: usize) -> Term {
    (0..n).fold(lit(Value::atom("nil")), |rest, i| {
        prim(
            Prim::Atom,
            vec![
                lit("cons"),
                lit(Value::tuple(Vec::new())),
                lit(i as i64),
                rest,
            ],
        )
    })
}

/// A world whose input port `x` holds `("s0", "s1", …)`, `n` strings; a read makes them
/// `n + 1` cells.
pub(crate) fn strings(n: usize) -> World {
    let mut w = World::new();
    let xs = (0..n).map(|i| Value::str(&format!("s{i}"))).collect();
    w.inputs.insert("x".into(), Value::tuple(xs));
    w
}

/// `x = read x; f = (y) -> match (x, y) { (a, b) -> b }; (f(0), f(1), …, f(n-1))`: `n`
/// matches, each binding the tuple `x` to `a`, which the arm does not use.
pub(crate) fn unused(n: usize) -> Term {
    let p = Pattern::Tuple(vec![Pattern::Bind("a".into()), Pattern::Bind("b".into())]);
    let s = prim(Prim::Tuple, vec![var("x"), var("y")]);
    let f = lam(&["y"], Term::Match(Shared::new(s), vec![(p, var("b"))]));
    let calls = (0..n).map(|i| app(var("f"), vec![lit(i as i64)])).collect();
    let_(
        "x",
        Term::Read("x".into()),
        let_("f", f, prim(Prim::Tuple, calls)),
    )
}

/// The small instances of the benchmarks of `bench/scaling.rs` that compile to an object file:
/// each shape compiles.
#[test]
fn each_deep_shape_compiles_to_an_object_file() {
    for t in [tiers(3, 0), nest(3), cases(3, 0), curried(4)] {
        let (g, p) = planned(&t);
        assert!(!zed_native::object(&g, &p).unwrap().is_empty(), "{t}");
    }
}

/// A match to the end of a constant binds its last element, and binds it again on a second
/// match of the same constant.
#[test]
fn a_match_reads_to_the_end_of_a_constant_each_time() {
    let (mut h, w, p) = rate_table(3);
    for _ in 0..2 {
        read_to_the_end(&mut h, &p, w);
    }
}

/// The value of cells that each hold the one below twice is the whole tree of paths.
#[test]
fn the_value_of_cells_that_share_their_parts_is_every_path() {
    let (mut h, w) = paired(2);
    let s = Value::str("total 12");
    let one = Value::tuple(vec![s.clone(), s]);
    assert_eq!(h.value(w).unwrap(), Value::tuple(vec![one.clone(), one]));
}

/// A list of atoms built natively, and matches binding a tuple the arm does not use, run as
/// the machine runs them and give the kernel's value.
#[test]
fn a_list_of_atoms_and_unused_binders_run_as_the_machine_does() {
    let t = list(3);
    let want = Evaluator::new(World::new()).run(&t).unwrap().to_string();
    assert_eq!(counted(&t), want);
    assert_eq!(counted_in(&unused(3), strings(4)), "(0, 1, 2)");
}
