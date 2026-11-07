//! The counting machine and the native code against the size of the program (the rule of low
//! complexity, DESIGN.md Part G): an atom of many named fields, many lookup ports,
//! many constants, many lambdas and one value used many times each run in time near linear in
//! their number (COMPLEXITY.md Z14); so do the runtime heap's match of a deep constant, many
//! matches of one, and the value of cells that share their parts (COMPLEXITY.md R3).

use std::mem::ManuallyDrop;
use std::sync::Arc;
use std::sync::Mutex;
use zed_kernel::Shared;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Lookup, Pattern, Prim, Term, Value, World};
use zed_rt::{Heap, Obj, Word};
use zed_tests::deep::{in_tuple, nested};
use zed_tests::scaling;
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
fn world(n: usize) -> World {
    let mut w = World::new();
    for i in 0..n {
        let p: Arc<dyn Lookup> = Arc::new(Same(Value::Int(i as i64)));
        w.sources.insert(format!("p{i}"), p);
    }
    w
}

/// `t` run by the counting machine and natively in `w`: both values, printed, which agree.
fn both(t: &Term, w: &World) -> String {
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
fn fields(n: usize) -> Term {
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
fn ports(n: usize) -> Term {
    prim(
        Prim::Tuple,
        (0..n)
            .map(|i| app(Term::Read(format!("p{i}").into()), vec![lit(0i64)]))
            .collect(),
    )
}

/// `("s0", "s1", …)`: a tuple of `n` constant strings.
fn consts(n: usize) -> Term {
    prim(
        Prim::Tuple,
        (0..n).map(|i| lit(format!("s{i}").as_str())).collect(),
    )
}

/// `f0 = (x) -> x ++ "0"; …; (f0("a"), f1("a"), …)`: `n` lambdas, each called once.
fn lambdas(n: usize) -> Term {
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
fn dups(n: usize) -> Term {
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

fn check(what: &str, n: usize, w: &World, make: fn(usize) -> Term) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 29)
            .spawn_scoped(s, || {
                scaling::check(what, n, |n| {
                    both(&make(n), w);
                })
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn an_atom_of_many_named_fields_scales() {
    check(
        "an atom of n named fields, matched",
        500,
        &World::new(),
        fields,
    );
}

#[test]
fn a_tuple_of_many_lookup_ports_scales() {
    let n = 250;
    check(
        "a tuple of n lookup ports",
        n,
        &world(scaling::FACTOR * n),
        ports,
    );
}

#[test]
fn many_constants_scale() {
    check("a tuple of n constants", 1000, &World::new(), consts);
}

#[test]
fn many_lambdas_scale() {
    check("n lambdas, each called", 125, &World::new(), lambdas);
}

#[test]
fn one_value_used_many_times_scales() {
    check(
        "one cell used n times by one node",
        1000,
        &World::new(),
        dups,
    );
}

/// `t` run by the counting machine and natively: both values and both counts agree.
fn counted(t: &Term) -> String {
    counted_in(t, World::new())
}

/// [`counted`], with the ports of `w`.
pub(super) fn counted_in(t: &Term, w: World) -> String {
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
fn tiers(d: usize, at: i64) -> Term {
    let chain = (0..d).rev().fold(lit("top"), |rest, i| {
        let c = prim(Prim::Lt, vec![var("x"), lit(i as i64)]);
        if_(c, lit(format!("t{i}").as_str()), rest)
    });
    let_("x", prim(Prim::Mul, vec![lit(at), lit(1i64)]), chain)
}

/// `if i < d then (y = (…) + 1; y) else i`, `d` deep through the first arms: each level holds
/// a node after its arm, so the arm's parent frame has work left when the arm ends.
fn nest(d: usize) -> Term {
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
fn cases(d: usize, at: i64) -> Term {
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
fn curried(d: usize) -> Term {
    let last = format!("a{}", d - 1);
    let sum = prim(Prim::Add, vec![var("a0"), var(&last)]);
    let f = (0..d).rev().fold(sum, |b, i| lam(&[&format!("a{i}")], b));
    (0..d).fold(f, |f, i| app(f, vec![lit(i as i64 + 1)]))
}

/// Runs `f` with a stack that holds the recursive passes of a term thousands deep: lowering,
/// planning and the drop of a graph.
fn on_big_stack(f: impl FnOnce() + Send) {
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

/// The depth of the terms below: far deeper than a thread of 128 KiB could hold in calls.
const DEEP: usize = 4000;

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
fn a_rate_table_thousands_deep_compiles_on_a_small_stack() {
    compiles_on_a_small_stack(deep_rate_table().0);
}

#[test]
fn a_rate_table_thousands_deep_runs_as_the_machine_does() {
    runs_as_the_machine_does(deep_rate_table());
}

#[test]
fn a_decoder_thousands_deep_compiles_on_a_small_stack() {
    compiles_on_a_small_stack(deep_decoder().0);
}

#[test]
fn a_decoder_thousands_deep_runs_as_the_machine_does() {
    runs_as_the_machine_does(deep_decoder());
}

#[test]
fn ifs_thousands_deep_compile_on_a_small_stack() {
    compiles_on_a_small_stack(deep_ifs().0);
}

#[test]
fn ifs_thousands_deep_run_as_the_machine_does() {
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
    assert!(p.regions.remove(arm).is_some(), "{:?}", p.regions.keys());
    assert_eq!(
        zed_native::object(&g, &p).unwrap_err(),
        format!("native: arm `{arm}` has no plan")
    );
}

/// `make` at each of `n` and `8n`, planned ahead of the timing, with the object file of each
/// timed by `scaling::check`.
fn check_depth(what: &str, n: usize, make: fn(usize) -> Term) {
    on_big_stack(|| {
        let at = |m: usize| planned(&make(m));
        let (small, large) = (at(n), at(8 * n));
        scaling::check(what, n, |m| {
            let (g, p) = if m == n { &small } else { &large };
            std::hint::black_box(zed_native::object(g, p).unwrap());
        });
    });
}

#[test]
fn a_rate_table_of_many_tiers_scales() {
    check_depth("a chain of n `if`s, to an object file", 250, |d| {
        tiers(d, 0)
    });
}

#[test]
fn ifs_nested_through_the_first_arm_scale() {
    check_depth("n nested `if`s, to an object file", 125, nest);
}

#[test]
fn a_decoder_of_many_cases_scales() {
    check_depth("a chain of n `match`es, to an object file", 500, |d| {
        cases(d, 0)
    });
}

#[test]
fn a_curried_function_of_many_parameters_scales() {
    check_depth("n nested lambdas, to an object file", 200, curried);
}

/// The runs one measured size can take: a warming run and five for each measurement.
const RUNS: usize = 1 + 5 * scaling::TRIES;

/// `make(m)` for each run at each of `n` and `8n`, built before any timing starts; `run` is timed
/// on one of them per run, and each is dropped after the timing ends (COMPLEXITY.md R3).
fn heap_scales<T: Send>(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> T,
    run: impl Fn(&mut T, usize) + Sync,
) {
    let made = Mutex::new(
        [n, scaling::FACTOR * n].map(|m| (m, (0..RUNS).map(|_| make(m)).collect::<Vec<_>>())),
    );
    let used = Mutex::new(Vec::new());
    scaling::check_order(what, n, 1, |m| {
        let mut x = {
            let mut made = made.lock().unwrap();
            let at = made.iter_mut().find(|(k, _)| *k == m).unwrap();
            at.1.pop().expect("a heap for each run")
        };
        run(&mut x, m);
        used.lock().unwrap().push(x);
    });
}

/// A heap holding a shipping rate table `depth` deep as a constant, its word, and the pattern
/// `(_, (_, … last))` that reads to its end, never dropped: a pattern drops by recursion.
fn rate_table(depth: usize) -> (Heap, Word, ManuallyDrop<Pattern>) {
    let mut h = Heap::new();
    let w = h.uncounted(nested(in_tuple, depth, Value::Int(0)));
    let p = (0..depth).fold(Pattern::Bind("last".into()), |p, _| {
        Pattern::Tuple(vec![Pattern::Wild, p])
    });
    (h, w, ManuallyDrop::new(p))
}

/// Matches `p` against `w` and checks the end of the table is bound.
fn read_to_the_end(h: &mut Heap, p: &Pattern, w: Word) {
    let mut out = Vec::new();
    assert!(h.matches(p, w, &mut Vec::new(), &mut out).unwrap());
    assert_eq!(out[0].0, Word::int(0));
}

#[test]
fn matching_a_deep_constant_scales() {
    heap_scales(
        "a match to the end of a constant n deep",
        1000,
        rate_table,
        |(h, w, p), _| read_to_the_end(h, p, *w),
    );
}

#[test]
fn matching_one_constant_many_times_scales() {
    heap_scales(
        "n matches to the end of a constant 100 deep",
        1000,
        |_| rate_table(100),
        |(h, w, p), n| {
            for _ in 0..n {
                read_to_the_end(h, p, *w);
            }
        },
    );
}

/// A heap holding a summary paired with itself `depth` times: `depth + 1` cells, `2^depth`
/// paths from the top.
fn paired(depth: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let mut w = h.fresh(&Value::str("total 12")).unwrap();
    for _ in 0..depth {
        h.inc(w).unwrap();
        w = h.alloc(Obj::Tuple(vec![w, w]));
    }
    (h, w)
}

#[test]
fn reading_a_value_whose_parts_share_cells_scales() {
    heap_scales(
        "the value of n cells, each holding the one below twice",
        1000,
        paired,
        |(h, w), _| {
            std::hint::black_box(h.value(*w).unwrap());
        },
    );
}

/// `#cons(n-1, #cons(…, #cons(0, #nil)))`: a list of `n` atoms, each built on the one before.
fn list(n: usize) -> Term {
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
pub(super) fn strings(n: usize) -> World {
    let mut w = World::new();
    let xs = (0..n).map(|i| Value::str(&format!("s{i}"))).collect();
    w.inputs.insert("x".into(), Value::tuple(xs));
    w
}

/// `x = read x; f = (y) -> match (x, y) { (a, b) -> b }; (f(0), f(1), …, f(n-1))`: `n`
/// matches, each binding the tuple `x` to `a`, which the arm does not use.
pub(super) fn unused(n: usize) -> Term {
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

/// The native run of `make` in `world` at `n` and `8n`, planned and with its world built
/// before the timing, against the counting machine's value and counts at `n`. The timed run
/// clones the world, which copies the ports' maps and shares their values.
pub(super) fn check_run(what: &str, n: usize, make: fn(usize) -> Term, world: fn(usize) -> World) {
    on_big_stack(|| {
        assert!(!counted_in(&make(n), world(n)).is_empty());
        let at = |m: usize| (planned(&make(m)), world(m));
        let (small, large) = (at(n), at(8 * n));
        scaling::check(what, n, |m| {
            let ((g, p), w) = if m == n { &small } else { &large };
            let o = zed_native::run(g, p, &mut Evaluator::new(w.clone())).unwrap();
            std::hint::black_box(o);
        });
    });
}

/// Each atom is made from its words, with no call to the kernel, which took the whole list
/// built so far as its payload (COMPLEXITY.md R2).
#[test]
fn a_list_of_many_atoms_scales() {
    check_run("a list of n atoms, built natively", 500, list, |_| {
        World::new()
    });
}

/// A binder the arm does not use is not copied out of the scrutinee (COMPLEXITY.md R7). The
/// tuple holds `64n` strings, so the copy would outweigh the `n` calls.
#[test]
fn many_matches_with_an_unused_binder_scale() {
    check_run(
        "n matches, each binding a tuple of 64n cells unused",
        50,
        unused,
        |n| strings(64 * n),
    );
}
