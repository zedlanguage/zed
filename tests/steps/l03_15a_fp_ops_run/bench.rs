//! Benchmarks of plan row FP-ops-run, run apart from the correctness tests
//! (`tools/run_tests.sh --bench`): the walk of a level in key order that `.any`, `.all`,
//! `.find`, `.foldl` and `.foldr` elaborate to, `.first` and `.last`, at n entries and at 8n,
//! and the same words through `zedc run`. Step L3.15a's own test is here too: a quantifier
//! whose deciding entry is the k-th, k fixed, costs the same at n and at 8n.
//!
//! The kernel runs time the terms zedc elaborates the words to (zedc-elab, walk/fp_ops.rs),
//! built before the runs; the whole-path runs time `zedc run` of a program whose display holds
//! the entries, so they measure the parse, the check, the elaboration and the run together.
//!
//! The reads of a list made by `++` that build no map of it (plan row
//! TEST-list-concat-no-map-build) each run once after every `++` of a right-nested chain, so a
//! read that built the map would make the chain quadratic.

use std::collections::HashMap;

use zed_kernel::term::GuardPos;
use zed_kernel::term::build::{app, lam, let_, lit, var};
use zed_kernel::{Evaluator, Family, Pattern, Prim, Term, Value, World, eval};
use zed_tests::kernel::*;
use zed_tests::scaling::{self, FACTOR, Meter, hold, hold_linear};

use super::program;
use zed_tests::step_helpers::l01_16_elaboration::{checked, elab, value, with_prelude};
use zed_tests::step_helpers::l01_36_cranelift as cranelift;
use zed_tests::step_helpers::l01_36a_executables::interpreter;

/// Entries of a kernel run.
const N_KERNEL: usize = 20_000;
/// Entries of the display of a whole-path run.
const N_PROGRAM: usize = 1_000;

/// `{0 -> 0, …, n-1 -> n-1}`.
fn entries(n: usize) -> Term {
    lit(Value::Family(Family::of((0..n as i64).map(|k| (k, k)))))
}

fn part(t: Term, i: i64) -> Term {
    Term::Prim(Prim::TupleGet, vec![t, lit(i)])
}

/// `true` while the entry `e` is one, `false` at the end, `()`.
fn not_at_end(e: Term) -> Term {
    Term::Match(
        rc(e),
        vec![
            (Pattern::Tuple(Vec::new()), lit(Value::Bool(false))),
            (Pattern::Wild, lit(Value::Bool(true))),
        ],
    )
}

/// The last frame of the `gen` family bound to `gn`.
fn last_frame(gn: &str) -> Term {
    let n = Term::Prim(Prim::Count, vec![var(gn)]);
    get(var(gn), sub(n, lit(1)))
}

/// The term `xs.any(p)` elaborates to (zedc-elab, `quantifier_term`), without the
/// pass-through of a loose atom `xs`, which these families are not: a `gen` over the frames
/// `(e, r, k)` that stops at the first entry `p` holds of.
fn any_term(xs: Term, p: Term) -> Term {
    let entry = part(var("fr"), 0);
    let step = Term::Prim(
        Prim::Tuple,
        vec![
            Term::Prim(Prim::EntryAfter, vec![var("xs"), entry.clone()]),
            Term::App(rc(var("p")), vec![part(entry.clone(), 1)]),
            part(entry.clone(), 0),
        ],
    );
    let guard = Term::Match(
        rc(part(var("fr"), 1)),
        vec![
            (Pattern::Lit(Value::Bool(false)), not_at_end(entry)),
            (Pattern::Wild, lit(Value::Bool(false))),
        ],
    );
    let frames = Term::Gen {
        init: rc(Term::Prim(
            Prim::Tuple,
            vec![
                Term::Prim(Prim::FirstEntry, vec![var("xs")]),
                lit(Value::Bool(false)),
                Term::Prim(Prim::Tuple, Vec::new()),
            ],
        )),
        step: rc(Term::Lam(vec!["fr".into()], rc(step))),
        guard: rc(Term::Lam(vec!["fr".into()], rc(guard))),
        pos: GuardPos::Before,
    };
    let body = let_("gn", frames, part(last_frame("gn"), 1));
    let_("xs", xs, let_("p", p, body))
}

/// The term `xs.foldl(0, (a, x) -> a + x)` elaborates to (zedc-elab, `fold_dir_term`): a
/// `gen` over the frames `(e, acc)`, walking the entries in key order.
fn foldl_term(xs: Term) -> Term {
    let_(
        "xs",
        xs,
        let_("gn", foldl_frames(), part(last_frame("gn"), 1)),
    )
}

/// The `gen` of [`foldl_term`] over the family bound to `xs`.
fn foldl_frames() -> Term {
    let entry = part(var("fr"), 0);
    let step = Term::Prim(
        Prim::Tuple,
        vec![
            Term::Prim(Prim::EntryAfter, vec![var("xs"), entry.clone()]),
            add(part(var("fr"), 1), part(entry.clone(), 1)),
        ],
    );
    Term::Gen {
        init: rc(Term::Prim(
            Prim::Tuple,
            vec![Term::Prim(Prim::FirstEntry, vec![var("xs")]), lit(0)],
        )),
        step: rc(Term::Lam(vec!["fr".into()], rc(step))),
        guard: rc(Term::Lam(vec!["fr".into()], rc(not_at_end(entry)))),
        pos: GuardPos::Before,
    }
}

/// The least instructions of three runs of `run` at `k`.
fn least(meter: &mut Meter, k: usize, run: &impl Fn(usize)) -> u64 {
    (0..3).map(|_| meter.work(|| run(k)).units).min().unwrap()
}

/// Holds the instructions of `run` at n and 8n under the limit for work of order
/// `n^power`, and returns the ratio; `None` when the test ran again alone, in a new process,
/// which measured and passed (`scaling::ran_alone_in_a_new_process`), and the caller returns.
fn ratio(what: &str, n: usize, power: u32, run: impl Fn(usize)) -> Option<f64> {
    let mut meter = Meter::new();
    // Counted here and held by `hold`, not by a check: beside other tests on a machine with no
    // counter of instructions the test runs again alone (BENCH-self-counted-meters-processor-time).
    if scaling::ran_alone_in_a_new_process(&meter) {
        return None;
    }
    let (small, large) = (
        least(&mut meter, n, &run),
        least(&mut meter, FACTOR * n, &run),
    );
    Some(hold(what, meter.unit(), small, large, power))
}

#[test]
fn a_quantifier_that_never_decides_walks_in_n_log_n() {
    // `x > n`: no entry holds, so the walk reads all n entries, each step O(log n).
    let terms = scaling::inputs(N_KERNEL, |k| {
        any_term(entries(k), lam(&["x"], lt(lit(k as i64), var("x"))))
    });
    let run = |k: usize| assert_eq!(eval(&terms[&k]).unwrap(), Value::Bool(false));
    scaling::check(
        "the kernel run of `xs.any(x -> x > n)` over n entries",
        N_KERNEL,
        run,
    );
    ratio(
        "the kernel run of `xs.any(x -> x > n)`, instructions",
        N_KERNEL,
        1,
        run,
    );
}

/// Step L3.15a's test: "fixed-k cost" — the deciding entry is the 10th at n and at 8n, so
/// the walk does the same work at both, up to the `log n` of each entry step.
#[test]
fn a_quantifier_decided_at_a_fixed_entry_costs_the_same_at_8n() {
    let terms = scaling::inputs(N_KERNEL, |k| {
        any_term(entries(k), lam(&["x"], le(lit(10), var("x"))))
    });
    let run = |k: usize| assert_eq!(eval(&terms[&k]).unwrap(), Value::Bool(true));
    ratio(
        "the kernel run of `xs.any(x -> x >= 10)` over n entries, instructions",
        N_KERNEL,
        0,
        run,
    );
}

/// The same test on the term zedc elaborates `xs.any(x -> x >= 10)` to, so that a change to
/// the elaboration that walks every entry (or a `gen` guard that stops reading the decided
/// result) fails here and not only in the hand-built mirror above. A whole-path run cannot
/// show it: parsing the n entries of a display is itself linear.
#[test]
fn the_elaborated_quantifier_decided_at_a_fixed_entry_costs_the_same_at_8n() {
    // A parameter of type `[int]` is not supported yet, so `xs` is a display here, and each run
    // binds its kernel name to the n entries around `q`'s own term.
    let unit =
        elab("xs = [0, 1, 2];\nq = xs.any(x -> x >= 10);").unwrap_or_else(|e| panic!("{e:?}"));
    let def = |name: &str| unit.defs.iter().find(|d| d.name == name).unwrap();
    let (xs, q) = (def("xs").kernel.clone(), def("q").term.clone());
    let terms = scaling::inputs(N_KERNEL, |k| {
        with_prelude(Term::Let(xs.clone(), rc(entries(k)), q.clone()))
    });
    let run = |k: usize| {
        let v = Evaluator::new(World::new()).run(&terms[&k]).unwrap();
        assert_eq!(v, Value::Bool(true));
    };
    ratio(
        "the elaborated `xs.any(x -> x >= 10)` over n entries, instructions",
        N_KERNEL,
        0,
        run,
    );
}

/// The term zedc elaborates the definition `q` in `src` to, run with `xs` bound to the n
/// entries of [`entries`] at each size, as in
/// [`the_elaborated_quantifier_decided_at_a_fixed_entry_costs_the_same_at_8n`].
fn elaborated(src: &str) -> HashMap<usize, Term> {
    let unit = elab(src).unwrap_or_else(|e| panic!("{e:?}"));
    let def = |name: &str| unit.defs.iter().find(|d| d.name == name).unwrap();
    let (xs, q) = (def("xs").kernel.clone(), def("q").term.clone());
    scaling::inputs(N_KERNEL, |k| {
        with_prelude(Term::Let(xs.clone(), rc(entries(k)), q.clone()))
    })
}

/// Entries of a list built by n concatenations.
const N_CONCAT: usize = 1_000;

/// The list `[x]`.
fn one(x: usize) -> Value {
    Value::Family(Family::of([(0, x as i64)]))
}

/// `(a, b) -> a ++ b` with the body zedc elaborates `a ++ b` to on two lists of `int`. The
/// chain is built here, as `let`s, with no fold around it; the folds zedc compiles since plan
/// row FP-ops-concat-fold-acc are timed by
/// [`a_left_fold_building_a_list_by_concatenation_runs_in_n_log_n`] and the test after it.
fn elaborated_concat() -> Term {
    let unit = elab("a = [0];\nb = [0];\nq = a ++ b;").unwrap_or_else(|e| panic!("{e:?}"));
    let def = |name: &str| unit.defs.iter().find(|d| d.name == name).unwrap();
    let (a, b) = (def("a").kernel.clone(), def("b").kernel.clone());
    lam(&[&a, &b], (*def("q").term).clone())
}

/// The k concatenations `[0] ++ ([1] ++ (… ++ ([k-1] ++ [0])))` (`right`) or
/// `(([0] ++ [0]) ++ [1]) ++ … ++ [k-1]`, each a call of [`elaborated_concat`] on the list made
/// by the one before, as `let`s.
fn concat_chain(k: usize, right: bool) -> Term {
    let step = |i: usize| match right {
        true => app(var("cat"), vec![lit(one(i)), var("acc")]),
        false => app(var("cat"), vec![var("acc"), lit(one(i))]),
    };
    let order: Vec<usize> = match right {
        true => (0..k).rev().collect(),
        false => (0..k).collect(),
    };
    let body = (order.iter().rev()).fold(var("acc"), |body, &i| let_("acc", step(i), body));
    let_("cat", elaborated_concat(), let_("acc", lit(one(0)), body))
}

/// The list `0, …, k-1` with a `0` after it (`right`) or before it, as [`concat_chain`] makes.
fn chain_value(k: usize, right: bool) -> Value {
    let xs = (0..k as i64).collect::<Vec<_>>();
    let all = match right {
        true => [xs, vec![0]].concat(),
        false => [vec![0], xs].concat(),
    };
    Value::Family(Family::of(
        all.into_iter().enumerate().map(|(i, x)| (i as i64, x)),
    ))
}

/// The benchmark of [`concat_chain`] at n and 8n concatenations, each result read whole by
/// `==` against [`chain_value`].
fn concat_chain_ratio(right: bool, what: &str) {
    let terms = scaling::inputs(N_CONCAT, |k| with_prelude(concat_chain(k, right)));
    let run = |k: usize| {
        let v = Evaluator::new(World::new()).run(&terms[&k]).unwrap();
        assert_eq!(v, chain_value(k, right));
    };
    ratio(what, N_CONCAT, 1, run);
}

/// Plan row PERF-list-concat-shared: n concatenations, each putting one entry in front of the
/// list built so far, `[x] ++ a`, the right-nested chain that a recursive
/// `f(k) = [k] ++ f(k + 1)` builds. Each `++` shares both operands, so the chain costs
/// O(n log n) in all; re-keying the right operand at each step costs O(n²).
#[test]
fn a_right_nested_chain_of_concatenations_runs_in_n_log_n() {
    concat_chain_ratio(
        true,
        "n elaborated `[x] ++ a`, each on the list made by the one before, instructions",
    );
}

/// The control of the test above: n concatenations, each putting one entry after the list
/// built so far, `a ++ [x]`, the left-nested chain that `xs.foldl([], (a, x) -> a ++ [x])`
/// builds.
#[test]
fn a_left_nested_chain_of_concatenations_runs_in_n_log_n() {
    concat_chain_ratio(
        false,
        "n elaborated `a ++ [x]`, each on the list made by the one before, instructions",
    );
}

/// The 2k steps `acc = acc ++ [i]` then `acc = acc ∪ {acc.count -> i}`, for `i` from 0 to
/// `k - 1`, on the list `[0]`, as `let`s: a `++` and then a change of one entry, alternately.
fn concat_change_chain(k: usize) -> Term {
    let acc = || var("acc");
    let change = |i: usize| {
        let one = Term::Prim(Prim::Entries, vec![count(acc()), lit(i as i64)]);
        Term::Prim(Prim::Union, vec![acc(), one])
    };
    let body = (0..k).rev().fold(acc(), |body, i| {
        let joined = app(var("cat"), vec![acc(), lit(one(i))]);
        let_("acc", joined, let_("acc", change(i), body))
    });
    let_("cat", elaborated_concat(), let_("acc", lit(one(0)), body))
}

/// Plan row PERF-list-concat-change: n `++`, each followed by a change that adds one entry,
/// each on the list made by the step before. Each step must cost O(log n), as the `++` alone
/// does; a change that builds the joined list's map, O(n), makes the chain O(n²): 55.6 times at
/// 8n before the union joined an added entry as `++` does (`value::list_union`, COMPLEXITY.md
/// F223c), 8.05 after.
#[test]
fn concatenations_alternating_with_one_entry_changes_run_in_n_log_n() {
    let terms = scaling::inputs(N_CONCAT, |k| with_prelude(concat_change_chain(k)));
    let run = |k: usize| {
        let v = Evaluator::new(World::new()).run(&terms[&k]).unwrap();
        let xs = [0].into_iter().chain((0..k as i64).flat_map(|i| [i, i]));
        let want = Family::of(xs.enumerate().map(|(j, x)| (j as i64, x)));
        assert_eq!(v, Value::Family(want));
    };
    ratio(
        "n `a ++ [x]`, each followed by `a ∪ {a.count -> x}`, instructions",
        N_CONCAT,
        1,
        run,
    );
}

/// The term zedc elaborates the fold `q` to, which builds the list of `xs`'s n entries back by
/// `++` on its accumulator (plan row FP-ops-concat-fold-acc), run at n and 8n and held under
/// the limit for n log n work: each `++` adds one entry to the shared tree, O(log n), as in
/// the chains above.
fn fold_concat_ratio(what: &str, q: &str) {
    let terms = elaborated(&format!("xs = [0, 1, 2];\nq = {q};"));
    let run = |k: usize| {
        let v = Evaluator::new(World::new()).run(&terms[&k]).unwrap();
        let want = Family::of((0..k as i64).map(|i| (i, i)));
        assert_eq!(v, Value::Family(want));
    };
    scaling::check(what, N_KERNEL, run);
    ratio(&format!("{what}, instructions"), N_KERNEL, 1, run);
}

#[test]
fn a_left_fold_building_a_list_by_concatenation_runs_in_n_log_n() {
    fold_concat_ratio(
        "the elaborated `xs.foldl([], (a, x) -> a ++ [x])` over n entries",
        "xs.foldl([], (a, x) -> a ++ [x])",
    );
}

#[test]
fn a_right_fold_building_a_list_by_concatenation_runs_in_n_log_n() {
    fold_concat_ratio(
        "the elaborated `xs.foldr((x, a) -> [x] ++ a, [])` over n entries",
        "xs.foldr((x, a) -> [x] ++ a, [])",
    );
}

/// [`concat_chain_ratio`] with the chain run natively (plan row PERF-list-concat-native): each
/// `++` a native call of `cat`, whose prim `ListConcat` the runtime hands to the kernel
/// (`zed_native::hooks`), which hands the operands over as kernel values, shared, not copied.
/// The terms are lowered, legalized and planned before the runs; each run compiles the program
/// too, most of its instructions, since `zed_native::run` does both. Before the fix the ratio
/// was 43.3 at n = 1000: the compile, whose table of constants compared the n one-entry lists
/// with one another, all of one count (`zed_native::tables`; a key `ConstKey` then hashed a
/// family's end entries too, and since PERF-family-hash-count-only `Value`'s own hash reads
/// every entry). Controls, not committed: the hash without the end entries fails at 37.76;
/// each `++` building its list's map, O(n) a step, fails at 14.71.
fn native_concat_chain_ratio(right: bool, what: &str) {
    scaling::on_a_thread(1 << 29, || {
        let planned = scaling::inputs(N_CONCAT, |k| {
            cranelift::planned(&with_prelude(concat_chain(k, right)))
        });
        let run = |k: usize| {
            let (g, p) = &planned[&k];
            let o = zed_native::run(g, p, &mut Evaluator::new(World::new())).unwrap();
            assert_eq!(o.value, chain_value(k, right));
        };
        ratio(what, N_CONCAT, 1, run);
    });
}

#[test]
fn a_native_right_nested_chain_of_concatenations_runs_in_n_log_n() {
    native_concat_chain_ratio(
        true,
        "n native `[x] ++ a`, each on the list made by the one before, instructions",
    );
}

#[test]
fn a_native_left_nested_chain_of_concatenations_runs_in_n_log_n() {
    native_concat_chain_ratio(
        false,
        "n native `a ++ [x]`, each on the list made by the one before, instructions",
    );
}

/// Plan row PERF-value-key-sites-bench: a native program holding n distinct constants
/// `[0, i, 0]`, of one count and the same end entries, the case `ConstKey` (F223b) left in one
/// bucket. `(x) -> (x, [0, 0, 0], …, [0, n-1, 0])` applied to 7: the parameter keeps the tuple
/// from being one constant, so the compile puts each list in the table of constants
/// (`zed_native::tables`, `const_at`, keyed by `Value`'s hash), O(1) expected compares each,
/// and the run builds the tuple. The terms are lowered, legalized and planned before the runs.
/// The correctness test at a small size is `zed_native`'s
/// `tables::tests::equal_constants_share_one_entry_and_others_do_not`.
#[test]
fn constants_of_families_of_one_size_and_ends_scale() {
    const N: usize = 2_000;
    let list = |i: usize| Value::Family(Family::of([(0_i64, 0), (1, i as i64), (2, 0)]));
    scaling::on_a_thread(1 << 29, || {
        let planned = scaling::inputs(N, |k| {
            let items = std::iter::once(var("x")).chain((0..k).map(|i| lit(list(i))));
            let body = Term::Prim(Prim::Tuple, items.collect());
            cranelift::planned(&app(lam(&["x"], body), vec![lit(7_i64)]))
        });
        let run = |k: usize| {
            let (g, p) = &planned[&k];
            let o = zed_native::run(g, p, &mut Evaluator::new(World::new())).unwrap();
            let Value::Tuple(parts) = &o.value else {
                panic!("not a tuple: {}", o.value)
            };
            assert_eq!(parts.len(), k + 1);
            assert_eq!(parts[k], list(k - 1));
        };
        scaling::check_order("a native program of n constants [0, i, 0]", N, 1, run);
    });
}

/// Plan row FP-ops-scan: the scan walks the entries once, each step an entry step,
/// O(log n), and the merges of the canonical tree's blocks, fewer than n over the walk, so
/// the whole is O(n log n). The frames number fewer than 3n: n of the walk, and for each
/// entry one inner frame for its leaf and one per merge.
#[test]
fn the_elaborated_scan_runs_in_n_log_n() {
    let terms = elaborated("xs = [0, 1, 2];\nq = xs.scan((+)).last;");
    let run = |k: usize| {
        let v = Evaluator::new(World::new()).run(&terms[&k]).unwrap();
        assert_eq!(v, Value::Int((k as i64) * (k as i64 - 1) / 2));
    };
    scaling::check(
        "the elaborated `xs.scan((+)).last` over n entries",
        N_KERNEL,
        run,
    );
    ratio(
        "the elaborated `xs.scan((+)).last` over n entries, instructions",
        N_KERNEL,
        1,
        run,
    );
}

/// Plan row FP-ops-scan: `chunkBy` walks the entries once, one call of `f` and one entry
/// step each, then reindexes the n frames, O(n log n) in all.
#[test]
fn the_elaborated_chunk_by_runs_in_n_log_n() {
    // Each entry is its own run, so the outer level has n keys, the most it can have.
    let terms = elaborated("xs = [0, 1, 2];\nq = xs.chunkBy(x -> x).count;");
    let run = |k: usize| {
        let v = Evaluator::new(World::new()).run(&terms[&k]).unwrap();
        assert_eq!(v, Value::Int(k as i64));
    };
    scaling::check(
        "the elaborated `xs.chunkBy(f).count` over n entries",
        N_KERNEL,
        run,
    );
    ratio(
        "the elaborated `xs.chunkBy(f).count` over n entries, instructions",
        N_KERNEL,
        1,
        run,
    );
}

/// The term zedc elaborates `q` to, with `xs` and `ys` the n entries `{0 -> 0, …}`, run at n
/// and 8n and held under the limit for n log n work; `want(n)` is `q`'s value.
fn elaborated_on_two_lists(what: &str, q: &str, want: impl Fn(usize) -> Value + Sync) {
    // `xs` and `ys` are displays here, each bound at each run to the n entries around `q`'s
    // own term, as in the quantifier test above.
    let unit = elab(&format!("xs = [0, 1, 2];\nys = [0, 1, 2];\nq = {q};"))
        .unwrap_or_else(|e| panic!("{e:?}"));
    let def = |name: &str| unit.defs.iter().find(|d| d.name == name).unwrap();
    let (xs, ys, q) = (
        def("xs").kernel.clone(),
        def("ys").kernel.clone(),
        def("q").term.clone(),
    );
    let terms = scaling::inputs(N_KERNEL, |k| {
        let inner = Term::Let(ys.clone(), rc(entries(k)), q.clone());
        with_prelude(Term::Let(xs.clone(), rc(entries(k)), rc(inner)))
    });
    let run = |k: usize| {
        let v = Evaluator::new(World::new()).run(&terms[&k]).unwrap();
        assert_eq!(v, want(k));
    };
    scaling::check(what, N_KERNEL, run);
    ratio(&format!("{what}, instructions"), N_KERNEL, 1, run);
}

/// Step L5.2: `xs ++ ys` adds the m entries of `ys` to `xs`'s tree, O(m log(n + m)); the sum
/// reads every entry, so a result missing or misplacing one fails.
#[test]
fn a_concatenation_runs_in_n_log_n() {
    elaborated_on_two_lists(
        "the elaborated `(xs ++ ys).foldl(0, (a, x) -> (a * 3 + x) mod 1000003)` over n \
         entries each",
        "(xs ++ ys).foldl(0, (a, x) -> (a * 3 + x) mod 1000003)",
        |k| {
            let fold = |a: i64, x: i64| (a * 3 + x) % 1_000_003;
            let one = (0..k as i64).fold(0, fold);
            Value::Int((0..k as i64).fold(one, fold))
        },
    );
}

/// Step L5.2: `xs.zip(ys)` reads both sides at each of the n keys, O(n log n).
#[test]
fn a_zip_runs_in_n_log_n() {
    elaborated_on_two_lists(
        "the elaborated `xs.zip(ys).map(p -> p[0] * p[1]).sum` over n entries each",
        "xs.zip(ys).map(p -> p[0] * p[1]).sum",
        |k| Value::Int((0..k as i64).map(|x| x * x).sum()),
    );
}

#[test]
fn a_foldl_walk_runs_in_n_log_n() {
    let terms = scaling::inputs(N_KERNEL, |k| foldl_term(entries(k)));
    let run = |k: usize| {
        let want = (k as i64) * (k as i64 - 1) / 2;
        assert_eq!(eval(&terms[&k]).unwrap(), Value::Int(want));
    };
    scaling::check(
        "the kernel run of `xs.foldl(0, (a, x) -> a + x)` over n entries",
        N_KERNEL,
        run,
    );
    ratio(
        "the kernel run of `xs.foldl(0, (a, x) -> a + x)`, instructions",
        N_KERNEL,
        1,
        run,
    );
}

#[test]
fn first_and_last_cost_the_same_at_8n() {
    let fams = scaling::inputs(N_KERNEL, entries);
    for (p, word) in [(Prim::First, "first"), (Prim::Last, "last")] {
        let terms: HashMap<usize, Term> = (fams.iter())
            .map(|(&k, f)| (k, Term::Prim(p, vec![f.clone()])))
            .collect();
        let run = |k: usize| {
            let want = if p == Prim::First { 0 } else { k as i64 - 1 };
            assert_eq!(eval(&terms[&k]).unwrap(), Value::Int(want));
        };
        ratio(
            &format!("the kernel run of `xs.{word}` over n entries, instructions"),
            N_KERNEL,
            0,
            run,
        );
    }
}

/// The k steps `prev = acc; acc = [i] ++ prev; read` for i from 1 to k, from `acc = [0]`, the
/// read `read(i)` run at each step with `acc` (i + 1 entries) and `prev` (i entries) bound, its
/// value matched and dropped; the term's value is the count of the last `acc`. The `++` chain
/// costs O(k log k); a read that builds the joined list's ordered map costs O(i) at step i, so
/// O(k²) in all (plan row TEST-list-concat-no-map-build).
fn read_at_each_step(k: usize, read: &impl Fn(i64) -> Term) -> Term {
    let mut body = Term::Prim(Prim::Count, vec![var("acc")]);
    for i in (1..=k).rev() {
        let then = Term::Match(rc(read(i as i64)), vec![(Pattern::Wild, body)]);
        let joined = Term::Prim(Prim::ListConcat, vec![lit(one(i)), var("prev")]);
        body = let_("prev", var("acc"), let_("acc", joined, then));
    }
    let_("acc", lit(one(0)), body)
}

/// Holds [`read_at_each_step`] at n and 8n steps under 9 times (`scaling::PREFERRED`): each read
/// is O(1) or O(log n) on a list made by `++`, which COMPLEXITY.md F223 lists, and builds no map.
fn joined_read_ratio(what: &str, read: impl Fn(i64) -> Term) {
    joined_read_under(what, scaling::PREFERRED, read);
}

/// [`joined_read_ratio`] held under `bound` times.
fn joined_read_under(what: &str, bound: f64, read: impl Fn(i64) -> Term) {
    let terms = scaling::inputs(N_CONCAT, |k| read_at_each_step(k, &read));
    let run = |k: usize| assert_eq!(eval(&terms[&k]).unwrap(), Value::Int(k as i64 + 1));
    let what = format!("`{what}` after each of n `[x] ++ a`, instructions");
    let Some(r) = ratio(&what, N_CONCAT, 1, run) else {
        return;
    };
    assert!(r < bound, "{what}: {r:.2} times at 8n, over {bound:.2}");
}

fn acc() -> Term {
    var("acc")
}

fn prev() -> Term {
    var("prev")
}

/// The key in the middle of `acc` at step `i`.
fn middle(i: i64) -> Term {
    lit((i + 1) / 2)
}

#[test]
fn a_read_by_key_of_a_joined_list_builds_no_map() {
    joined_read_ratio("a[k]", |i| get(acc(), middle(i)));
    joined_read_ratio("a.0", |i| {
        Term::Prim(Prim::TupleGet, vec![acc(), middle(i)])
    });
    joined_read_ratio("a[k] at a rank", |i| {
        Term::Prim(Prim::At, vec![acc(), middle(i)])
    });
}

#[test]
fn in_and_count_of_a_joined_list_build_no_map() {
    joined_read_ratio("k in a", |i| Term::Prim(Prim::Has, vec![middle(i), acc()]));
    joined_read_ratio("a.count", |_| count(acc()));
}

#[test]
fn the_entry_steps_of_a_joined_list_build_no_map() {
    let entry = |i: i64| Term::Prim(Prim::Tuple, vec![middle(i), lit(0)]);
    joined_read_ratio("firstEntry(a)", |_| {
        Term::Prim(Prim::FirstEntry, vec![acc()])
    });
    joined_read_ratio("lastEntry(a)", |_| Term::Prim(Prim::LastEntry, vec![acc()]));
    joined_read_ratio("entryAfter(a, e)", |i| {
        Term::Prim(Prim::EntryAfter, vec![acc(), entry(i)])
    });
    joined_read_ratio("entryBefore(a, e)", |i| {
        Term::Prim(Prim::EntryBefore, vec![acc(), entry(i)])
    });
}

#[test]
fn first_last_and_concat_of_a_joined_list_build_no_map() {
    joined_read_ratio("a.first", |_| Term::Prim(Prim::First, vec![acc()]));
    joined_read_ratio("a.last", |_| Term::Prim(Prim::Last, vec![acc()]));
    // `a ++ a` builds O(log n) nodes at step i, with allocation, where the reads above build
    // none: proved O(log min(p, q)) for operands of p and q leaves (R. Hinze and R. Paterson,
    // "Finger trees: a simple general-purpose data structure", JFP 16(2):197-217, 2006,
    // doi:10.1017/s0956796805005769, read 2026-11-21: sec. 3.3, p. 205, "the total time taken
    // is Θ(log(min{n1, n2}))"; the leaves here are lists, so p and q count lists; more at
    // zedc-elab `fp_ops.rs` `list_concat_term`; this test measures the ratio, it does not
    // prove the bound), so the
    // chain is O(n log n), held to 8 ln(8n) / ln(n), 10.41 at
    // n = 1000, the ratio of n log n at 8n (measured 9.92, 2026-11-16, load 40; 10.21 with
    // short leaves merged at a join, `chain::LEAF` 16, 2026-11-17, load 61 to 74, COMPLEXITY.md
    // F223d).
    let n = N_CONCAT as f64;
    let n_log_n = FACTOR as f64 * (FACTOR as f64 * n).ln() / n.ln();
    joined_read_under("a ++ a", n_log_n, |_| {
        Term::Prim(Prim::ListConcat, vec![acc(), acc()])
    });
}

/// The comparisons of `acc` with `prev`, one entry shorter and different at the first entry,
/// and with a list of its size made by another `++` that differs at the first entry: each
/// decided by the counts or the first entries, O(log n). Not here: `a == a` and `a <= a`, which
/// read every entry of any family, a map too, since a NaN inside is not equal to itself (the
/// IEEE 754 relations, `Relation::SurfaceEq`); `kernel::comparisons_of_a_joined_list_build_no_map`
/// shows that they build no map.
#[test]
fn comparisons_of_a_joined_list_build_no_map() {
    let other = |i: i64| Term::Prim(Prim::ListConcat, vec![lit(one(i as usize + 1)), prev()]);
    for p in [Prim::Eq, Prim::Ne, Prim::Lt, Prim::Ge, Prim::Min, Prim::Max] {
        joined_read_ratio(&format!("{p:?}(a, prev)"), |_| {
            Term::Prim(p, vec![acc(), prev()])
        });
    }
    joined_read_ratio("a == b, one size", |i| eq(acc(), other(i)));
    joined_read_ratio("a < b, one size", |i| lt(acc(), other(i)));
}

/// A list made by `++` read as a key of a family: the hash reads its count, and the order of
/// keys its first entries, O(log n).
#[test]
fn a_joined_list_as_a_key_builds_no_map() {
    let keyed = lit(Value::Family(Family::of([
        (one(usize::MAX >> 1), 0),
        (Value::Family(Family::of([(0, -2), (1, -3)])), 1),
    ])));
    joined_read_ratio("a in keyed", |_| {
        Term::Prim(Prim::Has, vec![acc(), keyed.clone()])
    });
}

/// The k steps `acc = [i] ++ acc` for i from 1 to k, from `acc = [0]`, made here by
/// `Family::concat`, with `read(&acc)` run after each. The chain costs O(k log k); a read that
/// builds the joined list's map costs O(i) at step i, so O(k²) in all.
fn rust_read_at_each_step(k: usize, read: &impl Fn(&Family)) {
    let list = |x: usize| Family::of([(0, x as i64)]);
    let mut acc = list(0);
    for i in 1..=k {
        acc = list(i).concat(&acc).unwrap();
        read(&acc);
    }
}

/// A union holding the list made by `++` beneath a key, run after each of n `[x] ++ a` (plan row
/// TEST-list-map-build-callers-complete): beside a key the other side lacks, the list is shared
/// whole, O(1); under a leaf of the other side, the collision is at the list's first keypath,
/// read in O(log n). Each is held under 9 times at 8n.
#[test]
fn a_union_holding_a_joined_list_builds_no_map() {
    let at = |k: i64, v: Value| Family::of([(Value::Int(k), v)]);
    let leaf = at(0, Value::Int(1));
    let five = at(1, Value::Int(5));
    for (what, collides) in [
        ("{0 -> a} ∪ {1 -> 5}", false),
        ("{0 -> 1} ∪ {0 -> a}", true),
    ] {
        let read = |acc: &Family| {
            let held = at(0, Value::Family(acc.clone()));
            match collides {
                false => assert_eq!(held.union(&five).unwrap().len(), 2),
                true => assert!(leaf.union(&held).is_err()),
            }
        };
        let what = format!("`{what}` after each of n `[x] ++ a`, instructions");
        let Some(r) = ratio(&what, N_CONCAT, 1, |k| rust_read_at_each_step(k, &read)) else {
            return;
        };
        assert!(
            r < scaling::PREFERRED,
            "{what}: {r:.2} times at 8n, over {:.2}",
            scaling::PREFERRED
        );
    }
}

/// `zedc run` of `body(xs)`, `xs` a string-keyed display of n entries `"k0000" -> 0, …`,
/// printing `want(n)`.
fn whole_path(name: &str, body: &str, want: impl Fn(usize) -> String + Sync) {
    let srcs: HashMap<usize, _> = scaling::inputs(N_PROGRAM, |k| {
        let xs = (0..k)
            .map(|x| format!("\"k{x:05}\" -> {x}"))
            .collect::<Vec<_>>()
            .join(", ");
        let text = body.replace("XS", &format!("{{{xs}}}"));
        program(&format!("{name}_{k}"), &text)
    });
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k], &[], &[]);
        assert_eq!(ran.stderr, "");
        assert_eq!(ran.stdout, want(k));
    };
    scaling::check(
        &format!("`zedc run` of `{body}` over n keyed entries"),
        N_PROGRAM,
        run,
    );
}

#[test]
fn the_words_on_a_keyed_display_run_in_n_log_n() {
    whole_path(
        "words",
        "${XS.count} ${XS.sum} ${XS.any(x -> x < 0)} ${XS.all(x -> x >= 0)} \
         ${XS.find(x -> x == 7) == \"k00007\"} ${XS.last} \
         ${XS.foldl(0, (a, x) -> a + x)} ${XS.foldr((x, a) -> a + x, 0)}",
        |k| {
            let sum = k * (k - 1) / 2;
            format!("{k} {sum} false true true {} {sum} {sum}\n", k - 1)
        },
    );
}

/// Plan row FP-ops-scan: `.scan` and `.chunkBy` through `zedc run`.
#[test]
fn scan_and_chunk_by_on_a_keyed_display_run_in_n_log_n() {
    whole_path(
        "scans",
        "${XS.scan((+)).last} ${XS.scan(max).last} ${XS.chunkBy(x -> x < 5).count}",
        |k| format!("{} {} 2\n", k * (k - 1) / 2, k - 1),
    );
}

/// Characters of a string a string function reads (plan row FP-ops-strings).
const N_TEXT: usize = 100_000;

/// The first `n` characters of a text holding empty pieces between commas and every line end:
/// `\n`, `\r\n`, a lone `\r`, and two line ends in a row.
fn text(n: usize) -> String {
    "ab,,c\r\nd\re\n\n,x".chars().cycle().take(n).collect()
}

fn str_term(x: &str) -> Term {
    lit(Value::str(x))
}

/// Step L3.2's test: the join law `concat(s.split(sep), sep: sep) == s` for nonempty `sep` on
/// generated strings of n and 8n characters, each split and joined in O(n). An empty `sep` is
/// the failure `#emptySeparator` (author decision P314), given before the text is read.
#[test]
fn split_then_concat_gives_the_text_back_in_linear_time() {
    for sep in [",", "\r\n"] {
        let terms = scaling::inputs(N_TEXT, |k| {
            let pieces = Term::Prim(Prim::Split, vec![str_term(&text(k)), str_term(sep)]);
            let term = Term::Prim(Prim::Join, vec![pieces, str_term(sep)]);
            (term, Value::str(&text(k)))
        });
        let run = |k: usize| {
            let (term, want) = &terms[&k];
            assert_eq!(&eval(term).unwrap(), want);
        };
        scaling::check_order(
            &format!(
                "the kernel run of `concat(s.split({sep:?}), sep: {sep:?})` over n characters"
            ),
            N_TEXT,
            1,
            run,
        );
    }
}

#[test]
fn lines_runs_in_linear_time() {
    let terms = scaling::inputs(N_TEXT, |k| {
        Term::Prim(
            Prim::Count,
            vec![Term::Prim(Prim::Lines, vec![str_term(&text(k))])],
        )
    });
    // Each cycle of 14 characters holds four line ends, the last two in a row.
    let run = |k: usize| match eval(&terms[&k]).unwrap() {
        Value::Int(c) => assert!((c as usize).abs_diff(4 * k / 14) <= 4, "{c} lines"),
        v => panic!("a count {v:?}"),
    };
    scaling::check_order(
        "the kernel run of `s.lines` over n characters",
        N_TEXT,
        1,
        run,
    );
}

/// Step L3.2's test: n and 8n pieces joined in O(n) in all.
#[test]
fn concat_of_n_pieces_runs_in_linear_time() {
    let terms = scaling::inputs(N_TEXT, |k| {
        let pieces = (0..k as i64).map(|x| {
            (
                Value::Int(x),
                Value::str(if x % 3 == 0 { "" } else { "ab" }),
            )
        });
        let pieces = lit(Value::Family(Family::of(pieces.collect::<Vec<_>>())));
        Term::Prim(Prim::Join, vec![pieces, str_term(", ")])
    });
    let run = |k: usize| match eval(&terms[&k]).unwrap() {
        Value::Str(s) => assert_eq!(s.len(), 2 * (k - k.div_ceil(3)) + 2 * (k - 1)),
        v => panic!("a string {v:?}"),
    };
    scaling::check_order(
        "the kernel run of `concat(pieces, sep: \", \")` over n pieces",
        N_TEXT,
        1,
        run,
    );
}

/// Calls of a generic function, or links of a chain of them, of the checked benchmarks below.
const N_CALLS: usize = 100;

/// `split`, `concat` and `lines` on a generic function's parameters, each operand checked at
/// each call by one need (plan row FP-ops-generic-strings).
const STRINGS: &str = "w(positional s, positional d) = \
                       (s.split(d).count, concat(s.split(d), sep: d), s.lines.count);\n";

#[test]
fn n_calls_of_a_generic_function_of_the_string_words_run_in_linear_time() {
    // The calls alternate two separators and strings, so each call's need is checked on its
    // own types (plan row FP-ops-generic-strings).
    let srcs = scaling::inputs(N_CALLS, |n| {
        let calls = (0..n)
            .map(|i| match i % 2 {
                0 => format!("x{i} = w(\"a,b,{i}\", \",\");\n"),
                _ => format!("x{i} = w(\"a b {i}\", \" \");\n"),
            })
            .collect::<String>();
        format!("{STRINGS}{calls}")
    });
    let run = |n: usize| {
        let i = n - 1;
        assert_eq!(
            value(&srcs[&n], &format!("x{i}")),
            format!("(3, \"a b {i}\", 1)")
        );
    };
    scaling::check(
        "n calls of a generic function of `split`, `concat` and `lines`, alternately at two \
         separators, whole path",
        N_CALLS,
        run,
    );
}

#[test]
fn a_chain_of_n_generic_functions_passing_on_the_string_words_runs_in_linear_time() {
    // `w`'s need waits on `g0`'s parameters, and each `g{i}` passes it on, so it is checked
    // once at each of the two calls at the chain's top (plan row FP-ops-generic-strings).
    let srcs = scaling::inputs(N_CALLS, |n| {
        let chain = (1..n)
            .map(|i| format!("g{i}(positional s, positional d) = g{}(s, d);\n", i - 1))
            .collect::<String>();
        let top = n - 1;
        format!(
            "{STRINGS}g0(positional s, positional d) = w(s, d);\n{chain}\
             a = (g{top}(\"a,b\", \",\"), g{top}(\"x y\", \" \"));\n"
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "a"), "((2, \"a,b\", 1), (2, \"x y\", 1))");
    };
    scaling::check(
        "a chain of n generic functions passing a string and a separator to `split`, `concat` \
         and `lines`, whole path",
        N_CALLS,
        run,
    );
}

/// `++` on a generic function's parameter beside a list, checked at each call by one need
/// (plan row FP-ops-concat-fold-acc).
const CONCAT: &str = "app(positional a) = a ++ [1];\n";

#[test]
fn n_calls_of_a_generic_function_of_concatenation_run_in_linear_time() {
    // The calls alternate a list and a range, so each call's need is checked on its own type.
    let srcs = scaling::inputs(N_CALLS, |n| {
        let calls = (0..n)
            .map(|i| match i % 2 {
                0 => format!("x{i} = app([{i}])[0];\n"),
                _ => format!("x{i} = app(0 ..< {i})[{i}];\n"),
            })
            .collect::<String>();
        format!("{CONCAT}{calls}")
    });
    let run = |n: usize| {
        let i = n - 1;
        let want = match i % 2 {
            0 => i.to_string(),
            _ => "1".to_string(),
        };
        assert_eq!(value(&srcs[&n], &format!("x{i}")), want);
    };
    scaling::check(
        "n calls of a generic function of `++`, alternately on a list and a range, whole path",
        N_CALLS,
        run,
    );
}

#[test]
fn a_chain_of_n_generic_functions_passing_on_concatenation_runs_in_linear_time() {
    // `app`'s need waits on `g0`'s parameter, and each `g{i}` passes it on, so it is checked
    // once at each of the two calls at the chain's top (plan row FP-ops-concat-fold-acc).
    let srcs = scaling::inputs(N_CALLS, |n| {
        let chain = (1..n)
            .map(|i| format!("g{i}(positional a) = g{}(a);\n", i - 1))
            .collect::<String>();
        let top = n - 1;
        format!(
            "{CONCAT}g0(positional a) = app(a);\n{chain}\
             a = (g{top}([5])[1], g{top}(0 ..< 2)[2]);\n"
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "a"), "(1, 1)");
    };
    scaling::check(
        "a chain of n generic functions passing a list and a range to `++`, whole path",
        N_CALLS,
        run,
    );
}

/// `zip` of a generic function's two parameters, checked at each call by one need on each
/// operand's class (plan row ZIP-generic-operands).
const ZIP: &str = "pairUp(positional a, positional b) = a.zip(b);\n";

#[test]
fn n_calls_of_a_generic_function_of_zip_run_in_linear_time() {
    // The calls alternate two lists and a range beside a map of it (a range's keys are its
    // values, which `map` keeps), so each call's need is checked on its own types.
    let srcs = scaling::inputs(N_CALLS, |n| {
        let calls = (0..n)
            .map(|i| match i % 2 {
                0 => format!("x{i} = pairUp([{i}], [1])[0][0];\n"),
                _ => format!(
                    "x{i} = pairUp(0 ..< {m}, (0 ..< {m}).map(k -> k + 1))[{i}][1];\n",
                    m = i + 1
                ),
            })
            .collect::<String>();
        format!("{ZIP}{calls}")
    });
    let run = |n: usize| {
        let i = n - 1;
        let want = match i % 2 {
            0 => i.to_string(),
            _ => (i + 1).to_string(),
        };
        assert_eq!(value(&srcs[&n], &format!("x{i}")), want);
    };
    scaling::check(
        "n calls of a generic function of `zip`, alternately on lists and on a range and its \
         map, whole path",
        N_CALLS,
        run,
    );
}

#[test]
fn a_chain_of_n_generic_functions_passing_on_zip_runs_in_linear_time() {
    // `pairUp`'s needs wait on `g0`'s parameters, and each `g{i}` passes them on, so they are
    // checked once at each of the two calls at the chain's top (plan row
    // ZIP-generic-operands).
    let srcs = scaling::inputs(N_CALLS, |n| {
        let chain = (1..n)
            .map(|i| format!("g{i}(positional a, positional b) = g{}(a, b);\n", i - 1))
            .collect::<String>();
        let top = n - 1;
        format!(
            "{ZIP}g0(positional a, positional b) = pairUp(a, b);\n{chain}\
             a = (g{top}([5], [6])[0][1], g{top}(0 ..< 2, (0 ..< 2).map(k -> k + 2))[1][1]);\n"
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "a"), "(6, 3)");
    };
    scaling::check(
        "a chain of n generic functions passing two lists, and a range and its map, to `zip`, \
         whole path",
        N_CALLS,
        run,
    );
}

/// Step L5.2 through `zedc run`: a `zip` of two keyed displays of n entries with the same keys.
#[test]
fn a_zip_of_keyed_displays_runs_in_n_log_n() {
    whole_path("zip", "${XS.zip(XS).map(p -> p[0] + p[1]).sum}", |k| {
        format!("{}\n", k * (k - 1))
    });
}

/// Plan row RANGE-literal-keys: checking n statements, the i-th
/// `((0 ..< i) ++ [i]).zip(0 ..= i).count`, is linear in n. A range with literal ends keeps
/// its keys as two ends, O(1) whatever i, so the unit checks in O(n); listing each range's i
/// keys in its key type, as an array display's, would check it in O(n²).
#[test]
fn ranges_with_literal_ends_check_in_linear_time() {
    const N_UNIT: usize = 300;
    let units = scaling::inputs(N_UNIT, |k| {
        let text: String = (0..k)
            .map(|i| format!("x{i} = ((0 ..< {i}) ++ [{i}]).zip(0 ..= {i}).count;\n"))
            .collect();
        checked(&text)
    });
    scaling::check(
        "checking n statements `((0 ..< i) ++ [i]).zip(0 ..= i).count`",
        N_UNIT,
        |k| assert!(units[&k].check().errors.is_empty()),
    );
}

/// Plan row RANGE-literal-reads: checking n statements, the i-th `(0 ..< i + 1)[i]` and
/// `(i ..< 2 ^ 70)[i]`, is linear in n. A read of exact keys at a known key tests the key
/// against the range's two ends, O(1) whatever the range's size; listing the keys, as the key
/// type of an array display does, would check it in O(n²), and a range past 64 bits not at all.
#[test]
fn reads_of_exact_keys_at_known_keys_check_in_linear_time() {
    const N_UNIT: usize = 300;
    let units = scaling::inputs(N_UNIT, |k| {
        let text: String = (0..k)
            .map(|i| format!("x{i} = (0 ..< {i} + 1)[{i}];\ny{i} = ({i} ..< 2 ^ 70)[{i}];\n"))
            .collect();
        checked(&text)
    });
    scaling::check(
        "checking n statements `(0 ..< i + 1)[i]` and `(i ..< 2 ^ 70)[i]`",
        N_UNIT,
        |k| assert!(units[&k].check().errors.is_empty()),
    );
}

/// Plan row RANGE-read-key-intervals: checking n functions, the i-th reading `(i ..< i + 3)`
/// at a key a ranged parameter bounds, at one an `if` bounds, and in the call form, each
/// declared to give an `int` with no miss, is linear in n. Each read tests the key's interval
/// set against the range's two ends, O(1) whatever the range's size; listing the keys would
/// check it in O(n²).
#[test]
fn reads_of_exact_keys_at_bounded_keys_check_in_linear_time() {
    const N_UNIT: usize = 300;
    let units = scaling::inputs(N_UNIT, |k| {
        let text: String = (0..k)
            .map(|i| {
                let (a, b, c) = (i, i + 2, i + 3);
                format!(
                    "rp{i}(k: int[{a}..={b}]) = ({a} ..< {c})[k];\n\
                     rt{i}(k: int) = if k >= {a} && k < {c} {{ ({a} ..< {c})[k] }} else {{ 0 }};\n\
                     rc{i}(k: int[{a}..={b}]) = ({a} ..< {c})(k);\n"
                )
            })
            .collect();
        checked(&text)
    });
    // Each function's result is an `int`, with no miss.
    let run = |k: usize| {
        let info = units[&k].check();
        assert!(info.errors.is_empty());
        assert_eq!(info.sigs.len(), 3 * k);
        for s in info.sigs.values() {
            assert!(!s.to_string().contains('#'), "{s}");
        }
    };
    scaling::check(
        "checking n functions reading `(i ..< i + 3)` at a key a parameter or a test bounds",
        N_UNIT,
        run,
    );
}

/// Plan row ZIP-count-facts: checking a `main` of n statements, the i-th
/// `x{i} = x{i-1}.map(v -> v)` and a line `c{i}` of `x0.zip(x{i}).count`, with `x0` the
/// lines of `m.stdin`, is linear in n. A port's keys are known to no type, so each zip finds
/// that `x{i}` has `x0`'s keys by following the chain of `map`s, which the memo of each name's
/// keyspace walks once in all (`Ck::keyspace`); walking it again at each zip would check the
/// unit in O(n²). The lines are pushed once, as one family (row FAIL-push-twice-old-benches:
/// a push per statement is two pushes to one port in one run, refused by DESIGN step L1.19).
#[test]
fn zips_along_a_chain_of_maps_check_in_linear_time() {
    const N_UNIT: usize = 300;
    let units = scaling::inputs(N_UNIT, |k| {
        let body: String = (1..k)
            .map(|i| {
                format!(
                    "  x{i} = x{}.map(v -> v);\n  c{i} = \"${{x0.zip(x{i}).count}}\";\n",
                    i - 1
                )
            })
            .collect();
        let lines: Vec<String> = (1..k).map(|i| format!("c{i}")).collect();
        checked(&format!(
            "main(m: MainArgs) {{\n  x0 = m.stdin;\n{body}  m.stdout <- [{}];\n}}\n",
            lines.join(", ")
        ))
    });
    scaling::check(
        "checking n statements `x{i} = x{i-1}.map(v -> v)` and `x0.zip(x{i})`, `x0` a port's \
         lines",
        N_UNIT,
        |k| assert!(units[&k].check().errors.is_empty()),
    );
}

/// Plan row ZIP-count-facts: checking n functions, the first zipping its two parameters and
/// each other passing its own two on to the one before, is linear in n. Each function's need
/// is found once, from its body, and each call meets the callee's needs once
/// (`Ck::record_fn`, `Ck::ks_call`).
#[test]
fn a_need_passed_through_a_chain_of_calls_checks_in_linear_time() {
    const N_UNIT: usize = 300;
    let units = scaling::inputs(N_UNIT, |k| {
        let text: String =
            // Named `pass{i}`: `f32` and `f64` would name the prelude's types.
            std::iter::once("pass0(positional a: Lines, positional b: Lines) = a.zip(b);\n".into())
                .chain((1..k).map(|i| {
                    format!(
                        "pass{i}(positional a: Lines, positional b: Lines) = pass{}(a, b);\n",
                        i - 1
                    )
                }))
                .collect::<String>();
        checked(&text)
    });
    scaling::check(
        "checking n functions, each passing its two parameters to the one before, the first \
         zipping them",
        N_UNIT,
        |k| assert!(units[&k].check().errors.is_empty()),
    );
}

/// A count of entry steps, the work of a walk by its construction: `foldl` over n entries
/// takes n + 1 frames, so the frames at 8n are near 8 times those at n.
#[test]
fn a_foldl_walk_takes_one_frame_per_entry() {
    let frames = |k: usize| {
        // The walk's `gen` family's size, in place of its last accumulator.
        let size = let_("gn", foldl_frames(), count(var("gn")));
        match eval(&let_("xs", entries(k), size)).unwrap() {
            Value::Int(c) => c as u64,
            v => panic!("a count {v:?}"),
        }
    };
    let (small, large) = (frames(N_KERNEL), frames(FACTOR * N_KERNEL));
    assert_eq!(small, N_KERNEL as u64 + 1);
    hold_linear("the frames of a `foldl` walk", "frames", small, large);
}
