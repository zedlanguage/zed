//! Benchmarks of plan row FP-ops-run, run apart from the correctness tests
//! (`tools/run_tests.sh --bench`): the walk of a level in key order that `.any`, `.all`,
//! `.find`, `.foldl` and `.foldr` elaborate to, `.first` and `.last`, at n entries and at 8n,
//! and the same words through `zedc run`. Step L3.15a's own test is here too: a quantifier
//! whose deciding entry is the k-th, k fixed, costs the same at n and at 8n.
//!
//! The kernel runs time the terms zedc elaborates the words to (zedc-elab, walk/fp_ops.rs),
//! built before the runs; the whole-path runs time `zedc run` of a program whose display holds
//! the entries, so they measure the parse, the check, the elaboration and the run together.

use std::collections::HashMap;

use zed_kernel::term::GuardPos;
use zed_kernel::term::build::{lam, let_, lit, var};
use zed_kernel::{Evaluator, Family, Pattern, Prim, Term, Value, World, eval};
use zed_tests::kernel::*;
use zed_tests::scaling::{self, FACTOR, Meter, hold, hold_linear};

use super::program;
use zed_tests::step_helpers::l01_16_elaboration::{checked, elab, with_prelude};
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
/// `n^power`, and returns the ratio.
fn ratio(what: &str, n: usize, power: u32, run: impl Fn(usize)) -> f64 {
    let mut meter = Meter::new();
    let (small, large) = (
        least(&mut meter, n, &run),
        least(&mut meter, FACTOR * n, &run),
    );
    hold(what, meter.unit(), small, large, power)
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
    // A parameter of type `[int]` is not compiled yet, so `xs` is a display here, and each run
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
