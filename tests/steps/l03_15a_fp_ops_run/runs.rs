//! Each case is an expression a program writes with `${…}`, and the kernel term the spec
//! defines it by, run on the M0 reference evaluator: the program's output must be the value the
//! model gives, from `zedc run` and from an executable `zedc build` makes. `.count` is `count`;
//! `.sum` and `.reduce(op)` are `fold(m, op)` with the operator's identity (the method
//! register's `sum` and `reduce` rows); `.any(p)` and `.all(p)` are `p` mapped over the
//! entries and folded by `||` and `&&` (step L3.15a, for a `p` that never fails); `.find(p)` is
//! the least key `p` holds at, or `#none`; `.first` and `.last` are the entries at the least
//! and greatest key; `.foldl` and `.foldr` are the folds of zed_tests::kernel. The models of
//! `split` and `lines` are the families of strings step L3.2 gives, and `concat(m, sep: s)` is
//! `m` reduced by `(a, b) -> a ++ s ++ b` with `""` for an empty `m`, so no model uses the
//! primitives it checks.

use zed_kernel::term::build::{let_, lit, var};
use zed_kernel::{Family, Pattern, Prim, Term, Value, eval};
use zed_tests::kernel::*;
use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable};

use super::{program, run};

fn i(n: i64) -> Value {
    Value::Int(n)
}

/// `[x0, x1, …]`: keyed by position from 0.
fn list(xs: &[i64]) -> Term {
    let entries = (xs.iter().enumerate()).map(|(k, &x)| (i(k as i64), i(x)));
    lit(Value::Family(Family::of(entries.collect::<Vec<_>>())))
}

/// `{"k0" -> x0, …}`: keyed by string.
fn named(entries: &[(&str, i64)]) -> Term {
    let entries = entries.iter().map(|&(k, x)| (s(k), i(x)));
    lit(Value::Family(Family::of(entries.collect::<Vec<_>>())))
}

/// `m >< (op)` with `identity` as the fold of an empty family.
fn reduce(m: Term, op: Prim, identity: Option<Value>) -> Term {
    fold(m, func(|[a, b]| bin(op, a, b)), identity.map(lit))
}

/// `e` with the bare atom `#atom` replaced by `d`.
fn or(e: Term, atom: &str, d: Term) -> Term {
    let arms = vec![
        (Pattern::Atom(atom.into(), vec![]), d),
        (Pattern::Wild, var("$e")),
    ];
    let_("$e", e, Term::Match(rc(var("$e")), arms))
}

/// The least key of `m`, `#empty` when it has none.
fn least_key(m: Term) -> Term {
    reduce(keyset(m), Prim::Min, None)
}

/// The greatest key of `m`, `#empty` when it has none.
fn greatest_key(m: Term) -> Term {
    reduce(keyset(m), Prim::Max, None)
}

/// `m.find(p) else d` over int keys: the least key whose entry `p` holds of.
fn find(m: Term, p: impl Fn(Term) -> Term, d: i64) -> Term {
    let kept = discard(m, func(|[_, v]| p(v)));
    or(least_key(kept), "empty", lit(d))
}

/// `m.chunkBy(f)` on a list (DESIGN.md sec:type_language, the `m.chunkBy(f)` row): the
/// reindex `(t, v) ↦ ((run(t), t), v)`, `run(t)` the number of keys `j` in `1..=t` at which
/// `f` gives a value other than at `j - 1`.
fn chunk_by(m: Term, f: impl Fn(Term) -> Term + Copy) -> Term {
    shared(m, |m| {
        let run = |t: Term| {
            count(discard_with(m.clone(), |p, v| {
                let j = key(p, 0);
                let before = f(get(m.clone(), sub(j.clone(), lit(1))));
                and(and(lt(lit(0), j.clone()), le(j, t)), not(eq(f(v), before)))
            }))
        };
        let kf = func(|[p, _]| path(vec![run(key(p.clone(), 0)), key(p, 0)]));
        reindex(m.clone(), kf, func(|[_, v]| v))
    })
}

/// `[s0, s1, …]`: strings keyed by position from 0, the model of what `split` and `lines` give.
fn strings(xs: &[&str]) -> Term {
    let entries = (xs.iter().enumerate()).map(|(k, &x)| (i(k as i64), s(x)));
    lit(Value::Family(Family::of(entries.collect::<Vec<_>>())))
}

/// `concat(m, sep: sep)`: `m` reduced by `(a, b) -> a ++ sep ++ b`, an associative operator,
/// with `""` as the reduction of an empty family (step L3.2).
fn joined(m: Term, sep: &str) -> Term {
    let op = func(|[a, b]| bin(Prim::Concat, bin(Prim::Concat, a, lit(s(sep))), b));
    fold(m, op, Some(lit(s(""))))
}

/// The cases: a name, the expression a program writes, and its model.
fn cases() -> Vec<(&'static str, &'static str, Term)> {
    let xs = || list(&[3, 1, 4, 1, 5]);
    let ab = || named(&[("b", 2), ("a", 5), ("c", 7)]);
    let big = |v: Term| lt(lit(3), v);
    vec![
        ("count_of_a_list", "${[3, 1, 4, 1, 5].count}", count(xs())),
        (
            "count_of_a_map",
            "${{\"b\" -> 2, \"a\" -> 5, \"c\" -> 7}.count}",
            count(ab()),
        ),
        (
            "sum_of_a_list",
            "${[3, 1, 4, 1, 5].sum}",
            reduce(xs(), Prim::Add, Some(i(0))),
        ),
        (
            "sum_of_a_map",
            "${{\"b\" -> 2, \"a\" -> 5, \"c\" -> 7}.sum}",
            reduce(ab(), Prim::Add, Some(i(0))),
        ),
        (
            "reduce_by_times",
            "${[3, 1, 4, 1, 5].reduce((*))}",
            reduce(xs(), Prim::Mul, Some(i(1))),
        ),
        (
            "reduce_by_max",
            "${[3, 1, 4, 1, 5].reduce(max)}",
            reduce(xs(), Prim::Max, None),
        ),
        (
            "any_holds",
            "${[3, 1, 4, 1, 5].any(x -> x > 3)}",
            reduce(map(xs(), big), Prim::Or, Some(Value::Bool(false))),
        ),
        (
            "all_fails",
            "${[3, 1, 4, 1, 5].all(x -> x > 3)}",
            reduce(map(xs(), big), Prim::And, Some(Value::Bool(true))),
        ),
        (
            "all_of_a_map",
            "${{\"b\" -> 2, \"a\" -> 5, \"c\" -> 7}.all(x -> x > 1)}",
            reduce(
                map(ab(), |v| lt(lit(1), v)),
                Prim::And,
                Some(Value::Bool(true)),
            ),
        ),
        (
            "find_the_first_key",
            "${[3, 1, 4, 1, 5].find(x -> x > 3) else -1}",
            find(xs(), big, -1),
        ),
        (
            "find_no_key",
            "${[3, 1, 4, 1, 5].find(x -> x > 9) else -1}",
            find(xs(), |v| lt(lit(9), v), -1),
        ),
        (
            "first_of_a_list",
            "${[3, 1, 4, 1, 5].first}",
            get(xs(), least_key(xs())),
        ),
        (
            "last_of_a_list",
            "${[3, 1, 4, 1, 5].last}",
            get(xs(), greatest_key(xs())),
        ),
        (
            "foldl_in_order",
            "${[3, 1, 4, 1, 5].foldl(0, (a, x) -> a * 10 + x)}",
            foldl(xs(), lit(0), func(|[a, x]| add(mul(a, lit(10)), x))),
        ),
        (
            "foldr_in_order",
            "${[3, 1, 4, 1, 5].foldr((x, a) -> a * 10 + x, 0)}",
            foldr(xs(), func(|[x, a]| add(mul(a, lit(10)), x)), lit(0)),
        ),
        (
            "scan_by_plus",
            "${[3, 1, 4, 1, 5].scan((+))}",
            scan(xs(), func(|[a, b]| add(a, b))),
        ),
        (
            "scan_by_max",
            "${[3, 1, 4, 1, 5].scan(max)}",
            scan(xs(), func(|[a, b]| bin(Prim::Max, a, b))),
        ),
        (
            "scan_of_a_map",
            "${{\"b\" -> 2, \"a\" -> 5, \"c\" -> 7}.scan((*))}",
            shared(ab(), |m| {
                fam_with(m.clone(), |k| {
                    let upto = discard_with(m, |p, _| not(lt(k, key(p, 0))));
                    fold(upto, func(|[a, b]| mul(a, b)), None)
                })
            }),
        ),
        (
            "chunk_by_a_test",
            "${[3, 1, 4, 1, 5].chunkBy(x -> x > 3)}",
            chunk_by(xs(), big),
        ),
        (
            "concat_without_sep",
            "${concat([\"p\", \"q\", \"r\"])}",
            joined(strings(&["p", "q", "r"]), ""),
        ),
        (
            "split_keeps_empty_pieces",
            "${concat(\"a,,b,\".split(\",\"), sep: \"|\")}",
            joined(strings(&["a", "", "b", ""]), "|"),
        ),
        (
            "split_by_the_empty_separator",
            "${concat(\"hé€\".split(\"\"), sep: \".\")}",
            joined(strings(&["h", "é", "€"]), "."),
        ),
        (
            "lines_at_each_line_end",
            "${concat(\"a\\r\\nb\\rc\\n\\nd\\n\".lines, sep: \"|\")}",
            joined(strings(&["a", "b", "c", "", "d"]), "|"),
        ),
        (
            "count_of_lines",
            "${\"x\\n\".lines.count}",
            count(strings(&["x"])),
        ),
    ]
}

/// What `${…}` prints of the model's value: a string as its characters, without the quotes of
/// its literal, and any other value as it is written.
fn expected(model: &Term) -> String {
    match eval(model) {
        Ok(Value::Str(s)) => format!("{s}\n"),
        Ok(v) => format!("{v}\n"),
        Err(e) => panic!("the model failed: {e:?}"),
    }
}

#[test]
fn each_case_run_by_the_interpreter_gives_the_models_value() {
    for (name, body, model) in cases() {
        let ran = run(name, body);
        assert_eq!(ran.stderr, "", "{name}");
        assert_eq!(ran.status, 0, "{name}");
        assert_eq!(ran.stdout, expected(&model), "{name}: {body}");
    }
}

#[test]
fn an_executable_gives_each_cases_value() {
    let cases = cases();
    let body = (cases.iter().map(|(_, b, _)| *b))
        .collect::<Vec<_>>()
        .join("\\n");
    let src = program("native", &body);
    let exe = dir("l03_15a_fp_ops_run/native").join("native");
    built(&src, &exe);
    let ran = executable(&exe, &[], &[]);
    assert_eq!(ran.stderr, "");
    assert_eq!(ran.status, 0);
    let want = (cases.iter().map(|(_, _, m)| expected(m))).collect::<Vec<_>>();
    // The program pushes one text, and `stdout` ends it with a newline as it does each push.
    assert_eq!(ran.stdout, want.concat());
}
