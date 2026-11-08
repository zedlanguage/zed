//! The transfer's time against the size of the term (the rule of low complexity, DESIGN.md
//! Part G): a name bound once is followed once however often it is read, and a test in guard
//! position is transferred once for each outcome.

use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Classes, Demand, Domains, exact_preimage, preimage, relations};

use super::{doms, listed, pre_listed, shown};

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

/// `x1 = i + i; x2 = x1 + x1; …; xk >= 0`: each name read twice.
fn doubling(k: usize) -> Term {
    let mut body = prim(Prim::Ge, var(&format!("x{k}")), int(0));
    for i in (1..=k).rev() {
        let prev = if i == 1 {
            "i".to_string()
        } else {
            format!("x{}", i - 1)
        };
        let e = prim(Prim::Add, var(&prev), var(&prev));
        body = Term::Let(format!("x{i}").into(), Shared::new(e), Shared::new(body));
    }
    body
}

/// `f0 = (v) -> v; f1 = (v) -> max(f0(v), f0(v + d)); …; fk(i) >= 0`: each function calls
/// the one before it twice, with arguments that differ when `d` is 1 and agree when it is 0.
fn calls(k: usize, d: i64) -> Term {
    let call = |j: usize, a: Term| Term::App(Shared::new(var(&format!("f{j}"))), vec![a]);
    let mut body = prim(Prim::Ge, call(k, var("i")), int(0));
    for j in (0..=k).rev() {
        let e = if j == 0 {
            var("v")
        } else {
            let second = if d == 0 {
                var("v")
            } else {
                prim(Prim::Add, var("v"), int(d))
            };
            prim(Prim::Max, call(j - 1, var("v")), call(j - 1, second))
        };
        let f = Term::Lam(vec!["v".into()], Shared::new(e));
        body = Term::Let(format!("f{j}").into(), Shared::new(f), Shared::new(body));
    }
    body
}

fn calls_apart(k: usize) -> Term {
    calls(k, 1)
}

fn calls_alike(k: usize) -> Term {
    calls(k, 0)
}

/// `if (if (… i >= 3 …) { i >= 1 } else { i <= -1 }) { i >= 0 } else { i <= 0 }`: each
/// branch's guard is the branch before it.
fn guards(k: usize) -> Term {
    let mut g = prim(Prim::Ge, var("i"), int(3));
    for j in 0..k as i64 {
        let (a, b) = (
            prim(Prim::Ge, var("i"), int(j)),
            prim(Prim::Le, var("i"), int(-j)),
        );
        g = Term::If(Shared::new(g), Shared::new(a), Shared::new(b));
    }
    g
}

/// `i >= 0 && i >= 1 && … && i >= k - 1`.
fn conjunction(k: usize) -> Term {
    (1..k as i64).fold(prim(Prim::Ge, var("i"), int(0)), |a, j| {
        prim(Prim::And, a, prim(Prim::Ge, var("i"), int(j)))
    })
}

#[test]
fn preimages_within_the_depth_are_exact() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let cases = [
        (doubling(6), "i [0..=50]; exact"),
        (guards(6), "i [5..=50]; exact"),
        (conjunction(6), "i [5..=50]; exact"),
    ];
    for (t, want) in cases {
        assert_eq!(shown(&preimage(&t, &ds, &Demand::Bool(true))), want, "{t}");
    }
}

#[test]
fn the_transfer_scales() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let ds = &ds;
    let run = |make: fn(usize) -> Term| {
        move |k: usize| {
            preimage(&make(k), ds, &Demand::Bool(true));
        }
    };
    scaling::check("a chain of `let`s, each name read twice", 6, run(doubling));
    scaling::check("branches nested in guard position", 6, run(guards));
    scaling::check("a conjunction of tests", 8, run(conjunction));
    scaling::check(
        "functions each calling the one before twice, alike",
        6,
        run(calls_alike),
    );
    scaling::check(
        "functions each calling the one before twice, apart",
        6,
        run(calls_apart),
    );
}

/// A function is summarized once for each abstraction of its arguments, so a chain of
/// functions each calling the one before twice is read in time linear in its length, not
/// exponential; and the preimage is still exact.
#[test]
fn nested_calls_are_summarized() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    for k in [1, 2, 5, 20, 48] {
        let p = preimage(&calls_alike(k), &ds, &Demand::Bool(true));
        assert_eq!(
            shown(&p),
            "i [0..=50]; exact",
            "{k} functions, arguments alike"
        );
        let p = preimage(&calls_apart(k), &ds, &Demand::Bool(true));
        let lo = -(k as i64).min(50);
        assert_eq!(
            shown(&p),
            format!("i [{lo}..=50]; exact"),
            "{k} functions, apart"
        );
    }
}

/// A chain of `let`s is followed to the end and memoized, never cut. An old count of nested
/// terms cut every chain of 22 or more and fell back on enumeration.
#[test]
fn a_long_chain_of_lets_is_not_cut() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    for k in 1..=64 {
        let p = preimage(&doubling(k), &ds, &Demand::Bool(true));
        assert_eq!(shown(&p), "i [0..=50]; exact", "a chain of {k} `let`s");
    }
}

/// `x * x mod 10 == 9` with `x` in `0..=n`, and `x * y mod 7 == 3` with each in `1..=n`.
fn squares(n: usize) -> (Term, zedc::store::preimage::Domains) {
    let sq = prim(Prim::Mul, var("x"), var("x"));
    let t = prim(Prim::Eq, prim(Prim::Mod, sq, int(10)), int(9));
    (t, doms(&[("x", Some(0), Some(n as i64))]))
}

fn products(n: usize) -> (Term, zedc::store::preimage::Domains) {
    let xy = prim(Prim::Mul, var("x"), var("y"));
    let t = prim(Prim::Eq, prim(Prim::Mod, xy, int(7)), int(3));
    let n = Some(n as i64);
    (t, doms(&[("x", Some(1), n), ("y", Some(1), n)]))
}

/// `x * y <= n` with each in `1..=n`: the plain preimage is exact on every sub-box under or
/// over the curve, so only the boxes the curve crosses are split.
fn hyperbola(n: usize) -> (Term, zedc::store::preimage::Domains) {
    let t = prim(Prim::Le, prim(Prim::Mul, var("x"), var("y")), int(n as i64));
    let n = Some(n as i64);
    (t, doms(&[("x", Some(1), n), ("y", Some(1), n)]))
}

/// Under `@exact` the search visits fewer than twice as many boxes as there are points in
/// the domain, each in time of the size of the term, so its time is of the order of the
/// number of points: `n` for one input in `0..=n`, `n^2` for two; and where the plain
/// preimage is exact on sub-boxes, of the boxes the boundary crosses: `n` for `x * y <= n`.
#[test]
fn the_exact_search_scales_with_the_number_of_points() {
    let run = |make: fn(usize) -> (Term, zedc::store::preimage::Domains)| {
        move |n: usize| {
            let (t, ds) = make(n);
            exact_preimage(&t, &ds, &Classes::new(), &Demand::Bool(true));
        }
    };
    scaling::check(
        "`x * x mod 10 == 9` over `0..=n` under `@exact`",
        256,
        run(squares),
    );
    scaling::check_order(
        "`x * y mod 7 == 3` over `1..=n` squared under `@exact`",
        16,
        2,
        run(products),
    );
    scaling::check(
        "`x * y <= n` over `1..=n` squared under `@exact`",
        64,
        run(hyperbola),
    );
}

/// `f0 = (v) -> v; f1 = (v) -> f0(v) + f0(v + d); …; fk(i) - j >= 0`: a sum, which the catalog
/// does not invert exactly with two inputs, so the linear-relation translation reads it.
fn sums(k: usize, d: i64) -> Term {
    let call = |n: usize, a: Term| Term::App(Shared::new(var(&format!("f{n}"))), vec![a]);
    let mut body = prim(
        Prim::Ge,
        prim(Prim::Sub, call(k, var("i")), var("j")),
        int(0),
    );
    for n in (0..=k).rev() {
        let e = if n == 0 {
            var("v")
        } else {
            let second = if d == 0 {
                var("v")
            } else {
                prim(Prim::Add, var("v"), int(d))
            };
            prim(Prim::Add, call(n - 1, var("v")), call(n - 1, second))
        };
        let f = Term::Lam(vec!["v".into()], Shared::new(e));
        body = Term::Let(format!("f{n}").into(), Shared::new(f), Shared::new(body));
    }
    body
}

#[test]
fn the_linear_translation_of_calls_scales() {
    let ds = doms(&[("i", Some(0), Some(50)), ("j", Some(-50), Some(50))]);
    let ds = &ds;
    for d in [0, 1] {
        scaling::check(
            "sums of calls, each calling the one before twice",
            6,
            move |k| {
                preimage(&sums(k, d), ds, &Demand::Bool(true));
            },
        );
    }
}

/// `x1 = max(i, i); x2 = max(x1, i); …; xk >= 0`: each name reads the input past every other.
fn reading_the_input(k: usize) -> Term {
    let mut body = prim(Prim::Ge, var(&format!("x{k}")), int(0));
    for j in (1..=k).rev() {
        let prev = if j == 1 {
            "i".to_string()
        } else {
            format!("x{}", j - 1)
        };
        let e = prim(Prim::Max, var(&prev), var("i"));
        body = Term::Let(format!("x{j}").into(), Shared::new(e), Shared::new(body));
    }
    body
}

/// `x0 >= 0 && x1 >= 1 && …`, an input for each test.
fn tests_of_many_inputs(k: usize) -> Term {
    (1..k as i64).fold(prim(Prim::Ge, var("x0"), int(0)), |a, j| {
        prim(Prim::And, a, prim(Prim::Ge, var(&format!("x{j}")), int(j)))
    })
}

fn many_inputs(k: usize) -> Domains {
    (0..k)
        .map(|j| {
            (
                format!("x{j}").into(),
                IntervalSet::range(End::of(-50), End::of(5000)),
            )
        })
        .collect()
}

/// The sizes the rule of low complexity is about: a summary reads each name in `O(log n)`, and
/// its result and context take the space of what its body reads, whatever encloses it. Sizes
/// 6 and 48 did not show a growth of `n^1.8` that sizes 48 and 384 do. They run on a 2 MiB
/// stack, since the transfer keeps its frames on the heap (PRE-stack-explicit); the terms are
/// built before the timing.
fn long(what: &'static str, make: fn(usize) -> Term, ds: fn(usize) -> Domains) {
    long_at(what, 48, make, ds)
}

/// [`long`] at sizes `n` and `8n`.
fn long_at(what: &'static str, n: usize, make: fn(usize) -> Term, ds: fn(usize) -> Domains) {
    let measure = move || {
        let large = n * scaling::FACTOR;
        let (a, b) = ((make(n), ds(n)), (make(large), ds(large)));
        scaling::check(what, n, |k| {
            let (t, d) = if k == n { &a } else { &b };
            preimage(t, d, &Demand::Bool(true));
        });
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

fn one(_: usize) -> Domains {
    doms(&[("i", Some(-50), Some(50))])
}

#[test]
fn long_calls_apart() {
    long(
        "functions each calling the one before twice, apart",
        calls_apart,
        one,
    );
}

#[test]
fn long_calls_alike() {
    long(
        "functions each calling the one before twice, alike",
        calls_alike,
        one,
    );
}

#[test]
fn long_doubling() {
    long("a chain of `let`s, each name read twice", doubling, one);
}

#[test]
fn long_reading_the_input() {
    long(
        "a chain of `let`s, each reading the input",
        reading_the_input,
        one,
    );
}

#[test]
fn long_tests_of_many_inputs() {
    long(
        "a conjunction of tests of many inputs",
        tests_of_many_inputs,
        many_inputs,
    );
}

/// `y = i + 1 + … + 1; y * y + … + y * y >= 0`, with `k` ones and `k` products: each product
/// is read as a square, and its two factors are found to be one term by its number, not by
/// comparing the `k` parts of `y`. The comparison of parts took `k` steps for each product before
/// the terms were numbered: 39.9 times the work at sizes 256 and 2048, 8.5 times now.
fn squares_of_one_name(k: usize) -> Term {
    let y = (0..k).fold(var("i"), |a, _| prim(Prim::Add, a, int(1)));
    let sq = || prim(Prim::Mul, var("y"), var("y"));
    let sum = (1..k).fold(sq(), |a, _| prim(Prim::Add, a, sq()));
    Term::Let(
        "y".into(),
        Shared::new(y),
        Shared::new(prim(Prim::Ge, sum, int(0))),
    )
}

/// `t0 = i >= 0; tj = if (i >= j) { t(j-1) } else { t(j-1) }`, both arms one shared term: a
/// term of `k` distinct parts and `2^k` paths, which is numbered in time of its parts.
fn shared_arms(k: usize) -> Term {
    (1..=k as i64).fold(prim(Prim::Ge, var("i"), int(0)), |t, j| {
        let t = Shared::new(t);
        Term::If(Shared::new(prim(Prim::Ge, var("i"), int(j))), t.clone(), t)
    })
}

#[test]
fn long_squares_of_one_name() {
    long_at(
        "squares of one long name, each read as a power",
        256,
        squares_of_one_name,
        one,
    );
}

#[test]
fn long_shared_arms() {
    long("branches whose arms are one shared term", shared_arms, one);
}

/// `t0 = i; tj = if (i >= j) { t(j-1) + 1 } else { j - i }; tk >= 0`: each value nested in
/// the arm of the next, so each auxiliary variable of the linear-relation domain names one
/// `if`. Its name shows the parts by their linear forms, the arm by the auxiliary variable
/// before it: printing the whole subterm instead took 62.4 times the work at sizes 256 and
/// 2048.
fn nested_values(k: usize) -> Term {
    let t = (1..=k as i64).fold(var("i"), |t, j| {
        Term::If(
            Shared::new(prim(Prim::Ge, var("i"), int(j))),
            Shared::new(prim(Prim::Add, t, int(1))),
            Shared::new(prim(Prim::Sub, int(j), var("i"))),
        )
    });
    prim(Prim::Ge, t, int(0))
}

/// `t0 = i; tj = if (i >= j) { t(j-1) } else { t(j-1) + 1 }; tk >= 0`, both arms reading one
/// shared term: `k` distinct parts and `2^k` paths. Printing each subterm took time of its
/// paths: 19 ms at `k = 12`, 383 ms at 16, 1.64 s at 18.
fn shared_values(k: usize) -> Term {
    let t = (1..=k as i64).fold(var("i"), |t, j| {
        let t = Shared::new(t);
        let more = prim(Prim::Add, (*t).clone(), int(1));
        Term::If(
            Shared::new(prim(Prim::Ge, var("i"), int(j))),
            t,
            Shared::new(more),
        )
    });
    prim(Prim::Ge, t, int(0))
}

/// [`long_at`] for the relations of the linear-relation domain.
fn long_relations(what: &'static str, n: usize, make: fn(usize) -> Term) {
    let measure = move || {
        let (a, b) = (make(n), make(n * scaling::FACTOR));
        let inputs: [Arc<str>; 1] = ["i".into()];
        scaling::check(what, n, |k| {
            let t = if k == n { &a } else { &b };
            relations(&[t], &inputs, false).expect("in the domain");
        });
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn long_nested_values() {
    let what = "values nested in the arms of `if`s";
    long_relations(what, 256, nested_values);
    long_at(what, 256, nested_values, one);
}

#[test]
fn long_shared_values() {
    long_relations("`if`s whose arms read one shared term", 256, shared_values);
}

/// `c0 = i >= 0 && i <= 9; cj = (if (i >= j) { c(j-1) } else { c(j-1) }) && i != j &&
/// i <= j + 9`, with `||` in place of `&&` at each odd `j`: chains of `&&` and `||` whose
/// `if` arms read one shared chain, `k` distinct chains and `2^k` paths. The inner `&&` of a
/// chain is an operand of that chain alone and is read inside it, with no memo entry of its
/// own; the `if` and the chain it reads have one, so each chain is translated once
/// (ST-formula-k2). With no memo entry for a chain or an `if`, k = 256 did not finish in 60 s.
fn shared_chains(k: usize) -> Term {
    let chain = |p: Prim, ts: [Term; 3]| {
        let [a, b, c] = ts;
        prim(p, prim(p, a, b), c)
    };
    let first = prim(
        Prim::And,
        prim(Prim::Ge, var("i"), int(0)),
        prim(Prim::Le, var("i"), int(9)),
    );
    let t = (1..=k as i64).fold(first, |t, j| {
        let t = Shared::new(t);
        let p = if j % 2 == 0 { Prim::And } else { Prim::Or };
        let guard = Shared::new(prim(Prim::Ge, var("i"), int(j)));
        chain(
            p,
            [
                Term::If(guard, t.clone(), t),
                prim(Prim::Ne, var("i"), int(j)),
                prim(Prim::Le, var("i"), int(j + 9)),
            ],
        )
    });
    prim(Prim::And, t, prim(Prim::Ge, var("i"), int(-5)))
}

#[test]
fn long_shared_chains() {
    long_relations(
        "chains of `&&` and `||` whose `if` arms read one shared chain",
        256,
        shared_chains,
    );
}

/// `a0 >= 0 && a1 >= 1 && … && a(k-1) >= k - 1` as the elaborator writes it, each `a && b` as
/// `if a { b } else { false }`, nested to the left: a chain of k `&&` on k names. Read as an
/// `if`, the conjunction of each prefix was made in turn, copying the prefix's constraints
/// again at each `&&` (PREIMAGE-and-chain).
fn and_ifs(k: usize) -> Term {
    let ge = |j: usize| prim(Prim::Ge, var(&format!("a{j}")), int(j as i64));
    let no = || Shared::new(Term::Lit(Value::Bool(false)));
    (1..k).fold(ge(0), |t, j| {
        Term::If(Shared::new(t), Shared::new(ge(j)), no())
    })
}

#[test]
fn a_chain_of_and_written_as_ifs_is_joined_in_one_pass() {
    // On origin/main 32654e93 this test fails: k = 256 to 2048 took 0.27 to 22.8 G instructions
    // (86 times) and 0.07 to 4.40 GB (60.1 times; limit 24). Read as a chain (`Walk::chain`):
    // 15.6 to 132 M instructions (8.5 times) and 8.0 times the bytes.
    let measure = || {
        let made = scaling::inputs(256, |k| {
            let names: Vec<Arc<str>> = (0..k).map(|j| format!("a{j}").into()).collect();
            (and_ifs(k), names)
        });
        scaling::check("a chain of k `&&` on k names, written as `if`s", 256, |k| {
            let (t, names) = &made[&k];
            relations(&[t], names, false).expect("in the domain");
        });
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

/// `a0 >= 0 || a1 >= 1 || … || a(k-1) >= k - 1` as the elaborator writes it, each `a || b` as
/// `if a { true } else { b }`, nested to the left: a chain of k `||` on k names. Read as an
/// `if`, each level made `g || (!g && b)` and copied the disjuncts of `g` into a new
/// disjunction (PREIMAGE-or-chain).
fn or_ifs(k: usize) -> Term {
    let ge = |j: usize| prim(Prim::Ge, var(&format!("a{j}")), int(j as i64));
    let yes = || Shared::new(Term::Lit(Value::Bool(true)));
    (1..k).fold(ge(0), |t, j| {
        Term::If(Shared::new(t), yes(), Shared::new(ge(j)))
    })
}

#[test]
fn a_chain_of_or_written_as_ifs_is_joined_in_one_pass() {
    // Read as an `if` (b4e083a7, or `Walk::or_if` turned off) this test fails: k = 256 to 2048
    // took 28.8 to 784 M instructions (27.2 times) and 15.6 to 663 MB (42.6 times; limit 24).
    // Read as `g || b`, a chain (`Walk::chain`): 15.8 to 128 M instructions (8.1 times) and
    // 4.8 to 38.1 MB (8.0 times).
    let measure = || {
        let made = scaling::inputs(256, |k| {
            let names: Vec<Arc<str>> = (0..k).map(|j| format!("a{j}").into()).collect();
            (or_ifs(k), names)
        });
        scaling::check("a chain of k `||` on k names, written as `if`s", 256, |k| {
            let (t, names) = &made[&k];
            relations(&[t], names, false).expect("in the domain");
        });
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

/// `w = (g, v) -> let ok = i >= 0 && i >= 1 && … && i >= k - 2 && seen(g(g, v)) in ok && (i
/// >= 1 || ok) && … && (i >= r - 1 || ok)`, read as `w(w, i)` with `seen = (u) -> i <= 1000`:
/// a check that calls itself, by self-application, through a function that ignores what the
/// call gives, and that tests its chain of `k` limits at `r` places. The call of `w` made while
/// `w` is being read stops there, and `seen` reads no argument, so `ok` has a formula; but the
/// stop is below the place where `ok` began, so its formula is not kept in the memo of the
/// whole transfer, and each of its `r` reads reads its chain again (ST-formula-k2-rec).
fn rereads(r: usize, k: usize) -> Term {
    let ge = |j: usize| prim(Prim::Ge, var("i"), int(j as i64));
    let app = |f: Term, args: Vec<Term>| Term::App(Shared::new(f), args);
    let seen = Term::Lam(
        vec!["u".into()],
        Shared::new(prim(Prim::Le, var("i"), int(1000))),
    );
    let again = app(var("g"), vec![var("g"), var("v")]);
    let limits = (1..k - 1).fold(ge(0), |a, j| prim(Prim::And, a, ge(j)));
    let ok = prim(Prim::And, limits, app(seen, vec![again]));
    let uses = (1..r).fold(var("ok"), |a, j| {
        prim(Prim::And, a, prim(Prim::Or, ge(j), var("ok")))
    });
    let body = Term::Let("ok".into(), Shared::new(ok), Shared::new(uses));
    let w = Term::Lam(vec!["g".into(), "v".into()], Shared::new(body));
    app(w.clone(), vec![w, var("i")])
}

/// [`rereads`] holds where `ok` does, on `i >= k - 2`, with the stop where `w` calls itself;
/// its relation reads `ok` at each of its `r` places, its limits tightened to the last.
#[test]
fn a_chain_read_at_many_places_under_recursion_is_translated() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let inputs: [Arc<str>; 1] = ["i".into()];
    for (r, k) in [(1, 2), (3, 4), (6, 5), (40, 30)] {
        let t = rereads(r, k);
        let p = preimage(&t, &ds, &Demand::Bool(true));
        let stop = "stop: a call of a function already being read at g(g, v)";
        assert_eq!(shown(&p), format!("i [{}..=50]; exact; {stop}", k - 2));
        let rs = relations(&[&t], &inputs, false).expect("in the domain");
        assert_eq!(rs.len(), 1);
        let ok = format!("i >= {} && i <= 1000", k - 2);
        let want = (1..r).fold(ok.clone(), |a, j| format!("{a} && (i >= {j} || ({ok}))"));
        assert_eq!(rs[0].to_string(), want, "r={r} k={k}");
    }
}

/// [`rereads`] with `r` places and `k` limits, each at `n` and `8n` and both at once: the
/// work is of order `r + k` and not `r k`, since a chain whose formula holds where it is
/// reached on the stack it was read at is read once there (COMPLEXITY.md S31b).
#[test]
fn long_chains_read_at_many_places_under_recursion() {
    let n = 64;
    let measure = move || {
        let inputs: [Arc<str>; 1] = ["i".into()];
        let large = n * scaling::FACTOR;
        let cases = [
            (
                "a chain of 64 limits under recursion read at r places",
                (n, 64),
                (large, 64),
            ),
            (
                "a chain of k limits under recursion read at 64 places",
                (64, n),
                (64, large),
            ),
            (
                "a chain of k limits under recursion read at k places",
                (n, n),
                (large, large),
            ),
        ];
        for (what, (r, k), (r8, k8)) in cases {
            let (a, b) = (rereads(r, k), rereads(r8, k8));
            scaling::check(what, n, |s| {
                let t = if s == n { &a } else { &b };
                relations(&[t], &inputs, false).expect("in the domain");
            });
        }
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

/// The preimage of [`shared_values`]: its value is `i + k` below 1, `k` up to `k` and `i`
/// above, so `t >= 0` holds exactly on `i >= -k`. The summary of the shared term as one
/// piecewise-affine function answers each demand once (COMPLEXITY.md S22).
#[test]
fn long_shared_values_preimage() {
    let answers = || {
        for k in [1, 7, 20, 49, 50, 51, 256, 2048] {
            let (t, ds) = (shared_values(k), one(k));
            let p = preimage(&t, &ds, &Demand::Bool(true));
            assert!(p.exact, "k={k}: {}", shown(&p));
            let lo = (-(k as i64)).max(-50);
            assert_eq!(
                p.domains["i"],
                IntervalSet::of(lo, 50),
                "k={k}: {}",
                shown(&p)
            );
            super::check(&t, &ds, &Demand::Bool(true), &p, (-50, 50));
        }
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(answers).unwrap().join().unwrap();
    long_at(
        "the preimage of `if`s whose arms read one shared term",
        256,
        shared_values,
        one,
    );
}

/// Each auxiliary variable is named by one level of its term.
#[test]
fn auxiliary_variables_are_named_one_level_deep() {
    let inputs: [Arc<str>; 2] = ["i".into(), "j".into()];
    let t = prim(
        Prim::Ge,
        prim(
            Prim::Max,
            prim(Prim::IntDiv, prim(Prim::Add, var("i"), var("j")), int(3)),
            Term::If(
                Shared::new(prim(Prim::Ge, var("i"), int(0))),
                Shared::new(var("j")),
                Shared::new(int(2)),
            ),
        ),
        int(0),
    );
    let rs = relations(&[&t], &inputs, false).expect("in the domain");
    assert_eq!(rs.len(), 1);
    let shown = rs[0].to_string();
    assert!(
        shown.contains("q0 = (i + j) div 3, q1 = (i + j) mod 3"),
        "{shown}"
    );
    assert!(shown.contains(" then j else 2"), "{shown}");
    assert!(shown.contains("q3 = max(q0, q2)"), "{shown}");
}

/// `w = (g, v) -> t_d`, read as `w(w, i)`, with `t_0 = seen(g(g, v))`, `seen = (u) -> i <=
/// 1000` and `t_j = if (i >= j) { t(j-1) } else { t(j-1) }`: a term of `d` distinct parts and
/// `2^d` paths under a call that stops where `w` calls itself, below where each part began.
fn shared_arms_under_recursion(d: usize) -> Term {
    let app = |f: Term, args: Vec<Term>| Term::App(Shared::new(f), args);
    let seen = Term::Lam(
        vec!["u".into()],
        Shared::new(prim(Prim::Le, var("i"), int(1000))),
    );
    let again = app(var("g"), vec![var("g"), var("v")]);
    let t = (1..=d as i64).fold(app(seen, vec![again]), |t, j| {
        let t = Shared::new(t);
        Term::If(Shared::new(prim(Prim::Ge, var("i"), int(j))), t.clone(), t)
    });
    let w = Term::Lam(vec!["g".into(), "v".into()], Shared::new(t));
    app(w.clone(), vec![w, var("i")])
}

/// Each part of [`shared_arms_under_recursion`] is read once, in the transfer and in the
/// translation, and not once for each path: d = 14 took 21.6 and 82.9 ms, four times d = 12,
/// before parts read below a stop were remembered (ST-formula-k2-rec).
#[test]
fn long_shared_arms_under_recursion() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let p = preimage(&shared_arms_under_recursion(6), &ds, &Demand::Bool(true));
    assert_eq!(
        shown(&p),
        "i [-50..=50]; exact; stop: a call of a function already being read at g(g, v)"
    );
    long_at(
        "`if`s under recursion whose arms are one shared term",
        32,
        shared_arms_under_recursion,
        one,
    );
    long_relations(
        "`if`s under recursion whose arms are one shared term",
        32,
        shared_arms_under_recursion,
    );
}

/// `x * x mod 10 == 9` with `x` listed as the `n` members `0, 3, 6, …`: a listed set is
/// enumerated, each member run once, so the time is of the order of the list the source wrote
/// (LIST-size). The same members as a range are never enumerated, whatever their number.
#[test]
fn a_listed_set_is_enumerated_in_time_of_its_length() {
    let make = |n: usize| {
        let members: Vec<i64> = (0..n as i64).map(|k| 3 * k).collect();
        let sq = prim(Prim::Mul, var("x"), var("x"));
        let t = prim(Prim::Eq, prim(Prim::Mod, sq, int(10)), int(9));
        (t, listed(&[("x", &members)]))
    };
    let (t, ds) = make(8);
    assert_eq!(
        shown(&pre_listed(&t, &ds, &Demand::Bool(true))),
        "x [3..=3]; exact; enumerated"
    );
    let inputs = scaling::inputs(512, make);
    scaling::check("a listed set of `n` members, enumerated", 512, |n| {
        let (t, ds) = &inputs[&n];
        pre_listed(t, ds, &Demand::Bool(true));
    });
}
