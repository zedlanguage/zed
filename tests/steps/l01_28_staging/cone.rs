//! Item STAGE-ends-cone (COMPLEXITY.md row F43): whether a build-stage term's form shows that
//! it ends is read from what the term needs and what each binding in scope holds, with one
//! reader kept for the whole mix, not from the term closed under every binding it needs. Each
//! evaluation used to read that closed term whole, and an evaluation whose form does not show
//! that it ends, or one at a root held inline, built it from every binding the term needs, so a
//! chain of `n` functions called at `n` places took time quadratic in `n`.

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::elab::{Def, Unit};
use zedc::stage::{self, Remix, Stage};

use super::scaling::deep;

const FORM: &str = "its form does not show that it ends";

pub(super) fn def(name: &str, term: Term) -> Def {
    Def {
        name: name.into(),
        kernel: name.into(),
        term: Shared::new(term),
        first_order: false,
    }
}

pub(super) fn unit(defs: Vec<Def>) -> Unit {
    Unit {
        defs,
        tests: Arc::from([]),
        warnings: Vec::new(),
    }
}

fn f(j: usize) -> String {
    format!("f{j}")
}

/// The first function of a chain.
#[derive(Clone, Copy)]
pub(super) enum F0 {
    /// `f0 = (y) -> y + 1`, so `fk(0)` is 1.
    Ends,
    /// `f0 = (y) -> y(y)`, whose form does not show that it ends, and so neither does any
    /// function of the chain.
    Loops,
    /// `f0 = (y) -> y + true`, whose form shows that it ends and whose every call fails.
    Fails,
}

/// `f0`, then for k = 1 to n `fk = (y) -> if y >= 1 { f(k-1)(y) } else { e }`, where `e` is
/// `f(k-2)(y)` when `two` and k >= 2, else the same node `f(k-1)(y)` as the first arm. With
/// `two` the names the functions read form a DAG whose paths from `fn` number the Fibonacci
/// number of n, so a walk of it as a tree would be exponential.
pub(super) fn chain(n: usize, f0: F0, two: bool) -> Vec<Def> {
    let f0 = match f0 {
        F0::Ends => lam(&["y"], prim(Prim::Add, vec![var("y"), lit(1i64)])),
        F0::Loops => lam(&["y"], app(var("y"), vec![var("y")])),
        F0::Fails => lam(&["y"], prim(Prim::Add, vec![var("y"), lit(true)])),
    };
    let call = |j: usize| Shared::new(app(var(&f(j)), vec![var("y")]));
    let mut out = vec![def(&f(0), f0)];
    for k in 1..=n {
        let down = call(k - 1);
        let other = match two && k >= 2 {
            true => call(k - 2),
            false => down.clone(),
        };
        let guard = Shared::new(prim(Prim::Ge, vec![var("y"), lit(1i64)]));
        out.push(def(&f(k), lam(&["y"], Term::If(guard, down, other))));
    }
    out
}

/// `(f1(0) + c, f2(0) + c, .., fn(0) + c)`.
pub(super) fn sites(n: usize) -> Term {
    let site = |j: usize| prim(Prim::Add, vec![app(var(&f(j)), vec![lit(0i64)]), var("c")]);
    prim(Prim::Tuple, (1..=n).map(site).collect())
}

/// The chain of `n` functions and `main = (c) -> sites(n)`.
fn with_main(n: usize, f0: F0, two: bool) -> Unit {
    let mut defs = chain(n, f0, two);
    defs.push(def("main", lam(&["c"], sites(n))));
    unit(defs)
}

/// The calls the report leaves to run, each with its reason, as text.
pub(super) fn left(report: &stage::Report) -> Vec<String> {
    let calls = report.left.iter();
    calls.map(|(t, why)| format!("{t:?}: {why}")).collect()
}

/// What mixing `sites(n)` over a chain whose form does not show that it ends leaves to run:
/// each call, once.
fn left_on_chain(n: usize) -> Vec<String> {
    let call = |j: usize| format!("{:?}: {FORM}", app(var(&f(j)), vec![lit(0i64)]));
    (1..=n).map(call).collect()
}

#[test]
fn calls_of_a_chain_whose_form_does_not_show_it_ends_are_left_to_run() {
    deep(|| {
        for two in [false, true] {
            let (_, report) = stage::mix(&with_main(3, F0::Loops, two), &["main"]);
            assert_eq!(left(&report), left_on_chain(3));
            let (mixed, report) = stage::mix(&with_main(3, F0::Ends, two), &["main"]);
            assert!(report.left.is_empty());
            assert_eq!(
                mixed.defs[4].term.to_string(),
                "c -> ((1 + c), (1 + c), (1 + c))"
            );
        }
    });
}

/// Checks that mixing `with_main(n, F0::Loops, two)` scales.
fn mixing_scales(what: &'static str, two: bool) {
    deep(move || {
        let n = 400;
        let units = scaling::inputs(n, |n| with_main(n, F0::Loops, two));
        scaling::check(what, n, |n| {
            let (_, report) = stage::mix(&units[&n], &["main"]);
            assert_eq!(report.left.len(), n);
        });
    });
}

#[test]
fn mixing_calls_of_a_long_chain_whose_form_does_not_show_it_ends_scales() {
    mixing_scales(
        "stage::mix on n calls of a chain of n functions whose form does not show it ends",
        false,
    );
}

#[test]
fn mixing_calls_of_functions_that_each_call_the_two_before_scales() {
    mixing_scales(
        "stage::mix on n calls of n functions, each calling the two before, whose form does \
         not show it ends",
        true,
    );
}

/// A call of a chain whose every call fails is run with stubs and fails at the stub of the
/// function below it, whose table keeps the error that call gives as written, so the call is
/// left to run with that error and is not run again as written: each function's call is run
/// once, in time linear in the chain over all the calls (COMPLEXITY.md row F43).
#[test]
fn failing_calls_of_a_long_chain_are_left_to_run_in_linear_time() {
    deep(|| {
        let (_, report) = stage::mix(&with_main(2, F0::Fails, false), &["main"]);
        let error = "type error: `+` applied to `int`, `bool`";
        let call = |j: usize| format!("{:?}: {error}", app(var(&f(j)), vec![lit(0i64)]));
        assert_eq!(left(&report), vec![call(1), call(2)]);
        let n = 100;
        let units = scaling::inputs(n, |n| with_main(n, F0::Fails, false));
        scaling::check(
            "stage::mix on n calls of a chain of n functions whose every call fails",
            n,
            |n| {
                let (_, report) = stage::mix(&units[&n], &["main"]);
                assert_eq!(report.left.len(), n);
            },
        );
    });
}

/// The chain of `n` functions and `main = (c) -> (f1(-0.0) + c, .., fn(-0.0) + c)`.
fn at_minus_zero(n: usize, f0: F0) -> Unit {
    let mut defs = chain(n, f0, false);
    let call = |j: usize| app(var(&f(j)), vec![Term::Lit(Value::float(-0.0))]);
    let site = |j: usize| prim(Prim::Add, vec![call(j), var("c")]);
    let sites = (1..=n).map(site).collect();
    defs.push(def("main", lam(&["c"], prim(Prim::Tuple, sites))));
    unit(defs)
}

/// A call at an argument no answer table takes (`-0.0`, which a key reads as `0.0`) is refused
/// by the stub and run again as written, under the functions of the chain as globals whose
/// values are made when the run first reads them (`Mixer::run_under`): the run of `fj(-0.0)`
/// fails at the guard of `fj` and reads no function below it, so each call takes constant
/// time and all of them time linear in `n` (COMPLEXITY.md row F43).
#[test]
fn failing_calls_no_answer_table_takes_are_run_as_written_in_linear_time() {
    deep(|| {
        let (_, report) = stage::mix(&at_minus_zero(2, F0::Fails), &["main"]);
        let error = "type error: `>=` applied to `f64`, `int`";
        let call = |j: usize| {
            let t = app(var(&f(j)), vec![Term::Lit(Value::float(-0.0))]);
            format!("{t:?}: {error}")
        };
        assert_eq!(left(&report), vec![call(1), call(2)]);
        let n = 100;
        let units = scaling::inputs(n, |n| at_minus_zero(n, F0::Fails));
        scaling::check(
            "stage::mix on n calls at -0.0 of a chain of n functions whose every call fails",
            n,
            |n| {
                let (_, report) = stage::mix(&units[&n], &["main"]);
                assert_eq!(report.left.len(), n);
            },
        );
    });
}

/// `k = e`, `g = (y) -> if y >= 1 { k } else { 0 }`, `f = (x) -> g(-0.0) + x` and
/// `main = (c) -> f(1)`.
fn reading_k(k: Term) -> Unit {
    let guard = prim(Prim::Ge, vec![var("y"), lit(1i64)]);
    let g = def("g", lam(&["y"], if_(guard, var("k"), lit(0i64))));
    let call = app(var("g"), vec![Term::Lit(Value::float(-0.0))]);
    let f = def("f", lam(&["x"], prim(Prim::Add, vec![call, var("x")])));
    let main = def("main", lam(&["c"], app(var("f"), vec![lit(1i64)])));
    unit(vec![def("k", k), g, f, main])
}

/// The Trick's mixer binds each definition mixed, as `mix` does (`Specializer::new`), so a
/// split sees what the build sees. `k = 2 + 2` is bound as `4`, and `g(-0.0)` fails at its own
/// guard. `k = 1 + true` fails where it is mixed, so `k` is left to run, and so is `g`, which
/// reads it: the split leaves `g(-0.0)` to run without evaluating it, as `mix` does, where the
/// mixer used to bind `k` as written and give the call the error of `+`, which it never reads.
#[test]
fn a_binding_the_trick_cannot_build_is_left_to_run_as_mix_leaves_it() {
    let split = |k: Term| {
        let u = reading_k(k);
        let (lam, report) =
            stage::split(&u, "f", 0, &stage::Domain::Ints(Some(0), Some(9))).expect("split");
        (lam.to_string(), left(&report))
    };
    let call = format!("{:?}", app(var("g"), vec![Term::Lit(Value::float(-0.0))]));
    let ge = "type error: `>=` applied to `f64`, `int`";
    let site = format!("Prim(Add, [{call}, Var(\"x\")])");
    let lam = "x -> match x { 1 -> (g(-0.0) + x), _ -> (g(-0.0) + x) }".to_string();
    let errors = vec![format!("{site}: {ge}"), format!("{call}: {ge}")];
    assert_eq!(
        split(prim(Prim::Add, vec![lit(2i64), lit(2i64)])),
        (lam, errors)
    );
    let bad = prim(Prim::Add, vec![lit(1i64), lit(true)]);
    let lam = "x -> match x { 1 -> (g(-0.0) + 1), _ -> (g(-0.0) + x) }".to_string();
    assert_eq!(split(bad.clone()), (lam, vec![]));
    // `mix` leaves `k` to run with the error of `+`, and nothing that reads it.
    let (_, report) = stage::mix(&reading_k(bad.clone()), &["main"]);
    let add = "type error: `+` applied to `int`, `bool`";
    assert_eq!(left(&report), vec![format!("{bad:?}: {add}")]);
    assert_eq!(
        stage::color(&reading_k(bad)),
        [
            ("k".to_string(), Stage::Run),
            ("g".to_string(), Stage::Run),
            ("f".to_string(), Stage::Run),
            ("main".to_string(), Stage::Run)
        ]
    );
}

/// `k = 2 + 2`, the chain of `n` functions whose first is `f0 = (y) -> y + k`, and
/// `g = (x) -> (f1(-0.0) + x, .., fn(-0.0) + x)`, called by `main = (c) -> g(1)`.
fn chain_reading_k(n: usize) -> Unit {
    let mut defs = vec![def("k", prim(Prim::Add, vec![lit(2i64), lit(2i64)]))];
    defs.extend(chain(n, F0::Ends, false));
    defs[1] = def(
        &f(0),
        lam(&["y"], prim(Prim::Add, vec![var("y"), var("k")])),
    );
    let call = |j: usize| app(var(&f(j)), vec![Term::Lit(Value::float(-0.0))]);
    let site = |j: usize| prim(Prim::Add, vec![call(j), var("x")]);
    let sites = (1..=n).map(site).collect();
    defs.push(def("g", lam(&["x"], prim(Prim::Tuple, sites))));
    defs.push(def("main", lam(&["c"], app(var("g"), vec![lit(1i64)]))));
    unit(defs)
}

/// Each call `fj(-0.0)` of a split is refused by the stub of `fj` and run as written. Its cone
/// reads `k = 2 + 2`, which the Trick's mixer bound as written and which made the call run
/// closed under every binding it needs, `O(n)` per call; bound mixed, `k` is `4`, the call
/// runs under the globals and fails at the guard of `fj`, in constant time (COMPLEXITY.md row
/// F43).
#[test]
fn calls_reading_a_definition_the_trick_builds_are_split_in_linear_time() {
    deep(|| {
        let ge = "type error: `>=` applied to `f64`, `int`";
        let (_, report) = stage::split(
            &chain_reading_k(2),
            "g",
            0,
            &stage::Domain::Ints(Some(0), Some(9)),
        )
        .expect("split");
        let call = |j: usize| app(var(&f(j)), vec![Term::Lit(Value::float(-0.0))]);
        let site = |j: usize| prim(Prim::Add, vec![call(j), var("x")]);
        // The tuple fails at its first site, and each call is left with its own error.
        let tuple = prim(Prim::Tuple, vec![site(1), site(2)]);
        let want: Vec<String> = [tuple, call(1), call(2)]
            .iter()
            .map(|t| format!("{t:?}: {ge}"))
            .collect();
        assert_eq!(left(&report), want);
        let n = 100;
        let units = scaling::inputs(n, chain_reading_k);
        scaling::check(
            "stage::split of a function of n calls at -0.0 of a chain of n functions reading \
             k = 2 + 2",
            n,
            |n| {
                let d = stage::Domain::Ints(Some(0), Some(9));
                let (_, report) = stage::split(&units[&n], "g", 0, &d).expect("split");
                assert_eq!(report.left.len(), n + 1);
            },
        );
    });
}

#[test]
fn remixing_a_root_held_inline_over_a_long_chain_scales() {
    deep(|| {
        let (_, mut r) = Remix::new(&with_main(3, F0::Ends, false));
        assert_eq!(r.mix(&sites(3)).to_string(), "((1 + c), (1 + c), (1 + c))");
        let n = 400;
        let inputs: HashMap<usize, (Unit, Term)> =
            scaling::inputs(n, |n| (with_main(n, F0::Ends, false), sites(n)));
        scaling::check(
            "Remix::new and Remix::mix of n calls of a chain of n functions, the root held \
             inline",
            n,
            |n| {
                let (u, root) = &inputs[&n];
                let (_, mut r) = Remix::new(u);
                let Term::Prim(Prim::Tuple, sites) = &r.mix(root) else {
                    panic!("a tuple")
                };
                assert_eq!(sites.len(), n);
            },
        );
    });
}

/// A random unit: definitions `d0`, `d1`, .. each a literal, a function of one parameter, a
/// function of a function and a value, or a name of an earlier one, and `main = (c) -> ..`
/// calling them at literals and at `c`, some calls shared by both arms of an `if`. Some
/// functions fail (`y + true`), and some do not show that they end (`y(y)`).
fn random_unit(rng: &mut Rng, n: usize) -> Unit {
    // The number of parameters of each definition: 0 for a literal.
    let mut arity: Vec<usize> = Vec::new();
    let mut defs = Vec::new();
    let name = |i: usize| format!("d{i}");
    let of = |arity: &[usize], a: usize| -> Vec<usize> {
        (0..arity.len()).filter(|&i| arity[i] == a).collect()
    };
    fn body(rng: &mut Rng, arity: &[usize], depth: usize) -> Term {
        let with =
            |a: usize| -> Vec<usize> { (0..arity.len()).filter(|&i| arity[i] == a).collect() };
        let (lits, unary, pair) = (with(0), with(1), with(2));
        let d = |i: usize| var(&format!("d{i}"));
        let y = || var("y");
        match rng.below(if depth == 0 { 3 } else { 9 }) {
            0 => prim(Prim::Add, vec![y(), lit(rng.int(-2, 2))]),
            1 if !lits.is_empty() => prim(Prim::Add, vec![d(rng.pick(&lits)), y()]),
            1 | 2 => prim(Prim::Mul, vec![y(), lit(rng.int(1, 3))]),
            3 => prim(Prim::Add, vec![y(), lit(true)]),
            4 => app(y(), vec![y()]),
            5 if !unary.is_empty() => {
                let inner = body(rng, arity, depth - 1);
                app(d(rng.pick(&unary)), vec![inner])
            }
            6 => {
                let guard = prim(Prim::Ge, vec![y(), lit(rng.int(-1, 2))]);
                let a = body(rng, arity, depth - 1);
                let b = body(rng, arity, depth - 1);
                if_(guard, a, b)
            }
            7 => {
                let g = lam(&["y"], body(rng, arity, depth - 1));
                let call = app(var("g"), vec![prim(Prim::Add, vec![y(), lit(1i64)])]);
                let_("g", g, call)
            }
            8 if !pair.is_empty() && !unary.is_empty() => {
                let h = d(rng.pick(&pair));
                app(h, vec![d(rng.pick(&unary)), y()])
            }
            _ => prim(Prim::Sub, vec![y(), lit(1i64)]),
        }
    }
    for i in 0..n {
        let unary = of(&arity, 1);
        let (term, a) = match rng.below(6) {
            0 => (lit(rng.int(-3, 3)), 0),
            1 if !unary.is_empty() => (var(&name(rng.pick(&unary))), 1),
            2 => {
                let call = app(var("h"), vec![var("y")]);
                (lam(&["h", "y"], prim(Prim::Add, vec![call, lit(1i64)])), 2)
            }
            _ => (lam(&["y"], body(rng, &arity, 3)), 1),
        };
        arity.push(a);
        defs.push(def(&name(i), term));
    }
    let (unary, pair) = (of(&arity, 1), of(&arity, 2));
    let mut sites = Vec::new();
    if !unary.is_empty() {
        for _ in 0..rng.int(1, 6) {
            let f = var(&name(rng.pick(&unary)));
            let site = match rng.below(5) {
                0 => prim(Prim::Add, vec![app(f, vec![lit(rng.int(-2, 3))]), var("c")]),
                1 => app(f, vec![var("c")]),
                2 => {
                    let x = lit(rng.int(-2, 3));
                    let call = app(f, vec![var("x")]);
                    let_("x", x, prim(Prim::Add, vec![call, var("c")]))
                }
                3 if !pair.is_empty() => {
                    let h = var(&name(rng.pick(&pair)));
                    let call = app(h, vec![f, lit(rng.int(-2, 3))]);
                    prim(Prim::Add, vec![call, var("c")])
                }
                _ => {
                    let call = app(f, vec![lit(rng.int(-2, 3))]);
                    let shared = Shared::new(prim(Prim::Add, vec![call, var("c")]));
                    let guard = Shared::new(prim(Prim::Ge, vec![var("c"), lit(0i64)]));
                    Term::If(guard, shared.clone(), shared)
                }
            };
            sites.push(site);
        }
    }
    defs.push(def("main", lam(&["c"], prim(Prim::Tuple, sites))));
    unit(defs)
}

/// Two roots held inline for [`Remix::mix`] on the random unit `u`, which has `n` definitions
/// besides `main`: calls of its functions of one parameter at literals, and `main` at one.
fn random_roots(rng: &mut Rng, u: &Unit, n: usize) -> [Term; 2] {
    let unary: Vec<&str> = u.defs[..n]
        .iter()
        .filter(|d| match &*d.term {
            Term::Lam(ps, _) => ps.len() == 1,
            Term::Var(_) => true,
            _ => false,
        })
        .map(|d| d.name.as_str())
        .collect();
    let calls = (0..rng.int(1, 4))
        .filter(|_| !unary.is_empty())
        .map(|_| app(var(rng.pick(&unary)), vec![lit(rng.int(-2, 3))]))
        .collect();
    let main = app(var("main"), vec![lit(rng.int(-2, 3))]);
    [prim(Prim::Tuple, calls), prim(Prim::Tuple, vec![main])]
}

/// The mixed definitions of `u` and the report, as text.
pub(super) fn mixed_text(u: &Unit) -> String {
    let (out, report) = stage::mix(u, &["main"]);
    let defs = out.defs.iter();
    let defs: String = defs
        .map(|d| format!("{} = {}\n", d.name, *d.term))
        .collect();
    defs + &format!("{report:?}\n")
}

#[test]
fn what_a_mix_keeps_across_evaluations_does_not_change_what_they_give() {
    deep(|| {
        for seed in 0..256u64 {
            let mut rng = Rng::new(seed);
            let n = 1 + rng.below(12);
            let u = random_unit(&mut rng, n);
            // Mixing twice, each time with a reader of its own, gives one result.
            assert_eq!(mixed_text(&u), mixed_text(&u), "seed {seed}");
            // Each root mixes alike first, second, or alone: what the remix keeps from one
            // root does not change what the other gives.
            let roots = random_roots(&mut rng, &u, n);
            let alone = roots.clone().map(|t| Remix::new(&u).1.mix(&t).to_string());
            for order in [[0, 1], [1, 0]] {
                let (_, mut r) = Remix::new(&u);
                for i in order {
                    assert_eq!(r.mix(&roots[i]).to_string(), alone[i], "seed {seed}");
                }
            }
        }
    });
}

/// `h = (g, y) -> g(y) + 1`, then `f0`, `f1`, .. each `(y) -> ..` built from `y + a`,
/// `y + true` (which fails), calls of earlier functions at `y`, `y + 1`, `y - 1` or a literal,
/// `if`s over those, a call whose value `+ true` fails after it, and `h(fj, y)`, whose function
/// argument no answer table takes; and `main = (c) -> (s1 + c, ..)`, each `s` a call `fj(a)` or
/// `h(fj, a)`. Every function ends; many calls fail, at the function itself or below it.
fn stub_fail_unit(rng: &mut Rng, n: usize) -> (Unit, Vec<Term>) {
    fn body(rng: &mut Rng, k: usize, depth: usize) -> Term {
        let y = || var("y");
        let call = |rng: &mut Rng| {
            let arg = match rng.below(4) {
                0 => y(),
                1 => prim(Prim::Add, vec![y(), lit(1i64)]),
                2 => prim(Prim::Sub, vec![y(), lit(1i64)]),
                _ => lit(rng.int(-2, 3)),
            };
            app(var(&f(rng.below(k))), vec![arg])
        };
        match rng.below(if k == 0 || depth == 0 { 2 } else { 7 }) {
            0 => prim(Prim::Add, vec![y(), lit(rng.int(-2, 2))]),
            1 => prim(Prim::Add, vec![y(), lit(true)]),
            2 | 3 => call(rng),
            4 => {
                let guard = prim(Prim::Ge, vec![y(), lit(rng.int(-1, 2))]);
                let a = body(rng, k, depth - 1);
                let b = body(rng, k, depth - 1);
                if_(guard, a, b)
            }
            5 => prim(Prim::Add, vec![call(rng), lit(true)]),
            _ => app(var("h"), vec![var(&f(rng.below(k))), y()]),
        }
    }
    let h = lam(
        &["g", "y"],
        prim(Prim::Add, vec![app(var("g"), vec![var("y")]), lit(1i64)]),
    );
    let mut defs = vec![def("h", h)];
    for k in 0..n {
        let b = body(rng, k, 3);
        defs.push(def(&f(k), lam(&["y"], b)));
    }
    let calls: Vec<Term> = (0..rng.int(2, 6))
        .map(|_| {
            let (j, a) = (rng.below(n), lit(rng.int(-2, 3)));
            match rng.below(4) {
                0 => app(var("h"), vec![var(&f(j)), a]),
                _ => app(var(&f(j)), vec![a]),
            }
        })
        .collect();
    let site = |t: &Term| prim(Prim::Add, vec![t.clone(), var("c")]);
    let sites = calls.iter().map(site).collect();
    defs.push(def("main", lam(&["c"], prim(Prim::Tuple, sites))));
    (unit(defs), calls)
}

/// On random chains of functions whose calls fail at many depths, a call whose run with stubs
/// fails gives what it gives as written: the mixed `main` holds each call's value as written,
/// or the call itself, left to run with the error the call as written stops with.
#[test]
fn calls_that_fail_in_a_chain_give_what_they_give_as_written() {
    deep(|| {
        for seed in 0..400u64 {
            let mut rng = Rng::new(seed);
            let n = 1 + rng.below(16);
            let (u, calls) = stub_fail_unit(&mut rng, n);
            let (mixed, report) = stage::mix(&u, &["main"]);
            let mut sites = Vec::new();
            let mut want_left = std::collections::BTreeSet::new();
            for t in &calls {
                let closed = u.close(t.clone());
                let out = match stage::ends(&closed) {
                    true => {
                        zed_kernel::eval(&zedc::interp::prelude(closed)).map_err(|e| e.to_string())
                    }
                    false => Err(FORM.to_string()),
                };
                match out {
                    Ok(v) => sites.push(prim(Prim::Add, vec![Term::Lit(v), var("c")])),
                    Err(e) => {
                        want_left.insert(format!("{t:?}: {e}"));
                        sites.push(prim(Prim::Add, vec![t.clone(), var("c")]));
                    }
                }
            }
            let want = lam(&["c"], prim(Prim::Tuple, sites)).to_string();
            let main = mixed.defs.last().expect("main");
            assert_eq!(
                main.term.to_string(),
                want,
                "seed {seed} {:?}",
                left(&report)
            );
            // Calls inside the functions are mixed too; only the sites are compared.
            let site = |s: &String| calls.iter().any(|t| s.starts_with(&format!("{t:?}: ")));
            let got: std::collections::BTreeSet<String> =
                left(&report).into_iter().filter(site).collect();
            assert_eq!(got, want_left, "seed {seed}");
        }
    });
}
