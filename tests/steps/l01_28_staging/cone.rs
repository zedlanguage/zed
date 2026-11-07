//! Item STAGE-ends-cone (COMPLEXITY.md row F43): whether a build-stage term's form shows that
//! it ends is read from what the term needs and what each binding in scope holds, with one
//! reader kept for the whole mix, not from the term closed under every binding it needs. Each
//! evaluation used to read that closed term whole, and an evaluation whose form does not show
//! that it ends, or one at a root held inline, built it from every binding the term needs, so a
//! chain of `n` functions called at `n` places took time quadratic in `n`.

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Prim, Shared, Term};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::elab::{Def, Unit};
use zedc::stage::{self, Remix};

use super::scaling::deep;

const FORM: &str = "its form does not show that it ends";

fn def(name: &str, term: Term) -> Def {
    Def {
        name: name.into(),
        kernel: name.into(),
        term: Shared::new(term),
        first_order: false,
    }
}

fn unit(defs: Vec<Def>) -> Unit {
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
enum F0 {
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
fn chain(n: usize, f0: F0, two: bool) -> Vec<Def> {
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
fn sites(n: usize) -> Term {
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
fn left(report: &stage::Report) -> Vec<String> {
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

/// A call of a chain whose every call fails is run with stubs, fails, and is run again as
/// written, closed over the whole chain below it: time linear in the chain per call, quadratic
/// in all (the complexity tradeoff at `Mixer::as_written`, COMPLEXITY.md row F43). The test
/// holds it to that order, so that it grows no worse.
#[test]
fn failing_calls_of_a_long_chain_are_left_to_run_in_quadratic_time() {
    deep(|| {
        let (_, report) = stage::mix(&with_main(2, F0::Fails, false), &["main"]);
        let error = "type error: `+` applied to `int`, `bool`";
        let call = |j: usize| format!("{:?}: {error}", app(var(&f(j)), vec![lit(0i64)]));
        assert_eq!(left(&report), vec![call(1), call(2)]);
        let n = 60;
        let units = scaling::inputs(n, |n| with_main(n, F0::Fails, false));
        scaling::check_order(
            "stage::mix on n calls of a chain of n functions whose every call fails",
            n,
            2,
            |n| {
                let (_, report) = stage::mix(&units[&n], &["main"]);
                assert_eq!(report.left.len(), n);
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
fn mixed_text(u: &Unit) -> String {
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
