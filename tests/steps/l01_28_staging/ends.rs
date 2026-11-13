//! The form rule `stage::ends` on terms whose parts are shared: a part reached from two places
//! (one `Shared` node twice) is read once, and its answer still depends on the names bound around each
//! place.

use std::collections::BTreeMap;
use zed_kernel::Shared;

use zed_kernel::term::build::{lam, lit, var};
use zed_kernel::{FixKind, GuardPos, Pattern, Prim, Term};
use zed_tests::scaling::{self, FACTOR};
use zedc::stage::{ends, reading};

use super::scaling::deep;

fn app(f: Term, args: Vec<Term>) -> Term {
    Term::App(Shared::new(f), args)
}

fn let_(x: &str, e: Term, b: Term) -> Term {
    Term::Let(x.into(), Shared::new(e), Shared::new(b))
}

fn if_(c: Term, a: Shared, b: Shared) -> Term {
    Term::If(Shared::new(c), a, b)
}

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

/// `n` and the operation `+` read as one would write `step(n) + 1`.
fn calls_step() -> Shared {
    Shared::new(prim(
        Prim::Add,
        vec![app(var("step"), vec![var("n")]), lit(1i64)],
    ))
}

#[test]
fn a_shared_part_under_two_bindings_of_a_name_it_calls_gets_two_answers() {
    // `step(n) + 1`, one part in memory, read where `step` is a `let` function and where it is
    // a parameter: the first ends, the second calls through a parameter.
    let body = calls_step();
    let increment = lam(&["k"], prim(Prim::Add, vec![var("k"), lit(1i64)]));
    let by_let = || Term::Let("step".into(), Shared::new(increment.clone()), body.clone());
    let by_param = || Term::Lam(vec!["step".into()], body.clone());
    assert!(ends(&by_let()));
    assert!(!ends(&by_param()));
    // Both places in one term, in either order: the answer of the first place read is not
    // reused at the second.
    let c = || var("flag");
    assert!(!ends(&if_(
        c(),
        Shared::new(by_let()),
        Shared::new(by_param())
    )));
    assert!(!ends(&if_(
        c(),
        Shared::new(by_param()),
        Shared::new(by_let())
    )));
    // Two `let` functions of the name: both places end.
    let decrement = lam(&["k"], prim(Prim::Sub, vec![var("k"), lit(1i64)]));
    let by_other_let = Term::Let("step".into(), Shared::new(decrement), body.clone());
    assert!(ends(&if_(
        c(),
        Shared::new(by_let()),
        Shared::new(by_other_let)
    )));
    // Inside the `let`, the part is read once bare and once under a parameter named `step`,
    // which shadows the `let`.
    let shadowed = Term::Let(
        "step".into(),
        Shared::new(increment.clone()),
        Shared::new(if_(c(), body.clone(), Shared::new(by_param()))),
    );
    assert!(!ends(&shadowed));
    // A parameter of another name does not shadow it.
    let other = Term::Let(
        "step".into(),
        Shared::new(increment),
        Shared::new(if_(
            c(),
            body.clone(),
            Shared::new(Term::Lam(vec!["m".into()], body.clone())),
        )),
    );
    assert!(ends(&other));
    // Free, `step` is a prelude word.
    assert!(ends(&body));
}

#[test]
fn a_let_function_that_calls_an_outer_name_needs_what_that_name_is_bound_to() {
    // `apply = (k) -> step(k); apply(n)`: `apply` ends when `step` does, so the answer is
    // decided by the binding of `step` around the `let`, which a shared part carries up.
    let inner = Shared::new(let_(
        "apply",
        lam(&["k"], app(var("step"), vec![var("k")])),
        app(var("apply"), vec![var("n")]),
    ));
    assert!(ends(&inner), "`step` free is a prelude word");
    assert!(!ends(&Term::Lam(vec!["step".into()], inner.clone())));
    let id = lam(&["k"], var("k"));
    assert!(ends(&Term::Let(
        "step".into(),
        Shared::new(id),
        inner.clone()
    )));
    // A function bound by `let` and never called need not end.
    let unused = let_(
        "spin",
        lam(&["f"], app(var("f"), vec![var("f")])),
        lit(1i64),
    );
    assert!(ends(&unused));
    // A name bound by `let` to a value that is not a function is not one to call.
    let not_a_function = let_("g", lit(3i64), app(var("g"), vec![lit(1i64)]));
    assert!(!ends(&not_a_function));
    // A name bound to another name is that name's function.
    let renamed = let_("g", var("len"), app(var("g"), vec![var("xs")]));
    assert!(ends(&renamed));
}

#[test]
fn the_smallest_terms_and_the_forms_that_do_not_show_an_end() {
    // A call with no arguments, a lambda with no parameters, a match with no arms.
    assert!(ends(&app(lam(&[], lit(1i64)), vec![])));
    assert!(ends(&prim(Prim::Add, vec![])));
    assert!(ends(&Term::Match(Shared::new(var("v")), vec![])));
    assert!(ends(&lit(0i64)));
    assert!(ends(&var("x")));
    // `fix` and `gen`, also inside a lambda nobody calls, and also when shared by both arms.
    let fix = Shared::new(Term::Fix {
        init: Shared::new(var("d")),
        step: Shared::new(var("this")),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Definedness,
        ev: Default::default(),
    });
    assert!(!ends(&fix));
    assert!(!ends(&Term::Lam(vec![], fix.clone())));
    assert!(!ends(&if_(var("c"), fix.clone(), fix.clone())));
    let gen_ = Term::Gen {
        init: Shared::new(lit(0i64)),
        step: Shared::new(lam(&["f"], var("f"))),
        guard: Shared::new(lam(&["f"], lit(false))),
        pos: GuardPos::Before,
    };
    assert!(!ends(&gen_));
    // A `let` function whose body has a `fix` ends when it is never called, and not when it is.
    let f = || Term::Lam(vec!["x".into()], fix.clone());
    assert!(ends(&let_("f", f(), lit(1i64))));
    assert!(!ends(&let_("f", f(), app(var("f"), vec![lit(1i64)]))));
    // A call through a parameter, and through a name a pattern binds.
    assert!(!ends(&lam(&["g"], app(var("g"), vec![lit(1i64)]))));
    let by_pattern = Term::Match(
        Shared::new(var("v")),
        vec![(
            Pattern::Tuple(vec![Pattern::Bind("g".into()), Pattern::Wild]),
            app(var("g"), vec![]),
        )],
    );
    assert!(!ends(&by_pattern));
    // A family operation handed a parameter.
    let fold = Term::Fold {
        family: Shared::new(var("xs")),
        op: Shared::new(var("op")),
        identity: None,
        depth: 1,
        ev: Default::default(),
    };
    assert!(ends(&fold), "`op` free is a prelude word");
    assert!(!ends(&Term::Lam(vec!["op".into()], Shared::new(fold))));
}

/// `t0 = n; tj = if n >= j { t(j-1) } else { t(j-1) + 1 }`, `k` levels, each arm holding the
/// same `t(j-1)`: `2^k` paths, `2k + 1` distinct parts. `base` is `t0`.
fn shared_arms(k: usize, base: Term) -> Term {
    (1..=k as i64).fold(base, |t, j| {
        let t = Shared::new(t);
        let plus = prim(Prim::Add, vec![(*t).clone(), lit(1i64)]);
        let guard = prim(Prim::Ge, vec![var("n"), lit(j)]);
        if_(guard, t, Shared::new(plus))
    })
}

#[test]
fn a_chain_whose_if_arms_share_their_term_is_read_in_time_near_its_size() {
    // The walk read the term as a tree: 2^k steps.
    deep(|| {
        let n = 1000;
        let terms: BTreeMap<usize, (Term, Term)> = [n, FACTOR * n]
            .into_iter()
            .map(|k| {
                let plain = shared_arms(k, var("n"));
                // The chain on `step(n)` under `step = (k) -> k + 1`, and under a parameter
                // `step`.
                let called = Shared::new(shared_arms(k, (*calls_step()).clone()));
                let inc = lam(&["k"], prim(Prim::Add, vec![var("k"), lit(1i64)]));
                let by_let = Term::Let("step".into(), Shared::new(inc), called.clone());
                let by_param = Term::Lam(vec!["step".into()], called);
                (
                    k,
                    (
                        plain,
                        if_(var("c"), Shared::new(by_let), Shared::new(by_param)),
                    ),
                )
            })
            .collect();
        scaling::check("stage::ends on k levels of shared if arms", n, |k| {
            let (plain, both) = &terms[&k];
            assert!(ends(plain));
            assert!(!ends(both));
        });
        let (_, both) = &terms[&n];
        let Term::If(_, by_let, _) = both else {
            unreachable!("built as an if")
        };
        assert!(ends(by_let));
    });
}

#[test]
fn many_let_functions_called_at_the_end_are_read_in_time_near_their_number() {
    // `f1 = (x) -> x + 1; …; fk = (x) -> x + k; f1(f2(…fk(0)))`: the names the body needs
    // grow to k, each binder removing one.
    let lets = |k: usize| {
        let body = (1..=k)
            .rev()
            .fold(lit(0i64), |a, i| app(var(&format!("f{i}")), vec![a]));
        (1..=k).rev().fold(body, |b, i| {
            let f = lam(&["x"], prim(Prim::Add, vec![var("x"), lit(i as i64)]));
            let_(&format!("f{i}"), f, b)
        })
    };
    deep(move || {
        let n = 1000;
        let terms: BTreeMap<usize, Term> =
            [n, FACTOR * n].into_iter().map(|k| (k, lets(k))).collect();
        scaling::check("stage::ends on k let functions called at the end", n, |k| {
            assert!(ends(&terms[&k]));
        });
        // A parameter `f7` around the chain is shadowed by the `let` of `f7`.
        assert!(ends(&Term::Lam(vec!["f7".into()], Shared::new(lets(10)))));
    });
}

#[test]
fn arms_that_call_different_let_functions_on_a_shared_part_are_read_in_time_near_their_size() {
    // `tj = if c { fj(t(j-1)) } else { hj(t(j-1)) }` under `let`s of every `fj` and `hj`: the
    // names the two arms need differ by one name each and share all the rest, so the sets
    // joined at each `if` hold up to 2j names.
    let chain = |k: usize| {
        let body = (1..=k).fold(var("n"), |t, j| {
            let t = Shared::new(t);
            let f = app(var(&format!("f{j}")), vec![(*t).clone()]);
            let h = app(var(&format!("h{j}")), vec![(*t).clone()]);
            if_(var("c"), Shared::new(f), Shared::new(h))
        });
        (1..=k).rev().fold(body, |b, j| {
            let b = let_(&format!("f{j}"), lam(&["x"], var("x")), b);
            let_(&format!("h{j}"), lam(&["x"], var("x")), b)
        })
    };
    deep(move || {
        let n = 1000;
        let terms: BTreeMap<usize, Term> =
            [n, FACTOR * n].into_iter().map(|k| (k, chain(k))).collect();
        scaling::check(
            "stage::ends on k levels of arms calling let functions",
            n,
            |k| {
                assert!(ends(&terms[&k]));
            },
        );
        // With the outer `let`, of `h1`, taken out, `h1` is a parameter instead and the chain
        // does not end.
        let Term::Let(_, _, rest) = &chain(3) else {
            unreachable!("built as a let")
        };
        assert!(!ends(&Term::Lam(vec!["h1".into()], rest.clone())));
    });
}

#[ignore = "STAGE-scaling-10_5: 10.5 times the bytes at 1000 and 8000, over the limit of 10.5; open"]
#[test]
fn two_chains_of_calls_joined_at_every_level_are_read_in_time_near_their_size() {
    // `pj = aj(p(j-1))`, `qj = bj(q(j-1))` and `pj + qj` for every j, with the names `a1, b1,
    // a2, b2, …` read first so that their numbers interleave: each join is of two sets of j
    // names whose tries differ everywhere, and only the pair joined one level down is shared.
    let joined = |k: usize| {
        let shared = |t: &Shared| Term::Push("out".into(), t.clone());
        let (mut p, mut q) = (Shared::new(var("n")), Shared::new(var("n")));
        let mut sums = Vec::new();
        for j in 1..=k {
            p = Shared::new(app(var(&format!("a{j}")), vec![shared(&p)]));
            q = Shared::new(app(var(&format!("b{j}")), vec![shared(&q)]));
            sums.push(prim(Prim::Add, vec![shared(&p), shared(&q)]));
        }
        let mixed = (1..=k)
            .flat_map(|j| [format!("a{j}"), format!("b{j}")])
            .map(|x| app(var(&x), vec![]))
            .collect();
        sums.push(prim(Prim::Add, mixed));
        prim(Prim::Add, sums)
    };
    deep(move || {
        let n = 1000;
        let terms: BTreeMap<usize, Term> = [n, FACTOR * n]
            .into_iter()
            .map(|k| (k, joined(k)))
            .collect();
        scaling::check(
            "stage::ends on two chains of k calls joined at every level",
            n,
            |k| {
                assert!(ends(&terms[&k]));
            },
        );
        assert!(!ends(&Term::Lam(vec!["b2".into()], Shared::new(joined(3)))));
        assert!(ends(&Term::Lam(vec!["b4".into()], Shared::new(joined(3)))));
    });
}

/// `k` levels of shared `if` arms, each level's arm either `t + 1` or a call of a `let`
/// function, a parameter or a match arm on it, built bottom up: `pad` runs before each part is
/// allocated, so the caller decides where in memory the parts land. Returns the term and each
/// level's shared part.
fn mixed_levels(k: usize, pad: &mut dyn FnMut()) -> (Term, Vec<Shared>) {
    let mut levels = Vec::new();
    let mut t = {
        pad();
        Shared::new(var("n"))
    };
    for j in 1..=k as i64 {
        levels.push(t.clone());
        pad();
        let arm = match j % 4 {
            0 => Shared::new(prim(Prim::Add, vec![(*t).clone(), lit(j)])),
            1 => Shared::new(app(var("step"), vec![(*t).clone()])),
            2 => Shared::new(Term::Match(
                t.clone(),
                vec![
                    (Pattern::Bind("g".into()), app(var("f"), vec![var("g")])),
                    (Pattern::Wild, lit(j)),
                ],
            )),
            _ => Shared::new(app(var("f"), vec![(*t).clone(), lit(j)])),
        };
        pad();
        let guard = Shared::new(prim(Prim::Ge, vec![var("n"), lit(j)]));
        pad();
        t = Shared::new(Term::If(guard, t, arm));
    }
    pad();
    let f = Shared::new(lam(&["x", "y"], var("x")));
    pad();
    let body = Shared::new(Term::Let("f".into(), f, t));
    // Read where `step` is a `let` function and where it is a parameter.
    let inc = lam(&["k"], prim(Prim::Add, vec![var("k"), lit(1i64)]));
    pad();
    let by_let = Shared::new(Term::Let("step".into(), Shared::new(inc), body.clone()));
    pad();
    let by_param = Shared::new(Term::Lam(vec!["step".into()], body));
    (if_(var("c"), by_let, by_param), levels)
}

/// The permutation that sorts the parts by address.
fn address_order(parts: &[Shared]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..parts.len()).collect();
    order.sort_by_key(|&i| &*parts[i] as *const Term as usize);
    order
}

#[test]
fn three_allocation_orders_read_alike() {
    // The reader knows a shared part by identity while the term is borrowed; the numbers it
    // gives the parts and their answers must not depend on where the parts are in memory.
    let k = 64;
    // In order, with nothing between the parts.
    let (plain, plain_levels) = mixed_levels(k, &mut || {});
    // With blocks of growing size held between the parts, so each part lands further on.
    let mut held: Vec<Vec<u8>> = Vec::new();
    let (spaced, spaced_levels) = mixed_levels(k, &mut || held.push(vec![7; 24 + held.len()]));
    // Into holes: parts of the same size are allocated and freed, last first, before each
    // part, so the allocator hands back freed blocks in an order of its own.
    let mut holes = || {
        let blocks: Vec<Shared> = (0..9).map(|i| Shared::new(lit(i))).collect();
        blocks.into_iter().rev().step_by(2).for_each(drop);
    };
    let (reused, reused_levels) = mixed_levels(k, &mut holes);
    let orders = [
        address_order(&plain_levels),
        address_order(&spaced_levels),
        address_order(&reused_levels),
    ];
    assert!(
        orders[0] != orders[1] || orders[0] != orders[2] || orders[1] != orders[2],
        "the three builds put the parts in the same order in memory, so the test reads one order"
    );
    let first = reading(&plain);
    // Each distinct part is numbered once: a handful per level, not the 2^k places.
    assert_eq!(first.len(), 460);
    assert_eq!(reading(&spaced), first);
    assert_eq!(reading(&reused), first);
    for t in [&plain, &spaced, &reused] {
        assert!(!ends(t), "`step` as a parameter is called");
        let Term::If(_, by_let, _) = t else {
            unreachable!("built as an if")
        };
        assert!(ends(by_let));
    }
    drop(held);
}

#[test]
fn reading_a_term_built_into_freed_blocks_scales() {
    deep(|| {
        let n = 1000;
        let holes = || {
            let blocks: Vec<Shared> = (0..9).map(|i| Shared::new(lit(i))).collect();
            blocks.into_iter().rev().step_by(2).for_each(drop);
        };
        let terms: BTreeMap<usize, Term> = [n, FACTOR * n]
            .into_iter()
            .map(|k| (k, mixed_levels(k, &mut { holes }).0))
            .collect();
        scaling::check(
            "stage::ends on k mixed levels of shared if arms built into freed blocks",
            n,
            |k| {
                let t = &terms[&k];
                assert!(!ends(t));
                let Term::If(_, by_let, _) = t else {
                    unreachable!("built as an if")
                };
                assert!(ends(by_let));
            },
        );
    });
}
