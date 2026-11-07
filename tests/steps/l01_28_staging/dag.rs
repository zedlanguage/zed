//! Staging reads a term as the graph of its distinct parts (ledger STAGE-dag): `free`, the
//! effects of a part and `mix` read a part held in one `Shared` node reached from two places
//! once, known by the node's id, and `mix` gives the two places one mixed part, so neither the
//! time nor the mixed term grows with the number of places. On `d` nested `if`s whose two
//! arms are one node, which has `2^d` places, the tree walks took `2^d` steps.

use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

use zed_kernel::term::build::{lam, lit, var};
use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::scaling::{self, FACTOR};
use zedc::elab::{Def, Unit};
use zedc::stage::{self, Stage, color, free, passed};

use super::scaling::deep;

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

/// `t0 = bottom; tj = if n >= j + 1 { t(j-1) } else { t(j-1) }`, the two arms one node when
/// `shared`, else two copies built apart (`2^d` places either way, and `2^d` nodes unshared).
fn ifs(d: usize, shared: bool, bottom: &Term) -> Term {
    fn level(j: i64, below: impl Fn() -> Shared, shared: bool) -> Term {
        let bound = prim(Prim::Add, vec![lit(j), lit(1i64)]);
        let guard = Shared::new(prim(Prim::Ge, vec![var("n"), bound]));
        let x = below();
        let y = if shared { x.clone() } else { below() };
        Term::If(guard, x, y)
    }
    fn at(j: usize, shared: bool, bottom: &Term) -> Term {
        match j {
            0 => bottom.clone(),
            _ => level(j as i64, || Shared::new(at(j - 1, shared, bottom)), shared),
        }
    }
    if !shared {
        return at(d, false, bottom);
    }
    (1..=d as i64).fold(bottom.clone(), |t, j| {
        let t = Shared::new(t);
        level(j, || t.clone(), true)
    })
}

/// `f(n, 1)`: a call of a definition with a literal argument.
fn call() -> Term {
    Term::App(Shared::new(var("f")), vec![var("n"), lit(1i64)])
}

fn def(name: &str, term: Term) -> Def {
    Def {
        name: name.into(),
        kernel: name.into(),
        term: Shared::new(term),
        first_order: false,
    }
}

/// `f = (x, y) -> x + y; main = (n) -> td` with `t0 = f(n, 1)`.
fn unit(d: usize, shared: bool) -> Unit {
    let f = lam(&["x", "y"], prim(Prim::Add, vec![var("x"), var("y")]));
    let main = Term::Lam(vec!["n".into()], Shared::new(ifs(d, shared, &call())));
    Unit {
        defs: vec![def("f", f), def("main", main)],
        tests: Arc::from([]),
        warnings: Vec::new(),
    }
}

/// The number of distinct `Shared` nodes of `t`, each counted once by its id.
pub(super) fn distinct(t: &Term) -> usize {
    let mut seen = HashSet::new();
    let mut todo = vec![t];
    while let Some(t) = todo.pop() {
        let mut held = |s: &'_ Shared| seen.insert(s.id());
        match t {
            Term::Lam(_, b) => {
                if held(b) {
                    todo.push(b);
                }
            }
            Term::If(c, x, y) => {
                for s in [c, x, y] {
                    if held(s) {
                        todo.push(s);
                    }
                }
            }
            Term::App(g, args) => {
                if held(g) {
                    todo.push(g);
                }
                todo.extend(args);
            }
            Term::Let(_, e, body) => {
                for s in [e, body] {
                    if held(s) {
                        todo.push(s);
                    }
                }
            }
            Term::Prim(_, args) => todo.extend(args),
            Term::Lit(_) | Term::Var(_) => {}
            other => panic!("not in the family: {other}"),
        }
    }
    seen.len()
}

#[test]
fn mixing_nested_ifs_whose_arms_are_one_part_gives_what_the_tree_gives() {
    for d in 0..=10 {
        let (shared, tree) = (unit(d, true), unit(d, false));
        let (a, b) = (&shared.defs[1].term, &tree.defs[1].term);
        assert_eq!(a, b, "the same term, d = {d}");
        assert_eq!(free(a), free(b));
        assert_eq!(color(&shared), color(&tree));
        assert_eq!(passed(&shared, "f", 1), passed(&tree, "f", 1));
        let (mixed_shared, report_shared) = stage::mix(&shared, &["main"]);
        let (mixed_tree, report_tree) = stage::mix(&tree, &["main"]);
        let printed = |u: &Unit| u.defs[1].term.to_string();
        assert_eq!(printed(&mixed_shared), printed(&mixed_tree), "d = {d}");
        assert_eq!(report_shared, report_tree);
        if d > 0 {
            assert!(!printed(&mixed_shared).contains('+'), "each `j + 1` built");
        }
        // The two arms of each mixed `if` are one node: per level the `if` and its guard (the
        // literal of `j + 1` is held inline), and below them the call and its callee.
        assert_eq!(distinct(&mixed_shared.defs[1].term), 2 * d + 2, "d = {d}");
    }
    assert_eq!(free(&ifs(3, true, &call())).len(), 2, "`f` and `n`");
    assert_eq!(
        passed(&unit(3, true), "f", 1),
        [Value::Int(1)].into_iter().collect()
    );
}

#[test]
fn the_effects_of_a_part_shared_by_both_arms_are_read() {
    let of = |bottom: Term| Unit {
        defs: vec![def("n", lit(5i64)), def("main", ifs(12, true, &bottom))],
        tests: Arc::from([]),
        warnings: Vec::new(),
    };
    // Every name read is build-stage: the build evaluates the whole chain.
    let pure = of(var("n"));
    assert_eq!(color(&pure)[1], ("main".to_string(), Stage::Build));
    let (mixed, report) = stage::mix(&pure, &["main"]);
    assert_eq!(mixed.defs[1].term.to_string(), "5");
    assert_eq!(report.built, vec!["main".to_string()]);
    // A port read at the bottom, reached from 2^12 places, makes it run-stage; each guard is
    // built, so the chain mixes to the read alone.
    let read = Term::Read("stdin".into());
    let port = of(read.clone());
    assert_eq!(color(&port)[1], ("main".to_string(), Stage::Run));
    let (mixed, report) = stage::mix(&port, &["main"]);
    assert_eq!(mixed.defs[1].term.to_string(), read.to_string());
    assert!(report.built.is_empty());
}

#[test]
fn mixing_nested_ifs_whose_arms_are_one_part_scales() {
    deep(|| {
        let n = 1000;
        let units: BTreeMap<usize, Unit> = [n, FACTOR * n]
            .into_iter()
            .map(|d| (d, unit(d, true)))
            .collect();
        scaling::check_order(
            "stage::mix on d nested ifs whose two arms are one part",
            n,
            1,
            |d| {
                let (mixed, _) = stage::mix(&units[&d], &["main"]);
                assert_eq!(distinct(&mixed.defs[1].term), 2 * d + 2);
            },
        );
    });
}

#[test]
fn reading_nested_ifs_whose_arms_are_one_part_scales() {
    deep(|| {
        let n = 1000;
        let units: BTreeMap<usize, Unit> = [n, FACTOR * n]
            .into_iter()
            .map(|d| (d, unit(d, true)))
            .collect();
        scaling::check_order(
            "stage::free on d nested ifs whose two arms are one part",
            n,
            1,
            |d| assert_eq!(free(&units[&d].defs[1].term).len(), 1, "`f`"),
        );
        scaling::check_order(
            "stage::color, free names and effects, on d nested ifs whose two arms are one part",
            n,
            1,
            |d| assert_eq!(color(&units[&d])[1].1, Stage::Build),
        );
        scaling::check_order(
            "stage::passed on d nested ifs whose two arms are one part",
            n,
            1,
            |d| assert_eq!(passed(&units[&d], "f", 1).len(), 1),
        );
    });
}

/// `main = (x, c) -> nd` with `n0 = x` and `nj = if c { let x = x + 1; n(j-1) } else { let x =
/// x + 2; n(j-1) }`: the two `let`s are two nodes and, when `shared`, hold one body node, else
/// two copies built apart. Each `x` the body reads is a binding not known at build, so the
/// body mixes to the same term under either `let`.
fn lets(d: usize, shared: bool) -> Unit {
    fn level(below: impl Fn() -> Shared) -> Term {
        let step = |k: i64, body: Shared| {
            let e = Shared::new(prim(Prim::Add, vec![var("x"), lit(k)]));
            Term::Let("x".into(), e, body)
        };
        Term::If(
            Shared::new(var("c")),
            Shared::new(step(1, below())),
            Shared::new(step(2, below())),
        )
    }
    fn tree(j: usize) -> Shared {
        match j {
            0 => Shared::new(var("x")),
            _ => Shared::new(level(|| tree(j - 1))),
        }
    }
    let body = if shared {
        (0..d).fold(Shared::new(var("x")), |below, _| {
            Shared::new(level(|| below.clone()))
        })
    } else {
        tree(d)
    };
    Unit {
        defs: vec![def("main", Term::Lam(vec!["x".into(), "c".into()], body))],
        tests: Arc::from([]),
        warnings: Vec::new(),
    }
}

#[test]
fn mixing_nested_lets_of_a_parameter_over_one_body_gives_what_the_tree_gives() {
    for d in 0..=8 {
        let (shared, tree) = (lets(d, true), lets(d, false));
        assert_eq!(
            shared.defs[0].term, tree.defs[0].term,
            "the same term, d = {d}"
        );
        assert_eq!(color(&shared), color(&tree));
        assert_eq!(
            color(&shared)[0].1,
            Stage::Build,
            "a function is build-stage"
        );
        let (mixed_shared, report_shared) = stage::mix(&shared, &["main"]);
        let (mixed_tree, report_tree) = stage::mix(&tree, &["main"]);
        let printed = |u: &Unit| u.defs[0].term.to_string();
        assert_eq!(printed(&mixed_shared), printed(&mixed_tree), "d = {d}");
        assert_eq!(report_shared, report_tree);
        // Nothing is built, and the body below both `let`s of a level stays one node: per
        // level the `if`, its guard, the two `let`s and their two sums, and the `x` at the
        // bottom.
        assert_eq!(distinct(&mixed_shared.defs[0].term), 6 * d + 1, "d = {d}");
    }
}

#[test]
fn mixing_nested_lets_of_a_parameter_over_one_body_scales() {
    deep(|| {
        let n = 1000;
        let units: BTreeMap<usize, Unit> = [n, FACTOR * n]
            .into_iter()
            .map(|d| (d, lets(d, true)))
            .collect();
        scaling::check_order(
            "stage::mix on d nested ifs whose two arms are lets of a parameter over one body",
            n,
            1,
            |d| {
                let (mixed, _) = stage::mix(&units[&d], &["main"]);
                assert_eq!(distinct(&mixed.defs[0].term), 6 * d + 1);
            },
        );
    });
}

/// `main = (c) -> let x = 0; nd` with `n0 = x` and `nj = if c { let x = x + a; n(j-1) } else
/// { let x = x + b; n(j-1) }`: the two `let`s are two nodes and, when `shared`, hold one body
/// node, else two copies built apart. Each `x` is known at build, so the body is mixed once
/// per value of `x` that reaches it, not once per path: the mixed term is all literals.
fn built(d: usize, a: i64, b: i64, shared: bool) -> Unit {
    fn level(a: i64, b: i64, below: impl Fn() -> Shared) -> Term {
        let step = |k: i64, body: Shared| {
            let e = Shared::new(prim(Prim::Add, vec![var("x"), lit(k)]));
            Term::Let("x".into(), e, body)
        };
        Term::If(
            Shared::new(var("c")),
            Shared::new(step(a, below())),
            Shared::new(step(b, below())),
        )
    }
    fn tree(j: usize, a: i64, b: i64) -> Shared {
        match j {
            0 => Shared::new(var("x")),
            _ => Shared::new(level(a, b, || tree(j - 1, a, b))),
        }
    }
    let body = if shared {
        (0..d).fold(Shared::new(var("x")), |below, _| {
            Shared::new(level(a, b, || below.clone()))
        })
    } else {
        tree(d, a, b)
    };
    let main = Term::Let("x".into(), Shared::new(lit(0i64)), body);
    Unit {
        defs: vec![def("main", Term::Lam(vec!["c".into()], Shared::new(main)))],
        tests: Arc::from([]),
        warnings: Vec::new(),
    }
}

#[test]
fn mixing_nested_lets_of_a_built_value_over_one_body_gives_what_the_tree_gives() {
    for (a, b) in [(0, 0), (1, 2), (1, 1), (2, -2)] {
        for d in 0..=8 {
            let (shared, tree) = (built(d, a, b, true), built(d, a, b, false));
            assert_eq!(shared.defs[0].term, tree.defs[0].term, "d = {d}");
            let (mixed_shared, report_shared) = stage::mix(&shared, &["main"]);
            let (mixed_tree, report_tree) = stage::mix(&tree, &["main"]);
            let printed = |u: &Unit| u.defs[0].term.to_string();
            assert_eq!(printed(&mixed_shared), printed(&mixed_tree), "d = {d}");
            assert_eq!(report_shared, report_tree);
            assert!(!printed(&mixed_shared).contains('+'), "each sum built");
            assert_eq!(
                distinct(&mixed_shared.defs[0].term),
                nodes(d, a == b),
                "d = {d}"
            );
        }
    }
}

/// The distinct nodes of `built(d, a, b)` mixed: per level the `if` and its guard over one
/// node below, when `a = b`; else at level `k` from the top one node for each of the `k + 1`
/// values of `x` there.
fn nodes(d: usize, same: bool) -> usize {
    match (d, same) {
        (0, _) => 1,
        (_, true) => 2 * d + 2,
        (_, false) => d * (d + 7) / 2,
    }
}

#[test]
fn mixing_nested_lets_of_a_built_value_over_one_body_scales() {
    deep(|| {
        let n = 1000;
        let same: BTreeMap<usize, Unit> = [n, FACTOR * n]
            .into_iter()
            .map(|d| (d, built(d, 0, 0, true)))
            .collect();
        scaling::check_order(
            "stage::mix on d nested ifs whose two arms are lets of one built value over one body",
            n,
            1,
            |d| {
                let (mixed, _) = stage::mix(&same[&d], &["main"]);
                assert_eq!(distinct(&mixed.defs[0].term), nodes(d, true));
            },
        );
        // The mixed term has a node for each value of `x` at each level, d(d + 7)/2 in all.
        let n = 50;
        let apart: BTreeMap<usize, Unit> = [n, FACTOR * n]
            .into_iter()
            .map(|d| (d, built(d, 1, 2, true)))
            .collect();
        scaling::check_order(
            "stage::mix on d nested ifs whose two arms are lets of two built values over one body",
            n,
            2,
            |d| {
                let (mixed, _) = stage::mix(&apart[&d], &["main"]);
                assert_eq!(distinct(&mixed.defs[0].term), nodes(d, false));
            },
        );
    });
}

/// `main = (c) -> let f = (y) -> y; nd` with `n0 = f(1)` and `nj = if c { let f = (y) -> f(y)
/// + 1; n(j-1) } else { let f = (y) -> f(y) + 2; n(j-1) }`, the two `let`s holding one body
/// node when `shared`. Each `f` is a function known at build, a different one on each path.
fn composed(d: usize, shared: bool) -> Unit {
    fn level(below: impl Fn() -> Shared) -> Term {
        let step = |k: i64, body: Shared| {
            let call = Term::App(Shared::new(var("f")), vec![var("y")]);
            let e = Shared::new(lam(&["y"], prim(Prim::Add, vec![call, lit(k)])));
            Term::Let("f".into(), e, body)
        };
        Term::If(
            Shared::new(var("c")),
            Shared::new(step(1, below())),
            Shared::new(step(2, below())),
        )
    }
    fn tree(j: usize) -> Shared {
        match j {
            0 => Shared::new(Term::App(Shared::new(var("f")), vec![lit(1i64)])),
            _ => Shared::new(level(|| tree(j - 1))),
        }
    }
    let body = if shared {
        let bottom = Shared::new(Term::App(Shared::new(var("f")), vec![lit(1i64)]));
        (0..d).fold(bottom, |below, _| Shared::new(level(|| below.clone())))
    } else {
        tree(d)
    };
    let main = Term::Let("f".into(), Shared::new(lam(&["y"], var("y"))), body);
    Unit {
        defs: vec![def("main", Term::Lam(vec!["c".into()], Shared::new(main)))],
        tests: Arc::from([]),
        warnings: Vec::new(),
    }
}

#[test]
fn mixing_lets_of_composed_functions_over_one_body_gives_what_the_tree_gives() {
    for d in 0..=6 {
        let (shared, tree) = (composed(d, true), composed(d, false));
        assert_eq!(shared.defs[0].term, tree.defs[0].term, "d = {d}");
        let (mixed_shared, report_shared) = stage::mix(&shared, &["main"]);
        let (mixed_tree, report_tree) = stage::mix(&tree, &["main"]);
        let printed = |u: &Unit| u.defs[0].term.to_string();
        assert_eq!(printed(&mixed_shared), printed(&mixed_tree), "d = {d}");
        assert_eq!(report_shared, report_tree);
    }
    // Each call `f(1)` at the bottom is built: f is y + s for the sum s of the path's steps.
    let (mixed, _) = stage::mix(&composed(2, true), &["main"]);
    assert!(
        mixed.defs[0]
            .term
            .to_string()
            .contains("if c { 3 } else { 4 }")
    );
}

/// A function bound on each path is numbered by its kind, and a part that calls it is keyed by
/// what it asked of it (COMPLEXITY.md F83): the `2^k` functions on the paths to level `k` take
/// `k + 1` values at 1, so the parts below level `k` are mixed once for each, and the mixed
/// term has `(3d^2 + 17d - 6) / 2` nodes, not `2^d` (before: 1298, 5144, 20510, 81956 nodes at
/// d = 8, 10, 12, 14). The quadratic is the output's own: it holds `d(d + 1) / 2` distinct `if`s, the
/// `k + 1` at depth `k` differing in the literals below them (the argument is at `Mixer::eval`),
/// so the test allows power 2.
#[test]
fn mixing_lets_of_composed_functions_over_one_body_scales() {
    deep(|| {
        let n = 12;
        let units: BTreeMap<usize, Unit> = [n, FACTOR * n]
            .into_iter()
            .map(|d| (d, composed(d, true)))
            .collect();
        scaling::check_order(
            "stage::mix on d nested ifs whose two arms are lets of two composed functions over one body",
            n,
            2,
            |d| {
                let (mixed, _) = stage::mix(&units[&d], &["main"]);
                assert_eq!(distinct(&mixed.defs[0].term), (3 * d * d + 17 * d - 6) / 2);
            },
        );
    });
}

/// A call whose argument holds a float zero is not answered by the function's stub, since the
/// key a port is asked reads `-0.0` as `0.0`: the part is evaluated as written, and
/// `f(-0.0)` is `1.0 / -0.0`, not `1.0 / 0.0`.
#[test]
fn a_call_the_stubs_cannot_answer_is_mixed_as_written() {
    let call = Shared::new(Term::App(
        Shared::new(var("f")),
        vec![Term::Lit(Value::float(-0.0))],
    ));
    let body = Term::If(Shared::new(var("c")), call.clone(), call);
    let f = lam(
        &["y"],
        prim(Prim::Div, vec![Term::Lit(Value::float(1.0)), var("y")]),
    );
    let main = Term::Let("f".into(), Shared::new(f), Shared::new(body));
    let unit = Unit {
        defs: vec![def("main", Term::Lam(vec!["c".into()], Shared::new(main)))],
        tests: Arc::from([]),
        warnings: Vec::new(),
    };
    let (mixed, report) = stage::mix(&unit, &["main"]);
    let printed = mixed.defs[0].term.to_string();
    let shown = |x: f64| Term::Lit(Value::float(x)).to_string();
    let (minus, plus) = (shown(f64::NEG_INFINITY), shown(f64::INFINITY));
    assert!(printed.contains(&minus), "{printed}");
    assert!(!printed.replace(&minus, "").contains(&plus), "{printed}");
    assert!(report.left.is_empty(), "{report:?}");
}

/// A call at a string held in more than one block is not answered by the function's stub:
/// `"a"` doubled 62 times is 56 nodes and `2^62` bytes long, and comparing it with a key asked
/// before would read every byte. The part is evaluated as written.
#[test]
fn a_call_at_a_long_join_is_mixed_as_written() {
    let twice = lam(&["s"], prim(Prim::Concat, vec![var("s"), var("s")]));
    let long = (0..62).fold(lit("a"), |s, _| {
        Term::App(Shared::new(var("twice")), vec![s])
    });
    let call = Term::App(Shared::new(var("f")), vec![long]);
    let part = Shared::new(Term::Let(
        "twice".into(),
        Shared::new(twice),
        Shared::new(call),
    ));
    let body = Term::If(Shared::new(var("c")), part.clone(), part);
    let main = Term::Let(
        "f".into(),
        Shared::new(lam(&["s"], lit(1i64))),
        Shared::new(body),
    );
    let unit = Unit {
        defs: vec![def("main", Term::Lam(vec!["c".into()], Shared::new(main)))],
        tests: Arc::from([]),
        warnings: Vec::new(),
    };
    let (mixed, report) = stage::mix(&unit, &["main"]);
    assert!(
        mixed.defs[0]
            .term
            .to_string()
            .contains("if c { 1 } else { 1 }")
    );
    assert!(report.left.is_empty(), "{report:?}");
}
/// `main = (n) -> n + td` with `t0 = w(w)`, `w = (f) -> f(f)`, and `tj = if j >= 1 { t(j-1) }
/// else { t(j-1) }`, the two arms one node: a build-stage term whose form does not show that
/// it ends, so mixing leaves it to run and records it in the report. The report holds the term
/// itself, its arms still one node, so the test compares it with `td` by structure (each
/// `Shared` compared first by id); its text, printed as a tree, is 2^d long (STAGE-print).
/// Before repair 5 the report held `t.to_string()`, 2^d time and text (repair 4, release
/// build, load 9: 2.3, 36, 143, 589, 2238 ms and 30.7 KB, 492 KB, 1.97 MB, 7.86 MB, 31.5 MB at
/// d = 10, 14, 16, 18, 20).
#[test]
fn reporting_a_term_left_to_run_whose_arms_are_one_part_scales() {
    fn unit(d: usize) -> (Unit, Term) {
        let w = lam(&["f"], Term::App(Shared::new(var("f")), vec![var("f")]));
        let bottom = Term::App(Shared::new(var("w")), vec![var("w")]);
        let t = (1..=d as i64).fold(bottom, |t, j| {
            let t = Shared::new(t);
            let guard = Shared::new(prim(Prim::Ge, vec![lit(j), lit(1i64)]));
            Term::If(guard, t.clone(), t)
        });
        let main = Term::Lam(
            vec!["n".into()],
            Shared::new(prim(Prim::Add, vec![var("n"), t.clone()])),
        );
        let unit = Unit {
            defs: vec![def("w", w), def("main", main)],
            tests: Arc::from([]),
            warnings: Vec::new(),
        };
        (unit, t)
    }
    // The text on a small input, where it is small: both arms written out.
    let (small, t) = unit(1);
    let (_, report) = stage::mix(&small, &["main"]);
    assert_eq!(report.left.len(), 1, "{report:?}");
    assert_eq!(*report.left[0].0, t);
    assert_eq!(
        report.left[0].0.to_string(),
        "if (1 >= 1) { w(w) } else { w(w) }"
    );
    assert_eq!(report.left[0].1, "its form does not show that it ends");
    deep(|| {
        let n = 1000;
        let units: BTreeMap<usize, (Unit, Term)> =
            [n, FACTOR * n].into_iter().map(|d| (d, unit(d))).collect();
        scaling::check_order(
            "stage::mix and its report of a term left to run, on d nested ifs whose two arms \
             are one node",
            n,
            1,
            |d| {
                let (unit, t) = &units[&d];
                let (_, report) = stage::mix(unit, &["main"]);
                assert_eq!(report.left.len(), 1);
                assert!(*report.left[0].0 == *t, "the term left to run is td");
                assert_eq!(report.left[0].1, "its form does not show that it ends");
            },
        );
    });
}
