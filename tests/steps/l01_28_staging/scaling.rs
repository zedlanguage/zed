//! Staging at the rule of low complexity (DESIGN.md Part G). Deciding the stage of a term
//! read its free names, and `mix` decided it at every node it entered, so a body of `n`
//! nested definitions was read `O(n)` times, each reading through a scope of `O(n)` names.
//! The checks at `n` and `8n`, and of each deep shape at depths that overflowed a stack of 2 MiB,
//! are in `bench::scaling`; these tests run the same checks at small sizes on the default stack.

use zed_kernel::Shared;

use std::sync::Arc;

use zed_kernel::term::build::{if_, lam, let_, lit, prim, var};
use zed_kernel::term::{Prim, Term};
use zedc::elab::{Def, Unit};
use zedc::run::{Program, load};
use zedc::stage::{Domain, Specializer, Stage, color, ends, free, mix, passed};

use super::out;
use zed_tests::step_helpers::l01_16_elaboration::elab;

/// `main` with `n` local definitions in a chain from a port, each read by the next; `all`
/// writes their sum, so the last term reads every one.
pub(super) fn chain(n: usize, all: bool) -> String {
    let mut s = String::from("main(m: MainArgs) {\n");
    s += "  x0 = int(m.stdin[0]) else 0;\n";
    for i in 1..=n {
        s += &format!("  x{i} = x{} + {i};\n", i - 1);
    }
    let last = match all {
        true => (0..=n)
            .map(|i| format!("x{i}"))
            .collect::<Vec<_>>()
            .join(" + "),
        false => format!("x{n}"),
    };
    s += &format!("  m.stdout <- String({last});\n}}\n");
    s
}

/// `p`, a loaded [`chain`], stages with nothing left to run.
pub(super) fn a_chain_staged(p: &Program) -> Program {
    let (s, report) = p.stage();
    assert!(report.left.is_empty());
    s
}

/// What the staged program of `chain(n, all)` writes on input 1: `1 + 1 + … + n` for the last
/// definition, and the sum of every definition's value for `all`.
fn chain_gives(n: usize, all: bool) -> usize {
    let x = |i: usize| 1 + i * (i + 1) / 2;
    match all {
        true => (0..=n).map(x).sum(),
        false => x(n),
    }
}

/// Chains of 1, 2 and 9 definitions, the last read and all read, staged and run
/// (`bench::scaling` times 400 and 200 definitions).
#[test]
fn mixing_a_chain_of_local_definitions() {
    for n in [1, 2, 9] {
        for all in [false, true] {
            let s = a_chain_staged(&load(chain(n, all).as_bytes()).unwrap());
            assert_eq!(out(&s, "1\n"), format!("{}\n", chain_gives(n, all)));
        }
    }
}

/// `f` and `n` definitions, each calling it with its own literal.
pub(super) fn callers(n: usize) -> String {
    let mut s = String::from("f(x: int, y: int) = x + y;\n");
    for i in 0..n {
        s += &format!("z{i}(a: int) = f(x: {i}, y: a);\n");
    }
    s
}

/// `u`, [`callers`]`(n)` elaborated, passes `n` values to `f`'s first parameter.
pub(super) fn the_values_passed(u: &Unit, n: usize) {
    assert_eq!(passed(u, "f", 0).len(), n);
}

/// 0, 1, 2 and 9 definitions calling `f` (`bench::scaling` times 2000 and 16,000).
#[test]
fn the_values_passed_by_many_definitions_are_read() {
    for n in [0, 1, 2, 9] {
        the_values_passed(&elab(&callers(n)).unwrap(), n);
    }
}

/// `n` nested lets, each binding `x_i` to `len(x_{i-1})`, around `x_n`.
pub(super) fn nested_lets_calling_len(n: usize) -> Term {
    (1..=n).rev().fold(var(&format!("x{n}")), |b, i| {
        let e = Term::App(Shared::new(var("len")), vec![var(&format!("x{}", i - 1))]);
        Term::Let(format!("x{i}").into(), Shared::new(e), Shared::new(b))
    })
}

/// The form rule on 1, 2 and 9 nested lets calling the prelude word `len`, and on a parameter
/// `f` around them, called and not (`bench::scaling` times 1000 and 8000 lets).
#[test]
fn the_form_rule_on_nested_lets_calling_a_prelude_word() {
    for n in [1, 2, 9] {
        assert!(ends(&nested_lets_calling_len(n)));
    }
    let call_f = |b| Term::App(Shared::new(var("f")), vec![b]);
    let bound_to_param = Term::Lam(vec!["f".into()], Shared::new(nested_lets_calling_len(3)));
    assert!(ends(&bound_to_param), "`len` is not `f`");
    let calls_param = Term::Lam(
        vec!["f".into()],
        Shared::new(call_f(nested_lets_calling_len(3))),
    );
    assert!(!ends(&calls_param));
}

/// `n` functions `h{i}`, each called by a `z{i}` with its own literal.
pub(super) fn many_callees(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!("h{i}(x: int, y: int) = x * y + {i};\nz{i}(a: int) = h{i}(x: {i}, y: a);\n")
        })
        .collect()
}

/// `u`, [`many_callees`]`(n)` elaborated, splits each of its `n` functions on its first
/// parameter into a lambda.
pub(super) fn every_function_split(u: &Unit, n: usize) {
    let d = Domain::Ints(Some(0), Some(1 << 20));
    let mut s = Specializer::new(u);
    for i in 0..n {
        let (lam, _) = s.split(&format!("h{i}"), 0, &d).unwrap();
        assert!(matches!(lam, zed_kernel::Term::Lam(..)));
    }
}

/// 1, 2 and 9 functions of one unit, each split (`bench::scaling` times 200 and 1600).
#[test]
fn splitting_many_functions_of_one_unit() {
    for n in [1, 2, 9] {
        every_function_split(&elab(&many_callees(n)).unwrap(), n);
    }
}

/// A run-stage shape of `main`'s body, `n` deep.
#[derive(Clone, Copy)]
pub(super) enum Shape {
    /// A `let` chain from `p`.
    Chain,
    /// A left-nested sum on `p`.
    Sum,
    /// `if`s on `p` nested in their `else`.
    Ifs,
    /// Nested lambdas over `p`.
    Lams,
}

impl Shape {
    pub(super) fn name(self) -> &'static str {
        match self {
            Shape::Chain => "a `let` chain",
            Shape::Sum => "a left-nested sum",
            Shape::Ifs => "`if`s nested in their `else`",
            Shape::Lams => "nested lambdas",
        }
    }
}

/// `main(p) = t` for the run-stage `shape` `t`, `n` deep, with the build-stage sum
/// `0 + 1 + … + 1` of `n` terms whose form shows that it ends.
pub(super) fn deep_unit(shape: Shape, n: usize) -> (Unit, Term) {
    let x = |i: usize| format!("x{i}");
    let t = match shape {
        Shape::Chain => (0..n).rev().fold(var(&x(n - 1)), |body, i| {
            let e = match i {
                0 => var("p"),
                _ => prim(Prim::Add, vec![var(&x(i - 1)), lit(1)]),
            };
            let_(&x(i), e, body)
        }),
        Shape::Sum => (0..n).fold(var("p"), |a, _| prim(Prim::Add, vec![a, lit(1)])),
        Shape::Ifs => (0..n).fold(lit(0), |b, _| if_(var("p"), lit(1), b)),
        Shape::Lams => (0..n).rev().fold(var("p"), |body, i| lam(&[&x(i)], body)),
    };
    let unit = Unit {
        defs: vec![Def {
            name: "main".into(),
            kernel: "main".into(),
            term: Shared::new(lam(&["p"], t)),
            first_order: false,
        }],
        tests: Arc::new([]),
        warnings: Vec::new(),
        int_params: Default::default(),
        limits: Default::default(),
    };
    // Built once per shape: cloning a term recursed (step T2-types).
    let ends = (0..n).fold(lit(0), |a, _| prim(Prim::Add, vec![a, lit(1)]));
    (unit, ends)
}

/// `u`, a [`deep_unit`] of `shape`, mixes with nothing left to run and no free name.
pub(super) fn a_deep_unit_mixed(u: &Unit, shape: Shape) {
    let (mixed, report) = mix(u, &["main"]);
    assert!(report.left.is_empty(), "{}", shape.name());
    assert!(free(&mixed.defs[0].term).is_empty(), "{}", shape.name());
}

/// `u`, a [`deep_unit`], colors `main` build-stage.
pub(super) fn a_deep_unit_colored(u: &Unit) {
    assert_eq!(color(u), [("main".to_string(), Stage::Build)]);
}

/// Each shape a few levels deep mixes and colors, and its sum ends, on the default stack. The
/// shapes deeper than a 2 MiB stack held before the walks kept their frames on the heap (about
/// 10,000 levels) are benchmarks since TEST-bench-move-l0125 (author P178): `bench::scaling`
/// runs them 6,250 and 50,000 deep on a 2 MiB stack, with the same checks.
#[test]
fn each_shape_a_few_levels_deep_is_staged() {
    for shape in [Shape::Chain, Shape::Sum, Shape::Ifs, Shape::Lams] {
        for depth in [1, 2, 3, 10] {
            let (u, ends_term) = deep_unit(shape, depth);
            a_deep_unit_mixed(&u, shape);
            a_deep_unit_colored(&u);
            assert!(ends(&ends_term), "{} {depth} deep", shape.name());
        }
    }
}

/// `main` with `n` bindings, each the square of a machine-word integer, so each is warned.
fn squares(n: usize) -> String {
    let mut s = String::from("main(m: MainArgs) {\n");
    for i in 0..n {
        s += &format!("  a{i} = {} * 3037000500;\n", 3037000500 + i);
    }
    s += "  m.stdout <- String(0);\n}\n";
    s
}

#[test]
fn mixing_a_unit_does_not_copy_its_warnings() {
    // The mixed unit copied the unit's warnings, which nothing reads from it, so mixing a unit
    // of `n` warnings allocated their bytes again. Now it allocates what the same unit with
    // no warnings does.
    let n = 1000;
    let with = elab(&squares(n)).unwrap();
    assert_eq!(with.warnings.len(), n);
    let without = Unit {
        defs: with.defs.clone(),
        tests: with.tests.clone(),
        warnings: Vec::new(),
        int_params: with.int_params.clone(),
        limits: with.limits,
    };
    let bytes = |u: &Unit| {
        let start = zed_alloc_count::allocated();
        let (mixed, _) = mix(u, &["main"]);
        assert!(mixed.warnings.is_empty());
        zed_alloc_count::allocated() - start
    };
    // The first mix in the process may allocate some state once; it is left out.
    bytes(&without);
    assert_eq!(bytes(&with), bytes(&without));
}
