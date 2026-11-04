//! Staging at the rule of low complexity (DESIGN.md Part G). Deciding the stage of a term
//! read its free names, and `mix` decided it at every node it entered, so a body of `n`
//! nested definitions was read `O(n)` times, each reading through a scope of `O(n)` names.

use std::collections::BTreeMap;
use zed_kernel::Shared;

use std::sync::Arc;
use zed_tests::scaling::{self, FACTOR};

use zed_kernel::term::build::{if_, lam, let_, lit, prim, var};
use zed_kernel::term::{Prim, Term};
use zedc::elab::{Def, Unit};
use zedc::stage::{Domain, Specializer, Stage, color, ends, free, mix, passed};

use super::{out, staged};
use crate::l01_16_elaboration::elab;

/// `main` with `n` local definitions in a chain from a port, each read by the next; `all`
/// writes their sum, so the last term reads every one.
fn chain(n: usize, all: bool) -> String {
    let mut s = String::from("main(stdin: Lines) -> (stdout: Lines) {\n");
    s += "  x0 = int(stdin[1]) else 0;\n";
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
    s += &format!("  stdout <- String({last});\n}}\n");
    s
}

/// `f` on a thread whose stack holds the recursion of a body `O(n)` deep.
pub(super) fn deep(f: impl FnOnce() + Send + 'static) {
    let t = std::thread::Builder::new().stack_size(1 << 29).spawn(f);
    t.unwrap().join().unwrap();
}

#[test]
fn mixing_a_chain_of_local_definitions_scales() {
    deep(|| {
        scaling::check("mixing a chain of n run-stage definitions", 400, |n| {
            let (_, s, report) = staged(&chain(n, false));
            assert!(report.left.is_empty());
            assert_eq!(out(&s, "1\n"), format!("{}\n", 1 + n * (n + 1) / 2));
        })
    });
}

#[test]
fn mixing_a_term_that_reads_every_definition_scales() {
    deep(|| {
        scaling::check(
            "mixing a chain of n definitions all read at the end",
            200,
            |n| {
                let (_, s, _) = staged(&chain(n, true));
                let want: usize = (0..=n).map(|i| 1 + i * (i + 1) / 2).sum();
                assert_eq!(out(&s, "1\n"), format!("{want}\n"));
            },
        )
    });
}

/// `f` and `n` definitions, each calling it with its own literal.
fn callers(n: usize) -> String {
    let mut s = String::from("f(x: int, y: int) = x + y;\n");
    for i in 0..n {
        s += &format!("z{i}(a: int) = f(x: {i}, y: a);\n");
    }
    s
}

#[test]
fn the_values_passed_by_many_definitions_are_read_in_time_that_scales() {
    // Each definition was looked for among the names of all of them.
    let units: BTreeMap<usize, Unit> = [2000, FACTOR * 2000]
        .into_iter()
        .map(|n| (n, elab(&callers(n)).unwrap()))
        .collect();
    scaling::check("the values passed by n definitions", 2000, |n| {
        assert_eq!(passed(&units[&n], "f", 0).len(), n);
    });
}

#[test]
fn the_form_rule_on_many_nested_lets_calling_a_prelude_word_scales() {
    // Each call through a name looked for it among every name bound around the call, and a
    // prelude word is bound by none of them.
    use zed_kernel::Term;
    use zed_kernel::term::build::var;
    use zedc::stage::ends;
    let lets = |n: usize| {
        (1..=n).rev().fold(var(&format!("x{n}")), |b, i| {
            let e = Term::App(Shared::new(var("len")), vec![var(&format!("x{}", i - 1))]);
            Term::Let(format!("x{i}").into(), Shared::new(e), Shared::new(b))
        })
    };
    deep(move || {
        let terms: BTreeMap<usize, Term> = [1000, FACTOR * 1000]
            .into_iter()
            .map(|n| (n, lets(n)))
            .collect();
        scaling::check("the form rule on n nested lets", 1000, |n| {
            assert!(ends(&terms[&n]));
        });
        let call_f = |b| Term::App(Shared::new(var("f")), vec![b]);
        let bound_to_param = Term::Lam(vec!["f".into()], Shared::new(lets(3)));
        assert!(ends(&bound_to_param), "`len` is not `f`");
        let calls_param = Term::Lam(vec!["f".into()], Shared::new(call_f(lets(3))));
        assert!(!ends(&calls_param));
    });
}

/// `n` functions `h{i}`, each called by a `z{i}` with its own literal.
fn many_callees(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!("h{i}(x: int, y: int) = x * y + {i};\nz{i}(a: int) = h{i}(x: {i}, y: a);\n")
        })
        .collect()
}

#[test]
fn splitting_many_functions_of_one_unit_scales() {
    // Each split mixed the whole unit again to find the values its calls pass, so splitting
    // each of `n` functions took `O(n²)`; the calls are now read from one mix.
    let units: BTreeMap<usize, Unit> = [200, FACTOR * 200]
        .into_iter()
        .map(|n| (n, elab(&many_callees(n)).unwrap()))
        .collect();
    let d = Domain::Ints(Some(0), Some(1 << 20));
    scaling::check_order("splitting n functions of a unit", 200, 1, |n| {
        let mut s = Specializer::new(&units[&n]);
        for i in 0..n {
            let (lam, _) = s.split(&format!("h{i}"), 0, &d).unwrap();
            assert!(matches!(lam, zed_kernel::Term::Lam(..)));
        }
    });
}

/// `main(p) = t` for each run-stage shape `t`, `n` deep, with the build-stage sum
/// `0 + 1 + … + 1` of `n` terms whose form shows that it ends.
fn deep_units(n: usize) -> Vec<(&'static str, Unit, Term)> {
    let x = |i: usize| format!("x{i}");
    let chain = (0..n).rev().fold(var(&x(n - 1)), |body, i| {
        let e = match i {
            0 => var("p"),
            _ => prim(Prim::Add, vec![var(&x(i - 1)), lit(1)]),
        };
        let_(&x(i), e, body)
    });
    let sum = (0..n).fold(var("p"), |a, _| prim(Prim::Add, vec![a, lit(1)]));
    let ifs = (0..n).fold(lit(0), |b, _| if_(var("p"), lit(1), b));
    let lams = (0..n).rev().fold(var("p"), |body, i| lam(&[&x(i)], body));
    let unit = |t: Term| Unit {
        defs: vec![Def {
            name: "main".into(),
            kernel: "main".into(),
            term: Shared::new(lam(&["p"], t)),
            first_order: false,
        }],
        tests: Arc::new([]),
        warnings: Vec::new(),
    };
    // Built once per shape: cloning a term recursed (step T2-types).
    let ends = || (0..n).fold(lit(0), |a, _| prim(Prim::Add, vec![a, lit(1)]));
    vec![
        ("a `let` chain", unit(chain), ends()),
        ("a left-nested sum", unit(sum), ends()),
        ("`if`s nested in their `else`", unit(ifs), ends()),
        ("nested lambdas", unit(lams), ends()),
    ]
}

#[test]
fn terms_100000_deep_are_staged_on_a_2_mib_stack() {
    // Reading the free names, the effects and whether a term ends, indexing it and mixing it
    // each recursed once per level of the term, and overflowed this stack near 10,000 levels.
    let n = 12_500;
    let deep = 8 * n;
    zed_tests::deep::on_small_stack(|| {
        let small = deep_units(n);
        let large = deep_units(deep);
        for ((what, s, se), (_, l, le)) in small.into_iter().zip(large) {
            let pick = |k: usize| if k == n { (&s, &se) } else { (&l, &le) };
            scaling::check_order(&format!("mixing {what}"), n, 1, |k| {
                let (mixed, report) = mix(pick(k).0, &["main"]);
                assert!(report.left.is_empty(), "{what}");
                assert!(free(&mixed.defs[0].term).is_empty(), "{what}");
            });
            scaling::check_order(&format!("coloring {what}"), n, 1, |k| {
                assert_eq!(color(pick(k).0), [("main".to_string(), Stage::Build)]);
            });
            scaling::check_order("deciding that a sum ends", n, 1, |k| {
                assert!(ends(pick(k).1));
            });
        }
    });
}

/// `main` with `n` bindings, each the square of a machine-word integer, so each is warned.
fn squares(n: usize) -> String {
    let mut s = String::from("main(stdin: Lines) -> (stdout: Lines) {\n");
    for i in 0..n {
        s += &format!("  a{i} = {} * 3037000500;\n", 3037000500 + i);
    }
    s += "  stdout <- String(0);\n}\n";
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
