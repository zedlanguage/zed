//! Staging at the rule of low complexity (DESIGN.md Part G). Deciding the stage of a term
//! read its free names, and `mix` decided it at every node it entered, so a body of `n`
//! nested definitions was read `O(n)` times, each reading through a scope of `O(n)` names.

use std::collections::BTreeMap;

use zed_tests::scaling::{self, FACTOR};
use zedc::elab::Unit;
use zedc::stage::{Domain, Specializer, passed};

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
    use std::sync::Arc;
    use zed_kernel::Term;
    use zed_kernel::term::build::var;
    use zedc::stage::ends;
    let lets = |n: usize| {
        (1..=n).rev().fold(var(&format!("x{n}")), |b, i| {
            let e = Term::App(Arc::new(var("len")), vec![var(&format!("x{}", i - 1))]);
            Term::Let(format!("x{i}").into(), Arc::new(e), Arc::new(b))
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
        let call_f = |b| Term::App(Arc::new(var("f")), vec![b]);
        let bound_to_param = Term::Lam(vec!["f".into()], Arc::new(lets(3)));
        assert!(ends(&bound_to_param), "`len` is not `f`");
        let calls_param = Term::Lam(vec!["f".into()], Arc::new(call_f(lets(3))));
        assert!(!ends(&calls_param));
    });
}

/// `n` functions `f{i}`, each called by a `z{i}` with its own literal.
fn many_callees(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!("f{i}(x: int, y: int) = x * y + {i};\nz{i}(a: int) = f{i}(x: {i}, y: a);\n")
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
            let (lam, _) = s.split(&format!("f{i}"), 0, &d).unwrap();
            assert!(matches!(lam, zed_kernel::Term::Lam(..)));
        }
    });
}
