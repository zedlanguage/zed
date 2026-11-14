//! The programs the benchmarks of `bench/scaling.rs` resolve, and what each resolution must be,
//! checked here at small sizes (TEST-bench-move-rest, P170). The deep programs resolved 20,000
//! deep on a 2 MiB stack are in `bench/deep.rs`.

use zedc::ast::Stmt;
use zedc::resolve::{Ref, Resolution};

use super::{at, errors, run};
pub(crate) use zed_tests::step_helpers::l01_14_name_resolution::overloads;

/// Blocks nested `n` deep, each binding a name, the innermost reading the top-level `c` `n`
/// times.
pub(super) fn nested(n: usize) -> String {
    let mut src = "c = 1;\nmain = ".to_string();
    for i in 0..n {
        src += &format!("{{\ny{i} = c;\n");
    }
    src += &format!("{}\n", vec!["c"; n].join(" + "));
    src += &"}\n".repeat(n);
    src + ";\n"
}

/// Resolves `k` overloads of one function and checks that each binds its name and its five
/// parameters.
pub(super) fn declares_overloads(k: usize) {
    assert_eq!(run(&overloads(k)).unwrap().binders.len(), 6 * k);
}

/// The statements of `k` overloads of `f` and one tuple of `k` uses of `f`, so that little but
/// the lookup is done for each use, built for the timing to measure resolution alone.
pub(super) fn used(k: usize) -> Vec<Stmt> {
    let text = overloads(k) + "g = (" + &vec!["f"; k].join(", ") + ");\n";
    let tokens = zedc::lex::lex_fence(&text).unwrap();
    let tree = zedc::parse::parse(&text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    zedc::ast::unit(&text, &tokens, &tree).unwrap()
}

/// Resolves `stmts`, the [`used`] of `k`, and checks that `k` uses are bound to `k` overloads
/// each.
pub(super) fn uses_resolve(stmts: &[Stmt], k: usize) -> Resolution {
    let r = zedc::resolve::resolve(stmts).unwrap();
    let sets = r
        .uses
        .values()
        .filter(|f| matches!(f, Ref::Bound(ids) if ids.len() == k));
    assert_eq!(sets.count(), k);
    r
}

/// Checks that every use in `r`, the resolution of the [`used`] of `n`, holds the one list of
/// overloads, not a copy of it. The timing alone does not tell a shared list from `n` copies at
/// the benchmark's sizes. A list of three or fewer is stored inline and copied, which costs no
/// more than a pointer, so `n` is more than 3.
pub(super) fn uses_share_one_list(r: &Resolution, n: usize) {
    assert!(n > 3, "a list of {n} is stored inline");
    let lists: Vec<_> = r
        .uses
        .values()
        .filter_map(|f| match f {
            Ref::Bound(ids) if ids.len() == n => Some(ids),
            _ => None,
        })
        .collect();
    assert_eq!(lists.len(), n);
    assert!(lists.iter().all(|ids| ids.ptr_eq(lists[0])));
}

/// Checks `r`, the resolution of the deep program of `shape` nested `deep` deep, for what that
/// shape binds: the `c` in nested blocks is the top level's, nested lambdas bind their
/// parameters in written order, and each nested call names the one `f`. Every resolution binds
/// some name.
pub(super) fn deep_resolves(shape: &str, r: &Resolution, deep: usize) {
    assert!(!r.binders.is_empty(), "{shape}");
    match shape {
        // The `c` inside every block is the top level's.
        "nested blocks" => {
            let c = r.binders.iter().position(|b| b.name == "c").unwrap();
            let reads_c = r.uses.values().filter(|u| **u == Ref::Bound([c].into()));
            assert_eq!(reads_c.count(), 1);
        }
        // Nested lambdas bind their parameters in written order, after `main`, its
        // port and `t`.
        "nested lambdas" => {
            let names = r.binders[3..].iter().map(|b| b.name.as_str());
            assert!(names.enumerate().all(|(i, x)| x == format!("x{i}")));
            assert_eq!(r.binders.len(), 3 + deep);
        }
        // Each call names the one `f`.
        "nested calls" => {
            let f = r.binders.iter().position(|b| b.name == "f").unwrap();
            let calls = r.uses.values().filter(|u| **u == Ref::Bound([f].into()));
            assert_eq!(calls.count(), deep);
        }
        _ => {}
    }
}

/// The deep shapes the benchmarks of `bench/scaling.rs` resolve.
pub(super) const DEEP_SHAPES: [&str; 9] = [
    "a left-nested sum",
    "nested negations",
    "nested lambdas",
    "a long sum in a function's body",
    "nested blocks",
    "an `else if` chain",
    "a sum nested in parentheses",
    "nested calls",
    "nested tuples",
];

/// Names read in nested blocks resolve, `k` overloads are declared and used, and every use
/// holds the one list of overloads, at small sizes; `bench/scaling.rs` holds the timing.
#[test]
fn nested_blocks_and_overloads_resolve_at_small_sizes() {
    for n in [1, 2, 9] {
        assert!(run(&nested(n)).is_ok());
        declares_overloads(n);
        uses_resolve(&used(n), n);
    }
    assert_eq!(at(&nested(3), "c", 2), ["binding c = 1;"]);
    uses_share_one_list(&uses_resolve(&used(9), 9), 9);
}

#[test]
fn a_second_declaration_with_the_same_parameter_types_is_rejected() {
    assert_eq!(
        errors("f(x: int) = x;\nf(y: int) = 1;\ng = 1;\ng(x) = x;\n"),
        [
            "`f` is already declared in this scope with these parameter types \
             [f(y: int) = 1;]; the first `f` with these parameter types [f(x: int) = x;]; \
             repair: give this binding a new name [f(y: int) = 1;]",
            "`g` is already bound in this scope [g(x) = x;]; the first binding of `g` [g = 1;]; \
             repair: give this binding a new name [g(x) = x;]",
        ]
    );
}

/// Each use of an overloaded name is bound to every overload, in declaration order; the types
/// in the parameters are the prelude's.
#[test]
fn each_use_of_an_overloaded_name_is_bound_to_every_overload_in_order() {
    let r = zedc::resolve::resolve(&used(3)).unwrap();
    let sets: Vec<Vec<usize>> = r
        .uses
        .values()
        .filter_map(|f| match f {
            Ref::Bound(ids) => Some(ids.iter().copied().collect()),
            Ref::Prelude(_) | Ref::Unit { .. } | Ref::Main(_) => None,
        })
        .collect();
    assert_eq!(sets.len(), 3);
    assert!(
        sets.iter()
            .all(|v| v.len() == 3 && v.is_sorted() && *v == sets[0])
    );
}

/// Each deep shape resolves, with what it binds, at small depths (4 is the least a deep program
/// has); `bench/scaling.rs` holds the timing at 12,500 and 100,000.
#[test]
fn each_deep_shape_resolves_at_small_depths() {
    use zed_tests::deep::{program, statements};
    for shape in DEEP_SHAPES {
        for n in [4, 5, 9] {
            let r = zedc::resolve::resolve(&statements(&program(shape, n).text)).unwrap();
            deep_resolves(shape, &r, n);
        }
    }
}
