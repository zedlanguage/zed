//! The checker on long chains of loose atoms: the programs the benchmarks of `bench.rs` measure,
//! the check each benchmark makes at every size besides the ratio, and that check at small sizes
//! (TEST-bench-move-l0138, author P170). `e else d` and each operator strip the loose atoms of
//! their operands; the strip complemented every loose atom so far, so a chain of n failures took
//! O(n²) (COMPLEXITY.md F21). Each run checks the chain twice: the emptiness results were kept
//! from one unit to the next, and the second check compared each of its types in full with an
//! equal kept one, which also took O(n²) (COMPLEXITY.md F32).

use zedc::check::walk::check;

use zed_tests::step_helpers::l01_26_type_resolution::info;

/// `x = #e0 + #e1 + … + #e(n-1);`
pub(super) fn chain(n: usize) -> String {
    let atoms: Vec<String> = (0..n).map(|i| format!("#e{i}")).collect();
    format!("x = {};\n", atoms.join(" + "))
}

/// The chain of `n` failure atoms is accepted, on each of two checks.
pub(super) fn checks_the_chain_twice(n: usize) {
    let text = chain(n);
    for _ in 0..2 {
        let (info, _) = info(&text);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    }
}

#[test]
fn a_chain_of_failure_atoms_is_accepted_on_each_check() {
    for n in [1, 2, 7] {
        checks_the_chain_twice(n);
    }
}

/// A unit parsed and resolved, ready to check.
pub(super) struct Ready {
    stmts: Vec<zedc::ast::Stmt>,
    res: zedc::resolve::Resolution,
}

pub(super) fn ready(text: &str) -> Ready {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap();
    Ready { stmts, res }
}

/// The errors of checking `u`.
pub(super) fn errors(u: &Ready) -> Vec<zedc::ast::Error> {
    check(&u.stmts, &u.res).errors
}

/// `n` bindings `_ = lookup(i)…;`, each followed by `tail`.
pub(super) fn discards(n: usize, tail: &str) -> String {
    let mut t = String::from("lookup(positional k: int) = if k > 0 { k } else { #notFound };\n");
    for i in 0..n {
        t.push_str(&format!("_ = lookup({i}){tail};\n"));
    }
    t
}

/// The two kinds of `n` discards: accepted, each with its default, and rejected, each with its
/// error and derivation; with the errors each binding gets.
pub(super) const DISCARDS: [(&str, &str, usize); 2] = [
    ("n bindings of `_` with an `else` default", " else 0", 0),
    ("n bindings of `_` that drop a failure", "", 1),
];

#[test]
fn each_discard_gets_its_own_error_or_none() {
    for (what, tail, per) in DISCARDS {
        for n in [1, 3] {
            assert_eq!(errors(&ready(&discards(n, tail))).len(), per * n, "{what}");
        }
    }
}

/// `a0 = lookup(1); a1 = a0 + 1; …; _ = a(n-1);`: one dropped failure, entering `n` names
/// before the `_`.
pub(super) fn deep_discard(n: usize) -> String {
    let mut t = String::from("lookup(positional k: int) = if k > 0 { k } else { #notFound };\n");
    t.push_str("a0 = lookup(1);\n");
    for i in 1..n {
        t.push_str(&format!("a{i} = a{} + 1;\n", i - 1));
    }
    t.push_str(&format!("_ = a{};\n", n - 1));
    t
}

/// The one error of a dropped failure behind names, whose first note says where it enters.
pub(super) fn found_through_the_names(u: &Ready) {
    let errors = errors(u);
    assert_eq!(errors.len(), 1);
    assert!(errors[0].notes[0].text.ends_with("enters here"));
}

#[test]
fn a_dropped_failure_behind_names_is_found_where_it_enters() {
    for n in [1, 2, 6] {
        found_through_the_names(&ready(&deep_discard(n)));
    }
}

/// `_ = if c > 0 { lookup(0) else #ok } else if c > 1 { … } … else { lookup(n){last} };` in a
/// function of `c`: `n` branches, each with its own default, and a last one that ends in
/// `last`.
pub(super) fn defaulted_branches(n: usize, last: &str) -> String {
    let mut t = String::from("lookup(positional k: int) = if k > 0 { k } else { #notFound };\n");
    let arms: Vec<String> = (0..n)
        .map(|i| format!("if c > {i} {{ lookup({i}) else #ok }}"))
        .collect();
    t.push_str(&format!(
        "f(positional c: int) = {{\n  _ = {} else {{ lookup({n}){last} }};\n  0\n}};\n",
        arms.join(" else ")
    ));
    t
}

/// The two last branches of [`defaulted_branches`], with a default and without, and the errors
/// each gives.
pub(super) const LAST_BRANCHES: [(&str, &str, usize); 2] = [
    ("an `if` of n branches, each with a default", " else #ok", 0),
    ("an `if` of n branches, the last without a default", "", 1),
];

/// `errors` errors, each saying where the dropped `#notFound` enters.
pub(super) fn the_branches_check(u: &Ready, errors_expected: usize) {
    let found = errors(u);
    assert_eq!(found.len(), errors_expected, "{found:?}");
    if let Some(e) = found.first() {
        assert_eq!(e.notes[0].text, "the loose failure #notFound enters here");
    }
}

#[test]
fn each_defaulted_branch_is_checked_alone() {
    for (_, last, errors) in LAST_BRANCHES {
        for n in [1, 4] {
            the_branches_check(&ready(&defaulted_branches(n, last)), errors);
        }
    }
}

/// `_ = if c { y else #ok } else if c { … } … else { y else #ok };` in a function of `c`, after
/// `y = lookup(1);`: `n` branches, each naming the miss of the one name `y`. Each branch costs
/// the checker little, so a walk over each `if`'s branches, even one that only counts them,
/// costs more than the rest of the check at these sizes.
pub(super) fn defaulted_names(n: usize) -> String {
    let mut t = String::from("lookup(positional k: int) = if k > 0 { k } else { #notFound };\n");
    let arms = vec!["if c { y else #ok }"; n];
    t.push_str(&format!(
        "f(positional c: bool) = {{\n  y = lookup(1);\n  _ = {} else {{ y else #ok }};\n  0\n}};\n",
        arms.join(" else ")
    ));
    t
}

#[test]
fn branches_that_each_default_one_name_are_accepted() {
    for n in [1, 5] {
        let found = errors(&ready(&defaulted_names(n)));
        assert!(found.is_empty(), "{found:?}");
    }
}

/// `n` statements, each dropping the value of a generic call: `apply`, whose result variable
/// is no parameter's own, with a default on its value, and `id`, which passes on its
/// argument, with a default on the argument.
pub(super) fn generic_calls(n: usize) -> String {
    let mut t = String::from(
        "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n\
         apply(positional g, positional x) = g(x);\n\
         id(positional x) = x;\n",
    );
    for i in 0..n {
        t.push_str(&format!(
            "_ = apply(lookup, {i}) else #ok;\n_ = id(lookup({i}) else #ok);\n"
        ));
    }
    t
}

#[test]
fn dropped_generic_calls_with_defaults_are_accepted() {
    for n in [1, 3] {
        let found = errors(&ready(&generic_calls(n)));
        assert!(found.is_empty(), "{found:?}");
    }
}

/// `f(positional x0: int | #e0, …) = x0 + x1 + … + x(n-1);`, operand i able to fail with
/// `#e(i % kinds)`: with one kind every operand carries the same failure.
pub(super) fn mixed_failures(n: usize, kinds: usize) -> String {
    let params: Vec<String> = (0..n)
        .map(|i| format!("positional x{i}: int | #e{}", i % kinds))
        .collect();
    let sum: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    format!("f({}) = {};\n", params.join(", "), sum.join(" + "))
}

/// The kinds of failure of [`mixed_failures`] and the `#errs` its result keeps: seven kinds,
/// one, and a different one on each operand (`None`), whose `#errs` holds `n` of them.
pub(super) const KINDS: [(Option<usize>, usize); 3] = [(Some(7), 1), (Some(1), 0), (None, 1)];

/// The result of the sum of `n` operands of `kinds` kinds of failure keeps `errs` flat `#errs`.
pub(super) fn merges(n: usize, kinds: Option<usize>, errs: usize) {
    let text = mixed_failures(n, kinds.unwrap_or(n));
    let sig = zed_tests::step_helpers::l01_26_type_resolution::sig(&text, "f");
    let result = sig.rsplit(" -> ").next().unwrap();
    assert_eq!(result.matches("#errs").count(), errs, "{result}");
}

#[test]
fn the_failures_of_a_chain_of_sums_merge_into_one_flat_errs() {
    // At 8 operands the seven kinds repeat, so the merge meets a failure it holds already.
    for (kinds, errs) in KINDS {
        merges(8, kinds, errs);
    }
}

/// `#a0 | #a1 | … | #a(n-1) | bool` as a named family.
pub(super) fn family(n: usize) -> zedc::check::ty::Ty {
    use zedc::check::ty::{Carrier, Ty};
    (0..n)
        .fold(Ty::carrier(Carrier::Bool), |t, i| {
            t.union(&Ty::set(zed_kernel::types::Type::atom(&format!("a{i}"))))
        })
        .named()
}

/// The program whose `v` is given the family's type.
pub(super) const FAMILY_TEXT: &str = "v = 0;\ny = if v { 1 } else { 2 };\n";

/// The one error of `if v` on a family of `n` atoms, whose repairs hold an `else` pattern for
/// the last atom.
pub(super) fn repairs_name_each_atom(u: &Ready, n: usize, given: zedc::check::ty::Ty) {
    let errors = zedc::check::walk::check_given(&u.stmts, &u.res, FAMILY_TEXT, given).errors;
    assert_eq!(errors.len(), 1);
    let last = format!(" else #a{} -> d", n - 1);
    assert!(errors[0].notes.iter().any(|note| note.text.contains(&last)));
}

#[test]
fn the_repairs_for_a_family_name_its_atoms() {
    let u = ready(FAMILY_TEXT);
    for n in [1, 4] {
        repairs_name_each_atom(&u, n, family(n));
    }
}
