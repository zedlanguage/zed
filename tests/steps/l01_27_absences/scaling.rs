//! The checker on a chain of loose atoms, at the rule of low complexity (DESIGN.md Part G).
//! `e else d` and each operator strip the loose atoms of their operands; the strip
//! complemented every loose atom so far, so a chain of n failures took O(n²) (COMPLEXITY.md
//! F21). Each run checks the chain twice: the emptiness results were kept from one unit to
//! the next, and the second check compared each of its types in full with an equal kept one,
//! which also took O(n²) (COMPLEXITY.md F32).

use std::collections::BTreeMap;

use zed_tests::scaling::{self, FACTOR};
use zedc::check::check;

use crate::l01_26_type_resolution::info;

/// `x = #e0 + #e1 + … + #e(n-1);`
fn chain(n: usize) -> String {
    let atoms: Vec<String> = (0..n).map(|i| format!("#e{i}")).collect();
    format!("x = {};\n", atoms.join(" + "))
}

#[test]
fn a_chain_of_many_failure_atoms_scales() {
    // The parser and checker recurse once per operator, so the chain runs on a large stack.
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 29)
            .spawn_scoped(s, || {
                scaling::check("a chain of n failure atoms, checked twice", 1000, |n| {
                    let text = chain(n);
                    for _ in 0..2 {
                        let (info, _) = info(&text);
                        assert!(info.errors.is_empty(), "{:?}", info.errors);
                    }
                })
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

/// A unit parsed and resolved, ready to check.
struct Ready {
    stmts: Vec<zedc::ast::Stmt>,
    res: zedc::resolve::Resolution,
}

fn ready(text: &str) -> Ready {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap();
    Ready { stmts, res }
}

/// `n` bindings `_ = lookup(i)…;`, each followed by `tail`.
fn discards(n: usize, tail: &str) -> String {
    let mut t = String::from("lookup(positional k: int) = if k > 0 { k } else { #notFound };\n");
    for i in 0..n {
        t.push_str(&format!("_ = lookup({i}){tail};\n"));
    }
    t
}

/// `a0 = lookup(1); a1 = a0 + 1; …; _ = a(n-1);`: one dropped failure, entering `n` names
/// before the `_`.
fn deep_discard(n: usize) -> String {
    let mut t = String::from("lookup(positional k: int) = if k > 0 { k } else { #notFound };\n");
    t.push_str("a0 = lookup(1);\n");
    for i in 1..n {
        t.push_str(&format!("a{i} = a{} + 1;\n", i - 1));
    }
    t.push_str(&format!("_ = a{};\n", n - 1));
    t
}

#[test]
fn checking_many_discards_scales() {
    // Accepted, each with its default, and rejected, each with its error and derivation.
    for (what, tail, errors) in [
        ("n bindings of `_` with an `else` default", " else 0", 0),
        ("n bindings of `_` that drop a failure", "", 1),
    ] {
        let units: BTreeMap<usize, Ready> = [500, FACTOR * 500]
            .into_iter()
            .map(|n| (n, ready(&discards(n, tail))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let u = &units[&n];
            assert_eq!(check(&u.stmts, &u.res).errors.len(), errors * n);
        });
    }
}

#[test]
fn a_dropped_failure_found_through_a_long_chain_of_names_scales() {
    // The walk to where the failure enters follows each name once, on its own stack.
    let units: BTreeMap<usize, Ready> = [500, FACTOR * 500]
        .into_iter()
        .map(|n| (n, ready(&deep_discard(n))))
        .collect();
    scaling::check_order("a dropped failure behind n names", 500, 1, |n| {
        let u = &units[&n];
        let errors = check(&u.stmts, &u.res).errors;
        assert_eq!(errors.len(), 1);
        assert!(errors[0].notes[0].text.ends_with("enters here"));
    })
}

/// `_ = if c > 0 { lookup(0) else #ok } else if c > 1 { … } … else { lookup(n){last} };` in a
/// function of `c`: `n` branches, each with its own default, and a last one that ends in
/// `last`.
fn defaulted_branches(n: usize, last: &str) -> String {
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

#[test]
fn a_chain_of_many_defaulted_branches_scales() {
    // Each branch is checked on its own: the defaults of the others name nothing in it. The
    // `if` nests once per `else if`, so the chain runs on a large stack.
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 29)
            .spawn_scoped(s, || {
                for (what, last, errors) in [
                    ("an `if` of n branches, each with a default", " else #ok", 0),
                    ("an `if` of n branches, the last without a default", "", 1),
                ] {
                    let units: BTreeMap<usize, Ready> = [500, FACTOR * 500]
                        .into_iter()
                        .map(|n| (n, ready(&defaulted_branches(n, last))))
                        .collect();
                    scaling::check_order(what, 500, 1, |n| {
                        let u = &units[&n];
                        let found = check(&u.stmts, &u.res).errors;
                        assert_eq!(found.len(), errors, "{found:?}");
                        if let Some(e) = found.first() {
                            assert_eq!(e.notes[0].text, "the loose failure #notFound enters here");
                        }
                    });
                }
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

/// `_ = if c { y else #ok } else if c { … } … else { y else #ok };` in a function of `c`, after
/// `y = lookup(1);`: `n` branches, each naming the miss of the one name `y`. Each branch costs
/// the checker little, so a walk over each `if`'s branches, even one that only counts them,
/// costs more than the rest of the check at these sizes.
fn defaulted_names(n: usize) -> String {
    let mut t = String::from("lookup(positional k: int) = if k > 0 { k } else { #notFound };\n");
    let arms = vec!["if c { y else #ok }"; n];
    t.push_str(&format!(
        "f(positional c: bool) = {{\n  y = lookup(1);\n  _ = {} else {{ y else #ok }};\n  0\n}};\n",
        arms.join(" else ")
    ));
    t
}

#[test]
fn a_long_chain_of_defaulted_names_scales() {
    // A check that walks each `if`'s branches again costs O(n²) here: a walk that only counts
    // the nodes under each `if` took 28.6 times the work from 2000 to 16000 branches.
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 29)
            .spawn_scoped(s, || {
                let units: BTreeMap<usize, Ready> = [2000, FACTOR * 2000]
                    .into_iter()
                    .map(|n| (n, ready(&defaulted_names(n))))
                    .collect();
                scaling::check_order(
                    "an `if` of n branches, each naming the miss of one name",
                    2000,
                    1,
                    |n| {
                        let u = &units[&n];
                        let found = check(&u.stmts, &u.res).errors;
                        assert!(found.is_empty(), "{found:?}");
                    },
                );
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

/// `n` statements, each dropping the value of a generic call: `apply`, whose result variable
/// is no parameter's own, with a default on its value, and `id`, which passes on its
/// argument, with a default on the argument.
fn generic_calls(n: usize) -> String {
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
fn many_dropped_generic_calls_scale() {
    let units: BTreeMap<usize, Ready> = [500, FACTOR * 500]
        .into_iter()
        .map(|n| (n, ready(&generic_calls(n))))
        .collect();
    scaling::check_order("n dropped generic calls", 500, 1, |n| {
        let u = &units[&n];
        let found = check(&u.stmts, &u.res).errors;
        assert!(found.is_empty(), "{found:?}");
    });
}
