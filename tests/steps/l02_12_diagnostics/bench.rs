//! Printing a diagnostic that quotes a string of n bytes is linear in n: the benchmark of this
//! step, run by `tools/run_tests.sh --bench` and left out of its default run
//! (TEST-bench-move-rest). Its check besides the ratio is made at small sizes by
//! `a_quoted_string_of_a_few_escapes_prints_escaped`.

use zed_tests::scaling;

use crate::type_names::{functions_fix_one_type_variable, lambdas_at_one_type_variable};
use crate::{prints_no_esc, quoted};

/// Row FAIL-typevar-free-in-checker: a call that passes n lambdas, each at a parameter of type
/// `(T) -> T`, puts each off and checks it against the signature with `T` fixed once, a queue
/// of n places and one replacement of a signature of size n: O(n) with persistent bindings.
#[test]
fn a_call_of_n_lambdas_at_one_type_variable_scales() {
    let inputs = scaling::inputs(200, lambdas_at_one_type_variable);
    scaling::check(
        "a call passing n lambdas at the type variable `T`",
        200,
        |n| {
            zedc::run::load(inputs[&n].as_bytes()).expect("accepted");
        },
    );
}

/// Row FAIL-typevar-fn-only-binding: a call of n functions at parameters `(T) -> T`, `T`
/// fixed through the first one's written parameter type (`bound_through_fn`, one comparison
/// per argument and an O(1) copy of the persistent bindings), the rest checked at the
/// instance: O(n).
#[test]
fn a_call_of_n_functions_fixing_a_type_variable_through_one_scales() {
    let inputs = scaling::inputs(200, functions_fix_one_type_variable);
    scaling::check(
        "a call passing n functions, `T` fixed through the first",
        200,
        |n| {
            zedc::run::load(inputs[&n].as_bytes()).expect("accepted");
        },
    );
}

/// PROOF-sweep-front-end: a unit of n definitions, each with a misspelled type, has its n
/// menus checked by one compile of the unit with every repair made (`front::menus_checked`,
/// `front::checking`), not one compile per menu: O(n) for the repairs and one more compile,
/// against O(n²).
#[test]
fn checking_the_menus_of_n_misspelled_types_scales() {
    let inputs = scaling::inputs(200, |n| {
        // `g`, not `f`: `f32` and `f64` name prelude types, a unit that does not compile
        // with the repairs made, so every menu would be withheld.
        let mut src: String = (0..n).map(|i| format!("g{i}(c: Strng) = {i};\n")).collect();
        src.push_str("main() = 0;\n");
        src
    });
    scaling::check("a unit of n definitions with a misspelled type", 200, |n| {
        let out = crate::rejected(&inputs[&n]);
        let head: Vec<&str> = out.lines().take(12).collect();
        assert_eq!(
            out.matches("repair: `String`").count(),
            n,
            "{}",
            head.join("\n")
        );
    });
}

/// FAIL-menus-checked-whole-unit: of n definitions with a misspelled type, every other one
/// uses a definition that fails to elaborate, so its menu is withheld and the others' are
/// offered. `front::checking` compiles the repaired unit, takes out the failing definitions
/// and every definition that uses one (a worklist over the uses, O(n)), and compiles the rest
/// again: a compile per stage that fails, at most four, against one compile per menu, O(n²).
#[test]
fn checking_the_menus_beside_n_failing_definitions_scales() {
    let inputs = scaling::inputs(200, |n| {
        let mut src = String::new();
        for i in 0..n {
            if i % 2 == 0 {
                src.push_str(&format!("g{i}(c: Strng) = {i};\n"));
            } else {
                src.push_str(&format!("g{i}(c: Strng) = b{i};\nb{i} = {i} + \"a\";\n"));
            }
        }
        src.push_str("main() = 0;\n");
        src
    });
    scaling::check(
        "a unit of n definitions with a misspelled type, half using a failing one",
        200,
        |n| {
            let out = crate::rejected(&inputs[&n]);
            assert_eq!(out.matches("repair: `String`").count(), n / 2);
        },
    );
}

#[test]
fn printing_a_quoted_string_scales() {
    let inputs = scaling::inputs(4000, quoted);
    scaling::check_order("a diagnostic quoting a string of n bytes", 4000, 1, |n| {
        let (d, t) = &inputs[&n];
        prints_no_esc(d, t);
    });
}
