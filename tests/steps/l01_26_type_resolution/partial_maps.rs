//! A lookup in a partial map, `m[k]` with `m: K ->? V` (DESIGN.md sec:type_language, the
//! `->?` row): the type promises no key, so the lookup is `V | #notFound`, which the program
//! must dispose of before the value reaches a place that does not take it. A total function
//! type `K -> V` answers on every key, so its lookup is `V` alone. This checker keeps one domain
//! per function, so `K ->? V` is the function type `(K) -> V | #notFound`, and is printed so.

use zed_tests::scaling;

use super::{Resolved, sig, type_errors};

#[test]
fn a_lookup_in_a_partial_map_may_be_not_found() {
    assert_eq!(
        sig("price(m: String ->? int, k: String) = m[k];", "price"),
        "(m: ((String) -> int | #notFound), k: String) -> int | #notFound"
    );
}

#[test]
fn a_lookup_in_a_total_function_type_is_its_value_alone() {
    assert_eq!(
        sig("price(m: String -> int, k: String) = m[k];", "price"),
        "(m: ((String) -> int), k: String) -> int"
    );
}

#[test]
fn else_disposes_of_the_miss() {
    assert_eq!(
        sig(
            "price(m: String ->? int, k: String) = m[k] else 0;",
            "price"
        ),
        "(m: ((String) -> int | #notFound), k: String) -> int"
    );
}

#[test]
fn a_value_type_that_already_holds_not_found_is_the_same_type() {
    assert_eq!(
        sig(
            "price(m: String ->? int | #notFound, k: String) = m[k];",
            "price"
        ),
        sig("price(m: String ->? int, k: String) = m[k];", "price")
    );
}

#[test]
fn a_miss_passes_by_a_call_that_takes_the_value_type() {
    // The miss of `m[k]` is a loose atom: `twice` takes an `int`, so the call runs on a value
    // and the miss passes out of it (rule 6 of sec:type_resolution). A port that takes no
    // `#notFound` rejects it (`l01_19c_environment`).
    assert_eq!(
        type_errors(
            "twice(positional n: int) = n + n;\n\
             f(m: String ->? int, k: String) = twice(m[k]);\n"
        ),
        Vec::<String>::new(),
        "the miss passes by the call, as any loose atom does"
    );
    assert_eq!(
        sig(
            "twice(positional n: int) = n + n;\n\
             f(m: String ->? int, k: String) = twice(m[k]);\n",
            "f"
        ),
        "(m: ((String) -> int | #notFound), k: String) -> int | #notFound"
    );
}

#[test]
fn a_function_that_answers_not_found_fits_a_partial_map_and_not_a_total_one() {
    let partial = "look(m: String ->? int) = m[\"a\"] else 0;\n\
                   x = look(m: (k) -> if k == \"a\" { 1 } else { #notFound });\n";
    assert_eq!(type_errors(partial), Vec::<String>::new());
    let total = "look(m: String -> int) = m[\"a\"];\n\
                 x = look(m: (k) -> if k == \"a\" { 1 } else { #notFound });\n";
    assert!(!type_errors(total).is_empty(), "{:?}", type_errors(total));
}

#[test]
fn a_partial_map_of_partial_maps_misses_at_either_step() {
    assert_eq!(
        sig(
            "seen(m: String ->? (int ->? bool), k: String, i: int) = m[k][i];",
            "seen"
        ),
        "(m: ((String) -> #notFound | ((int) -> bool | #notFound)), k: String, i: int) \
         -> bool | #notFound"
    );
}

/// `n` partial maps as parameters, each looked up once and the lookups summed, and a partial
/// map nested `n` deep looked up to the bottom: each written `->?` is denoted once, so checking
/// is linear in `n`.
fn many(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("m{i}: String ->? int")).collect();
    let reads: Vec<String> = (0..n).map(|i| format!("(m{i}[\"k\"] else 0)")).collect();
    let deep = format!("{}int{}", "String ->? (".repeat(n), ")".repeat(n));
    format!(
        "f({}) = {};\ng(m: {deep}) = m{} else 0;\n",
        params.join(", "),
        reads.join(" + "),
        "[\"k\"]".repeat(n)
    )
}

#[test]
fn checking_many_and_deep_partial_maps_scales() {
    assert_eq!(type_errors(&many(3)), Vec::<String>::new(), "{}", many(3));
    assert_eq!(
        sig(&many(2), "g"),
        "(m: ((String) -> #notFound | ((String) -> int | #notFound))) -> int"
    );
    let units: std::collections::BTreeMap<usize, Resolved> = [100, scaling::FACTOR * 100]
        .into_iter()
        .map(|m| (m, Resolved::new(&many(m))))
        .collect();
    scaling::check_order(
        "n partial maps, and one nested n deep, looked up",
        100,
        1,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}
