//! A lookup in a partial map, `m[k]` with `m: K ->? V` (DESIGN.md sec:type_language, the
//! `->?` row): the type promises no key, so the lookup is `V | #notFound`, which the program
//! must dispose of before the value reaches a place that does not take it. A total function
//! type `K -> V` answers on every key, so its lookup is `V` alone. This checker keeps one domain
//! per function, so `K ->? V` is the function type `(K) -> V | #notFound`, printed `K ->? V`
//! as `#morphism` of sec:introspection writes it. A bounded map `L .. U -> V` is the two arrows
//! `(L) -> V` and `(U) -> V | #notFound`: a key in `L` finds its value, a key in `U` alone may
//! not, and a key not inside `U` is a static error (the lookup rows of sec:type_language).

use zed_tests::scaling;

use super::{Resolved, sig, type_errors};

#[test]
fn a_lookup_in_a_partial_map_may_be_not_found() {
    assert_eq!(
        sig("price(m: String ->? int, k: String) = m[k];", "price"),
        "(m: String ->? int, k: String) -> int | #notFound"
    );
}

#[test]
fn a_lookup_in_a_total_function_type_is_its_value_alone() {
    assert_eq!(
        sig("price(m: String -> int, k: String) = m[k];", "price"),
        "(m: (String) -> int, k: String) -> int"
    );
}

#[test]
fn else_disposes_of_the_miss() {
    assert_eq!(
        sig(
            "price(m: String ->? int, k: String) = m[k] else 0;",
            "price"
        ),
        "(m: String ->? int, k: String) -> int"
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
        "(m: String ->? int, k: String) -> int | #notFound"
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
        "(m: String ->? int ->? bool, k: String, i: int) \
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
    assert_eq!(sig(&many(2), "g"), "(m: String ->? String ->? int) -> int");
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

/// `f(m: M, k: K) = m[k];` with the map type `M` and the key type `K`: the signature of `f`.
fn lookup(m: &str, k: &str) -> String {
    sig(&format!("f(m: {m}, k: {k}) = m[k];"), "f")
}

#[test]
fn a_key_in_the_guarantee_of_a_bounded_map_finds_its_value() {
    assert_eq!(
        lookup("int .. int | String -> bool", "int"),
        "(m: int .. int | String -> bool, k: int) -> bool"
    );
    assert_eq!(
        sig("f(m: #a .. #a | #b -> int) = m[#a];", "f"),
        "(m: #a .. #a | #b -> int) -> int"
    );
}

#[test]
fn a_key_in_the_permission_alone_may_be_not_found() {
    assert_eq!(
        lookup("int .. int | String -> bool", "String"),
        "(m: int .. int | String -> bool, k: String) -> bool | #notFound"
    );
    assert_eq!(
        lookup("int .. int | String -> bool", "int | String"),
        "type T1 = int | String;\n(m: int .. T1 -> bool, k: T1) -> bool | #notFound"
    );
    assert_eq!(
        sig("f(m: #a .. #a | #b -> int) = m[#b];", "f"),
        "(m: #a .. #a | #b -> int) -> int | #notFound"
    );
    // An atom key that may lie outside the guarantee selects the arrow of the permission,
    // not the first arrow that takes some of its atoms.
    assert_eq!(
        lookup("#a .. #a | #b | #c -> int", "#a | #b"),
        "(m: #a .. #a | #b | #c -> int, k: #a | #b) -> int | #notFound"
    );
}

#[test]
fn a_key_not_inside_the_permission_is_a_static_error() {
    assert_eq!(
        type_errors("f(m: int .. int | String -> bool, k: bool) = m[k];"),
        [
            "this read can never find its key: the key is `bool` and the map's keys are `int | String`, which share no value, so the read can only give `#notFound` [m[k]]"
        ]
    );
    assert_eq!(
        type_errors("f(m: int .. int | String -> bool, k: int | bool) = m[k];"),
        ["this function does not take (bool): no arrow of this function takes these types [m[k]]"]
    );
}

#[test]
fn bounds_that_meet_are_a_total_map_and_an_empty_guarantee_a_partial_one() {
    assert_eq!(
        lookup("int .. int -> bool", "int"),
        "(m: (int) -> bool, k: int) -> bool"
    );
    assert_eq!(
        sig("f(m: String ->? int) = m;", "f"),
        "(m: String ->? int) -> String ->? int"
    );
}

#[test]
fn a_function_that_answers_on_the_permission_fits_a_bounded_map() {
    let pass = "f(m: int .. int | String -> bool) = m;\n";
    assert_eq!(
        type_errors(&format!("{pass}g = f(m: (k) -> true);")),
        Vec::<String>::new()
    );
    assert_eq!(
        type_errors(&format!(
            "{pass}h(positional k: int | String) = true;\ng = f(m: h);"
        )),
        Vec::<String>::new()
    );
    // A function that may answer `#notFound` promises no key of the guarantee.
    assert_eq!(
        type_errors(&format!("{pass}g = f(m: (k) -> #notFound);")),
        [
            "the lambda returns #notFound, and `int .. int | String -> bool` returns bool: the lambda is passed where a function of type `int .. int | String -> bool` is expected, so its result must be bool\n  T1 stands for a part written more than once:\n    type T1 = int | String; [#notFound]"
        ]
    );
}

#[test]
fn a_bounded_map_reads_back_in_every_position() {
    // Each parameter type, as written and as written back, and the signature: item
    // PRINT-fmt-audit gives `int | String`, used twice in it, a definition placed first. Before,
    // the first was `(m: (int .. int | String -> bool, int)) -> (int .. int | String -> bool,
    // int)`.
    let t1 = "type T1 = int | String;\n";
    for (m, shown, signature) in [
        (
            "(int .. int | String -> bool, int)",
            "(int .. int | String -> bool, int)",
            format!("{t1}(m: (int .. T1 -> bool, int)) -> (int .. T1 -> bool, int)"),
        ),
        (
            "(int .. int | String -> bool) | int",
            "int | (int .. int | String -> bool)",
            format!("{t1}(m: int | (int .. T1 -> bool)) -> int | (int .. T1 -> bool)"),
        ),
        (
            "int .. int | String -> (int .. int | String -> bool)",
            "int .. int | String -> int .. int | String -> bool",
            format!("{t1}(m: int .. T1 -> int .. T1 -> bool) -> int .. T1 -> int .. T1 -> bool"),
        ),
        (
            "(String ->? int, int)",
            "(String ->? int, int)",
            "(m: (String ->? int, int)) -> (String ->? int, int)".to_string(),
        ),
        (
            "(String ->? int) | int",
            "int | (String ->? int)",
            "(m: int | (String ->? int)) -> int | (String ->? int)".to_string(),
        ),
        (
            "(int ->? int) ->? int",
            "(int ->? int) ->? int",
            "(m: (int ->? int) ->? int) -> (int ->? int) ->? int".to_string(),
        ),
    ] {
        let text = format!("f(m: {m}) = m;");
        assert_eq!(sig(&text, "f"), signature, "{text}");
        let again = format!("f(m: {shown}) = m;");
        assert_eq!(sig(&again, "f"), sig(&text, "f"), "{again}");
    }
}

/// `n` bounded maps looked up by a key of their permission, and one bounded map nested `n`
/// deep looked up `n` times.
fn bounded(n: usize) -> String {
    let params: Vec<String> = (0..n)
        .map(|i| format!("m{i}: int .. int | String -> int, k{i}: String"))
        .collect();
    let reads: Vec<String> = (0..n).map(|i| format!("(m{i}[k{i}] else 0)")).collect();
    let deep = format!(
        "{}bool{}",
        "int .. int | String -> (".repeat(n),
        ")".repeat(n)
    );
    format!(
        "f({}) = {};\ng(m: {deep}, k: int) = m{} else false;\n",
        params.join(", "),
        reads.join(" + "),
        "[k]".repeat(n)
    )
}

#[test]
fn checking_and_printing_many_and_deep_bounded_maps_scales() {
    assert_eq!(
        type_errors(&bounded(3)),
        Vec::<String>::new(),
        "{}",
        bounded(3)
    );
    assert_eq!(
        sig(&bounded(2), "g"),
        "type T1 = int | String;\n(m: int .. T1 -> int .. T1 -> bool, k: int) -> bool"
    );
    let units: std::collections::BTreeMap<usize, Resolved> = [100, scaling::FACTOR * 100]
        .into_iter()
        .map(|m| (m, Resolved::new(&bounded(m))))
        .collect();
    scaling::check_order(
        "n bounded maps, and one nested n deep, looked up and printed",
        100,
        1,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            let printed: usize = info.sigs.values().map(|s| s.to_string().len()).sum();
            assert!(printed > n, "{printed}");
        },
    );
}
