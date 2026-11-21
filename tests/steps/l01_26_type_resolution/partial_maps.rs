//! A lookup in a partial map, `m[k]` with `m: K ->? V` (DESIGN.md sec:type_language, the
//! `->?` row): the type promises no key, so the lookup is `V | #notFound`, which the program
//! must dispose of before the value reaches a place that does not take it. A total function
//! type `K -> V` answers on every key, so its lookup is `V` alone. This checker keeps one domain
//! per function, so `K ->? V` is the function type `(K) -> V | #notFound`, printed `K ->? V`
//! as `#morphism` of sec:introspection writes it. A bounded map `L .. U -> V` is the two arrows
//! `(L) -> V` and `(U) -> V | #notFound`: a key in `L` finds its value, a key in `U` alone may
//! not, and a key not inside `U` is a static error (the lookup rows of sec:type_language).

use super::{sig, type_errors};

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
        "(m: String -> int, k: String) -> int"
    );
}

#[test]
fn else_disposes_of_the_miss() {
    assert_eq!(
        sig(
            "price(m: String ->? int, k: String) = m[k] else #notFound -> 0;",
            "price"
        ),
        "(m: String ->? int, k: String) -> int"
    );
}

/// A value type that holds `#notFound` gives the same lookup, `V | #notFound`, but is another
/// type: such a map stores the atom as a value (DESIGN.md sec:corner_cases, author P350), so at
/// a key an exact arrow guarantees it may still answer `#notFound`. Before
/// (FAIL-types-partial-arrow-value-type), the two read as one type and printed alike.
#[test]
fn a_value_type_that_holds_not_found_gives_the_same_lookup_and_is_another_type() {
    let stored = sig(
        "price(m: String ->? int | #notFound, k: String) = m[k];",
        "price",
    );
    assert_eq!(
        stored,
        "type Part1 = int | #notFound;\n(m: String ->? Part1, k: String) -> Part1"
    );
    assert_ne!(
        stored,
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
    let partial = "look(m: String ->? int) = m[\"a\"] else #notFound -> 0;\n\
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
pub(super) fn many(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("m{i}: String ->? int")).collect();
    let reads: Vec<String> = (0..n)
        .map(|i| format!("(m{i}[\"k\"] else #notFound -> 0)"))
        .collect();
    let deep = format!("{}int{}", "String ->? (".repeat(n), ")".repeat(n));
    format!(
        "f({}) = {};\ng(m: {deep}) = m{} else #notFound -> 0;\n",
        params.join(", "),
        reads.join(" + "),
        "[\"k\"]".repeat(n)
    )
}

#[test]
fn many_and_deep_partial_maps_are_looked_up() {
    // A small instance of the benchmark
    // `bench::partial_maps::checking_many_and_deep_partial_maps_scales`.
    assert_eq!(type_errors(&many(3)), Vec::<String>::new(), "{}", many(3));
    assert_eq!(sig(&many(2), "g"), "(m: String ->? String ->? int) -> int");
}

/// `f(m: M, k: K) = m[k];` with the map type `M` and the key type `K`: the signature of `f`.
fn lookup(m: &str, k: &str) -> String {
    sig(&format!("f(m: {m}, k: {k}) = m[k];"), "f")
}

#[test]
fn a_key_in_the_guarantee_of_a_bounded_map_finds_its_value() {
    assert_eq!(
        lookup("int .. (int | String) -> bool", "int"),
        "(m: int .. (int | String) -> bool, k: int) -> bool"
    );
    assert_eq!(
        sig("f(m: #a .. (#a | #b) -> int) = m[#a];", "f"),
        "(m: #a .. (#a | #b) -> int) -> int"
    );
}

#[test]
fn a_key_in_the_permission_alone_may_be_not_found() {
    assert_eq!(
        lookup("int .. (int | String) -> bool", "String"),
        "(m: int .. (int | String) -> bool, k: String) -> bool | #notFound"
    );
    assert_eq!(
        lookup("int .. (int | String) -> bool", "int | String"),
        "type Part1 = int | String;\n(m: int .. Part1 -> bool, k: Part1) -> bool | #notFound"
    );
    assert_eq!(
        sig("f(m: #a .. (#a | #b) -> int) = m[#b];", "f"),
        "(m: #a .. (#a | #b) -> int) -> int | #notFound"
    );
    // An atom key that may lie outside the guarantee selects the arrow of the permission,
    // not the first arrow that takes some of its atoms.
    assert_eq!(
        lookup("#a .. (#a | #b | #c) -> int", "#a | #b"),
        "(m: #a .. (#a | #b | #c) -> int, k: #a | #b) -> int | #notFound"
    );
}

#[test]
fn a_key_not_inside_the_permission_is_a_static_error() {
    assert_eq!(
        type_errors("f(m: int .. (int | String) -> bool, k: bool) = m[k];"),
        [
            "this read can never find its key: the key is `bool` and the map's keys are `int | String`, which share no value, so the read can only give `#notFound`. [m[k]]"
        ]
    );
    assert_eq!(
        type_errors("f(m: int .. (int | String) -> bool, k: int | bool) = m[k];"),
        ["this function does not take (bool): no arrow of this function takes these types. [m[k]]"]
    );
}

#[test]
fn bounds_that_meet_are_a_total_map_and_an_empty_guarantee_a_partial_one() {
    assert_eq!(
        lookup("int .. int -> bool", "int"),
        "(m: int -> bool, k: int) -> bool"
    );
    assert_eq!(
        sig("f(m: String ->? int) = m;", "f"),
        "(m: String ->? int) -> String ->? int"
    );
}

#[test]
fn a_function_that_answers_on_the_permission_fits_a_bounded_map() {
    let pass = "f(m: int .. (int | String) -> bool) = m;\n";
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
            "the lambda returns #notFound, and `int .. (int | String) -> bool` returns bool: the lambda is passed where a function of type `int .. (int | String) -> bool` is expected, so its result must be bool.\n  Part1 stands for a part written more than once:\n    type Part1 = int | String; [#notFound]"
        ]
    );
}

#[test]
fn a_bounded_map_reads_back_in_every_position() {
    // Each parameter type, as written and as written back, and the signature: item
    // PRINT-fmt-audit gives `int | String`, used twice in it, a definition placed first. Before,
    // the first was `(m: (int .. int | String -> bool, int)) -> (int .. int | String -> bool,
    // int)`.
    let t1 = "type Part1 = int | String;\n";
    for (m, shown, signature) in [
        (
            "(int .. (int | String) -> bool, int)",
            "(int .. (int | String) -> bool, int)",
            format!("{t1}(m: (int .. Part1 -> bool, int)) -> (int .. Part1 -> bool, int)"),
        ),
        (
            "(int .. (int | String) -> bool) | int",
            "int | (int .. (int | String) -> bool)",
            format!("{t1}(m: int | (int .. Part1 -> bool)) -> int | (int .. Part1 -> bool)"),
        ),
        (
            "int .. (int | String) -> (int .. (int | String) -> bool)",
            "int .. (int | String) -> int .. (int | String) -> bool",
            format!(
                "{t1}(m: int .. Part1 -> int .. Part1 -> bool) -> int .. Part1 -> int .. Part1 -> bool"
            ),
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
pub(super) fn bounded(n: usize) -> String {
    let params: Vec<String> = (0..n)
        .map(|i| format!("m{i}: int .. (int | String) -> int, k{i}: String"))
        .collect();
    let reads: Vec<String> = (0..n)
        .map(|i| format!("(m{i}[k{i}] else #notFound -> 0)"))
        .collect();
    let deep = format!(
        "{}bool{}",
        "int .. (int | String) -> (".repeat(n),
        ")".repeat(n)
    );
    format!(
        "f({}) = {};\ng(m: {deep}, k: int) = m{};\n",
        params.join(", "),
        reads.join(" + "),
        "[k]".repeat(n)
    )
}

/// A family may store `#notFound` as a value (DESIGN.md sec:corner_cases, author P350), and its
/// entries are then the values its arrows store, that `#notFound` among them: only a partial
/// arrow's `#notFound` is a miss (`Arrow::value`). `zip` pairs the stored `#notFound` and keeps
/// it in the pair. Before (plan row TYPES-entries-keep-stored-notfound), every `#notFound` of an
/// arrow's result was read as a miss, so `zip` found no key it could show was in both operands
/// and refused these programs.
#[test]
fn zip_keeps_a_stored_not_found_in_the_pair() {
    for (src, want) in [
        (
            "f(n: int) = [n, #notFound].zip([n, #notFound]);",
            "type Part1 = int | #notFound;\n(n: int) -> (0 | 1) -> (Part1, Part1)",
        ),
        (
            "f(n: int) = [n, #notFound].map(x -> x).zip([n, 4]);",
            "(n: int) -> (0 | 1) -> (int | #notFound, int)",
        ),
        (
            "f(n: int) = {\"a\" -> 1, \"b\" -> #notFound}.zip({\"a\" -> 1, \"b\" -> #notFound});",
            "type Part1 = 1 | #notFound;\n(n: int) -> (\"a\" | \"b\") -> (Part1, Part1)",
        ),
        // The contrast: a family that stores no `#notFound` zips as before.
        (
            "f(n: int) = [n, n].zip([n, n]);",
            "(n: int) -> (0 | 1) -> (int, int)",
        ),
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
}

/// The words that read a family's entries see a stored `#notFound` as an entry: `first` may
/// give it, `group` keeps it in its groups, and a read at a key every arrow guarantees gives it
/// and no miss. A read that may miss gives the miss beside it, `#outOfBounds` on a list. Before
/// (TYPES-entries-keep-stored-notfound), `first` gave `int | #none`, `group` dropped the value,
/// and `[3, #notFound][0]` gave `3 | #outOfBounds`: the stored value read as a miss.
#[test]
fn the_words_that_read_entries_keep_a_stored_not_found() {
    for (src, want) in [
        (
            "f(n: int) = [n, #notFound].first;",
            "(n: int) -> int | #notFound",
        ),
        (
            "f(n: int) = [n, #notFound].group(x -> 1);",
            "(n: int) -> 1 ->? (0 | 1) ->? int | #notFound",
        ),
        (
            "f(n: int) = [3, #notFound][0];",
            "(n: int) -> 3 | #notFound",
        ),
        (
            "f(k: int) = [3, #notFound][k];",
            "(k: int) -> 3 | #notFound | #outOfBounds",
        ),
        (
            "f(n: int) = {\"a\" -> 1, \"b\" -> #notFound}[\"b\"];",
            "(n: int) -> 1 | #notFound",
        ),
        // The contrasts: a list that stores no `#notFound` misses with `#outOfBounds` alone,
        // and a partial family's miss is `#notFound`.
        ("f(k: int) = [3, 4][k];", "(k: int) -> 3 | 4 | #outOfBounds"),
        (
            "f(n: int) = [3, 4].where(x -> x > 3)[0];",
            "(n: int) -> 3 | 4 | #notFound",
        ),
        (
            "f(n: int) = [1, 2].where(x -> x > 0).first;",
            "(n: int) -> 1 | 2 | #none",
        ),
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
}

/// A stored `#notFound` is an atom entry like any other, so the words that refuse an atom
/// entry refuse it as they refuse `#a`: a sum by `(+)`, and a remap level that must hold
/// families. Before (TYPES-entries-keep-stored-notfound), the `#notFound` was dropped as a miss:
/// `[n, #notFound] >< (+)` was typed `int`, which a run that adds `#notFound` does not give.
#[test]
fn a_stored_not_found_is_refused_where_an_atom_entry_is() {
    for (stored, atom) in [
        (
            "f(n: int) = [n, #notFound] >< (+);",
            "f(n: int) = [n, #a] >< (+);",
        ),
        (
            "f(n: int) = [[1], #notFound] as (i -> j -> v) into (j -> i -> v);",
            "f(n: int) = [[1], #a] as (i -> j -> v) into (j -> i -> v);",
        ),
    ] {
        assert_eq!(type_errors(atom).len(), 1, "{atom}");
        assert_eq!(type_errors(stored).len(), 1, "{stored}");
    }
}

/// Plan row FP-chunkby-runs-partial: each run of `chunkBy` holds only some of the source's
/// keys, so its arrows are partial, `K ->? V`, and a read of a key of another run misses. Before,
/// the runs kept the source's exact arrows and printed `(0 | 1 | 2) -> 1 | 2`, promising every
/// key of the source in every run.
#[test]
fn the_runs_of_chunk_by_are_partial_maps() {
    for (src, want) in [
        (
            "f(n: int) = [1, 1, 2].chunkBy(x -> x);",
            "(n: int) -> [(0 | 1 | 2) ->? 1 | 2]",
        ),
        (
            "f(n: int) = [1, 1, 2].chunkBy(x -> x)[0];",
            "(n: int) -> ((0 | 1 | 2) ->? 1 | 2) | #outOfBounds",
        ),
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
}

#[test]
fn many_and_deep_bounded_maps_are_looked_up_and_printed() {
    // A small instance of the benchmark
    // `bench::partial_maps::checking_and_printing_many_and_deep_bounded_maps_scales`.
    assert_eq!(
        type_errors(&bounded(3)),
        Vec::<String>::new(),
        "{}",
        bounded(3)
    );
    assert_eq!(
        sig(&bounded(2), "g"),
        "type Part1 = int | String;\n(m: int .. Part1 -> int .. Part1 -> bool, k: int) -> bool"
    );
}

/// The words that read the entries of a family, `map`, `zip` and `><`, take a parameter
/// declared a partial map: DESIGN.md sec:failure ("All or the failures") takes
/// `total(positional m: File ->? int) = m >< (+)` as a valid function. Before
/// (FAIL-declared-partial-param-entries) each was refused as reading a value with no entries.
#[test]
fn the_words_that_read_entries_take_a_declared_partial_map() {
    for src in [
        "total(positional m: String ->? int) = m >< (+);",
        "f(positional m: String ->? int) = m.map(x -> (x, 1));",
        "f(positional m: String ->? int) = m.zip(m);",
        "f(positional m: String ->? int | #notFound) = m.map(x -> (x, 1));",
        "f(positional m: String ->? int | #notFound) = m.zip(m);",
        "f(positional m: String ->? int) = (m.sum, m.count, m.foldl(0, (a, x) -> a + x));",
        "f(positional m: int ->? int) = m.any(x -> x > 0);",
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    }
}

/// The words run on the family passed: `zedc run` and the built executable print the same.
#[test]
fn the_words_that_read_entries_run_on_a_declared_partial_map_both_ways() {
    use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable, interpreter};
    let program = "total(positional m: String ->? int) = m >< (+);\n\
                   twice(positional m: String ->? int) = m.map(x -> x * 2);\n\
                   pairs(positional m: String ->? int) = m.zip(m).map(p -> p[0] + p[1]);\n\
                   main(a: MainArgs) {\n    \
                   m = { \"a\" -> 2, \"b\" -> 3 };\n    \
                   a.stdout <- \"${total(m)} ${total(twice(m))} ${pairs(m).sum}\";\n}\n";
    // 2 + 3; 4 + 6; (2 + 2) + (3 + 3).
    let want = "5 10 10\n";
    let d = dir("l01_26_type_resolution/declared_partial_entries");
    let src = d.join("declared_partial_entries.zed");
    std::fs::write(&src, program).unwrap();
    let ran = interpreter(&src, &[], &[]);
    assert_eq!((ran.stderr.as_str(), ran.status), ("", 0));
    assert_eq!(ran.stdout, want, "zedc run");
    let exe = d.join("declared_partial_entries");
    built(&src, &exe);
    let ran = executable(&exe, &[], &[]);
    assert_eq!((ran.stderr.as_str(), ran.status), ("", 0));
    assert_eq!(ran.stdout, want, "the executable");
}

/// A function of the declared type has no entries, so a call that passes one where a word
/// reads the entries is refused, as a remap's is (`keys_at`), and the message names the word.
#[test]
fn a_function_passed_where_a_word_reads_the_entries_is_refused() {
    let src = "total(positional m: String ->? int) = m >< (+);\n\
               g(positional k: String) = 1;\n\
               x = total(g);\n\
               y = total({ \"a\" -> 1 });\n";
    assert_eq!(
        type_errors(src),
        ["`total` takes `m` as a family, which `><` reads: `g` may not be one. [g]"]
    );
}

/// A read at a key outside a display's keys is refused (DESIGN.md sec:type_language, the
/// `m[k]` row: a static error where the key's domain is disjoint from the keys), whatever the
/// display stores; the repair that widens the keys writes the map's type with the values it
/// stores, a stored `#notFound` among them, as `->?` reads it back (author P350). Before
/// 3ceb4d7ab the repair took `#notFound` out of the values and wrote `String ->? 1`, a map
/// that stores no `#notFound` (MSG-key-outside-drops-stored-notfound).
#[test]
fn a_read_outside_the_keys_names_the_map_type_with_a_stored_not_found() {
    for (display, declared) in [
        (
            "{\"a\" -> 1, \"b\" -> #notFound}",
            "String ->? 1 | #notFound",
        ),
        ("{\"a\" -> 1, \"b\" -> 2}", "String ->? 1 | 2"),
    ] {
        let src = format!("f = {display}[\"c\"];");
        let resolved = super::Resolved::new(&src);
        let checked = resolved.check();
        let errors = &checked.errors;
        assert_eq!(errors.len(), 1, "{src}");
        assert!(
            errors[0]
                .message
                .starts_with("this read can never find its key"),
            "{src}: {}",
            errors[0].message
        );
        let repair = format!(
            "repair: declare the map with the wider keys `{declared}`, and handle `#notFound` \
             where the key is missing"
        );
        let notes: Vec<&str> = errors[0].notes.iter().map(|n| n.text.as_str()).collect();
        assert!(notes.contains(&repair.as_str()), "{src}: {notes:#?}");
    }
}
