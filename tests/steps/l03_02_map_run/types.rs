//! What the checker refuses among the forms of this step, and the forms of step L3.2 not built
//! yet, each refused with the step named.

use super::run;

/// The first line of what `zedc run` writes for `body`, which it must refuse.
fn refused(name: &str, body: &str) -> String {
    let ran = run(name, body);
    assert_ne!(ran.status, 0, "{name}: {body} ran: {}", ran.stdout);
    ran.stderr
}

#[test]
fn a_key_disjoint_from_the_keys_is_refused() {
    // R11 (author): a key whose type shares no value with the keys is a static error.
    let e = refused("disjoint", "${[10, 20][5]}");
    assert!(e.contains("5"), "{e}");
}

#[test]
fn map_takes_one_function_by_position() {
    let e = refused("map_two", "${[1].map(x -> x, x -> x)}");
    assert!(
        e.contains("`map` takes one function, passed by position"),
        "{e}"
    );
    let e = refused("map_value", "${[1].map(3)}");
    assert!(
        e.contains("`map` takes a function, and this value is"),
        "{e}"
    );
}

#[test]
fn map_of_a_value_with_no_entries_is_refused() {
    let e = refused("map_int", "${(3).map(x -> x)}");
    assert!(e.contains("`map` works on each entry of a family"), "{e}");
}

#[test]
fn where_takes_a_function_giving_bool() {
    let e = refused("where_int", "${[10, 20].where(x -> x + 1)}");
    assert!(
        e.contains("`where` keeps the entries its function gives `true` for"),
        "{e}"
    );
}

#[test]
fn a_fold_of_a_row_that_may_be_empty_needs_else() {
    // `max` has no identity at `int` (DESIGN sec:reduction, "Identity as data"), so the empty
    // row `[]` folds to `#empty` alone, and `+` on a value that can only be an atom is an error.
    // `(+)` folds it to its identity `0` (case `sum_of_an_empty_row_is_zero`).
    let e = refused(
        "empty_row",
        "${{0 -> [1], 1 -> []}.map(r -> (r >< max) + 1)}",
    );
    assert!(
        e.contains("the function given to `map` does not take"),
        "{e}"
    );
}

#[test]
fn a_fold_by_a_non_associative_operator_is_rejected() {
    // Bare `><` folds in any grouping and so needs an associative operator (DESIGN.md
    // sec:reduction); the repairs are the directional folds, which owe no law, written with the
    // program's own operand (MSG-example-repairs).
    let e = refused("minus", "${[1, 2] >< (-)}");
    assert!(e.contains("`-` is not associative"), "{e}");
    assert!(e.contains("`[1, 2].foldl(init, (a, x) -> a - x)`"), "{e}");
    assert!(e.contains("`[1, 2].foldr((x, a) -> x - a, init)`"), "{e}");
}

#[test]
fn a_section_is_a_function_and_not_data() {
    // `(+)` outside `><` is the function `(a, b) -> a + b`; interpolation takes data.
    let e = refused("section", "${(+)}");
    assert!(
        e.contains("Cannot show a value that may hold a function: `(+) : (T, T) -> T for T in int | f32 | f64 | rat` \
             in `\"${(+)}\"`."),
        "{e}"
    );
    let e = refused("section_map", "${[1, 2].map((+))}");
    assert!(
        e.contains("`map` calls its function with one argument, and this function needs 2"),
        "{e}"
    );
}

#[test]
fn foldl_and_foldr_take_a_start_value_and_a_function_of_two_parameters() {
    for (name, body, what) in [
        (
            "foldl_one",
            "${[1, 2].foldl(0)}",
            "`foldl` takes a start value and a function, passed by position",
        ),
        (
            "foldl_arity",
            "${[1, 2].foldl(0, x -> x)}",
            "`foldl` calls its function with 2 arguments, and this function takes 1",
        ),
        (
            "foldr_order",
            "${[1, 2].foldr(0, (+))}",
            "`foldr` takes a function of two parameters, and this value is 0",
        ),
        (
            "foldl_scalar",
            "${(3).foldl(0, (+))}",
            "`foldl` folds the entries of a family, and this value is 3",
        ),
        (
            "foldl_grows",
            "${[1, 2].foldl((0, 0), (a, x) -> (a, x))}",
            "no one type holds every step",
        ),
    ] {
        let e = refused(name, body);
        assert!(e.contains(what), "{name}: {e}");
    }
}

#[test]
fn a_range_runs_over_integers() {
    for (name, body, end, t, repair) in [
        (
            "range_float_low",
            "${0.5 ..< 3}",
            "low",
            "0.5",
            "as `0 ..< n`",
        ),
        (
            "range_bool_high",
            "${0 ..< true}",
            "high",
            "true",
            "as `0 ..< n`",
        ),
        (
            "range_string_high",
            "${0 ..= \"9\"}",
            "high",
            "\"9\"",
            "as `0 ..< n`",
        ),
        // Plan row RANGE-open: `a ..` has only a low end to give.
        (
            "open_range_float_low",
            "${3 in 0.5 ..}",
            "low",
            "0.5",
            "as `0 ..`",
        ),
    ] {
        let e = refused(name, body);
        let want = format!("a range runs over integers, and its {end} end may be {t}");
        assert!(e.contains(&want), "{name}: {e}");
        assert!(e.contains(repair), "{name}: {e}");
    }
    // A read of a range may miss, and its type says so: the miss is handled before a push
    // (pushes.rs).
}

#[test]
fn the_forms_not_built_are_refused_as_not_built() {
    // The messages name no step: the program's words only. The plan rows are named at the
    // refusals: a range with no upper end other than read by a key, `in` or a stream read
    // (RANGE-open-names), metadata reads (META-read-run), `for` (FOR-one-generator) and
    // `discard` (DISCARD-standalone) in zedc-resolve; a fold by a
    // function that owes a proof of associativity (REDUCE-by-function) in the checker. A
    // directional fold over a keyed level is built (FP-ops-run; l03_15a_fp_ops_run::cases).
    for (name, body, what) in [
        (
            "range_with_no_upper_end",
            "${[0 ..]}",
            "a range with no upper end, `a ..`, read other than by a key, by `in`, or by \
             `.first`, `.find(p)`, `.any(p)` or `.all(p)` after any number of `.map(f)` and \
             `.where(p)`, is part of the Zed language",
        ),
        (
            "read",
            "${[1]::len}",
            "a metadata read `::` is part of the Zed language",
        ),
        (
            "fold_by_function",
            "${[1, 2] >< ((a, b) -> a + b)}",
            "a fold `><` by a function other than `max`, `min` or an operator section is part \
             of the Zed language",
        ),
        (
            "one_generator_for",
            "${for x in [1, 2] { x }}",
            "a `for` is part of the Zed language",
        ),
        (
            "standalone_discard",
            "${discard([1, 2], x -> x > 1)}",
            "the prelude word `discard` is part of the Zed language",
        ),
    ] {
        let e = refused(name, body);
        assert!(e.contains(what), "{name}: {e}");
        assert!(e.contains("does not compile it yet"), "{name}: {e}");
    }
}

#[test]
fn reads_of_a_range_with_no_upper_end_that_never_end_are_refused() {
    // Plan row RANGE-open-walk: a read of every entry of `a ..`, or of a stream over it, is
    // refused before the program runs, with what it reads and the reads that end.
    for (name, body, what) in [
        ("open_count", "${(0 ..).count}", "`.count` of"),
        (
            "open_last",
            "${(0 ..).where(x -> x > 3).last}",
            "`.last` of",
        ),
        ("open_fold", "${(0 ..).map(x -> x * 2) >< (+)}", "`><` of"),
        ("open_print", "${(0 ..).map(x -> x * 2)}", "printing of"),
        ("open_equal", "${(1 ..) == (1 ..)}", "`==` of"),
        ("open_unequal", "${(1 ..) != {1, 2}}", "`!=` of"),
    ] {
        let e = refused(name, body);
        let want = format!("{what} a range with no upper end, `a ..`, would never end");
        assert!(e.contains(&want), "{name}: {e}");
        assert!(
            e.contains("repair: give the range an upper end"),
            "{name}: {e}"
        );
        assert!(!e.contains("does not compile it yet"), "{name}: {e}");
    }
}

#[test]
fn a_function_of_the_program_named_like_a_read_is_not_given_a_range_with_no_upper_end() {
    // `.first` and `.any` defined by the program may walk the whole range, so `a ..` passed
    // to them is refused, as it is passed to any function.
    for (name, body) in [
        ("own_first", "${(0 ..).first}"),
        ("own_any", "${(0 ..).any(x -> x > 3)}"),
    ] {
        let src = super::program(name, body);
        let text = std::fs::read_to_string(&src).unwrap();
        let own = "first(positional xs) = 0;\nany(positional xs, positional p) = true;\n";
        std::fs::write(&src, format!("{own}{text}")).unwrap();
        let ran = zed_tests::step_helpers::l01_36a_executables::interpreter(&src, &[], &[]);
        assert_ne!(ran.status, 0, "{name}: {}", ran.stdout);
        assert!(
            ran.stderr
                .contains("a range with no upper end, `a ..`, read other than"),
            "{name}: {}",
            ran.stderr
        );
    }
}

#[test]
fn where_over_loose_atoms_is_not_built() {
    // The test of `where` gives the atom, not a verdict, for an entry that is a loose atom,
    // and what `where` keeps then is not settled.
    let e = refused("where_atoms", "${{0 -> 1, 1 -> #oops}.where(x -> x > 0)}");
    assert!(
        e.contains("`where` over entries that may be the atoms"),
        "{e}"
    );
    assert!(e.contains("does not compile it yet"), "{e}");
}
