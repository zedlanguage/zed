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
fn a_fold_of_rows_that_are_all_empty_needs_else() {
    // `max` has no identity at `int` (DESIGN sec:reduction, "Identity as data"), so a row that
    // is always empty folds to `#empty` alone, and `+` on a value that can only be an atom is
    // an error (author's standing rule, 2026-11-09). `(+)` folds it to its identity `0` (case
    // `sum_of_an_empty_row_is_zero`).
    for (name, body) in [
        ("empty_row", "${{0 -> []}.map(r -> (r >< max) + 1)}"),
        ("empty_rows", "${[[], []].map(r -> (r >< max) + 1)}"),
    ] {
        let e = refused(name, body);
        assert!(
            e.contains("the function given to `map` does not take"),
            "{e}"
        );
    }
}

#[test]
fn a_fold_of_an_empty_display_always_fails() {
    // `[]` has no entries and no type of entry, so no carrier gives `+` or `max` an identity
    // and the fold is `#empty` on every run: an operation that always fails, rejected at the
    // fold (DESIGN sec:type_language, the `m >< op` row: "`[] >< max` is rejected";
    // sec:failure; row FAIL-empty-literal-fold-always-fails). An `else` on the atom does not
    // make the fold useful, so it is refused with it. These were run cases before the row.
    for (name, body, fold) in [
        ("plus", "${([] >< (+)) else #empty -> -1}", "`[] >< (+)`"),
        ("max", "${([] >< max) else #empty -> -1}", "`[] >< max`"),
        ("min", "${[] >< min}", "`[] >< min`"),
        ("reduce", "${[].reduce((+))}", "`[].reduce((+))`"),
        ("sum", "${[].sum}", "`[].sum`"),
    ] {
        let e = refused(&format!("empty_{name}"), body);
        assert!(
            e.contains(&format!("{fold} here always fails with `#empty`")),
            "{body}: {e}"
        );
        assert!(e.contains("repair: give the entries a type"), "{body}: {e}");
    }
}

#[test]
fn a_fold_that_may_have_entries_is_not_refused() {
    // The rule refuses only a receiver proved to have no entries. A value that is `[]` on one
    // branch alone may have entries, and the checker does not evaluate `1 > 2` (it never runs
    // the program's code), so the fold is accepted; each row of a display of rows that holds
    // `[]` beside a row with entries is `a_fold_of_a_row_that_may_be_empty_passes_empty_by`.
    for body in [
        "${(if 1 > 2 { [3, 4] } else { [] }) >< (+)}",
        "${(if 1 > 2 { [3, 4] } else { [] }) >< max}",
    ] {
        let ran = run("branch", body);
        assert_eq!(ran.status, 0, "{body}: {}", ran.stderr);
    }
}

#[test]
fn a_fold_of_a_row_that_may_be_empty_passes_empty_by() {
    // The function's input is either row, so `r >< max` is `int | #empty`: a number for some
    // inputs and the atom for others, which is no error (the rule's other half) and gives the
    // atom for the empty row, as `.map(r -> r >< max)` gives it. The checker refused this
    // before (row FAIL-fold-rotating-tuple-rounds, E2b).
    for (name, body, out) in [
        (
            "plus",
            "${{0 -> [1], 1 -> []}.map(r -> (r >< max) + 1)}",
            "{0 -> 2, 1 -> #empty}",
        ),
        (
            "list",
            "${[[1], []].map(r -> (r >< max) + 1)}",
            "{0 -> 2, 1 -> #empty}",
        ),
        (
            "abs",
            "${{0 -> [-1], 1 -> []}.map(r -> abs(r >< max))}",
            "{0 -> 1, 1 -> #empty}",
        ),
        (
            "else",
            "${{0 -> [1], 1 -> []}.map(r -> (r >< max) + 1 else #empty -> 0)}",
            "{0 -> 2, 1 -> 0}",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, out),
            "{name}: {}",
            ran.stderr
        );
    }
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
            "zedc finds no one type that holds every step",
        ),
    ] {
        let e = refused(name, body);
        assert!(e.contains(what), "{name}: {e}");
    }
}

/// An accumulator that `f` nests deeper each round is refused, and the repair is written in
/// the start value's own form: for a tuple, a function that gives back each of its parts
/// (row FAIL-fold-rotating-tuple-rounds); for a scalar, `+`.
#[test]
fn a_growing_accumulator_is_refused_with_a_repair_in_its_own_form() {
    for (name, body, repair) in [
        (
            "grows_foldl_pair",
            "${[1, 2].foldl((0, 0), (a, x) -> (a, x))}",
            "repair: give the function a result of the start value's type, as \
             `(a, x) -> (a[0], a[1])`",
        ),
        (
            "grows_foldr_triple",
            "${[1, 2].foldr((x, a) -> (x, a, 0), (0, 0, 0))}",
            "repair: give the function a result of the start value's type, as \
             `(x, a) -> (a[0], a[1], a[2])`",
        ),
        (
            "grows_foldl_one",
            "${[1, 2].foldl((0,), (a, x) -> (a,))}",
            "repair: give the function a result of the start value's type, as \
             `(a, x) -> (a[0],)`",
        ),
        (
            "grows_foldl_scalar",
            "${[1, 2].foldl(0, (a, x) -> (a, x))}",
            "repair: give the function a result of the start value's type, as \
             `(a, x) -> a + x`",
        ),
        (
            "grows_foldl_payload",
            "${[1, 2].foldl(#a(0), (a, x) -> #a(a))}",
            "repair: give the function a result of the start value's type, as \
             `(a, x) -> a`",
        ),
        (
            "grows_foldr_payload",
            "${[1, 2].foldr((x, a) -> #ok(a), #start(n: 0))}",
            "repair: give the function a result of the start value's type, as \
             `(x, a) -> a`",
        ),
    ] {
        let e = refused(name, body);
        assert!(
            e.contains("zedc finds no one type that holds every step"),
            "{name}: {e}"
        );
        assert!(e.contains(repair), "{name}: {e}");
    }
}

/// Every refusal repair emitted by `fold_dir_end` fits its start value and entries and checks
/// with zero errors when substituted into the program.
#[test]
fn fold_refusal_repairs_fit_every_start_value_and_check() {
    use zed_tests::step_helpers::l01_26_type_resolution::Resolved;
    for (name, failing, want_repair, fixed) in [
        (
            "open_tuple",
            "f(y) = [1, 2].foldl((y, 0), (a, x) -> (a, x));\n",
            "`(a, x) -> (a[0], a[1])`",
            "f(y) = [1, 2].foldl((y, 0), (a, x) -> (a[0], a[1]));\n",
        ),
        (
            "empty_tuple",
            "f() = [1, 2].foldl((), (a, x) -> (a, x));\n",
            "`(a, x) -> ()`",
            "f() = [1, 2].foldl((), (a, x) -> ());\n",
        ),
        (
            "string_over_int",
            "f() = [1, 2].foldl(\"hi\", (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl(\"hi\", (a, x) -> a);\n",
        ),
        (
            "string_over_string",
            "f() = [\"a\", \"b\"].foldl(\"hi\", (a, x) -> (a, x));\n",
            "`(a, x) -> a ++ x`",
            "f() = [\"a\", \"b\"].foldl(\"hi\", (a, x) -> a ++ x);\n",
        ),
        (
            "int_over_string",
            "f() = [\"a\", \"b\"].foldl(0, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [\"a\", \"b\"].foldl(0, (a, x) -> a);\n",
        ),
        (
            "float_over_int",
            "f() = [1, 2].foldl(1.5, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl(1.5, (a, x) -> a);\n",
        ),
        (
            "bool_start",
            "f() = [1, 2].foldl(true, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl(true, (a, x) -> a);\n",
        ),
        (
            "atom_start",
            "f() = [1, 2].foldl(#a, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl(#a, (a, x) -> a);\n",
        ),
        (
            "payload_start",
            "f() = [1, 2].foldl(#ok(0), (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl(#ok(0), (a, x) -> a);\n",
        ),
        (
            "array_start",
            "f() = [1, 2].foldl([0], (a, x) -> (a, x));\n",
            "`(a, x) -> a ++ [x]`",
            "f() = [1, 2].foldl([0], (a, x) -> a ++ [x]);\n",
        ),
        (
            "foldr_array_start",
            "f() = [1, 2].foldr((x, a) -> (a, x), [0]);\n",
            "`(x, a) -> [x] ++ a`",
            "f() = [1, 2].foldr((x, a) -> [x] ++ a, [0]);\n",
        ),
        (
            "union_of_tuples",
            "f(b: bool) = [1, 2].foldl(if b { (0, 0) } else { (1, 1, 1) }, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f(b: bool) = [1, 2].foldl(if b { (0, 0) } else { (1, 1, 1) }, (a, x) -> a);\n",
        ),
        (
            "fn_start",
            "f() = [1, 2].foldl(y -> y, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl(y -> y, (a, x) -> a);\n",
        ),
        (
            "foldr_string_over_int",
            "f() = [1, 2].foldr((x, a) -> (a, x), \"hi\");\n",
            "`(x, a) -> a`",
            "f() = [1, 2].foldr((x, a) -> a, \"hi\");\n",
        ),
        (
            "foldr_string_over_string",
            "f() = [\"a\", \"b\"].foldr((x, a) -> (a, x), \"hi\");\n",
            "`(x, a) -> x ++ a`",
            "f() = [\"a\", \"b\"].foldr((x, a) -> x ++ a, \"hi\");\n",
        ),
        (
            "map_string_keys",
            "f() = [1, 2].foldl({\"a\" -> 0}, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl({\"a\" -> 0}, (a, x) -> a);\n",
        ),
        (
            "map_non_rank_keys",
            "f() = [1, 2].foldl({10 -> 0}, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl({10 -> 0}, (a, x) -> a);\n",
        ),
        (
            "range_non_zero_start",
            "f() = [1, 2].foldl(1 ..= 3, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl(1 ..= 3, (a, x) -> a);\n",
        ),
        (
            "set_start",
            "f() = [1, 2].foldl({1, 2}, (a, x) -> (a, x));\n",
            "`(a, x) -> a`",
            "f() = [1, 2].foldl({1, 2}, (a, x) -> a);\n",
        ),
        (
            "empty_list_start",
            "f() = [1, 2].foldl([], (a, x) -> (a, x));\n",
            "`(a, x) -> a ++ [x]`",
            "f() = [1, 2].foldl([], (a, x) -> a ++ [x]);\n",
        ),
        (
            "zero_based_range_start",
            "f() = [1, 2].foldl(0 ..= 2, (a, x) -> (a, x));\n",
            "`(a, x) -> a ++ [x]`",
            "f() = [1, 2].foldl(0 ..= 2, (a, x) -> a ++ [x]);\n",
        ),
    ] {
        let inf = Resolved::new(failing).check();
        assert_eq!(inf.errors.len(), 1, "{name}: {:?}", inf.errors);
        assert!(
            inf.errors[0]
                .message
                .contains("zedc finds no one type that holds every step"),
            "{name}: {}",
            inf.errors[0].message
        );
        assert!(
            inf.errors[0]
                .notes
                .iter()
                .any(|n| n.text.contains(want_repair)),
            "{name}: {:?}",
            inf.errors[0].notes
        );
        let ok = Resolved::new(fixed).check();
        assert!(
            ok.errors.is_empty(),
            "{name} repair failed: {:?}",
            ok.errors
        );
    }
}

/// The repair fits a start value that is not a tuple, and runs: `+` only where the start is
/// a number of the entries' carrier (`0.5 + 1` is refused), the entry at the end for a list,
/// and the accumulator given back for an atom, a payload, a function or a union of tuples
/// (Opus seat, round 1). Each repair, written into the program, runs and prints the line
/// given; the function the repaired fold gives is called at 3 (before the kernel's `gen` held
/// functions, row FAIL-fold-rotating-tuple-rounds, that call stopped the run).
#[test]
fn a_growing_accumulator_that_is_not_a_tuple_gets_a_repair_that_fits_it() {
    let pair = "if m.args.count > 0 { (0, 0) } else { (0, 0, 0) }";
    for (name, start, right, repair, expected) in [
        ("grows_atom", "#n", false, "(a, x) -> a", "true"),
        ("grows_payload", "#p(0)", false, "(a, x) -> a", "true"),
        ("grows_f64", "0.5", false, "(a, x) -> a", "0.5"),
        (
            "grows_list",
            "[0]",
            false,
            "(a, x) -> a ++ [x]",
            "{0, 1, 2}",
        ),
        (
            "grows_list_r",
            "[0]",
            true,
            "(x, a) -> [x] ++ a",
            "{0 -> 1, 1 -> 2, 2 -> 0}",
        ),
        ("grows_union", pair, false, "(a, x) -> a", "(0, 0, 0)"),
        ("grows_fn", "y -> y", false, "(a, x) -> a", "3"),
    ] {
        let fold = |f: &str| match right {
            false => format!("[1, 2].foldl({start}, {f})"),
            true => format!("[1, 2].foldr({f}, {start})"),
        };
        let grows = if right {
            "(x, a) -> (x, a)"
        } else {
            "(a, x) -> (a, x)"
        };
        let e = refused(name, &format!("${{{}}}", fold(grows)));
        let offered =
            format!("repair: give the function a result of the start value's type, as `{repair}`");
        assert!(e.contains(&offered), "{name}: {e}");
        let shown = match start {
            "#n" | "#p(0)" => format!("${{{} == {start}}}", fold(repair)),
            "y -> y" => format!("${{{}(3)}}", fold(repair)),
            _ => format!("${{{}}}", fold(repair)),
        };
        let ran = run(&format!("{name}_repaired"), &shown);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {shown}\n{}",
            ran.stderr
        );
    }
}

/// A fold whose function makes a function that calls the accumulator is refused, and the
/// message says how its two steps differ, though they print alike: each `y -> a(y) + x`
/// needs a call of `a`, whose type holds the step before, one level deeper each round, so no
/// type zedc can write holds every step. Before, the message read "makes it _ -> int, then
/// _ -> int" with nothing to tell the two apart.
#[test]
fn a_fold_whose_steps_print_alike_says_how_they_differ() {
    let e = refused(
        "fold_composes",
        "${[1, 2, 3].foldl(y -> y, (a, x) -> (y -> a(y) + x))(10)}",
    );
    assert!(
        e.contains(
            "makes it _ -> int, and later _ -> int, which print alike but differ in what the \
             function needs of its argument: zedc finds no one type that holds every step"
        ),
        "{e}"
    );
    let e_tuple = refused(
        "fold_tuple_composes",
        "${[1, 2, 3].foldl((0, y -> y), (a, x) -> (a[0] + x, y -> a[1](y) + x))[1](10)}",
    );
    assert!(
        e_tuple.contains("which print alike but differ in what the function needs of its argument"),
        "{e_tuple}"
    );
}

/// A scan by an operator whose fold is not built is named as a scan, with the function the
/// program wrote (row TEST-types-unreached-paths-3: `FoldForm::what`). A scan of a value that
/// is not a family is refused before the fold, by the words on one level (`levels_of`), with
/// `[1, 2, 3].scan(...)` as the repair.
#[test]
fn a_refused_scan_is_named_as_a_scan() {
    let e = refused("scan_concat", "${[\"a\", \"b\"].scan((++))}");
    assert!(
        e.contains("a scan `.scan((++))` of entries of type \"a\" | \"b\""),
        "{e}"
    );
    assert!(e.contains("not supported by this version of zedc"), "{e}");
    let e = refused("scan_scalar", "${(3).scan((+))}");
    assert!(
        e.contains("`.scan` reads the entries of a family, and this value is 3"),
        "{e}"
    );
    assert!(
        e.contains("repair: call it on a family, as `[1, 2, 3].scan((+))`"),
        "{e}"
    );
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
        assert!(
            e.contains("not supported by this version of zedc"),
            "{name}: {e}"
        );
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
        assert!(
            !e.contains("not supported by this version of zedc"),
            "{name}: {e}"
        );
    }
}

#[test]
fn a_function_of_the_program_named_like_a_read_is_not_given_a_range_with_no_upper_end() {
    // `.first` and `.any` defined by the program may walk the whole range, so `a ..` passed
    // to them is refused, as it is passed to any function.
    // A link of the stream named by the program's own `map` or `where` is an ordinary call
    // too (zedc-resolve resolve.rs `Task::OpenStream`), though the read is the prelude's.
    for (name, body) in [
        ("own_first", "${(0 ..).first}"),
        ("own_any", "${(0 ..).any(x -> x > 3)}"),
        ("own_map", "${(0 ..).map(x -> x * 2).first}"),
        ("own_where", "${(0 ..).where(x -> x > 3).any(x -> x > 5)}"),
    ] {
        let src = super::program(name, body);
        let text = std::fs::read_to_string(&src).unwrap();
        let own = match name {
            "own_map" => "map(positional xs, positional f) = xs;\n",
            "own_where" => "where(positional xs, positional p) = xs;\n",
            _ => "first(positional xs) = 0;\nany(positional xs, positional p) = true;\n",
        };
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

/// A key of a map or set display whose type holds more than one value is one of them, not
/// each, so it is permitted, not guaranteed (`display_ty` in zedc-check walk.rs, found by the
/// audit proofdoc2b): a read of another key may miss. A key of one value,
/// as a literal, is still guaranteed, beside a computed one too.
#[test]
fn a_key_of_many_values_is_permitted_not_guaranteed() {
    use zed_tests::step_helpers::l01_26_type_resolution::sig;
    let mut wrong = Vec::new();
    for (src, want) in [
        // Before: `(n: int) -> 10`, and `f(n: 2)` ran to `#notFound`.
        (
            "f(n: int) = { n -> 10 }[n + 1];\n",
            "(n: int) -> 10 | #notFound",
        ),
        ("f(n: int) = { n }[n + 1];\n", "(n: int) -> int | #notFound"),
        (
            "f(n: int) = { 2 -> 10, n -> 20 }[2];\n",
            "(n: int) -> 10 | 20",
        ),
        (
            "f(n: int) = { 2 -> 10, n -> 20 }[3];\n",
            "(n: int) -> 10 | 20 | #notFound",
        ),
        // Unchanged: a display of literal keys, whose values a read joins into one type.
        (
            "f(n: int) = { 2 -> 10 }[n];\n",
            "(n: int) -> 10 | #notFound",
        ),
        (
            "f(n: int) = { 2 -> 10, 3 -> 20 }[2];\n",
            "(n: int) -> 10 | 20",
        ),
    ] {
        let got = sig(src, "f");
        if got != want {
            wrong.push(format!("{src}  gave {got}, wanted {want}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
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
    assert!(e.contains("not supported by this version of zedc"), "{e}");
}
