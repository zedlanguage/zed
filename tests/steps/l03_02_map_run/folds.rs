//! Folds whose accumulator type settles only after many rounds of the checker's fixed point
//! (row FAIL-fold-rotating-tuple-rounds): a tuple of n parts whose function rotates it gains
//! `f64` at one more part each round, so its type settles at `(int | f64, ...)` after n
//! rounds, whatever n is. Each expected line is worked by hand: `foldl` with
//! `(a, x) -> (a[1], ..., a[n - 1], a[0])` moves the part at index i to index i - 1 (mod n),
//! so after k entries the 1.5 that starts at index 0 is at index (-k mod n); `foldr` with
//! `(x, a) -> (a[n - 1], a[0], ..., a[n - 2])` moves it to index k mod n.

use super::run;

/// The tuple of `n` parts with `1.5` at index `at` and `0` elsewhere, as zedc prints it.
fn with_one_at(n: usize, at: usize) -> String {
    let parts: Vec<&str> = (0..n).map(|i| if i == at { "1.5" } else { "0" }).collect();
    format!("({})", parts.join(", "))
}

/// The body that folds the 9 entries `[1, ..., 9]` from the tuple of `n` parts that holds
/// `1.5` at index 0, by `foldl` when `left`, else by `foldr`, each rotating the tuple.
fn rotating(n: usize, left: bool) -> String {
    let start = with_one_at(n, 0);
    let entries = "[1, 2, 3, 4, 5, 6, 7, 8, 9]";
    if left {
        let parts: Vec<String> = (0..n).map(|i| format!("a[{}]", (i + 1) % n)).collect();
        format!(
            "${{{entries}.foldl({start}, (a, x) -> ({}))}}",
            parts.join(", ")
        )
    } else {
        let parts: Vec<String> = (0..n).map(|i| format!("a[{}]", (i + n - 1) % n)).collect();
        format!(
            "${{{entries}.foldr((x, a) -> ({}), {start})}}",
            parts.join(", ")
        )
    }
}

#[test]
fn a_rotated_tuple_accumulator_settles_and_runs_at_any_width() {
    for n in [2, 6, 7, 8, 9, 12, 20] {
        for left in [true, false] {
            let body = rotating(n, left);
            let name = format!("rotate_{}_{n}", if left { "foldl" } else { "foldr" });
            let ran = run(&name, &body);
            let at = if left { (9 * (n - 1)) % n } else { 9 % n };
            assert_eq!(
                (ran.status, ran.stdout.trim_end()),
                (0, with_one_at(n, at).as_str()),
                "{name}: {body}\n{}",
                ran.stderr
            );
        }
    }
}

/// Rotations whose parts are tuples, and a result that drops the accumulator, settle: their
/// results keep one skeleton, so the fold's test of growth never refuses them. Worked by
/// hand: rotating `((1.5,), (0,), (0,))` left over 4 entries moves `(1.5,)` from index 0 to
/// index (-4 mod 3) = 2; `(a, x) -> (x, x)` over `[1, 2, 3]` ends at `(3, 3)`.
#[test]
fn a_rotation_of_nested_tuples_and_a_result_without_the_accumulator_settle() {
    for (name, body, expected) in [
        (
            "rotate_nested",
            "${[1, 2, 3, 4].foldl(((1.5,), (0,), (0,)), (a, x) -> (a[1], a[2], a[0]))}",
            "((0,), (0,), (1.5,))",
        ),
        (
            "drops_acc",
            "${[1, 2, 3].foldl(0, (a, x) -> (x, x))}",
            "(3, 3)",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {body}\n{}",
            ran.stderr
        );
    }
}

/// Accumulator pruning keeps each kept piece's payload shapes (`acc.of_piece`) instead of
/// dropping them to `#name(..)` via `Piece::ty()`.
#[test]
fn fold_pruning_preserves_atom_payloads() {
    use zed_tests::step_helpers::l01_26_type_resolution::sig;
    assert_eq!(
        sig("f() = [1, 2].foldl(#ok(0), (a, x) -> #ok(1.5));\n", "f"),
        "() -> #ok(int) | #ok(f64)"
    );
    assert_eq!(
        sig("f() = [1, 2].foldl(#ok(0), (a, x) -> #err(x));\n", "f"),
        "() -> #err(int) | #ok(int)"
    );
    assert_eq!(
        sig(
            "f() = [1, 2].foldl(#ok(v: 0), (a, x) -> #ok(v: 1.5));\n",
            "f"
        ),
        "() -> #ok(v: int) | #ok(v: f64)"
    );
}

/// Accumulator pruning preserves named atom family markings (`Ty.family`), so family members
/// remain data atoms (kept by `else` and rejected by `+`) rather than turning into loose
/// failure atoms.
#[test]
fn fold_pruning_preserves_named_atom_families() {
    use zed_kernel::types::Type as KType;
    use zedc::check::ty::Ty;
    use zedc::check::walk::check_given;
    let color = Ty::set(KType::atom("red"))
        .union(&Ty::set(KType::atom("green")))
        .named();
    let src = "c = 0;\nf() = ([1, 2].foldl(c, (a, x) -> #blue)) else 0;\n\
               g() = ([1, 2].foldl(c, (a, x) -> #blue)) + 1;\n";
    let tokens = zedc::lex::lex_fence(src).unwrap();
    let tree = zedc::parse::parse(src, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(src, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap();
    let inf = check_given(&stmts, &res, src, color);
    let mut sigs: Vec<(usize, String)> = inf
        .sigs
        .iter()
        .map(|(id, s)| (*id, s.to_string()))
        .collect();
    sigs.sort_by_key(|(id, _)| *id);
    // `f` strips only the loose `#blue` and keeps the named family `#green | #red`.
    assert_eq!(sigs[0].1, "() -> 0 | #green | #red");
    // `g` rejects `+` on the named family atoms `#green | #red`.
    assert_eq!(inf.errors.len(), 1, "{:?}", inf.errors);
    assert!(
        inf.errors[0].message.contains("`+` does not take"),
        "{}",
        inf.errors[0].message
    );
}

/// Rotating tuples of arrays, ranges, maps, and functions settle instead of hitting a false
/// canonical-form collision (refusal (a)): `Ty::carriers` keeps each `Sig` whole, and canonical
/// forms distinguish their finite scalar literals and written range ends.
#[test]
fn rotated_tuples_of_families_ranges_and_functions_settle() {
    use zed_tests::step_helpers::l01_26_type_resolution::Resolved;
    for (name, src) in [
        (
            "rot3_arrays_foldl",
            "f() = [1, 2, 3].foldl(([0], [1], [2]), (a, x) -> (a[1], a[2], a[0]));\n",
        ),
        (
            "rot3_arrays_foldr",
            "f() = [1, 2, 3].foldr((x, a) -> (a[2], a[0], a[1]), ([0], [1], [2]));\n",
        ),
        (
            "rot3_ranges",
            "f() = [1, 2, 3].foldl((0 ..= 0, 0 ..= 1, 0 ..= 2), (a, x) -> (a[1], a[2], a[0]));\n",
        ),
        (
            "rot3_fns",
            "f() = [1, 2, 3].foldl(((y: int) -> 0, (y: int) -> 1, (y: int) -> 2), (a, x) -> (a[1], a[2], a[0]));\n",
        ),
        (
            "rot3_maps",
            "f() = [1, 2, 3].foldl(({0 -> 0}, {0 -> 1}, {0 -> 2}), (a, x) -> (a[1], a[2], a[0]));\n",
        ),
    ] {
        let inf = Resolved::new(src).check();
        assert!(inf.errors.is_empty(), "{name}: {:?}", inf.errors);
    }
    let ran = run(
        "rot3_arrays_run",
        "${[1, 2, 3, 4].foldl(([0], [1], [2]), (a, x) -> (a[1], a[2], a[0]))}",
    );
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, "({0 -> 1}, {0 -> 2}, {0})"),
        "{}",
        ran.stderr
    );
}

/// A generic fold whose accumulator rotates three pre-fold type variables settles: known
/// variables do not count toward skeleton width, so moving from 2 to 3 variables in a 2-tuple
/// does not falsely trip refusal (b).
#[test]
fn generic_fold_with_three_pre_fold_type_variables_settles() {
    use zed_tests::step_helpers::l01_26_type_resolution::sig;
    assert_eq!(
        sig(
            "h(y, z, w) = [1, 2, 3].foldl((y, z), (a, x) -> (a[1], if x > 1 { a[0] } else { w }));\n",
            "h"
        ),
        "(y: T, z: U, w: V) -> (T | U | V, T | U | V)"
    );
}

/// A result whose parts read the accumulator's parts one level down settles once each part
/// has been read (B1 of round 1 of FAIL-fold-rotating-tuple-rounds; Opus seat's test, with
/// the Codex seat's shift added): `fold_depth_limit` proves its depth stops growing. Worked by
/// hand over `[1, 2, 3]`: `(a, x) -> (0, (a[0],), (a[1],))` from `(0, 0, 0)` gives
/// `(0, (0,), (0,))`, then `(0, (0,), ((0,),))`, then the same; `(a, x) -> ((a[1],), (a[2],),
/// 0)` gives `((0,), (0,), 0)`, then `(((0,),), (0,), 0)`, then the same. Each bound is
/// `D = 3`.
#[test]
fn a_result_that_reads_the_accumulator_one_level_down_settles() {
    for (name, body, expected) in [
        (
            "delay_foldl",
            "${[1, 2, 3].foldl((0, 0, 0), (a, x) -> (0, (a[0],), (a[1],)))}",
            "(0, (0,), ((0,),))",
        ),
        (
            "delay_foldr",
            "${[1, 2, 3].foldr((x, a) -> (0, (a[0],), (a[1],)), (0, 0, 0))}",
            "(0, (0,), ((0,),))",
        ),
        (
            "shift_foldl",
            "${[1, 2, 3].foldl((0, 0, 0), (a, x) -> ((a[1],), (a[2],), 0))}",
            "(((0,),), (0,), 0)",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {body}\n{}",
            ran.stderr
        );
    }
}

/// A delay chain whose result is chosen by an `if` that does not read the accumulator settles
/// as the unconditional one does (Codex seat, round 2 of FAIL-fold-rotating-tuple-rounds,
/// R2-1: `fold_depth_limit` read only a body that is a tuple, so this fold was refused).
/// Worked by hand over `[1, 2, 3]`: the first gives `(0, (0,), (0,))`, then `(0, (0,),
/// ((0,),))`, then the same; the second gives `(2, (0,), (0,))` at `x = 1`, `(1, (2,),
/// ((0,),))` at `x = 2`, `(0, (1,), ((2,),))` at `x = 3`.
#[test]
fn a_delay_chain_under_an_if_settles() {
    for (name, body, expected) in [
        (
            "if_delay_foldl",
            "${[1, 2, 3].foldl((0, 0, 0), (a, x) -> \
             if x > 0 { (0, (a[0],), (a[1],)) } else { (1, (a[0],), (a[1],)) })}",
            "(0, (0,), ((0,),))",
        ),
        (
            "else_if_delay_foldl",
            "${[1, 2, 3].foldl((0, 0, 0), (a, x) -> \
             if x > 2 { (0, (a[0],), (a[1],)) } else if x > 1 { (1, (a[0],), (a[1],)) } \
             else { (2, (a[0],), (a[1],)) })}",
            "(0, (1,), ((2,),))",
        ),
        (
            "if_delay_foldr",
            "${[1, 2, 3].foldr((x, a) -> \
             if x > 0 { (0, (a[0],), (a[1],)) } else { (1, (a[0],), (a[1],)) }, (0, 0, 0))}",
            "(0, (0,), ((0,),))",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {body}\n{}",
            ran.stderr
        );
    }
}

/// The accumulator keeps the payload its atoms were built with as its type settles: the fold
/// of `#ok(0)` that may turn to `#err(x)` is `#err(int) | #ok(int)`, not `#ok(..)`, whose
/// payload is not known; and a refused fold shows the payload of its start value in each
/// step (Opus seat, B2 of round 1).
#[test]
fn an_accumulator_keeps_the_payload_of_its_atoms() {
    let body = "${[1, 2, 3].foldl(#ok(0), (a, x) -> if x > 1 { #err(x) } else { a }) + 1}";
    let ran = run("payload_kept", body);
    assert!(
        ran.stderr
            .contains("this expression is String | #err(int) | #ok(int)"),
        "{}",
        ran.stderr
    );
    let ran = run(
        "payload_kept_grows",
        "${[1, 2].foldl(#p(0), (a, x) -> (a, x))}",
    );
    assert!(
        ran.stderr
            .contains("and later ((#p(int), int) | #p(int), 1 | 2)"),
        "{}",
        ran.stderr
    );
}

/// Joining a different result keeps the start value's payload field type for the two
/// handlers (Codex seat, B2 of round 1).
#[test]
fn an_accumulator_join_preserves_payload_fields() {
    let body = "${([1, 2].foldl(#start(n: 0), (a, x) -> #ok(n: x)) \
                 else #start(n:) -> n) else #ok(n:) -> n}";
    let ran = run("fold_known_payloads", body);
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, "2"),
        "{}",
        ran.stderr
    );

    let wrong_field = body.replace("#start(n: 0)", "#start(other: 0)");
    let ran = run("fold_missing_payload_field", &wrong_field);
    assert_eq!(ran.status, 1, "{}", ran.stdout);
    assert!(ran.stderr.contains("#start(other: int)"), "{}", ran.stderr);
}

/// The repairs the refusal offers check and run for their start values: a closed tuple's
/// copies every part; a payload, a union and an open tuple give back the accumulator (Codex
/// seat).
#[test]
fn an_accumulator_repair_checks_for_its_seed() {
    for (name, body, expected) in [
        (
            "fold_pair_repair",
            "${[1, 2].foldl((0, 1), (a, x) -> (a[0], a[1]))}",
            "(0, 1)",
        ),
        (
            "fold_triple_repair",
            "${[1, 2].foldr((x, a) -> (a[0], a[1], a[2]), (0, 1, 2))}",
            "(0, 1, 2)",
        ),
        (
            "fold_single_repair",
            "${[1, 2].foldl((0,), (a, x) -> (a[0],))}",
            "(0,)",
        ),
        (
            "fold_payload_right_repair",
            "${[1, 2].foldr((x, a) -> a, #start(n: 3)) else #start(n:) -> n}",
            "3",
        ),
        (
            "fold_union_repair",
            "${[1, 2].foldl(if m.args.count > 0 { (0,) } else { (0, 1) }, (a, x) -> a)}",
            "(0, 1)",
        ),
        (
            "fold_open_tuple_repair",
            "${(z -> [1, 2].foldl((z,), (a, x) -> a))(0)}",
            "(0,)",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {}",
            ran.stderr
        );
    }
}

/// The fold's type keeps which rows go together: the start value is the only result whose
/// second part is `int`, so `(int | f64, int)` is not in it, and a parameter that takes
/// `(int, int) | (int | f64, f64)` takes the fold but not `(1.5, 0)` (Codex seat; the
/// correlation PERF-fold-projection-fast-path must keep).
#[test]
fn projection_retains_the_seed_and_result_row_correlation() {
    let accepts = r#"
require(positional a: (int, int) | (int | f64, f64)) = 7;
main(m: MainArgs) {
    m.stdout <- "${require([1.5, 2.5].foldl((0, 0), (a, x) -> (a[1], x)))}";
}
"#;
    let mistakenly_added =
        accepts.replace("[1.5, 2.5].foldl((0, 0), (a, x) -> (a[1], x))", "(1.5, 0)");
    for (name, source, status) in [
        ("fold_projection_rows", accepts, 0),
        ("fold_projection_extra_row", &mistakenly_added, 1),
    ] {
        let src = super::dir(&format!("l03_02_map_run/{name}")).join("main.zed");
        std::fs::write(&src, source).unwrap();
        let ran = super::interpreter(&src, &[], &[]);
        assert_eq!(ran.status, status, "{name}: {}", ran.stderr);
        if status == 0 {
            assert_eq!(ran.stdout.trim_end(), "7");
        } else {
            assert!(
                ran.stderr.contains("`require` does not take"),
                "{}",
                ran.stderr
            );
        }
    }
}

/// A start value passed through a function whose parameter type is written holds the type
/// the fold's results take, so the fold settles at once (Codex seat: the escape a written
/// type gives).
#[test]
fn a_written_invariant_holds_two_steps_of_tuple_nesting() {
    let source = r#"
invariant(positional a: (int, int, int) | ((int | (int,),), (int,), int)) = a;
main(m: MainArgs) {
    m.stdout <- "${[1, 2, 3].foldl(invariant((0, 0, 0)), (a, x) -> ((a[1],), (a[2],), 0))}";
}
"#;
    let src = super::dir("l03_02_map_run/fold_written_invariant").join("main.zed");
    std::fs::write(&src, source).unwrap();
    let ran = super::interpreter(&src, &[], &[]);
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, "(((0,),), (0,), 0)"),
        "{}",
        ran.stderr
    );
}

/// Folds whose results take finitely many shapes settle: results chosen by the
/// accumulator's own shape, a family accumulator, a fold inside a fold, and a fold of a
/// generic function's parameters (Codex seat).
#[test]
fn conditional_nested_and_generic_fold_results() {
    for (name, body, expected) in [
        (
            "fold_conditional_nested",
            "${[1, 2, 3].foldl(0, (a, x) -> if a is int { (x,) } else { \
                if a is (int,) { ((x,),) } else { a } })}",
            "((2,),)",
        ),
        (
            "fold_conditional_wide_right",
            "${[1, 2, 3].foldr((x, a) -> if a is (int,) { (x, x) } else { \
                if a is (int, int) { (x, x, x) } else { a } }, (0,))}",
            "(2, 2, 2)",
        ),
        (
            "fold_family_accumulator",
            "${[1, 2, 3].foldl([0], (a, x) -> [x])}",
            "{0 -> 3}",
        ),
        (
            "fold_in_a_fold",
            "${[1, 2, 3].foldl((0,), (a, x) -> [x].foldl(a, (b, y) -> (y,)))}",
            "(3,)",
        ),
        (
            "fold_generic_receiver_and_reducer",
            "${((f, xs) -> xs.foldl(0, f))((+), [1, 2, 3])}",
            "6",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {}",
            ran.stderr
        );
    }
}

/// `else` on a read of the accumulator, whose entries' type the start value fixed, checks
/// and runs. Worked by hand: `[0]` becomes `[1]`, `[2]`, `[3]`, which prints as a family.
/// Before, the checker refused it with "gives int here, which is not int": the replay of
/// `a[0] else 0` gave `0 | $3`, `$3` the solved entry type of `[0]`, which it did not read.
#[test]
fn else_on_a_read_of_the_accumulator_checks() {
    for (name, body, expected) in [
        (
            "fold_else_entry",
            "${[1, 2, 3].foldl([0], (a, x) -> [(a[0] else 0) + 1])}",
            "{0 -> 3}",
        ),
        (
            "fold_else_entry_right",
            "${[1, 2, 3].foldr((x, a) -> [(a[0] else 0) + x], [0])}",
            "{0 -> 6}",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {}",
            ran.stderr
        );
    }
}

/// A fold whose accumulator is a function runs, and the function it ends with is called.
/// Worked by hand: `(a, x) -> (y -> y + x)` over `[1, 2, 3]` ends at `y -> y + 3`, which
/// gives 13 at 10; `(a, x) -> a` keeps `y -> y`, which gives 3 at 3. Before, the checker took
/// both, and the run stopped with zedc's message for a bug of its own ("expected data, found
/// a function"): the kernel's `gen`, which runs `foldl` and `foldr`, held only data frames.
#[test]
fn a_fold_whose_accumulator_is_a_function_runs() {
    for (name, body, expected) in [
        (
            "fold_fn_replaced",
            "${[1, 2, 3].foldl(y -> y, (a, x) -> (y -> y + x))(10)}",
            "13",
        ),
        (
            "fold_fn_kept",
            "${[1, 2].foldl(y -> y, (a, x) -> a)(3)}",
            "3",
        ),
        (
            "fold_fn_kept_right",
            "${[1, 2].foldr((x, a) -> a, y -> y)(3)}",
            "3",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {}",
            ran.stderr
        );
    }
}

/// A fold following a chain of `map` helpers that reserve sparse R10 classes checks without
/// indexing unmaterialized internal classes (`M62 VIOLATION`).
#[test]
fn fold_after_map_chain_does_not_read_unmaterialized_classes() {
    use zed_tests::step_helpers::l01_26_type_resolution::Resolved;
    let src = "\
h0(positional m) = m.map(x -> x);
h1(positional m) = h0(m).map(x -> x);
f() = [1, 2].foldl(0, (a, x) -> a + x);
";
    let inf = Resolved::new(src).check();
    assert!(inf.errors.is_empty(), "{:?}", inf.errors);
}

/// Widening a whole scalar carrier inside a list, map, or function across carriers of different
/// name lengths (`int` to `bool` or `String`) settles instead of tripping width growth on
/// `leaf_texts`.
#[test]
fn fold_widening_int_to_bool_or_string_inside_family_or_fn_settles() {
    use zed_tests::step_helpers::l01_26_type_resolution::Resolved;
    for (name, src) in [
        (
            "widen_list_bool",
            "f() = [1, 2, 3].foldl((0, true, [0]), (a, x) -> (a[1], a[0], [a[0]]));\n",
        ),
        (
            "widen_list_str",
            "f() = [1, 2, 3].foldl((0, \"hi\", [0]), (a, x) -> (a[1], a[0], [a[0]]));\n",
        ),
        (
            "widen_map_str",
            "f() = [1, 2, 3].foldl((0, \"hi\", {0 -> 0}), (a, x) -> (a[1], a[0], {0 -> a[0]}));\n",
        ),
        (
            "widen_fn_str",
            "f() = [1, 2, 3].foldl((0, \"hi\", (y: int) -> 0), (a, x) -> (a[1], a[0], (y: int) -> a[0]));\n",
        ),
        (
            "widen_foldr_str",
            "f() = [1, 2, 3].foldr((x, a) -> (a[1], a[0], [a[0]]), (0, \"hi\", [0]));\n",
        ),
    ] {
        let inf = Resolved::new(src).check();
        assert!(inf.errors.is_empty(), "{name}: {:?}", inf.errors);
    }
}

/// Native code generation (`zedc build`) handles function accumulators across `foldl`, `foldr`,
/// nested folds, annotated composition, tuple-held functions, and empty lists.
#[test]
fn a_fold_whose_accumulator_is_a_function_builds_and_runs_natively() {
    use zed_tests::step_helpers::l01_36a_executables::{built, executable};
    let cases = [
        (
            "${[1, 2, 3].foldl(y -> y, (a, x) -> (y -> y + x))(10)}",
            "13",
        ),
        ("${[1, 2].foldl(y -> y, (a, x) -> a)(3)}", "3"),
        (
            "${[1, 2, 3].foldr((x, a) -> (y -> y + x), y -> y)(10)}",
            "11",
        ),
        (
            "${[1, 2, 3].foldl((y: int) -> y, (a, x) -> ((y: int) -> a(y) + x))(10)}",
            "16",
        ),
        (
            "${[1, 2].foldl(y -> y, (a, x) -> [x, x + 1].foldl(a, (b, z) -> (y -> y + z)))(10)}",
            "13",
        ),
        (
            "${[1, 2].foldl((0, y -> y), (a, x) -> (a[0] + x, y -> y + x))[1](10)}",
            "12",
        ),
        ("${[].foldl((y: int) -> y + 1, (a, x) -> a)(10)}", "11"),
    ];
    let lines: Vec<String> = cases
        .iter()
        .map(|(body, _)| format!("\"{body}\""))
        .collect();
    let text = format!(
        "main(m: MainArgs) {{\n    m.stdout <- [{}];\n}}\n",
        lines.join(", ")
    );
    let d = super::dir("l03_02_map_run/native_fn_folds");
    let src = d.join("main.zed");
    let exe = d.join("main");
    std::fs::write(&src, text).unwrap();
    built(&src, &exe);
    let ran = executable(&exe, &[], &[]);
    let expected = cases.iter().map(|(_, e)| *e).collect::<Vec<_>>().join("\n");
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, expected.as_str()),
        "{}",
        ran.stderr
    );
}

/// The delay chain settles where the function is not a lambda whose body is a tuple of
/// projections: a generic receiver, a function parameter, a named function, a block that
/// names the accumulator again, an `if` that may give the accumulator back, payload parts, an
/// `if` inside a part, and a named shift (Opus seat, round 2 of
/// FAIL-fold-rotating-tuple-rounds, E1: 5cbb0fb6c refused each; 22fd64d3a ran the first
/// five). Worked by hand over `[1, 2, 3]`: the delay chain is the one of
/// `a_result_that_reads_the_accumulator_one_level_down_settles`; the payload fold gives
/// `(#ok(0), #ok(1))`, `(#ok(#ok(1)), #ok(2))`, `(#ok(#ok(2)), #ok(3))`; the shift
/// `((a[1],), (x,))` from `(0, 0)` gives `((0,), (1,))`, `(((1,),), (2,))`, `(((2,),), (3,))`.
#[test]
fn a_delay_chain_settles_where_the_function_is_not_a_tuple_of_projections() {
    let step = "(0, (a[0],), (a[1],))";
    let chain = "(0, (0,), ((0,),))";
    for (name, defs, body, expected) in [
        (
            "delay_receiver",
            format!("h(positional xs) = xs.foldl((0, 0, 0), (a, x) -> {step});"),
            "h([1, 2, 3])".to_string(),
            chain,
        ),
        (
            "delay_parameter",
            "h(positional f) = [1, 2, 3].foldl((0, 0, 0), f);".to_string(),
            format!("h((a, x) -> {step})"),
            chain,
        ),
        (
            "delay_named",
            format!("step(positional a, positional x) = {step};"),
            "[1, 2, 3].foldl((0, 0, 0), step)".to_string(),
            chain,
        ),
        (
            "delay_block",
            String::new(),
            "[1, 2, 3].foldl((0, 0, 0), (a, x) -> { b = a; (0, (b[0],), (b[1],)) })".to_string(),
            chain,
        ),
        (
            "delay_if",
            String::new(),
            format!("[1, 2, 3].foldl((0, 0, 0), (a, x) -> if x > 0 {{ {step} }} else {{ a }})"),
            chain,
        ),
        (
            "delay_payload",
            String::new(),
            "[1, 2, 3].foldl((0, 0), (a, x) -> (#ok(a[1]), #ok(x)))".to_string(),
            "(#ok(#ok(2)), #ok(3))",
        ),
        (
            "delay_part_if",
            String::new(),
            "[1, 2, 3].foldl((0, 0, 0), (a, x) -> \
             (0, (a[0],), if x > 0 { (a[1],) } else { (a[1],) }))"
                .to_string(),
            chain,
        ),
        (
            "shift_named",
            "step(positional a, positional x) = ((a[1],), (x,));".to_string(),
            "[1, 2, 3].foldl((0, 0), step)".to_string(),
            "(((2,),), (3,))",
        ),
    ] {
        let src = super::dir(&format!("l03_02_map_run/{name}")).join(format!("{name}.zed"));
        let text = format!("{defs}\nmain(m: MainArgs) {{\n    m.stdout <- \"${{{body}}}\";\n}}\n");
        std::fs::write(&src, &text).unwrap();
        let ran = zed_tests::step_helpers::l01_36a_executables::interpreter(&src, &[], &[]);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {text}\n{}",
            ran.stderr
        );
    }
}

/// A tuple accumulator whose first part is read with `else` and whose second is read plainly
/// settles: the plain read adds no atom from outside, so the second part stays `int` (Opus
/// seat, round 2 of FAIL-fold-rotating-tuple-rounds, E2: refused with "does not take"). Worked
/// by hand from `(0, 0)` over `[1, 2, 3]`: `(1, 1)`, `(3, 2)`, `(6, 3)`.
#[test]
fn a_handled_part_beside_a_plain_part_settles() {
    let body = "${[1, 2, 3].foldl((0, 0), (a, x) -> ((a[0] else 0) + x, a[1] + 1))}";
    let ran = run("handled_beside_plain", body);
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, "(6, 3)"),
        "{}",
        ran.stderr
    );
}

/// A cycle of projections whose weights sum to zero settles: `((a[1],), a[0][0])` moves part 1
/// one level down into part 0 and part 0 one level up into part 1 (Codex seat, round 2 of
/// FAIL-fold-rotating-tuple-rounds). Worked by hand from `((0,), (0,))`: `((0,), 0)`, then
/// `((0,), 0)` again at the value level, with the type `((0,) | ((0,),), ...)` settling.
#[test]
fn a_balanced_projection_cycle_settles() {
    let body = "${[1, 2, 3].foldl(((0,), (0,)), (a, x) -> ((a[1],), a[0][0]))}";
    let ran = run("balanced_cycle", body);
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, "(((0,),), 0)"),
        "{}",
        ran.stderr
    );
}

/// A swap of two lists whose entries print with different lengths settles: the width of a
/// union of literals is not growth (Codex seat, round 2 of FAIL-fold-rotating-tuple-rounds).
#[test]
fn a_swap_of_lists_of_literals_of_different_lengths_settles() {
    let body = "${[1, 2, 3].foldl(([0], [1000]), (a, x) -> (a[1], a[0]))}";
    let ran = run("literal_width_swap", body);
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, "({0 -> 1000}, {0})"),
        "{}",
        ran.stderr
    );
}

/// A fold refused on a map whose keys are not ranks is offered the repair `(a, x) -> a`, which
/// checks, not `a ++ [x]`, which does not (Codex seat, round 2 of
/// FAIL-fold-rotating-tuple-rounds, R2-2).
#[test]
fn a_fold_on_a_map_of_string_keys_gets_a_repair_that_checks() {
    let grows = run(
        "map_grows",
        "${[1, 2].foldl({\"key\" -> 0}, (a, x) -> (a, x))}",
    );
    let identity = run(
        "map_repair",
        "${[1, 2].foldl({\"key\" -> 0}, (a, x) -> a).count}",
    );
    let append = run(
        "map_bad_repair",
        "${[1, 2].foldl({\"key\" -> 0}, (a, x) -> a ++ [x]).count}",
    );
    assert_eq!(
        (identity.status, identity.stdout.trim_end()),
        (0, "1"),
        "{}",
        identity.stderr
    );
    assert!(
        append.stderr.contains("whose keys are not ranks"),
        "{}",
        append.stderr
    );
    assert_eq!(grows.status, 1, "{}", grows.stderr);
    assert!(
        grows.stderr.contains(
            "repair: give the function a result of the start value's type, as `(a, x) -> a`"
        ),
        "{}",
        grows.stderr
    );
}

/// A part that reads one entry of a list the other part fixes settles, though the union of
/// the entries it can hold prints longer than either (Codex seat, round 2 of
/// FAIL-fold-rotating-tuple-rounds, R2-3). Worked by hand: the first part reads `0`, then
/// `1000`; the second is `[1000]` from the first entry on.
#[test]
fn a_part_that_reads_an_entry_of_another_part_settles() {
    for (name, body, expected) in [
        (
            "number_entries",
            "${[1, 2, 3].foldl(([0], [0]), (a, x) -> ([a[1][0]], [1000]))}",
            "({0 -> 1000}, {0 -> 1000})",
        ),
        (
            "string_entries",
            "${[1, 2, 3].foldl(([\"a\"], [\"a\"]), (a, x) -> ([a[1][0]], [\"b\"]))}",
            "({0 -> \"b\"}, {0 -> \"b\"})",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {}",
            ran.stderr
        );
    }
}

/// A fold after generic calls that reserve class ids without filling them (sparse R10
/// classes) checks, and the test confirms that ids were reserved (Codex seat, round 2 of
/// FAIL-fold-rotating-tuple-rounds, R2-4: the fold read every id below the watermark and
/// panicked on an unfilled one).
#[test]
fn a_fold_checks_after_class_ids_are_reserved_without_records() {
    use zed_tests::step_helpers::l01_26_type_resolution::Resolved;
    use zedc::check::probe::last_r10_stats;
    let src = "h0(positional f, positional m) = m.map(f);
h1(positional f, positional m) = h0(f, m).map(f);
h2(positional f, positional m) = h1(f, m).map(f);
h3(positional f, positional m) = h2(f, m).map(f);
folded() = [1, 2].foldl((0, 0), (a, x) -> (a[1], 1.5));
";
    let info = Resolved::new(src).check();
    let stats = last_r10_stats();
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert!(
        stats.admitted > 0 && stats.logical_classes > stats.alloc_classes,
        "{stats:?}"
    );
}

/// A fold whose accumulator is a function, with an entry known only at run time, runs in the
/// interpreter and natively (Codex seat, round 2 of FAIL-fold-rotating-tuple-rounds).
#[test]
fn a_function_accumulator_over_a_run_time_entry_runs_with_both_engines() {
    use zed_tests::step_helpers::l01_36a_executables::{built, executable};
    let (name, body, expected) = (
        "fold_runtime_entry",
        "${[1, 2, m.args.count].foldl(y -> y, (a, x) -> (y -> y + x))(10)}",
        "10",
    );
    let ran = run(name, body);
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, expected),
        "{}",
        ran.stderr
    );
    let exe = super::dir(&format!("l03_02_map_run/{name}")).join("native");
    built(&super::program(name, body), &exe);
    let ran = executable(&exe, &[], b"");
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, expected),
        "{}",
        ran.stderr
    );
}

/// A fold that composes functions runs when the parameters are written `int`: the control for
/// the refused unwritten form, whose acceptance is plan row L6.11 (Codex seat, round 2 of
/// FAIL-fold-rotating-tuple-rounds). Worked by hand: `y -> y`, then `y -> y + 1`, `y -> y + 1
/// + 2`, `y -> y + 1 + 2 + 3`, applied to `10`: `16`.
#[test]
fn a_composing_fold_with_written_parameter_types_runs() {
    let body = "${[1, 2, 3].foldl((y: int) -> y, (a, x) -> ((y: int) -> a(y) + x))(10)}";
    let ran = run("written_composition", body);
    assert_eq!(
        (ran.status, ran.stdout.trim_end()),
        (0, "16"),
        "{}",
        ran.stderr
    );
}

/// A propagated read `a[0]?.abs` and an `else` on a family whose keys are known only at run
/// time check and run in a fold (Codex seat, round 2 of FAIL-fold-rotating-tuple-rounds).
#[test]
fn propagated_and_else_reads_of_the_accumulator_check() {
    for (name, body) in [
        (
            "propagated_read",
            "${[1, 2, 3].foldl([0], (a, x) -> [(a[0]?.abs) + 1])}",
        ),
        (
            "partial_else",
            "${[1, 2, 3].foldl(m.args.map(y -> 0), (a, x) -> [(a[0] else 0) + 1])}",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, "{0 -> 3}"),
            "{name}: {}",
            ran.stderr
        );
    }
}
