//! Placing diagnostics at the rule of low complexity (DESIGN.md Part G). Each diagnostic and
//! each of its steps was placed by decoding the file from its first byte, so a file of `n`
//! lines with an error on each took `O(n²)`.
//!
//! Each input below has a check of what its message says at any size, run here at small sizes
//! that reach every branch of the input, and by `bench::scaling` at `n` and `8n`
//! (TEST-bench-move-l0125, author P169, P170).

use super::rejected;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// `n` definitions, each reading a name nothing declares.
pub(super) fn unresolved(n: usize) -> String {
    (0..n).map(|i| format!("h{i} = missing{i};\n")).collect()
}

/// One diagnostic per line, the last at the last line, after `h{n-1} = `.
pub(super) fn a_diagnostic_on_every_line(src: &str, n: usize) {
    let out = rejected(src);
    let last = n - 1;
    let col = format!("h{last} = ").len() + 1;
    assert_eq!(out.lines().count(), n);
    let want = format!(
        "{n}:{col}: {}",
        zed_tests::undefined(&format!("missing{last}"))
    );
    assert_eq!(out.lines().last(), Some(want.as_str()));
}

#[test]
fn a_diagnostic_is_placed_on_every_line() {
    for n in [1, 3, 12] {
        a_diagnostic_on_every_line(&unresolved(n), n);
    }
}

/// A chain of `n` bindings, each reading the one before twice, ending in an error.
pub(super) fn doubled(n: usize) -> String {
    let mut src = String::from("main(m: MainArgs) {\n  a0 = 1;\n");
    for i in 1..n {
        src += &format!("  a{i} = a{p} + a{p};\n", p = i - 1);
    }
    src + &format!("  m.stdout <- \"x\" ++ a{};\n}}\n", n - 1)
}

pub(super) fn derived_through_values_read_twice(src: &str) {
    let out = rejected(src);
    assert!(
        out.contains("`a0` is defined as this expression, 1"),
        "{out}"
    );
}

#[test]
fn deriving_through_values_read_twice() {
    for n in [1, 2, 6] {
        derived_through_values_read_twice(&doubled(n));
    }
}

/// A function adding `n` untyped parameters and testing the sum as a condition: one class
/// with `n` reasons, shown in one diagnostic. Each parameter and each addition has a line of
/// its own, since each step of a diagnostic shows the whole line it is on.
pub(super) fn summed_condition(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    format!(
        "f({}) = if {} {{ 1 }} else {{ 2 }};\n",
        ps.join(",\n"),
        xs.join("\n+ ")
    )
}

/// One reason per merge of the class, `n - 1` for `n` parameters.
pub(super) fn the_reasons_of_a_class_merged(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(out.matches("gives these values one carrier").count(), n - 1);
}

#[test]
fn the_reasons_of_a_class_narrowed_many_times() {
    // Each reason was looked for among those shown before it (COMPLEXITY.md F29).
    let out = rejected(&summed_condition(3));
    assert!(out.contains("not bool"), "{out}");
    assert_eq!(
        out.matches("gives these values one carrier").count(),
        2,
        "{out}"
    );
    for n in [2, 3, 9] {
        the_reasons_of_a_class_merged(&summed_condition(n), n);
    }
}

/// `h` passes `g` a pair of `n` parts, each written twice: `((#a0 | #b0, #a0 | #b0), …)`.
pub(super) fn shared_parts(n: usize) -> String {
    let pairs: Vec<String> = (0..n)
        .map(|i| format!("(#a{i} | #b{i}, #a{i} | #b{i})"))
        .collect();
    format!(
        "g(x: int) = x;\nh(y: ({})) = g(x: y);\nmain() = 0;\n",
        pairs.join(", ")
    )
}

/// One message names its `n` definitions in one numbering and writes each once, on its own
/// line (step MSG-type-defs-layout).
pub(super) fn a_message_with_definitions(src: &str, n: usize) {
    let out = rejected(src);
    let last = format!("    type Part{n} = #a{m} | #b{m};\n", m = n - 1);
    assert!(out.contains(&last), "{out}");
    assert_eq!(out.matches("    type Part").count(), n);
}

#[test]
fn a_message_with_many_definitions() {
    for n in [1, 2, 7] {
        a_message_with_definitions(&shared_parts(n), n);
    }
}

/// `n` names, each defined as a `/` of literals that meets no carrier and read once by a `*`
/// that does not take it: `2n` rejections, each read stepping through its name with one lookup
/// of the name's definition (`Ck::defined_open`).
pub(super) fn read_divisions(n: usize) -> String {
    (0..n)
        .map(|i| format!("q{i} = 1 / 2;\nz{i} = q{i} * \"a\";\n"))
        .collect()
}

pub(super) fn derived_reads_of_divisions_of_literals(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(
        out.matches("is read here; it is defined as an operation on literals alone")
            .count(),
        n,
        "{out}"
    );
}

#[test]
fn deriving_reads_of_many_divisions_of_literals() {
    for n in [1, 3, 8] {
        derived_reads_of_divisions_of_literals(&read_divisions(n), n);
    }
}

/// A chain of `n` names from `-0r` to a divisor, with `0r` written first: one message whose
/// derivation steps through every name, each step finding the literal at the chain's end
/// (item MSG-neg-zero-chain).
pub(super) fn zero_chain(n: usize) -> String {
    let mut src = String::from("a = 0r;\nz0 = -0r;\n");
    for i in 1..n {
        src += &format!("z{i} = z{};\n", i - 1);
    }
    src + &format!("f(x: rat) = x / z{};\n", n - 1)
}

/// Each step of the derivation follows the chain to its literal; a walk from each step to the
/// end, with no memo shared by the steps, is O(n²) (COMPLEXITY.md F165).
pub(super) fn a_chain_of_names_to_a_negated_zero(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(out.matches(" is -0r here").count(), n);
    assert_eq!(out.matches("defined as this expression, -0r").count(), n);
    assert!(!out.contains(" 0r here"));
}

#[test]
fn a_chain_of_names_to_a_negated_zero_prints_every_step() {
    for n in [1, 2, 9] {
        a_chain_of_names_to_a_negated_zero(&zero_chain(n), n);
    }
}

/// `n` rejections whose fixes are each checked as written (MSG-converted-claims-checked): the
/// menu fixes `1.0 + gr(true)` and `1.0r + gr(true)`, dropped, the message naming `true`; a
/// comparison cast, `int(r)`, dropped; a cast beside
/// a decimal literal, `f64(k)`, dropped. Each costs a few checks of its own construct, so the
/// whole is linear in `n`.
pub(super) fn checked_fixes(n: usize) -> String {
    let mut src = String::from(
        "gr(positional c: bool) = if c { 1r } else { true };\nn = 1;\nr = 2.5r;\n\
         k = 1152921504606846977;\n",
    );
    for i in 0..n {
        src += &format!("a{i} = 1.0f64 + gr(true);\nb{i} = n == r;\nc{i} = k == 0.5;\n");
    }
    src
}

pub(super) fn each_offered_fix_checked_as_written(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(
        out.matches("does not take (1.0f64, true)").count(),
        n,
        "{out}"
    );
    assert!(!out.contains("gr(true);    "), "{out}");
    assert!(!out.contains("int(r)"), "{out}");
    assert!(!out.contains("f64(k)"), "{out}");
}

#[test]
fn checking_each_offered_fix_as_written() {
    for n in [1, 3] {
        each_offered_fix_checked_as_written(&checked_fixes(n), n);
    }
}

/// A tuple of `n` `rat` components compared with a `rat`: each component is offered,
/// `t[i] == 1r`, and each is checked as written, the comparison checked again with the
/// component in place of the tuple, which is not copied for it.
pub(super) fn tuple_compared(n: usize) -> String {
    let xs = vec!["1r"; n];
    format!("t = ({});\ny = t == 1r;\n", xs.join(", "))
}

pub(super) fn the_components_offered_for_a_tuple(src: &str, n: usize) {
    let out = rejected(src);
    let last = format!("t[{}] == 1r", n - 1);
    assert!(out.contains(&last), "{out}");
}

#[test]
fn checking_the_components_offered_for_a_wide_tuple() {
    for n in [2, 3, 10] {
        the_components_offered_for_a_tuple(&tuple_compared(n), n);
    }
}

/// A function of `n` parameters of carrier `c` called with `n` literals `1.0f64`
/// (MSG-many-arguments-output): one message for the call, whose steps name each literal once.
/// At `rat` its one fix writes the call once, `y = f(1.0, …)`; at `int` there is no fix, as
/// no literal `1.0f64` takes an `int` (DESIGN row "Two numeric values with no common
/// carrier"). Each literal its own message, each with its fix checked by checking the call
/// again with the other literals refused again, cost O(n³) and wrote the call n times, Θ(n²)
/// bytes.
pub(super) fn many_literal_arguments(n: usize, c: &str) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional p{i}: {c}")).collect();
    let xs = vec!["1.0f64"; n];
    format!("f({}) = 1;\ny = f({});\n", ps.join(", "), xs.join(", "))
}

/// The message of [`many_literal_arguments`] at the carrier `c`, whose fixed call writes each
/// literal as `fixed`, or that has no fixed call.
pub(super) fn literal_arguments_refused(src: &str, n: usize, c: &str, fixed: Option<&str>) {
    let out = rejected(src);
    let head = format!("{n} arguments of `f` are literals at carriers they cannot take.");
    assert!(out.contains(&head), "{out}");
    assert_eq!(out.matches(&format!("never `{c}`")).count(), n);
    if let Some(x) = fixed {
        let fixed = format!("y = f({});", vec![x; n].join(", "));
        assert_eq!(out.matches(fixed.as_str()).count(), 1);
    } else {
        assert!(!out.contains("Try"), "{out}");
    }
    let call = format!("y = f({});", vec!["1.0f64"; n].join(", "));
    assert_eq!(out.matches(call.as_str()).count(), 1);
}

#[test]
fn many_literal_arguments_refused_at_their_parameters() {
    for n in [2, 5] {
        literal_arguments_refused(&many_literal_arguments(n, "rat"), n, "rat", Some("1.0"));
    }
}

#[test]
fn many_literal_arguments_refused_at_int_parameters() {
    for n in [2, 5] {
        literal_arguments_refused(&many_literal_arguments(n, "int"), n, "int", None);
    }
}

/// A call of `n` arguments `k * 0.5` at `rat` parameters, one per line, `k` an `int`
/// (MSG-many-args-repair-loop): each argument is its own error, whose fix `rat(k) * 0.5` gives
/// its argument the type `rat` and is carried to the call, which checks them. One check of
/// the call per carried fix, each copying the other arguments, cost O(n²) (31 times the
/// instructions at 8 times the arguments); the fixes of one round are now checked by one
/// check of a call of one parameter each and one check of the whole call. One argument per
/// line, so that each message quotes a line of its own and the output is linear in `n`.
pub(super) fn carried_fixes(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional p{i}: rat")).collect();
    let xs = vec!["  k * 0.5"; n];
    format!(
        "k = 1;\nf({}) = 1;\ny = f(\n{});\n",
        ps.join(", "),
        xs.join(",\n")
    )
}

pub(super) fn the_carried_fixes_of_the_arguments(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(
        out.matches("A decimal literal is never an `int`: `k : int * 0.5`.")
            .count(),
        n,
        "{out}"
    );
    // The headline's repair ends at the argument, without the `)` that closes the call on
    // the last argument's line (MSG-try-closing-paren) or the `,` after the others.
    assert_eq!(
        out.matches("Try `rat(k) * 0.5` instead.").count(),
        n,
        "{out}"
    );
    // The signature of `f`, n parameters long, is given in the first error only, and each
    // later one points to it (MSG-call-signature-per-message): it was in every error, n² bytes.
    assert_eq!(
        out.matches("the type the checker found for `f` is `")
            .count(),
        1,
        "{out}"
    );
    assert_eq!(
        out.matches("the error above gives the type the checker found for `f`")
            .count(),
        n - 1,
        "{out}"
    );
}

#[test]
fn the_carried_fixes_of_many_arguments() {
    for n in [1, 2, 6] {
        the_carried_fixes_of_the_arguments(&carried_fixes(n), n);
    }
}

/// The listing of the errors of [`carried_fixes`] grows linearly in the arguments: at 8 times
/// the arguments, less than 9 times the bytes (MSG-call-signature-per-message). Measured: 8.08
/// times from 16 to 128 arguments (13972 and 112875 bytes); with the type of `f` in every
/// error, 12.7 times (15547 and 197330 bytes), and growing with n.
#[test]
fn the_carried_fixes_of_many_arguments_print_linear_output() {
    let bytes = |n: usize| rejected(&carried_fixes(n)).len();
    let (small, large) = (bytes(16), bytes(128));
    assert!(
        large * 10 < small * 90,
        "{small} bytes at 16 arguments, {large} at 128"
    );
}

/// A call of `n` decimal literals at parameters with no type, `f(1.5, …)`
/// (MSG-many-args-decimal): nothing gives the literals a carrier, so each is the `f64` it
/// writes (DESIGN.md step L1.26b, author decision 2026-11-12) and the call checks. They were
/// one message that wrote the call once per fix, `f(1.5f64, …)` and `f(1.5r, …)`.
pub(super) fn unfixed_decimal_arguments(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional p{i}")).collect();
    format!(
        "f({}) = 1;\ny = f({});\n",
        ps.join(", "),
        vec!["1.5"; n].join(", ")
    )
}

/// The program of [`unfixed_decimal_arguments`] checks, and `y` is `1`.
pub(super) fn unfixed_decimal_arguments_checked(src: &str) {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    assert_eq!(value(src, "y"), "1", "{src}");
}

#[test]
fn many_unfixed_decimal_arguments() {
    for n in [2, 5] {
        unfixed_decimal_arguments_checked(&unfixed_decimal_arguments(n));
    }
}

/// [`unfixed_decimal_arguments`] with each literal `1e400`, past the range of `f64`, so that
/// none takes `f64` and the call keeps the one message for all of them, whose fix is `rat`.
pub(super) fn past_f64_arguments(n: usize) -> String {
    unfixed_decimal_arguments(n).replace("1.5", "1e400")
}

/// The program of [`past_f64_arguments`] gives one message naming its `n` literals, whose one
/// fix writes each as a `rat`.
pub(super) fn past_f64_arguments_rejected(src: &str, n: usize) {
    let errors = type_errors(src);
    let [e] = &errors[..] else {
        panic!("{src}: {errors:?}")
    };
    let head =
        format!("{n} parts of the arguments of `f` are literals that nothing here gives a carrier");
    assert!(e.starts_with(&head), "{e}");
    let fix = format!("y = f({});", vec!["1e400r"; n].join(", "));
    assert!(
        e.contains(&format!("Try `{}` instead.", &fix[..fix.len() - 1])),
        "{e}"
    );
    assert!(e.contains(&format!("\n    {fix}")), "{e}");
}

#[test]
fn many_decimal_arguments_past_f64() {
    for n in [2, 5] {
        past_f64_arguments_rejected(&past_f64_arguments(n), n);
    }
}

/// [`unfixed_decimal_arguments`] with each argument the division `1 / 2`, which nothing gives
/// a carrier: the call is rejected once for all of them (row MSG-call-division-args-grouping),
/// as [`past_f64_arguments`] is, and not once per `/`.
pub(super) fn division_arguments(n: usize) -> String {
    unfixed_decimal_arguments(n).replace("1.5", "1 / 2")
}

/// The program of [`division_arguments`] gives one message naming its `n` divisions, with
/// the step that `f` has no type written, once, and the fixes writing every one at `rat` and
/// at `f64`.
pub(super) fn division_arguments_rejected(src: &str, n: usize) {
    let errors = type_errors(src);
    let [e] = &errors[..] else {
        panic!("{src}: {errors:?}")
    };
    let head =
        format!("{n} parts of the arguments of `f` are literals that nothing here gives a carrier");
    assert!(e.starts_with(&head), "{e}");
    let out = rejected(src);
    let step = ": Nothing gives the literal `1` a carrier\n";
    assert_eq!(out.matches(step).count(), n, "{out}");
    assert_eq!(out.matches("`f` is declared here").count(), 1, "{out}");
    for lit in ["1r", "1.0f64"] {
        let fix = format!("y = f({});", vec![format!("{lit} / 2"); n].join(", "));
        assert!(e.contains(&format!("\n    {fix}")), "{e}");
    }
}

#[test]
fn many_division_arguments() {
    for n in [2, 5] {
        division_arguments_rejected(&division_arguments(n), n);
    }
}

/// One division among other arguments, or beside a literal past `f64`, is rejected as before:
/// only two or more divisions of one call are grouped.
#[test]
fn one_division_argument_is_rejected_alone() {
    for (args, n) in [("1 / 2, 1", 1), ("1 / 2, 1e400", 2)] {
        let src = format!("f(positional p0, positional p1) = 1;\ny = f({args});\n");
        let errors = type_errors(&src);
        assert_eq!(errors.len(), n, "{src}: {errors:?}");
        assert!(
            errors[0].starts_with("Nothing gives the literal `1` a carrier. Try `y = f(1r / 2"),
            "{errors:?}"
        );
    }
}

/// A default that reads another parameter (PROOF-params-own-apart-fresh). `p2 = p0` puts
/// `p0`'s variable into `p2`'s type, `(T, _, p2: T) -> 1`, so the call is not checked a
/// parameter at a time; `p2 = p0 == p1` needs nothing of their types, `(_, _, p2: bool) ->
/// 1`, so it is. Either way the two divisions are one error whose fixes each check as
/// written, also with `p2` given: an `f64` for `p2 = p0`, which `T` takes beside the `rat`
/// of `p0`, since nothing bounds it.
#[test]
fn division_arguments_with_a_default_reading_another_parameter() {
    for (default, sig, given) in [
        ("p0", "(T, _, p2: T) -> 1", ", p2: 1.5f64"),
        ("p0 == p1", "(_, _, p2: bool) -> 1", ", p2: true"),
    ] {
        for p2 in ["", given] {
            let decl = format!("f(positional p0, positional p1, p2 = {default}) = 1;\n");
            let src = format!("{decl}y = f(1 / 2, 1 / 2{p2});\n");
            let errors = type_errors(&src);
            let [e] = &errors[..] else {
                panic!("{src}: {errors:?}")
            };
            let head =
                "2 parts of the arguments of `f` are literals that nothing here gives a carrier";
            assert!(e.starts_with(head), "{src}\n{e}");
            let out = rejected(&src);
            assert!(out.contains(&format!("is `{sig}`")), "{src}\n{out}");
            for lit in ["1r", "1.0f64"] {
                let fix = format!("y = f({lit} / 2, {lit} / 2{p2});");
                assert!(e.contains(&format!("\n    {fix}")), "{src}\n{e}");
                let fixed = format!("{decl}{fix}\n");
                assert_eq!(type_errors(&fixed), Vec::<String>::new(), "{fixed}");
                assert_eq!(value(&fixed, "y"), "1", "{fixed}");
            }
        }
    }
}

/// Two division arguments of parameters that share one variable, `(T, T) -> bool`
/// (MSG-shared-bound-var-rat-fix-dropped). Carrying `rat` into one argument alone leaves the
/// other at the carrier the program gives it as written, `f64`, which `T` does not take beside
/// `rat`, so the `rat` fix was dropped and only `f64` was offered; the fix's type is lent to the
/// other arguments that hold only such literals, and each fix whose program checks is offered,
/// `rat` first, and each runs. Also with three such arguments, and with one argument fixed by
/// the program, where one division alone is rejected.
#[test]
fn division_arguments_of_parameters_of_one_variable_offer_each_carrier() {
    for (decl, args, want) in [
        (
            "f(positional p0, positional p1) = p0 < p1;\n",
            ["{lit} / 2", "{lit} / 2"].join(", "),
            "false",
        ),
        (
            "f(positional p0, positional p1, positional p2) = p0 < p1 + p2;\n",
            ["{lit} / 2", "{lit} / 2", "{lit} / 4"].join(", "),
            "true",
        ),
    ] {
        let src = format!("{decl}y = f({});\n", args.replace("{lit}", "1"));
        let errors = type_errors(&src);
        let [e] = &errors[..] else {
            panic!("{src}: {errors:?}")
        };
        let rat = format!("y = f({});", args.replace("{lit}", "1r"));
        let f64 = format!("y = f({});", args.replace("{lit}", "1.0f64"));
        let head = format!("Try `{}` instead.", rat.trim_end_matches(';'));
        assert!(e.contains(&head), "{src}\n{e}");
        let (Some(r), Some(d)) = (
            e.find(&format!("\n    {rat}")),
            e.find(&format!("\n    {f64}")),
        ) else {
            panic!("{src}\n{e}")
        };
        assert!(r < d, "{src}\n{e}");
        for fix in [rat, f64] {
            let fixed = format!("{decl}{fix}\n");
            assert_eq!(type_errors(&fixed), Vec::<String>::new(), "{fixed}");
            assert_eq!(value(&fixed, "y"), want, "{fixed}");
        }
    }
    let decl = "f(positional p0, positional p1) = p0 < p1;\n";
    let src = format!("{decl}y = f(1r / 2, 1 / 2);\n");
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    assert_eq!(value(&src, "y"), "false", "{src}");
}

/// The defaults of `p2` in `a_cast_argument_beside_a_division_of_one_variable_offers_each_carrier`
/// and `the_fix_of_an_argument_the_result_does_not_hold_is_kept`: none, and one that reads
/// `p0` directly, through one call and through two, each with the expression the body reads
/// in place of `p0`.
const P0_DEFAULTS: [(&str, &str); 4] = [
    ("", "p0"),
    (", p2 = p0", "p2"),
    (", p2 = id(v: p0)", "p2"),
    (", p2 = id2(v: p0)", "p2"),
];

/// A division beside a cast argument of parameters that share one variable,
/// `f(1 / 2, k * 0.5)` for `(T, T) -> bool` (TEST-params-own-apart-red), also where `p2`'s
/// default reads `p0`. Carrying `rat(k)` into the second argument alone leaves the first at
/// `f64`, which `T` does not take beside `rat`, so `rat(k)` was dropped and only `f64(k)` was
/// offered; the program with `rat(k)` written checks, its `1 / 2` taking `rat` through `T`,
/// and runs. Both fixes are offered, `rat(k)` first, and each runs to `true`.
#[test]
fn a_cast_argument_beside_a_division_of_one_variable_offers_each_carrier() {
    for (default, p0) in P0_DEFAULTS {
        let decl = format!(
            "id(v) = v;\nid2(v) = id(v: v);\nf(positional p0, positional p1{default}) = {p0} < \
             p1;\nk = 3;\n"
        );
        let src = format!("{decl}y = f(1 / 2, k * 0.5);\n");
        let errors = type_errors(&src);
        let [_, e] = &errors[..] else {
            panic!("{src}: {errors:?}")
        };
        let rat = "y = f(1 / 2, rat(k) * 0.5);";
        let f64 = "y = f(1 / 2, f64(k) * 0.5);";
        let head = format!("Try `{}` instead.", rat.trim_end_matches(';'));
        assert!(e.contains(&head), "{src}\n{e}");
        let (Some(r), Some(d)) = (
            e.find(&format!("\n    {rat}")),
            e.find(&format!("\n    {f64}")),
        ) else {
            panic!("{src}\n{e}")
        };
        assert!(r < d, "{src}\n{e}");
        for fix in [rat, f64] {
            let fixed = format!("{decl}{fix}\n");
            assert_eq!(type_errors(&fixed), Vec::<String>::new(), "{fixed}");
            assert_eq!(value(&fixed, "y"), "true", "{fixed}");
        }
    }
}

/// A call of `f(positional p0, …, positional p{n-1}) = p0 < p1` with `1 / 2` first, the cast
/// argument `k * 0.5` second and `1` at each other parameter, `n >= 3`.
pub(super) fn cast_beside_a_division(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("positional p{i}")).collect();
    let args = vec!["1"; n - 2].join(", ");
    format!(
        "f({}) = p0 < p1;\nk = 3;\ny = f(1 / 2, k * 0.5, {args});\n",
        params.join(", ")
    )
}

/// The program of [`cast_beside_a_division`] offers `rat(k)` and `f64(k)` for its cast,
/// `rat(k)` first: the `rat` that `rat(k)` gives `p1` is lent to the division, and the other
/// `n - 2` arguments are passed over (TEST-params-own-apart-red).
pub(super) fn cast_beside_a_division_offered(src: &str, n: usize) {
    let errors = type_errors(src);
    let [_, e] = &errors[..] else {
        panic!("{src}: {errors:?}")
    };
    let rest = vec!["1"; n - 2].join(", ");
    let (Some(r), Some(d)) = (
        e.find(&format!("\n    y = f(1 / 2, rat(k) * 0.5, {rest});")),
        e.find(&format!("\n    y = f(1 / 2, f64(k) * 0.5, {rest});")),
    ) else {
        panic!("{e}")
    };
    assert!(r < d, "{e}");
}

#[test]
fn a_cast_beside_a_division_of_one_variable_among_many_arguments_offers_each_carrier() {
    for n in [3, 6] {
        cast_beside_a_division_offered(&cast_beside_a_division(n), n);
    }
}

/// The fixes of an argument that the result does not hold, beside one that it does:
/// `x = f(k * 0.5, k * 0.25)` for `(T, _) -> T`, also where `p2`'s default reads `p0`,
/// `(T, _, p2: T) -> T`, with `x < 1r` after. `p0`'s fix decides `x`'s type, so `f64(k)` there
/// is refused by `x < 1r` and only `rat(k)` is offered; `p1`'s fix changes neither the result
/// nor what `p0` meets, so both of its fixes are offered, and each runs beside `p0`'s. Checking
/// the call a parameter at a time, as `params_own_apart` (crates/zedc-check/src/check/walk.rs)
/// allows only where the result holds no variable, joins a fix of `p1` with one of `p0` into
/// one type for the call, and drops it with `p0`'s where `x < 1r` refuses that type: forcing
/// `params_own_apart` to true drops one of `p1`'s fixes here (TEST-params-own-apart-red).
#[test]
fn the_fix_of_an_argument_the_result_does_not_hold_is_kept() {
    for (default, p0) in P0_DEFAULTS {
        let decl = format!(
            "id(v) = v;\nid2(v) = id(v: v);\nf(positional p0, positional p1{default}) = {p0};\nk \
             = 3;\n"
        );
        let src = format!("{decl}x = f(k * 0.5, k * 0.25);\ny = x < 1r;\n");
        let errors = type_errors(&src);
        let [first, second] = &errors[..] else {
            panic!("{src}: {errors:?}")
        };
        assert!(
            first.contains("\n    x = f(rat(k) * 0.5, k * 0.25);"),
            "{src}\n{first}"
        );
        assert!(!first.contains("f64(k)"), "{src}\n{first}");
        for cast in ["rat", "f64"] {
            let fix = format!("x = f(k * 0.5, {cast}(k) * 0.25);");
            assert!(second.contains(&format!("\n    {fix}")), "{src}\n{second}");
            let fixed = format!("{decl}x = f(rat(k) * 0.5, {cast}(k) * 0.25);\ny = x < 1r;\n");
            assert_eq!(type_errors(&fixed), Vec::<String>::new(), "{fixed}");
            assert_eq!(value(&fixed, "y"), "false", "{fixed}");
        }
    }
}

/// [`super::rare`]'s value that flows into `g` through a chain of `n` defaults, `k(h0 = g,
/// h1 = h0, ...)`, which passes `x -> "s"` as the last; then `n` more parameters whose
/// defaults read the two ends of the chain in turn, `m0 = h0, m1 = h{n-1}, m2 = h0, ...`, so
/// that each of their merges names a class at the far end of the chain from the last one.
pub(super) fn defaults_chain(n: usize) -> String {
    let last = n - 1;
    let params: Vec<String> = std::iter::once("h0 = g".to_string())
        .chain((1..n).map(|i| format!("h{i} = h{}", i - 1)))
        .chain((0..n).map(|j| format!("m{j} = h{}", if j % 2 == 0 { 0 } else { last })))
        .collect();
    format!(
        "f(positional g) {{\n  a = g(1) + 1;\n  k({}) = h{last}(2);\n  b = k(h{last}: x -> \"s\");\n  \
         return a;\n}}\n",
        params.join(", ")
    )
}

/// Each default merges a parameter with the one it reads; the derivation walks the merges
/// from the lambda's class to `g`'s, one note per default of the chain (MSG-flow-origin;
/// COMPLEXITY.md F195). A merge reroots the smaller of the two trees of merges: rerooting the
/// tree of the chain at `h0` and at `h{n-1}` in turn would cost n at each `m`.
pub(super) fn the_merges_between_a_value_and_its_use(src: &str, n: usize) {
    let out = rejected(src);
    let defaults = out
        .lines()
        .filter(|l| l.contains(": the default `h"))
        .count();
    assert_eq!(defaults, n, "{out}");
}

#[test]
fn the_merges_between_a_value_and_its_use_are_each_noted() {
    for n in [2, 3, 8] {
        the_merges_between_a_value_and_its_use(&defaults_chain(n), n);
    }
}

/// A call of one line whose first argument is a text of `n` letters and whose second is an
/// `int` at a `rat` parameter, `y = h("aa…a", k)` (row MSG-apply-try-headline): its headline
/// ends with the call rewritten, `h("aa…a", rat(k))`. The repairs' notes are copied once
/// beside the notes, O(r), and only the first repair is written, once, in the length of the
/// call, O(n), when the check ends; writing each repair's call as it is found would cost
/// O(n) per repair. A call of `n` arguments is no test of this: its message has a step per
/// argument, and placing those steps costs O(n²) before this row (4.5 s at 400 arguments,
/// 20 s at 800).
pub(super) fn one_repair_in_a_long_call(n: usize) -> String {
    let text = "a".repeat(n);
    format!("k = 1;\nh(positional a: String, positional b: rat) = 1;\ny = h(\"{text}\", k);\n")
}

pub(super) fn the_headline_repair_of_a_call(src: &str, n: usize) {
    let out = rejected(src);
    let want = format!("Try `h(\"{}\", rat(k))` instead.", "a".repeat(n));
    let head = out.lines().next().unwrap_or_default();
    assert!(head.ends_with(&want), "{}", &out[..out.len().min(400)]);
}

#[test]
fn the_headline_repair_of_a_long_call() {
    for n in [0, 1, 50] {
        the_headline_repair_of_a_call(&one_repair_in_a_long_call(n), n);
    }
}

/// A call of `n` arguments that its `rat` parameters take, `2r` literals and, in the second
/// half, a name `x` of type `rat`, and one more, the `int` `k`, that it refuses, `y = h(2r,
/// …, x, …, k)`, its arguments on one line or one per line (row MSG-many-args-steps-square).
/// Only `k` is offered a repair. Before the row, each argument the call takes was tried in its
/// other forms, `2` and `2.0` for `2r`, `String(x)` and `f64(x)` for `x`, each trial a
/// check of the whole call: O(n²), 17.7 s at 800 arguments.
pub(super) fn taken_beside_one_refused(n: usize, sep: &str) -> String {
    let params: Vec<String> = (0..=n).map(|i| format!("positional a{i}: rat")).collect();
    let args = (0..n).map(|i| if i < n / 2 { "2r" } else { "x" });
    let args: Vec<&str> = args.chain(["k"]).collect();
    format!(
        "k = 1;\nx = 1r;\nh({}) = 1;\ny = h({});\n",
        params.join(", "),
        args.join(sep)
    )
}

pub(super) fn only_the_refused_argument_repaired(src: &str) {
    let out = rejected(src);
    assert_eq!(out.matches("repair: ").count(), 1, "{out}");
    assert!(
        out.contains("repair: write `rat(k)`; the checker accepts that"),
        "{out}"
    );
}

#[test]
fn a_long_call_taking_all_but_one_argument_repairs_that_one() {
    for n in [1, 2, 9] {
        for sep in [", ", ",\n  "] {
            only_the_refused_argument_repaired(&taken_beside_one_refused(n, sep));
        }
    }
}

/// A call `g(x)` of a function that takes only a `String`, with `x` a union of tuples of every
/// length from 1 to k, `(int) | (int, int) | …`, about `n` components in all (row
/// MSG-headline-l01_26). `String(x)` checks, so before it is offered the call is tried with
/// each tuple length alone, to see whether it takes some value that `String` would change;
/// it takes none, so all k = O(√n) are tried and the headline ends with `g(String(x))`. A
/// trial costs about the same at both sizes, as types are shared, so the trials add O(√n) to
/// the O(n) check. Negative control, run once: a trial that also writes out the whole type,
/// O(n) each, O(n^1.5) in all, failed at 21.7 times the bytes.
pub(super) fn a_call_of_many_tuple_lengths(n: usize) -> String {
    let k = (1..).find(|k| k * (k + 1) / 2 >= n).unwrap_or(1);
    let shapes: Vec<String> = (1..=k)
        .map(|len| format!("({})", vec!["int"; len].join(", ")))
        .collect();
    format!(
        "g(positional s: String) = 1;\nf(x: {}) = g(x);\n",
        shapes.join(" | ")
    )
}

pub(super) fn a_text_repair_of_shapes(src: &str) {
    let out = rejected(src);
    let head = out.lines().next().unwrap_or_default();
    assert!(head.ends_with("Try `g(String(x))` instead."), "{head}");
}

#[test]
fn a_text_repair_of_many_shapes() {
    // One tuple length, then two, then seven.
    for n in [1, 3, 28] {
        a_text_repair_of_shapes(&a_call_of_many_tuple_lengths(n));
    }
}

/// `n` functions, each multiplying an `int` by a text the cast `int` takes, so each rejection
/// offers the literal the cast gives (row REPAIR-literal-cast).
pub(super) fn texts_for_ints(n: usize) -> String {
    (0..n)
        .map(|i| format!("h{i}(positional x: int) = x * \"{i}\";\n"))
        .collect()
}

pub(super) fn the_literal_a_cast_gives(src: &str, n: usize) {
    let out = rejected(src);
    let last = n - 1;
    assert!(out.contains(&format!("Try `x * {last}` instead.")), "{out}");
}

#[test]
fn writing_the_literal_a_cast_gives() {
    for n in [1, 3, 12] {
        the_literal_a_cast_gives(&texts_for_ints(n), n);
    }
}

/// One text of `d` digits multiplied with an `int`.
pub(super) fn a_long_text_multiplied(d: usize) -> String {
    format!("f(positional x: int) = x * \"{}\";\n", "7".repeat(d))
}

/// One text of d digits: its cast, its printing and its reading back.
pub(super) fn the_literal_of_a_long_text(src: &str, d: usize) {
    let out = rejected(src);
    assert!(
        out.contains(&format!("Try `x * {}` instead.", "7".repeat(d))),
        "{out}"
    );
}

#[test]
fn writing_the_literal_of_a_long_text() {
    // 30 digits pass the 64 and 128 bits of a machine word.
    for d in [1, 30] {
        the_literal_of_a_long_text(&a_long_text_multiplied(d), d);
    }
}

/// `n` functions, each comparing an `int` by `==` or `<` with a text the cast `int` takes, the
/// text on either side, so each rejection offers first the literal the cast gives (row
/// REPAIR-compare-order): at `==` up to three more trials of the comparison, one per number
/// type, each after one cast of the one literal.
pub(super) fn texts_compared(n: usize) -> String {
    (0..n)
        .map(|i| match i % 4 {
            0 => format!("h{i}(positional x: int) = x == \"{i}\";\n"),
            1 => format!("h{i}(positional x: int) = \"{i}\" != x;\n"),
            2 => format!("h{i}(positional x: int) = x < \"{i}\";\n"),
            _ => format!("h{i}(positional x: int) = \"{i}\" >= x;\n"),
        })
        .collect()
}

/// [`texts_compared`] at `n`, a multiple of 4, so that the last comparison is `>=`.
pub(super) fn the_literal_offered_first_in_comparisons(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(out.matches("Try `x == ").count(), n.div_ceil(4), "{out}");
    // Each text reads as a number, so no ordering offers to compare texts, `String(x)`
    // (row REPAIR-string-compare-offer).
    assert_eq!(out.matches("String(x)").count(), 0, "{out}");
    let last = n - 1;
    assert!(
        out.contains(&format!("Try `{last} >= x` instead.")),
        "{out}"
    );
}

#[test]
fn offering_the_literal_first_in_comparisons() {
    for n in [4, 8] {
        the_literal_offered_first_in_comparisons(&texts_compared(n), n);
    }
}

/// One text of `d` digits compared with an `int` by `==`.
pub(super) fn a_long_text_compared(d: usize) -> String {
    format!("f(positional x: int) = x == \"{}\";\n", "7".repeat(d))
}

/// One text of d digits compared by `==`: its cast, its printing, its reading back, and the
/// text written in the headline.
pub(super) fn the_literal_of_a_long_text_in_a_comparison(src: &str, d: usize) {
    let out = rejected(src);
    let want = format!(
        "Try `x == {}` to compare the numbers instead.",
        "7".repeat(d)
    );
    assert!(out.contains(&want), "{out}");
}

#[test]
fn offering_the_literal_of_a_long_text_in_a_comparison() {
    for d in [1, 30] {
        the_literal_of_a_long_text_in_a_comparison(&a_long_text_compared(d), d);
    }
}

/// One `f64` ordered against a fraction text of 2d + 1 characters, which the cast `rat` reads
/// and no `f64` literal writes.
pub(super) fn an_f64_ordered_with_a_long_fraction_text(d: usize) -> String {
    format!(
        "f(positional x: f64) = x < \"{}/{}\";\n",
        "7".repeat(d),
        "3".repeat(d)
    )
}

/// The casts run on the text to see it is a number (row REPAIR-string-compare-offer), then no
/// repair.
pub(super) fn an_ordering_with_a_number_text_offers_no_text_comparison(src: &str) {
    let out = rejected(src);
    assert!(!out.contains("String(x)"), "{out}");
    assert!(!out.lines().next().unwrap_or("").contains("Try"), "{out}");
}

#[test]
fn deciding_an_ordering_with_a_long_number_text_offers_no_text_comparison() {
    for d in [1, 30] {
        an_ordering_with_a_number_text_offers_no_text_comparison(
            &an_f64_ordered_with_a_long_fraction_text(d),
        );
    }
}

/// `n` functions, each comparing a `rat` by `==` or `!=` with a fraction text no literal
/// writes, `1/(3i + 3)`, whose denominator has the factor 3, the text on either side, so each rejection offers the cast kept around the
/// literal (row REPAIR-eq-kept-cast): besides the trials of the literals, one application
/// of the cast to the literal.
pub(super) fn fractions_compared(n: usize) -> String {
    (0..n)
        .map(|i| match i % 4 {
            0 => format!("h{i}(positional r: rat) = r == \"1/{}\";\n", 3 * i + 3),
            1 => format!("h{i}(positional r: rat) = \"1/{}\" != r;\n", 3 * i + 3),
            2 => format!("h{i}(positional r: rat) = r != \"1/{}\";\n", 3 * i + 3),
            _ => format!("h{i}(positional r: rat) = \"1/{}\" == r;\n", 3 * i + 3),
        })
        .collect()
}

/// [`fractions_compared`] at `n`, a multiple of 4, so that the last comparison is `"…" == r`.
pub(super) fn the_cast_of_a_literal_offered_in_comparisons(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(
        out.matches("Try `r == rat(\"").count(),
        n.div_ceil(4),
        "{out}"
    );
    assert_eq!(out.matches("Try `rat(\"").count(), n / 2, "{out}");
    let last = n - 1;
    assert!(
        out.contains(&format!("Try `rat(\"1/{}\") == r`", 3 * last + 3)),
        "{out}"
    );
}

#[test]
fn offering_the_cast_of_a_literal_in_comparisons() {
    for n in [4, 8] {
        the_cast_of_a_literal_offered_in_comparisons(&fractions_compared(n), n);
    }
}

/// `n` functions, each comparing an `f64` by `==` or `!=` with a number cast of a text, on
/// either side (row REPAIR-both-sides-cast): `rat("i.5")`, which the literal `i.5` writes,
/// or `rat("1/(3i + 3)")`, which no `f64` is, so the rejection offers the answer alone.
pub(super) fn casts_compared(n: usize) -> String {
    (0..n)
        .map(|i| match i % 4 {
            0 => format!("h{i}(positional x: f64) = x == rat(\"{i}.5\");\n"),
            1 => format!("h{i}(positional x: f64) = rat(\"1/{}\") != x;\n", 3 * i + 3),
            2 => format!("h{i}(positional x: f64) = x != rat(\"{i}.5\");\n"),
            _ => format!("h{i}(positional x: f64) = rat(\"1/{}\") == x;\n", 3 * i + 3),
        })
        .collect()
}

/// [`casts_compared`] at `n`, a multiple of 4, so that the comparison before the last is
/// `x != rat("….5")`.
pub(super) fn the_literal_of_a_cast_of_a_literal_offered(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(out.matches("Try `x == ").count(), n.div_ceil(4), "{out}");
    assert_eq!(out.matches("Try `x != ").count(), (n + 1) / 4, "{out}");
    assert_eq!(
        out.matches("Try `true` instead").count(),
        (n + 2) / 4,
        "{out}"
    );
    assert_eq!(out.matches("Try `false` instead").count(), n / 4, "{out}");
    let last = n - 2;
    assert!(out.contains(&format!("Try `x != {last}.5`")), "{out}");
}

#[test]
fn offering_the_literal_of_a_cast_of_a_literal_in_comparisons() {
    for n in [4, 8] {
        the_literal_of_a_cast_of_a_literal_offered(&casts_compared(n), n);
    }
}

/// One cast of a text of `d` digits compared by `==` with an `int`.
pub(super) fn a_long_cast_of_a_text_compared(d: usize) -> String {
    format!("f(positional n: int) = n == rat(\"{}\");\n", "7".repeat(d))
}

/// The cast run on the text's value, its printing, its reading back, and the cast written in
/// the headline.
pub(super) fn the_literal_of_a_long_cast_of_a_text(src: &str, d: usize) {
    let out = rejected(src);
    let want = format!("Try `n == {}`", "7".repeat(d));
    assert!(out.contains(&want), "{out}");
}

#[test]
fn offering_the_literal_of_a_long_cast_of_a_text_in_a_comparison() {
    for d in [1, 30] {
        the_literal_of_a_long_cast_of_a_text(&a_long_cast_of_a_text_compared(d), d);
    }
}

/// One text of `d` digits over 9 compared by `==` with a `rat`.
pub(super) fn a_long_fraction_text_compared(d: usize) -> String {
    format!("f(positional r: rat) = r == \"{}/9\";\n", "7".repeat(d))
}

/// Its cast, its printing, the failed reading back as a literal, the cast checked as written,
/// and the text in the headline.
pub(super) fn the_cast_of_a_long_fraction_text(src: &str, d: usize) {
    let out = rejected(src);
    let want = format!(
        "Try `r == rat(\"{}/9\")` to compare the numbers instead.",
        "7".repeat(d)
    );
    assert!(out.contains(&want), "{out}");
}

#[test]
fn offering_the_cast_of_a_long_fraction_text_in_a_comparison() {
    // A count of digits that is not a multiple of 3: then `7…7` is prime to 9.
    for d in [1, 2, 31] {
        the_cast_of_a_long_fraction_text(&a_long_fraction_text_compared(d), d);
    }
    // `777/9` is not in lowest terms, so `rat` reads no number from it and the comparison is
    // always `false`.
    let out = rejected(&a_long_fraction_text_compared(3));
    assert!(
        out.contains("is always `false`. Try `false` instead."),
        "{out}"
    );
}

/// One `int` ordered against the fraction text `10…0/3` of d + 3 characters, which `rat` reads
/// and no `rat` literal writes.
pub(super) fn an_int_ordered_with_a_long_fraction_text(d: usize) -> String {
    format!("f(positional n: int) = n < \"1{}/3\";\n", "0".repeat(d))
}

/// The casts run on the text to see it is a number, then both operands are cast to `rat` and
/// the ordering checked (row REPAIR-text-number-both-sides). The denominator is one word, so
/// the lowest-terms test of the cast is linear (COMPLEXITY.md K41); a fraction of two wide
/// parts costs the cast's half-gcd, which the kernel's own scaling tests hold (NUM-subquad).
pub(super) fn an_ordering_of_an_int_with_a_fraction_text_repaired(src: &str, d: usize) {
    let out = rejected(src);
    let want = format!("Try `rat(n) < rat(\"1{}/3\")` instead.", "0".repeat(d));
    assert!(out.contains(&want), "{out}");
}

#[test]
fn repairing_an_ordering_of_an_int_with_a_long_fraction_text() {
    for d in [0, 1, 30] {
        an_ordering_of_an_int_with_a_fraction_text_repaired(
            &an_int_ordered_with_a_long_fraction_text(d),
            d,
        );
    }
}

/// `n` functions, each ordering an `int` with the fraction text `1/(3i + 3)`, the text on
/// either side and each of the four orderings in turn: each rejection is repaired by
/// casting both operands to `rat` (row REPAIR-text-number-both-sides).
pub(super) fn int_orderings_with_fractions(n: usize) -> String {
    (0..n)
        .map(|i| {
            let op = ["<", "<=", ">", ">="][i % 4];
            let text = format!("\"1/{}\"", 3 * i + 3);
            if i % 2 == 0 {
                format!("h{i}(positional n: int) = n {op} {text};\n")
            } else {
                format!("h{i}(positional n: int) = {text} {op} n;\n")
            }
        })
        .collect()
}

pub(super) fn orderings_of_ints_with_fraction_texts_repaired(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(out.matches("Try `rat(n) ").count(), n.div_ceil(2), "{out}");
    assert_eq!(out.matches("Try `rat(\"1/").count(), n / 2, "{out}");
    assert!(out.contains("rat(n) < rat(\"1/3\")"), "{out}");
}

#[test]
fn repairing_orderings_of_ints_with_fraction_texts() {
    for n in [1, 4, 7] {
        orderings_of_ints_with_fraction_texts_repaired(&int_orderings_with_fractions(n), n);
    }
}

/// A chain of `n` calls to a use that fails: `h0` takes its argument apart into 3 names, each
/// `h{k}` passes its argument to `h{k-1}`, and `main` calls `h{n}` with a pair (plan row
/// DIAG-call-chain-full, step L1.29).
pub(super) fn call_chain(n: usize) -> String {
    let mut src = String::from("h0(positional p) {\n  a, b, c = p;\n  return a;\n}\n");
    for k in 1..=n {
        src += &format!("h{k}(positional p) = h{}(p);\n", k - 1);
    }
    src + &format!(
        "main(m: MainArgs) {{\n  m.stdout <- if h{n}((1, 3)) is int {{ \"int\" }} else {{ \"other\" }};\n}}\n"
    )
}

/// The rejection at the call names each of the `n + 1` calls on the path once, outermost
/// first, and the use in `h0` last.
pub(super) fn each_call_of_the_chain_named(src: &str, n: usize) {
    let out = rejected(src);
    let note = |k: usize| format!("`h{k}` needs this of its argument here");
    assert_eq!(
        out.matches("needs this of its argument here").count(),
        n + 1,
        "{out}"
    );
    let mut from = 0;
    for k in (0..=n).rev() {
        let at = out[from..]
            .find(&note(k))
            .unwrap_or_else(|| panic!("no note for `h{k}` after the one before:\n{out}"));
        from += at + 1;
    }
    assert!(out[from..].contains("a, b, c = p;"), "{out}");
}

#[test]
fn naming_each_call_of_a_chain() {
    for n in [1, 2, 3, 9] {
        each_call_of_the_chain_named(&call_chain(n), n);
    }
}
