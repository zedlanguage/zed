//! Placing diagnostics at the rule of low complexity (DESIGN.md Part G). Each diagnostic and
//! each of its steps was placed by decoding the file from its first byte, so a file of `n`
//! lines with an error on each took `O(n²)`.

use zed_tests::scaling;

use super::rejected;

/// `n` definitions, each reading a name nothing declares.
fn unresolved(n: usize) -> String {
    (0..n).map(|i| format!("h{i} = missing{i};\n")).collect()
}

#[test]
fn placing_a_diagnostic_on_every_line_scales() {
    scaling::check("placing a diagnostic on each of n lines", 500, |n| {
        let out = rejected(&unresolved(n));
        // One diagnostic per line, the last at the last line, after `h{n-1} = `.
        let last = n - 1;
        let col = format!("h{last} = ").len() + 1;
        assert_eq!(out.lines().count(), n);
        let want = format!(
            "{n}:{col}: {}",
            zed_tests::undefined(&format!("missing{last}"))
        );
        assert_eq!(out.lines().last(), Some(want.as_str()));
    });
}

/// A chain of `n` bindings, each reading the one before twice, ending in an error.
fn doubled(n: usize) -> String {
    let mut src = String::from("main(m: MainArgs) {\n  a0 = 1;\n");
    for i in 1..n {
        src += &format!("  a{i} = a{p} + a{p};\n", p = i - 1);
    }
    src + &format!("  m.stdout <- \"x\" ++ a{};\n}}\n", n - 1)
}

#[test]
fn deriving_through_values_read_twice_scales() {
    scaling::check(
        "the derivation of a chain read twice at each of n bindings",
        400,
        |n| {
            let out = rejected(&doubled(n));
            assert!(
                out.contains("`a0` is defined as this expression, 1"),
                "{out}"
            );
        },
    );
}

/// A function adding `n` untyped parameters and testing the sum as a condition: one class
/// with `n` reasons, shown in one diagnostic. Each parameter and each addition has a line of
/// its own, since each step of a diagnostic shows the whole line it is on.
fn summed_condition(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    format!(
        "f({}) = if {} {{ 1 }} else {{ 2 }};\n",
        ps.join(",\n"),
        xs.join("\n+ ")
    )
}

#[test]
fn the_reasons_of_a_class_narrowed_many_times_scale() {
    // Each reason was looked for among those shown before it (COMPLEXITY.md F29).
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            let out = rejected(&summed_condition(3));
            assert!(out.contains("not bool"), "{out}");
            assert_eq!(
                out.matches("gives these values one carrier").count(),
                2,
                "{out}"
            );
            scaling::check("the reasons of a class merged n times", 1000, |n| {
                let out = rejected(&summed_condition(n));
                assert_eq!(out.matches("gives these values one carrier").count(), n - 1);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `h` passes `g` a pair of `n` parts, each written twice: `((#a0 | #b0, #a0 | #b0), …)`.
fn shared_parts(n: usize) -> String {
    let pairs: Vec<String> = (0..n)
        .map(|i| format!("(#a{i} | #b{i}, #a{i} | #b{i})"))
        .collect();
    format!(
        "g(x: int) = x;\nh(y: ({})) = g(x: y);\nmain() = 0;\n",
        pairs.join(", ")
    )
}

#[test]
fn a_message_with_many_definitions_scales() {
    // One message names its `n` definitions in one numbering and writes each once, on its own
    // line (step MSG-type-defs-layout).
    scaling::check("a message with n parts written more than once", 200, |n| {
        let out = rejected(&shared_parts(n));
        let last = format!("    type T{n} = #a{m} | #b{m};\n", m = n - 1);
        assert!(out.contains(&last), "{out}");
        assert_eq!(out.matches("    type T").count(), n);
    });
}

/// `n` names, each defined as a `/` of literals that meets no carrier and read once by a `*`
/// that does not take it: `2n` rejections, each read stepping through its name with one lookup
/// of the name's definition (`Ck::defined_open`).
fn read_divisions(n: usize) -> String {
    (0..n)
        .map(|i| format!("q{i} = 1 / 2;\nz{i} = q{i} * \"a\";\n"))
        .collect()
}

#[test]
fn deriving_reads_of_many_divisions_of_literals_scales() {
    scaling::check_order(
        "the derivations of n reads of names defined as divisions of literals",
        200,
        1,
        |n| {
            let out = rejected(&read_divisions(n));
            assert_eq!(
                out.matches("is read here; it is defined as an operation on literals alone")
                    .count(),
                n,
                "{out}"
            );
        },
    );
}

/// A chain of `n` names from `-0r` to a divisor, with `0r` written first: one message whose
/// derivation steps through every name, each step finding the literal at the chain's end
/// (item MSG-neg-zero-chain).
fn zero_chain(n: usize) -> String {
    let mut src = String::from("a = 0r;\nz0 = -0r;\n");
    for i in 1..n {
        src += &format!("z{i} = z{};\n", i - 1);
    }
    src + &format!("f(x: rat) = x / z{};\n", n - 1)
}

#[test]
fn a_chain_of_names_to_a_negated_zero_prints_in_linear_time() {
    // Each step of the derivation follows the chain to its literal; a walk from each step
    // to the end, with no memo shared by the steps, is O(n²) (COMPLEXITY.md F165).
    let srcs = scaling::inputs(1000, zero_chain);
    scaling::check(
        "the message of a division by the last of a chain of n names from -0r",
        1000,
        |n| {
            let out = rejected(&srcs[&n]);
            assert_eq!(out.matches(" is -0r here").count(), n);
            assert_eq!(out.matches("defined as this expression, -0r").count(), n);
            assert!(!out.contains(" 0r here"));
        },
    );
}

/// `n` rejections whose fixes are each checked as written (MSG-converted-claims-checked): the
/// menu fixes `1.0 + gr(true)` and `1.0r + gr(true)`, dropped, the message naming `true`; a
/// comparison cast, `int(r)`, dropped; a cast beside
/// a decimal literal, `f64(k)`, dropped. Each costs a few checks of its own construct, so the
/// whole is linear in `n`.
fn checked_fixes(n: usize) -> String {
    let mut src = String::from(
        "gr(positional c: bool) = if c { 1r } else { true };\nn = 1;\nr = 2.5r;\n\
         k = 1152921504606846977;\n",
    );
    for i in 0..n {
        src += &format!("a{i} = 1.0f64 + gr(true);\nb{i} = n == r;\nc{i} = k == 0.5;\n");
    }
    src
}

#[test]
fn checking_each_offered_fix_as_written_scales() {
    scaling::check("checking the fixes of 3n rejections as written", 200, |n| {
        let out = rejected(&checked_fixes(n));
        assert_eq!(
            out.matches("does not take (1.0f64, true)").count(),
            n,
            "{out}"
        );
        assert!(!out.contains("gr(true);    "), "{out}");
        assert!(!out.contains("int(r)"), "{out}");
        assert!(!out.contains("f64(k)"), "{out}");
    });
}

/// A tuple of `n` `rat` components compared with a `rat`: each component is offered,
/// `t[i] == 1r`, and each is checked as written, the comparison checked again with the
/// component in place of the tuple, which is not copied for it.
fn tuple_compared(n: usize) -> String {
    let xs = vec!["1r"; n];
    format!("t = ({});\ny = t == 1r;\n", xs.join(", "))
}

#[test]
fn checking_the_components_offered_for_a_wide_tuple_scales() {
    scaling::check(
        "checking the n components offered for an n-tuple",
        200,
        |n| {
            let out = rejected(&tuple_compared(n));
            let last = format!("t[{}] == 1r", n - 1);
            assert!(out.contains(&last), "{out}");
        },
    );
}

/// A function of `n` parameters of carrier `c` called with `n` literals `1.0f64`
/// (MSG-many-arguments-output): one message for the call, whose steps name each literal once.
/// At `rat` its one fix writes the call once, `y = f(1.0, …)`; at `int` there is no fix, as
/// no literal `1.0f64` takes an `int` (DESIGN row "Two numeric values with no common
/// carrier"). Each literal its own message, each with its fix checked by checking the call
/// again with the other literals refused again, cost O(n³) and wrote the call n times, Θ(n²)
/// bytes.
fn many_literal_arguments(n: usize, c: &str) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional p{i}: {c}")).collect();
    let xs = vec!["1.0f64"; n];
    format!("f({}) = 1;\ny = f({});\n", ps.join(", "), xs.join(", "))
}

/// The checks of [`many_literal_arguments`] at the carrier `c`, whose fixed call writes each
/// literal as `fixed`, or that has no fixed call.
fn many_literal_arguments_scale(c: &str, fixed: Option<&str>) {
    let srcs = scaling::inputs(200, |n| many_literal_arguments(n, c));
    scaling::check(
        &format!("the message of a call of n literals at n {c} parameters"),
        200,
        |n| {
            let out = rejected(&srcs[&n]);
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
        },
    );
}

#[test]
fn many_literal_arguments_refused_at_their_parameters_scale() {
    many_literal_arguments_scale("rat", Some("1.0"));
}

#[test]
fn many_literal_arguments_refused_at_int_parameters_scale() {
    many_literal_arguments_scale("int", None);
}

/// A call of `n` arguments `k * 0.5` at `rat` parameters, one per line, `k` an `int`
/// (MSG-many-args-repair-loop): each argument is its own error, whose fix `rat(k) * 0.5` gives
/// its argument the type `rat` and is carried to the call, which checks them. One check of
/// the call per carried fix, each copying the other arguments, cost O(n²) (31 times the
/// instructions at 8 times the arguments); the fixes of one round are now checked by one
/// check of a call of one parameter each and one check of the whole call. One argument per
/// line, so that each message quotes a line of its own and the output is linear in `n`.
fn carried_fixes(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional p{i}: rat")).collect();
    let xs = vec!["  k * 0.5"; n];
    format!(
        "k = 1;\nf({}) = 1;\ny = f(\n{});\n",
        ps.join(", "),
        xs.join(",\n")
    )
}

#[test]
fn the_carried_fixes_of_many_arguments_scale() {
    let srcs = scaling::inputs(100, carried_fixes);
    scaling::check(
        "checking the carried fixes of a call of n arguments",
        100,
        |n| {
            let out = rejected(&srcs[&n]);
            assert_eq!(
                out.matches("A decimal literal is never an `int`: `k : int * 0.5`.")
                    .count(),
                n,
                "{out}"
            );
            assert_eq!(out.matches("Try `rat(k) * 0.5").count(), n, "{out}");
        },
    );
}

/// A call of `n` decimal literals at parameters with no type, `f(1.5, …)`
/// (MSG-many-args-decimal): nothing gives the literals a carrier, and they are one message
/// that writes the call once per fix, `f(1.5f64, …)` and `f(1.5r, …)`, with a step for each.
fn unfixed_decimal_arguments(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional p{i}")).collect();
    format!(
        "f({}) = 1;\ny = f({});\n",
        ps.join(", "),
        vec!["1.5"; n].join(", ")
    )
}

#[test]
fn many_unfixed_decimal_arguments_scale() {
    let srcs = scaling::inputs(200, unfixed_decimal_arguments);
    scaling::check(
        "the message of a call of n decimal literals at n parameters with no type",
        200,
        |n| {
            let out = rejected(&srcs[&n]);
            let head = format!("{n} parts of the arguments of `f` are literals that nothing");
            assert!(out.contains(&head), "{out}");
            assert_eq!(
                out.matches("Nothing gives the literal `1.5` a carrier")
                    .count(),
                n
            );
            let fixed = format!("y = f({});", vec!["1.5f64"; n].join(", "));
            assert_eq!(out.matches(fixed.as_str()).count(), 1, "{out}");
            let call = format!("y = f({});", vec!["1.5"; n].join(", "));
            assert_eq!(out.matches(call.as_str()).count(), 1, "{out}");
        },
    );
}

/// [`super::rare`]'s value that flows into `g` through a chain of `n` defaults, `k(h0 = g,
/// h1 = h0, ...)`, which passes `x -> "s"` as the last; then `n` more parameters whose
/// defaults read the two ends of the chain in turn, `m0 = h0, m1 = h{n-1}, m2 = h0, ...`, so
/// that each of their merges names a class at the far end of the chain from the last one.
fn defaults_chain(n: usize) -> String {
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

#[test]
fn the_merges_between_a_value_and_its_use_scale() {
    // Each default merges a parameter with the one it reads; the derivation walks the merges
    // from the lambda's class to `g`'s, one note per default of the chain (MSG-flow-origin;
    // COMPLEXITY.md F195). A merge reroots the smaller of the two trees of merges: rerooting
    // the tree of the chain at `h0` and at `h{n-1}` in turn would cost n at each `m`.
    let inputs = scaling::inputs(1000, defaults_chain);
    scaling::check(
        "the merges between a value and its use, 2n defaults",
        1000,
        |n| {
            let out = rejected(&inputs[&n]);
            let defaults = out
                .lines()
                .filter(|l| l.contains(": the default `h"))
                .count();
            assert_eq!(defaults, n, "{out}");
        },
    );
}

/// A call of one line whose first argument is a text of `n` letters and whose second is an
/// `int` at a `rat` parameter, `y = h("aa…a", k)` (row MSG-apply-try-headline): its headline
/// ends with the call rewritten, `h("aa…a", rat(k))`. The repairs' notes are copied once
/// beside the notes, O(r), and only the first repair is written, once, in the length of the
/// call, O(n), when the check ends; writing each repair's call as it is found would cost
/// O(n) per repair. A call of `n` arguments is no test of this: its message has a step per
/// argument, and placing those steps costs O(n²) before this row (4.5 s at 400 arguments,
/// 20 s at 800).
fn one_repair_in_a_long_call(n: usize) -> String {
    let text = "a".repeat(n);
    format!("k = 1;\nh(positional a: String, positional b: rat) = 1;\ny = h(\"{text}\", k);\n")
}

#[test]
fn the_headline_repair_of_a_long_call_scales() {
    let srcs = scaling::inputs(4000, one_repair_in_a_long_call);
    scaling::check("the headline repair of a call n bytes long", 4000, |n| {
        let out = rejected(&srcs[&n]);
        let want = format!("Try `h(\"{}\", rat(k))` instead.", "a".repeat(n));
        let head = out.lines().next().unwrap_or_default();
        assert!(head.ends_with(&want), "{}", &out[..out.len().min(400)]);
    });
}

/// A call `g(x)` of a function that takes only a `String`, with `x` a union of tuples of every
/// length from 1 to k, `(int) | (int, int) | …`, about `n` components in all (row
/// MSG-headline-l01_26). `String(x)` checks, so before it is offered the call is tried with
/// each tuple length alone, to see whether it takes some value that `String` would change;
/// it takes none, so all k = O(√n) are tried and the headline ends with `g(String(x))`. A
/// trial costs about the same at both sizes, as types are shared, so the trials add O(√n) to
/// the O(n) check. Negative control, run once: a trial that also writes out the whole type,
/// O(n) each, O(n^1.5) in all, failed at 21.7 times the bytes.
fn a_call_of_many_tuple_lengths(n: usize) -> String {
    let k = (1..).find(|k| k * (k + 1) / 2 >= n).unwrap_or(1);
    let shapes: Vec<String> = (1..=k)
        .map(|len| format!("({})", vec!["int"; len].join(", ")))
        .collect();
    format!(
        "g(positional s: String) = 1;\nf(x: {}) = g(x);\n",
        shapes.join(" | ")
    )
}

#[test]
fn a_text_repair_of_many_shapes_scales() {
    let srcs = scaling::inputs(800, a_call_of_many_tuple_lengths);
    scaling::check(
        "the text repair of a union of n tuple components",
        800,
        |n| {
            let out = rejected(&srcs[&n]);
            let head = out.lines().next().unwrap_or_default();
            assert!(head.ends_with("Try `g(String(x))` instead."), "{head}");
        },
    );
}
