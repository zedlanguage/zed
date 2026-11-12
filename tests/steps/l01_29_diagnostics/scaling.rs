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

/// `n` rejections whose fixes are each checked as written (MSG-converted-claims-checked): a
/// menu fix, `y = 1 + gi(true)`, dropped; a comparison cast, `int(r)`, dropped; a cast beside
/// a decimal literal, `f64(k)`, dropped. Each costs a few checks of its own construct, so the
/// whole is linear in `n`.
fn checked_fixes(n: usize) -> String {
    let mut src = String::from(
        "gi(positional c: bool) = if c { 1 } else { true };\nn = 1;\nr = 2.5r;\n\
         k = 1152921504606846977;\n",
    );
    for i in 0..n {
        src += &format!("a{i} = 1.0f64 + gi(true);\nb{i} = n == r;\nc{i} = k == 0.5;\n");
    }
    src
}

#[test]
fn checking_each_offered_fix_as_written_scales() {
    scaling::check("checking the fixes of 3n rejections as written", 200, |n| {
        let out = rejected(&checked_fixes(n));
        assert_eq!(out.matches("No fix is offered").count(), n, "{out}");
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
