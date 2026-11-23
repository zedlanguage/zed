//! Each rejection says why the use refuses the value and offers its repairs, written as the
//! program's code (DESIGN.md sec:diagnostics), on programs that read their input.

use super::rejected;
use zedc::run::load;

/// A program whose `main` reads `n` from the first line of input and then runs `body`.
fn reading(body: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n  n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n{body}\n}}\n"
    )
}

#[test]
fn each_rejection_explains_itself_and_offers_its_repairs() {
    let cases = [
        (
            reading("  r = if n { 1 } else { 2 };\n  m.stdout <- String(r);"),
            "3:10: the condition of `if` is int, not bool: `if` chooses its branch by a `bool`, \
             and this condition may be another value.",
            vec![
                "repair: compare the value, so that the condition is a `bool`, as `if x == 0 { … }`",
            ],
        ),
        (
            reading("  m.stdout <- String(2^(n - 5));"),
            "3:22: Int power with an exponent that may be negative: `2 : int ^ (n - 5) : int`. Try \
             `2r^(n - 5)` instead.",
            vec![
                "repair: `2r^(n - 5)`",
                "repair: `exponent = n - 5; if exponent >= 0 { 2^exponent } else { … }`",
            ],
        ),
        (
            reading("  m.stdout <- n;"),
            "3:15: A `Lines` port takes a `String` or a family of strings: \
             `m.stdout <- n : int`. Try `m.stdout <- \"${n}\";` instead.",
            vec![
                "the port `m.stdout` writes each value pushed to it as one line of text",
                "repair: write the value into a string, as `m.stdout <- \"${n}\";`",
            ],
        ),
        (
            reading("  m.stdout <- String(popCount(n));"),
            "3:22: `popCount` takes `x` in int[0..]: `popCount(n : int)`. Try \
             `if n >= 0 { popCount(n) } else { … }` instead.",
            vec![
                "repair: `if n >= 0 { popCount(n) } else { … }`",
                "repair: pass as `x` a value in int[0..]",
                "`popCount` reads `x` as binary digits, and an int below 0 has no finite row of them",
            ],
        ),
        (
            reading("  t = (n, 2);\n  m.stdout <- String(t[2]);"),
            "4:22: (int, 2) has no component 2: its components are at the positions 0 to 1, and \
             this index is 2.",
            vec!["repair: use an index from 0 to 1"],
        ),
        (
            reading("  m.stdout <- String(n(1));"),
            "3:22: `n` is int, not a function: this call applies `n` to arguments, and a value \
             of type int cannot be applied.",
            vec!["repair: call a function here, or write `n` without the parentheses"],
        ),
        // A read `v[x]` names the value as written, as a call `n(1)` does (plan row
        // MSG-value-call-code); before, it was "this value".
        (
            reading("  m.stdout <- String(n[n]);"),
            "3:22: `n` is int, not a function: this call applies `n` to an argument, and a value \
             of type int cannot be applied.",
            vec!["repair: call a function here, or drop the argument list after the value"],
        ),
        (
            format!(
                "inc(positional x: int) = x + 1;\n{}",
                reading("  m.stdout <- String(inc == inc);")
            ),
            "4:22: Cannot compare a value that may hold a function: `inc : int -> int` in \
             `inc == inc`.",
            vec!["data is a value that holds no function at any depth"],
        ),
        (
            reading("  m.stdout <- String(min((n, 2), (1, 2, 3)));"),
            "3:22: `min` does not take (int, 2) and (1, 2, 3): no tuple of 2 on the other side.",
            vec!["repair: pass two tuples of the same length"],
        ),
        (
            format!(
                "f(positional x: int = \"a\") = x;\n{}",
                reading("  m.stdout <- String(f(n));")
            ),
            "1:23: the default of `x` is \"a\", not int: a default is a value of its parameter's \
             type.",
            vec![
                "repair: write a default of type int",
                "repair: declare `x` with a type that holds \"a\" as well, as `x: int | \"a\"`",
            ],
        ),
        (
            reading("  m.stdout <- String(sum((n, \"a\")));"),
            "3:22: `sum` does not take (int, \"a\"): it adds only numbers.",
            vec!["repair: pass a tuple whose components are all numbers, as `sum((1, 2, 3))`"],
        ),
        (
            format!(
                "scale(positional k: int) = (x: int) -> k * x;\n{}",
                reading("  m.stdout <- String(scale(n)(\"a\"));")
            ),
            "4:22: `scale(n)` does not take (\"a\"): no arrow of `scale(n)` takes these types.",
            vec!["`scale(n)` takes"],
        ),
    ];
    for (src, message, repairs) in cases {
        let out = rejected(&src);
        assert!(out.starts_with(&format!("{message}\n")), "{src}\n{out}");
        for r in repairs {
            assert!(out.contains(r), "{src}\n{r}\n{out}");
        }
    }
}

/// A call through a parameter, misfit by the function its argument gives, is reported by
/// elaboration at the call in the body as well as by the checker at the call that passes the
/// function; elaboration's error carries the misfit's repairs too (row MSG-value-call-code,
/// part (b)), the ones a value with no declaration takes. Before, it had no repair at all.
#[test]
fn a_misfit_reported_in_the_body_through_a_parameter_offers_its_repairs() {
    let cases = [
        (
            "g(f) = f(y: 1);\na = g(f: x -> x);\n",
            "1:13: this argument is passed by the name `y`, and `T -> T` has no parameter",
            vec![
                "repair: remove this argument",
                "repair: declare a named function in place of this value, as `f(y: …) = …;`",
            ],
        ),
        (
            "g(f) = f(1, 2);\na = g(f: x -> x);\n",
            "1:13: this argument is one more than `T -> T` takes",
            vec!["repair: remove this argument"],
        ),
        (
            "g(f) = f(1);\nk(x) = x;\na = g(f: k);\n",
            "1:10: this argument is passed by position, and the parameter it reaches, `x` of \
             `(x: T) -> T`",
            vec!["repair: pass `x` by name, as `x: …`"],
        ),
    ];
    for (src, message, repairs) in cases {
        let out = rejected(&zed_tests::step_helpers::l01_29_diagnostics::with_main(src));
        // The error that starts with `message`, through the line before the next error.
        let at = out.find(message).unwrap_or_else(|| panic!("{src}\n{out}"));
        let rest = &out[at..];
        let end = (rest.match_indices('\n'))
            .map(|(i, _)| i + 1)
            .find(|&i| rest[i..].starts_with(|c: char| !c.is_whitespace()))
            .unwrap_or(rest.len());
        let error = &rest[..end];
        for r in repairs {
            assert!(error.contains(r), "{src}\n{r}\n{out}");
        }
    }
}

/// Two literals of two suffixes share no carrier, and the refusal names the carrier of the
/// other operand, not `int`, which no operand has (row REPAIR-grouped-refusal-message, part
/// (b); DESIGN.md sec:diagnostics, row "Two numeric values with no common carrier": "`1.0` for
/// `1.0f64` beside an `f32`"). Before, each program below said "The suffix makes the literal
/// `0.5f64` an `f64`, never `int`.", the `rat` one too, and offered no fix.
#[test]
fn two_literals_of_two_suffixes_are_refused_at_a_carrier_one_of_them_has() {
    let out = rejected("f() = 0.5f64 + 0.25f32;\n");
    assert!(
        out.starts_with(
            "1:7: The suffix makes the literal `0.5f64` an `f64`, never `f32`. Try \
             `f() = 0.5 + 0.25f32` instead.\n"
        ),
        "{out}"
    );
    assert!(
        out.contains("  fixes, each checked here:\n    f() = 0.5 + 0.25f32;"),
        "{out}"
    );
    for src in [
        "f(x: int) = x * (0.5f64 + 0.25f32);\n",
        "f(x: rat) = x * (0.5f64 + 0.25f32);\n",
    ] {
        let out = rejected(src);
        assert!(
            out.starts_with("1:18: The suffix makes the literal `0.5f64` an `f64`, never `f32`."),
            "{src}\n{out}"
        );
        assert!(!out.contains("never `int`"), "{src}\n{out}");
    }
}

/// Several literals of one application refused together give one grouped headline with a step
/// for each (REPAIR-grouped-refusal-message (a)). Where every argument is a literal, no repair
/// of another argument is tried, so the message offers none and does not say that each one
/// tried was rejected (walk.rs `Ck::repairs` passes over literal arguments, and
/// `Ck::repairs_tried` stays as it was). Read with a debug print of `none_kept`,
/// `repairs_tried` and `trying` at the grouped refusal (b22-checkwalk10, 2026-11-23): on these
/// three programs and on six other probes of two refused literals, `none_kept` was never
/// true, so the counter changes no grouped message found; four of the probes reach the
/// refusal only inside a repair's trial (`trying`), where nothing is printed.
#[test]
fn literals_refused_together_give_one_headline_and_no_repair_tried() {
    for (src, head, n) in [
        (
            "k(a: int, b: int) = a; f() = k(a: 0.5f64, b: 0.25f32);\n",
            "1:35: 2 arguments of `k` are literals at carriers they cannot take.\n",
            [35, 46],
        ),
        (
            "k(x: int, a: int, b: int) = x; f(x: int) = k(x: x, a: 0.5f64, b: 0.25f32);\n",
            "1:55: 2 arguments of `k` are literals at carriers they cannot take.\n",
            [55, 66],
        ),
        (
            "f() = 0.5f64 div 0.25f32;\n",
            "1:7: 2 operands of `div` are literals at carriers they cannot take.\n",
            [7, 18],
        ),
    ] {
        let out = zed_tests::step_helpers::l01_29_diagnostics::rejected_with_main(src);
        assert!(out.starts_with(head), "{src}\n{out}");
        let lits = [("0.5f64", "f64"), ("0.25f32", "f32")];
        for (i, (col, (lit, suffix))) in n.into_iter().zip(lits).enumerate() {
            let step = format!(
                "  [{}] 1:{col}: The suffix makes the literal `{lit}` an `{suffix}`, never `int`",
                i + 1
            );
            assert!(out.lines().any(|l| l == step), "{src}\n{out}");
        }
        assert!(!out.contains("fixes"), "{src}\n{out}");
        assert!(!out.contains("No fix is offered"), "{src}\n{out}");
    }
}

/// A lambda has no declaration, so the repairs of passing it an argument by name are the ones
/// that need none: pass it by position, or declare a named function.
#[test]
fn a_lambda_passed_an_argument_by_name_offers_only_repairs_that_need_no_declaration() {
    let src = format!(
        "scale(positional k: int) = (x: int) -> k * x;\n{}",
        reading("  m.stdout <- String(scale(n)(x: 2));")
    );
    assert_eq!(
        rejected(&src),
        "4:34: this argument is passed by name, as `x: …`, and `x` of `int -> int` is \
         positional, so a call passes it only by position.\n  \
         [1] 4:34: repair: pass `x` by position: remove `x: ` and put the value in `x`'s place \
         among the arguments\n      \
         4 |   m.stdout <- String(scale(n)(x: 2));\n        \
         |                                  ^\n  \
         [2] 4:34: repair: declare a named function in place of this value, as \
         `f(x: …) = …;`, and call it by its name; a declared function's parameters are \
         passed by name unless declared `positional`"
    );
    // Each repair, applied, is accepted: the argument by position, and a named function whose
    // parameters a call passes by name.
    for fixed in [
        format!(
            "scale(positional k: int) = (x: int) -> k * x;\n{}",
            reading("  m.stdout <- String(scale(n)(2));")
        ),
        format!(
            "f(k: int, x: int) = k * x;\n{}",
            reading("  m.stdout <- String(f(k: n, x: 2));")
        ),
    ] {
        assert!(load(fixed.as_bytes()).is_ok(), "{fixed}");
    }
}
