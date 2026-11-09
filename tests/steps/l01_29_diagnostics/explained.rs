//! Each rejection says why the use refuses the value and offers its repairs, written as the
//! program's code (DESIGN.md sec:diagnostics), on programs that read their input.

use super::rejected;
use zedc::run::load;

/// A program whose `main` reads `n` from the first line of input and then runs `body`.
fn reading(body: &str) -> String {
    format!("main(stdin: Lines) -> (stdout: Lines) {{\n  n = int(stdin[0]) else 0;\n{body}\n}}\n")
}

#[test]
fn each_rejection_explains_itself_and_offers_its_repairs() {
    let cases = [
        (
            reading("  r = if n { 1 } else { 2 };\n  stdout <- String(r);"),
            "3:10: the condition of `if` is int, not bool: `if` chooses its branch by a `bool`, \
             and this condition may be another value",
            vec![
                "repair: compare the value, so that the condition is a `bool`, as `if x == 0 { … }`",
            ],
        ),
        (
            reading("  stdout <- String(2^(n - 5));"),
            "3:20: `^` on an int needs an exponent of at least 0, and this one is int: an int \
             raised to a negative power is a fraction, not an int",
            vec![
                "repair: test the exponent first, as `if n >= 0 { x^n } else { … }`",
                "repair: declare the exponent with a type of no int below 0, as `n: int[0..]`",
            ],
        ),
        (
            reading("  stdout <- n;"),
            "3:13: a `Lines` port takes a `String` or a family of strings, not int: the port \
             `stdout` writes each value pushed to it as one line of text, and the value pushed \
             here may be something other than text",
            vec!["repair: write the value into a string, as `stdout <- \"${v}\";`"],
        ),
        (
            reading("  stdout <- String(popCount(n));"),
            "3:20: `popCount` takes `x` in int[0..], and this `x` is int: `popCount` reads `x` \
             as binary digits, and an int below 0 has no finite row of them",
            vec![
                "repair: test the value first, as `if v is int[0..] { … } else { … }`",
                "repair: declare the value with a type in int[0..], as `v: int[0..]`",
            ],
        ),
        (
            reading("  t = (n, 2);\n  stdout <- String(t[2]);"),
            "4:20: (int, 2) has no component 2: its components are at the positions 0 to 1, and \
             this index is 2",
            vec!["repair: use an index from 0 to 1"],
        ),
        (
            reading("  stdout <- String(n(1));"),
            "3:20: `n` is int, not a function: this call applies `n` to arguments, and a value \
             of type int cannot be applied",
            vec!["repair: call a function here, or write `n` without the parentheses"],
        ),
        (
            format!(
                "inc(positional x: int) = x + 1;\n{}",
                reading("  stdout <- String(inc == inc);")
            ),
            "4:20: `==` takes data, and this value may hold a function, `(int) -> int`: data is \
             a value that holds no function at any depth",
            vec!["repair: call the function before the value gets here"],
        ),
        (
            reading("  stdout <- String(min((n, 2), (1, 2, 3)));"),
            "3:20: `min` does not take (int, 2) and (1, 2, 3): a tuple of 2 components has none \
             of its length to compare with",
            vec!["repair: pass two tuples of the same length"],
        ),
        (
            format!(
                "f(positional x: int = \"a\") = x;\n{}",
                reading("  stdout <- String(f(n));")
            ),
            "1:23: the default of `x` is \"a\", not int: a default is a value of its parameter's \
             type",
            vec![
                "repair: write a default of type int",
                "repair: declare `x` with a type that holds \"a\" as well, as `x: int | \"a\"`",
            ],
        ),
        (
            reading("  stdout <- String(sum((n, \"a\")));"),
            "3:20: `sum` does not take (int, \"a\"): `sum` adds the components of a tuple, and \
             they must all be numbers",
            vec!["repair: pass a tuple whose components are all numbers, as `sum((1, 2, 3))`"],
        ),
        (
            format!(
                "scale(positional k: int) = (x: int) -> k * x;\n{}",
                reading("  stdout <- String(scale(n)(\"a\"));")
            ),
            "4:20: the function called here does not take (\"a\"): these are the types of its \
             arguments here, and the function called here has no arrow that takes them all",
            vec!["the function called here takes"],
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

/// A lambda has no declaration, so the repairs of passing it an argument by name are the ones
/// that need none: pass it by position, or declare a named function.
#[test]
fn a_lambda_passed_an_argument_by_name_offers_only_repairs_that_need_no_declaration() {
    let src = format!(
        "scale(positional k: int) = (x: int) -> k * x;\n{}",
        reading("  stdout <- String(scale(n)(x: 2));")
    );
    assert_eq!(
        rejected(&src),
        "4:32: this argument is passed by name, as `x: …`, and `x` of `(int) -> int` is \
         positional, so a call passes it only by position\n  \
         [1] 4:32: repair: pass `x` by position: remove `x: ` and put the value in `x`'s place \
         among the arguments\n      \
         4 |   stdout <- String(scale(n)(x: 2));\n        \
         |                                ^\n  \
         [2] 4:32: repair: declare a named function in place of this value, as \
         `f(x: …) = …;`, and call it by its name; a declared function's parameters are \
         passed by name unless declared `positional`"
    );
    // Each repair, applied, is accepted: the argument by position, and a named function whose
    // parameters a call passes by name.
    for fixed in [
        format!(
            "scale(positional k: int) = (x: int) -> k * x;\n{}",
            reading("  stdout <- String(scale(n)(2));")
        ),
        format!(
            "f(k: int, x: int) = k * x;\n{}",
            reading("  stdout <- String(f(k: n, x: 2));")
        ),
    ] {
        assert!(load(fixed.as_bytes()).is_ok(), "{fixed}");
    }
}
