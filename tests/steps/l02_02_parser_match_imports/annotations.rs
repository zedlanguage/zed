//! The `@` annotation syntax: a bare `@name`, or `@name(args)` with the arguments of a call,
//! written before a declaration. The syntax is built whole; resolution names each one's layer.

use super::check;

#[test]
fn annotations_before_declarations() {
    check(&[
        (
            "@memoized\nfib(n) = n;",
            "(annotated @memoized (def fib (n) = n))",
        ),
        (
            "@cost(n * log(n), space: n)\n@noalloc\nsort(xs) = xs;",
            "(annotated (@cost (* n (call log n)) (space: n)) @noalloc (def sort (xs) = xs))",
        ),
        (
            "@log @exact\nf(x) = x;",
            "(annotated @log @exact (def f (x) = x))",
        ),
        ("@log()\nf(x) = x;", "(annotated (@log) (def f (x) = x))"),
        (
            "@foreign(\"c\", name: \"cos\")\ncos(x: f64) = x;",
            "(annotated (@foreign (str \"c\") (name: (str \"cos\"))) (def cos ((x: f64)) = x))",
        ),
        (
            "@invariant(x >= 0)\nstruct Account { x: int }",
            "(annotated (@invariant (>= x 0)) (struct Account (x: int)))",
        ),
        ("@export\nimport a.b;", "(annotated @export (import a.b))"),
        // From layer L7 an annotation followed by `;` is a unit item; resolution refuses
        // `@log;` with its reason (tests/steps/l07_03_unit_log_off).
        ("@log;\nf(x) = x;", "(unit @log)\n(def f (x) = x)"),
        (
            "f(x) {\n  @measure(x)\n  g(y) = y;\n  g(x)\n}",
            "(def f (x) (block (annotated (@measure x) (def g (y) = y)) (return (call g x))))",
        ),
    ]);
}

#[test]
fn malformed_annotations() {
    check(&[
        (
            "@cost(n, ...)\nf(x) = x;",
            "error: the arguments of `@cost` end in `...`, which only a call takes",
        ),
        ("@log", "syntax"),
        ("@log(\nf(x) = x;", "syntax"),
    ]);
}

/// An annotation on an operand (rule AnnotExpr, layer L10, as in `d = @fpsafe (x - y);`)
/// parses, and is refused with its layer until it is built; before, such a unit reached an
/// `unreachable!` in the builder of `Prefix`.
#[test]
fn annotated_operands() {
    let later = "error: this form (AnnotExpr) is built from layer L10";
    check(&[
        ("x = @log 1;", later),
        ("d = @fpsafe (x - y);", later),
        ("d = @fpsafe x - y;", later),
        ("r = @approx(relErr: 0.001) rsqrt(x) * 2.0;", later),
        ("r = -@approx(relErr: 0.001) rsqrt(x);", later),
        ("f(x) = !@fpsafe x;", later),
    ]);
}
