//! The cases COMPLETENESS.md lists that the other files of this group leave out: each scalar
//! primitive of the kernel on each kind of operand it takes, its corner values, an atom in
//! each argument position, and each ill-typed application the evaluator reports.

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::{Family, Pattern, Prim, Term, Value, eval};
use zed_tests::kernel::rc;

use Prim::*;

/// `n` as a `rat`.
fn r(n: i64) -> Term {
    prim(CastRat, vec![lit(n)])
}

/// The `rat` `n / d`.
fn q(n: i64, d: i64) -> Term {
    prim(Div, vec![r(n), r(d)])
}

/// 10^20, past a machine word.
fn big() -> Term {
    lit(Value::int_text("100000000000000000000", 10)
        .unwrap()
        .unwrap())
}

fn f(x: f64) -> Term {
    lit(Value::float(x))
}

fn f32_(x: f32) -> Term {
    lit(Value::float32(x))
}

fn t(xs: Vec<Value>) -> Term {
    lit(Value::tuple(xs))
}

fn atom(name: &str) -> Term {
    lit(Value::atom(name))
}

/// The family `{1 -> 2}`.
fn one_entry() -> Term {
    lit(Value::Family(Family::of([(Value::Int(1), Value::Int(2))])))
}

/// The value of `term`, printed, or `error: <what the evaluator met>` for an ill-typed term.
fn run(term: &Term) -> String {
    match eval(term) {
        Ok(v) => v.to_string(),
        Err(e) => {
            let e = e.to_string();
            let met = "here the evaluator met this: ";
            let at = e.find(met).unwrap_or_else(|| panic!("{e}")) + met.len();
            let what = &e[at..];
            format!(
                "error: {}",
                &what[..what.find(". Please").unwrap_or(what.len())]
            )
        }
    }
}

/// Each `(what, term, value)` of `cases` evaluated.
fn table(cases: Vec<(&str, Term, &str)>) {
    for (what, term, want) in cases {
        assert_eq!(run(&term), want, "{what}");
    }
}

#[test]
fn integer_arithmetic_widens_past_a_word_and_comes_back() {
    // DESIGN.md L1.17: an integer is one word while it fits and a big integer beyond.
    table(vec![
        ("add", prim(Add, vec![lit(2), lit(3)]), "5"),
        (
            "add past the top",
            prim(Add, vec![lit(i64::MAX), lit(1)]),
            "9223372036854775808",
        ),
        (
            "sub past the bottom",
            prim(Sub, vec![lit(i64::MIN), lit(1)]),
            "-9223372036854775809",
        ),
        (
            "mul past the top",
            prim(Mul, vec![lit(i64::MAX), lit(2)]),
            "18446744073709551614",
        ),
        (
            "negate the least word",
            prim(Neg, vec![lit(i64::MIN)]),
            "9223372036854775808",
        ),
        (
            "negate it back into a word",
            prim(Neg, vec![prim(Neg, vec![lit(i64::MIN)])]),
            "-9223372036854775808",
        ),
        (
            "abs of the least word",
            prim(Abs, vec![lit(i64::MIN)]),
            "9223372036854775808",
        ),
        ("abs", prim(Abs, vec![lit(-3)]), "3"),
        (
            "negate a big",
            prim(Neg, vec![big()]),
            "-100000000000000000000",
        ),
        (
            "big plus a word",
            prim(Add, vec![big(), lit(1)]),
            "100000000000000000001",
        ),
        ("big minus itself", prim(Sub, vec![big(), big()]), "0"),
        ("big mod a word", prim(Mod, vec![big(), lit(7)]), "2"),
        (
            "negative big div a word, Euclidean",
            prim(IntDiv, vec![prim(Neg, vec![big()]), lit(7)]),
            "-14285714285714285715",
        ),
        ("power", prim(Pow, vec![lit(2), lit(10)]), "1024"),
        ("zero to the zero", prim(Pow, vec![lit(0), lit(0)]), "1"),
    ]);
}

#[test]
fn integer_division_by_zero_is_an_atom_and_the_remainder_is_never_negative() {
    // DESIGN.md L1.18: Euclidean `div` and `mod`; sec:failure: a zero divisor gives
    // `#divByZero`.
    table(vec![
        (
            "div by zero",
            prim(IntDiv, vec![lit(7), lit(0)]),
            "#divByZero",
        ),
        ("mod by zero", prim(Mod, vec![lit(7), lit(0)]), "#divByZero"),
        ("-7 div 2", prim(IntDiv, vec![lit(-7), lit(2)]), "-4"),
        ("-7 mod 2", prim(Mod, vec![lit(-7), lit(2)]), "1"),
        ("7 mod -2", prim(Mod, vec![lit(7), lit(-2)]), "1"),
    ]);
}

#[test]
fn rationals_stay_reduced_and_exact() {
    // DESIGN.md L1.17: a `rat` is kept reduced with a positive denominator, printed `1r/3r`;
    // `/` by `0r` is `#divByZero`; a negative int power inverts.
    table(vec![
        ("add", prim(Add, vec![r(1), q(1, 3)]), "4r/3r"),
        ("negate", prim(Neg, vec![q(1, 3)]), "-1r/3r"),
        ("divide by zero", prim(Div, vec![r(1), r(0)]), "#divByZero"),
        ("compare", prim(Lt, vec![q(1, 3), q(1, 2)]), "true"),
        (
            "equal when reduced",
            prim(Eq, vec![q(2, 4), q(1, 2)]),
            "true",
        ),
        ("negative power", prim(Pow, vec![r(2), lit(-1)]), "1r/2r"),
        ("abs", prim(Abs, vec![q(-2, 3)]), "2r/3r"),
        ("an int is not a rat", prim(Eq, vec![lit(1), r(1)]), "false"),
    ]);
}

#[test]
fn floats_follow_ieee_754_at_f64_and_round_once_at_f32() {
    // DESIGN.md L1.18: `f32` `+ - * /` round once to `f32`; comparisons are IEEE 754, so a NaN
    // is unordered and unequal to itself, and `0.0 == -0.0`.
    table(vec![
        ("f64 add", prim(Add, vec![f(0.5), f(0.25)]), "0.75"),
        ("f64 negate zero", prim(Neg, vec![f(0.0)]), "-0.0"),
        ("f64 NaN <", prim(Lt, vec![f(f64::NAN), f(1.0)]), "false"),
        (
            "f64 NaN ==",
            prim(Eq, vec![f(f64::NAN), f(f64::NAN)]),
            "false",
        ),
        (
            "f64 NaN !=",
            prim(Ne, vec![f(f64::NAN), f(f64::NAN)]),
            "true",
        ),
        ("f64 0 == -0", prim(Eq, vec![f(0.0), f(-0.0)]), "true"),
        (
            "f64 power",
            prim(Pow, vec![f(2.0), f(0.5)]),
            "1.4142135623730951",
        ),
        (
            "f64 max with NaN",
            prim(Max, vec![f(f64::NAN), f(1.0)]),
            "nan",
        ),
        ("f32 add", prim(Add, vec![f32_(0.5), f32_(0.25)]), "0.75f32"),
        ("f32 sub", prim(Sub, vec![f32_(0.5), f32_(0.25)]), "0.25f32"),
        (
            "f32 mul",
            prim(Mul, vec![f32_(0.5), f32_(0.25)]),
            "0.125f32",
        ),
        (
            "f32 div rounds once",
            prim(Div, vec![f32_(1.0), f32_(3.0)]),
            "0.33333334f32",
        ),
        ("f32 negate", prim(Neg, vec![f32_(1.5)]), "-1.5f32"),
        ("f32 <", prim(Lt, vec![f32_(1.0), f32_(2.0)]), "true"),
        ("f32 >=", prim(Ge, vec![f32_(1.0), f32_(2.0)]), "false"),
        ("f32 ==", prim(Eq, vec![f32_(1.0), f32_(1.0)]), "true"),
        (
            "f32 NaN <",
            prim(Lt, vec![f32_(f32::NAN), f32_(1.0)]),
            "false",
        ),
        ("f32 min", prim(Min, vec![f32_(1.0), f32_(2.0)]), "1.0f32"),
        (
            "f32 power by an f32",
            prim(Pow, vec![f32_(2.0), f32_(3.0)]),
            "8.0f32",
        ),
        (
            "f32 power by an int (DESIGN.md L1.17's arrow `f32 ^ int`)",
            prim(Pow, vec![f32_(2.0), lit(3)]),
            "8.0f32",
        ),
    ]);
}

#[test]
fn min_max_not_and_or_and_the_comparisons_of_non_numbers() {
    // DESIGN.md sec:order: strings by code point; tuples component by component, a proper
    // prefix first.
    table(vec![
        ("min", prim(Min, vec![lit(3), lit(2)]), "2"),
        ("max", prim(Max, vec![lit(3), lit(2)]), "3"),
        (
            "min of strings",
            prim(Min, vec![lit("b"), lit("a")]),
            "\"a\"",
        ),
        ("not", prim(Not, vec![lit(true)]), "false"),
        ("and", prim(And, vec![lit(true), lit(false)]), "false"),
        ("or", prim(Or, vec![lit(false), lit(true)]), "true"),
        ("string <", prim(Lt, vec![lit("a"), lit("b")]), "true"),
        ("string ==", prim(Eq, vec![lit("é"), lit("é")]), "true"),
        (
            "tuple <",
            prim(
                Lt,
                vec![
                    t(vec![Value::Int(1), Value::Int(2)]),
                    t(vec![Value::Int(1), Value::Int(3)]),
                ],
            ),
            "true",
        ),
        (
            "a proper prefix first",
            prim(
                Lt,
                vec![
                    t(vec![Value::Int(1)]),
                    t(vec![Value::Int(1), Value::Int(0)]),
                ],
            ),
            "true",
        ),
    ]);
}

#[test]
fn strings_concatenate_and_the_text_words_work_on_code_points() {
    table(vec![
        (
            "concat",
            prim(Concat, vec![lit("ab"), lit("cd")]),
            "\"abcd\"",
        ),
        ("concat empty", prim(Concat, vec![lit(""), lit("")]), "\"\""),
        ("len", prim(Len, vec![lit("héllo")]), "5"),
        ("len empty", prim(Len, vec![lit("")]), "0"),
        ("lower", prim(Lower, vec![lit("ÀB")]), "\"àb\""),
        ("upper", prim(Upper, vec![lit("àb")]), "\"ÀB\""),
        ("upper in full", prim(Upper, vec![lit("ß")]), "\"SS\""),
        (
            "trim Unicode space",
            prim(Trim, vec![lit("\u{2003} a \n")]),
            "\"a\"",
        ),
        ("trim to empty", prim(Trim, vec![lit("  ")]), "\"\""),
    ]);
}

#[test]
fn tuples_and_atoms_are_built_and_read() {
    // Keys count from 0 forward, so a negative index is out of bounds like one past the end.
    let pair = || t(vec![Value::Int(1), Value::Int(2)]);
    table(vec![
        ("tuple", prim(Tuple, vec![lit(1), lit("a")]), "(1, \"a\")"),
        ("empty tuple", prim(Tuple, vec![]), "()"),
        ("tuple get", prim(TupleGet, vec![pair(), lit(1)]), "2"),
        (
            "tuple get past the end",
            prim(TupleGet, vec![pair(), lit(5)]),
            "#outOfBounds",
        ),
        (
            "tuple get at -1",
            prim(TupleGet, vec![pair(), lit(-1)]),
            "#outOfBounds",
        ),
        (
            "at past the end",
            prim(At, vec![pair(), lit(5)]),
            "#outOfBounds",
        ),
        (
            "atom, empty payload",
            prim(Atom, vec![lit("e"), t(vec![])]),
            "#e()",
        ),
        (
            "atom, tuple payload",
            prim(Atom, vec![lit("e"), t(vec![]), lit(1)]),
            "#e(1)",
        ),
        (
            "atom, struct payload",
            prim(Atom, vec![lit("e"), t(vec![Value::str("p")]), lit(1)]),
            "#e(p: 1)",
        ),
    ]);
}

#[test]
fn sum_of_a_tuple_is_its_total_and_merges_its_failures() {
    // DESIGN.md L1.18: `sum` of a tuple is `0` for the empty tuple and merges the failures
    // among its components.
    table(vec![
        (
            "sum",
            prim(Sum, vec![t(vec![Value::Int(1), Value::Int(2)])]),
            "3",
        ),
        ("sum of ()", prim(Sum, vec![t(vec![])]), "0"),
        (
            "sum of floats",
            prim(
                Sum,
                vec![t(vec![
                    Value::float(0.1),
                    Value::float(0.2),
                    Value::float(0.3),
                ])],
            ),
            "0.6000000000000001",
        ),
        (
            "an atom in the sum",
            prim(Sum, vec![t(vec![Value::Int(1), Value::atom("missing")])]),
            "#missing",
        ),
        (
            "two atoms in the sum",
            prim(
                Sum,
                vec![t(vec![Value::atom("a"), Value::Int(1), Value::atom("b")])],
            ),
            "#errs({#a, #b})",
        ),
    ]);
}

#[test]
fn numeric_casts_are_exact_or_give_an_atom() {
    // DESIGN.md L1.18: numeric casts exact, `#inexact` or `#overflow`; `int` of an infinity
    // or the NaN is `#invalid`; `f64` of an int or a rat is the float equal to it.
    table(vec![
        ("int of 2.7", prim(CastInt, vec![f(2.7)]), "#inexact"),
        ("int of -2.7", prim(CastInt, vec![f(-2.7)]), "#inexact"),
        ("int of 2.0", prim(CastInt, vec![f(2.0)]), "2"),
        (
            "int of 1e20, past a word",
            prim(CastInt, vec![f(1e20)]),
            "100000000000000000000",
        ),
        ("int of NaN", prim(CastInt, vec![f(f64::NAN)]), "#invalid"),
        (
            "int of inf",
            prim(CastInt, vec![f(f64::INFINITY)]),
            "#invalid",
        ),
        ("int of 7r/2r", prim(CastInt, vec![q(7, 2)]), "#inexact"),
        ("int of \"12\"", prim(CastInt, vec![lit("12")]), "12"),
        ("rat of 0.5", prim(CastRat, vec![f(0.5)]), "1r/2r"),
        (
            "rat of \"-1r/3r\"",
            prim(CastRat, vec![lit("-1r/3r")]),
            "-1r/3r",
        ),
        ("f64 of 3", prim(CastF64, vec![lit(3)]), "3.0"),
        ("f64 of 1r/3r", prim(CastF64, vec![q(1, 3)]), "#inexact"),
        (
            "f64 of 2^53 + 1",
            prim(CastF64, vec![lit(9007199254740993i64)]),
            "#inexact",
        ),
        (
            "f64 of 10^20",
            prim(CastF64, vec![big()]),
            "100000000000000000000.0",
        ),
        ("f32 of 0.1", prim(CastF32, vec![f(0.1)]), "#inexact"),
    ]);
}

#[test]
fn show_writes_data_and_passes_an_atom_through() {
    table(vec![
        ("an int", prim(Show, vec![lit(12)]), "\"12\""),
        ("a float", prim(Show, vec![f(0.1)]), "\"0.1\""),
        ("a rat", prim(Show, vec![q(1, 3)]), "\"1r/3r\""),
        ("a string", prim(Show, vec![lit("a")]), "\"a\""),
        (
            "a tuple",
            prim(Show, vec![t(vec![Value::Int(1), Value::str("a")])]),
            "\"(1, \\\"a\\\")\"",
        ),
        ("an atom", prim(Show, vec![atom("q")]), "#q"),
    ]);
}

#[test]
fn a_failure_atom_passes_through_every_primitive_but_tuple_atom_eq_and_ne() {
    // DESIGN.md sec:failure and L1.18: a primitive given an atom returns it; given several,
    // their merge; `==` and `!=` compare atoms as data and `Tuple` stores them.
    table(vec![
        (
            "left of +",
            prim(Add, vec![atom("missing"), lit(1)]),
            "#missing",
        ),
        (
            "right of +",
            prim(Add, vec![lit(1), atom("missing")]),
            "#missing",
        ),
        (
            "two atoms",
            prim(Add, vec![atom("a"), atom("b")]),
            "#errs({#a, #b})",
        ),
        (
            "one atom twice",
            prim(Add, vec![atom("a"), atom("a")]),
            "#a",
        ),
        ("++", prim(Concat, vec![lit("a"), atom("m")]), "#m"),
        ("len", prim(Len, vec![atom("m")]), "#m"),
        ("a cast", prim(CastInt, vec![atom("m")]), "#m"),
        ("tuple get", prim(TupleGet, vec![atom("m"), lit(0)]), "#m"),
        ("an if condition", if_(atom("c"), lit(1), lit(2)), "#c"),
        ("==", prim(Eq, vec![atom("a"), atom("a")]), "true"),
        ("!= with an int", prim(Ne, vec![atom("a"), lit(1)]), "true"),
        ("tuple", prim(Tuple, vec![atom("a"), lit(1)]), "(#a, 1)"),
        ("applied", app(atom("x"), vec![lit(1)]), "#x"),
    ]);
}

#[test]
fn applying_a_family_reads_its_entry() {
    table(vec![
        ("count", prim(Count, vec![one_entry()]), "1"),
        (
            "get, no entry",
            prim(Get, vec![one_entry(), lit(5)]),
            "#notFound",
        ),
        ("applied", app(one_entry(), vec![lit(1)]), "2"),
        (
            "applied, no entry",
            app(one_entry(), vec![lit(3)]),
            "#notFound",
        ),
    ]);
}

#[test]
fn match_takes_the_first_arm_whose_pattern_matches() {
    table(vec![
        (
            "a wildcard",
            Term::Match(rc(lit(3)), vec![(Pattern::Wild, lit("w"))]),
            "\"w\"",
        ),
        (
            "any atom before a wildcard",
            Term::Match(
                rc(atom("q")),
                vec![(Pattern::AnyAtom, lit("any")), (Pattern::Wild, lit("w"))],
            ),
            "\"any\"",
        ),
        (
            "a named field",
            Term::Match(
                rc(prim(Atom, vec![lit("e"), t(vec![Value::str("p")]), lit(1)])),
                vec![(
                    Pattern::Fields("e".into(), vec![("p".into(), Pattern::Bind("v".into()))]),
                    var("v"),
                )],
            ),
            "1",
        ),
    ]);
}

#[test]
fn an_ill_typed_application_is_reported_as_a_compiler_bug_naming_it() {
    // The checker never lets these through (DESIGN.md L1.17: anything but one kind on both
    // sides of an operator is a type error), so meeting one is a bug in zedc.
    table(vec![
        (
            "int + String",
            prim(Add, vec![lit(1), lit("a")]),
            "error: `+` applied to `int`, `String`",
        ),
        (
            "! of an int",
            prim(Not, vec![lit(1)]),
            "error: `!` applied to `int`",
        ),
        (
            "int < f64",
            prim(Lt, vec![lit(1), f(2.0)]),
            "error: `<` applied to `int`, `f64`",
        ),
        (
            "min of int and String",
            prim(Min, vec![lit(1), lit("a")]),
            "error: `min` applied to `int`, `String`",
        ),
        (
            "`/` of ints, which has no int arrow",
            prim(Div, vec![lit(7), lit(2)]),
            "error: `/` applied to `int`, `int`",
        ),
        (
            "an int power by a negative int",
            prim(Pow, vec![lit(2), lit(-1)]),
            "error: `^` applied to `int`, `int`",
        ),
        (
            "a sum of two kinds",
            prim(Sum, vec![t(vec![Value::Int(1), Value::float(0.5)])]),
            "error: `+` applied to `int`, `f64`",
        ),
        (
            "int of a tuple",
            prim(CastInt, vec![t(vec![])]),
            "error: `int` applied to `(..)`",
        ),
        (
            "a match no arm takes",
            Term::Match(rc(lit(3)), vec![(Pattern::Lit(Value::Int(4)), lit("w"))]),
            "error: no arm matches a value of type `int`",
        ),
        (
            "an int applied",
            app(lit(3), vec![lit(1)]),
            "error: a value of type `int` is not a function",
        ),
        (
            "a lambda given too few arguments",
            app(lam(&["a", "b"], lit(1)), vec![lit(1)]),
            "error: a function of 2 parameters called with 1 arguments",
        ),
        (
            "a lambda given too many arguments",
            app(lam(&["a"], lit(1)), vec![lit(1), lit(2)]),
            "error: a function of 1 parameters called with 2 arguments",
        ),
    ]);
}

#[test]
fn the_remaining_operand_kinds_of_arithmetic_order_and_reads() {
    // DESIGN.md L1.17-L1.18 and sec:linalg: `sqrt` is IEEE 754 `squareRoot` at each float
    // width; NaN in gives NaN out, `pow` included; `f32 ^ int` is the one arrow between two
    // carriers. sec:reduction: of two tuples the first component in which they differ decides
    // `min` and `max`. sec:type_language, the `m[k]` row: a tuple's keys are `0..<n`, so any
    // other key, a big integer or a string included, misses with `#outOfBounds`, as a key a
    // proven interval family lacks does.
    let pair = || t(vec![Value::Int(1), Value::Int(2)]);
    let other = || t(vec![Value::Int(1), Value::Int(3)]);
    // NaN at `f32`, as `0 / 0` gives it.
    let nan32 = run(&prim(Div, vec![f32_(0.0), f32_(0.0)]));
    let nan32 = nan32.as_str();
    table(vec![
        ("rat subtract", prim(Sub, vec![r(1), q(1, 3)]), "2r/3r"),
        ("f64 sqrt", prim(Sqrt, vec![f(2.25)]), "1.5"),
        ("f64 sqrt of -0", prim(Sqrt, vec![f(-0.0)]), "-0.0"),
        ("f64 sqrt of -1", prim(Sqrt, vec![f(-1.0)]), "nan"),
        ("f32 sqrt", prim(Sqrt, vec![f32_(2.25)]), "1.5f32"),
        ("f64 NaN ^ 0", prim(Pow, vec![f(f64::NAN), f(0.0)]), "nan"),
        ("f64 1 ^ NaN", prim(Pow, vec![f(1.0), f(f64::NAN)]), "nan"),
        (
            "f32 NaN ^ 0",
            prim(Pow, vec![f32_(f32::NAN), f32_(0.0)]),
            nan32,
        ),
        (
            "f32 NaN ^ int",
            prim(Pow, vec![f32_(f32::NAN), lit(0)]),
            nan32,
        ),
        (
            "f32 -1 ^ an even exponent past 2^53",
            prim(Pow, vec![f32_(-1.0), big()]),
            "1.0f32",
        ),
        (
            "f32 -1 ^ an odd exponent past 2^53",
            prim(Pow, vec![f32_(-1.0), prim(Add, vec![big(), lit(1)])]),
            "-1.0f32",
        ),
        (
            "f32 2 ^ a negative exponent past 2^53",
            prim(Pow, vec![f32_(2.0), prim(Neg, vec![big()])]),
            "0.0f32",
        ),
        ("f64 <=", prim(Le, vec![f(1.0), f(1.0)]), "true"),
        ("f64 >", prim(Gt, vec![f(1.0), f(2.0)]), "false"),
        ("f32 <=", prim(Le, vec![f32_(2.0), f32_(1.0)]), "false"),
        ("f32 >", prim(Gt, vec![f32_(2.0), f32_(1.0)]), "true"),
        ("int <=", prim(Le, vec![lit(2), lit(2)]), "true"),
        ("min of tuples", prim(Min, vec![other(), pair()]), "(1, 2)"),
        ("max of tuples", prim(Max, vec![pair(), other()]), "(1, 3)"),
        (
            "tuple get at a big integer",
            prim(TupleGet, vec![pair(), big()]),
            "#outOfBounds",
        ),
        (
            "tuple get at a string",
            prim(TupleGet, vec![pair(), lit("a")]),
            "#outOfBounds",
        ),
        ("at in bounds", prim(At, vec![pair(), lit(0)]), "1"),
        (
            "at a key the family lacks",
            prim(At, vec![one_entry(), lit(5)]),
            "#outOfBounds",
        ),
        (
            "at a key the family has",
            prim(At, vec![one_entry(), lit(1)]),
            "2",
        ),
    ]);
}
