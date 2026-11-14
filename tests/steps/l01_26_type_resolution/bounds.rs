//! The bounds clause `t for X in t1 | … | tn` (DESIGN.md sec:type_language, step L1.26): `X`
//! is a type variable in scope in `t`, its bound is resolved outside it, and the function type
//! that holds every use of `X` takes one carrier of the bound for it at each call.

use super::{info, sig, type_errors};
use zed_tests::step_helpers::l01_10_lambdas_types_else_tuples::sx;
use zed_tests::step_helpers::l01_13_formatter::fmt;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zedc::ast::unit;
use zedc::check::read::parse_type;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

/// The resolution errors of the unit `text`, each `message [text]`, each note after it as
/// `; note [text]`.
fn resolve_errors(text: &str) -> Vec<String> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let Err(es) = resolve(&stmts) else {
        return Vec::new();
    };
    es.iter()
        .map(|e| {
            let mut out = format!("{} [{}]", e.message, &text[e.span.start..e.span.end]);
            for n in &e.notes {
                out += &format!("; {} [{}]", n.text, &text[n.span.start..n.span.end]);
            }
            out
        })
        .collect()
}

/// A function that applies a bounded function to an int and to an f64.
const TWICE: &str =
    "twice(positional v: int, g: (x: T) -> T for T in int | f64) = g(x: g(x: v));\n";

#[test]
fn the_clause_parses_loosest() {
    let cases = [
        (
            "f is ((T) -> T for T in int)",
            "(is f (for (-> (T) T) (T int)))",
        ),
        (
            "f is ((T, U) -> T for T in int | f64, U in String)",
            "(is f (for (-> (T U) T) (T (| int f64)) (U String)))",
        ),
        // The clause binds looser than the arrow, and the bound is a union of carriers.
        (
            "f is (T -> T -> T for T in int | rat)",
            "(is f (for (-> (T) (-> (T) T)) (T (| int rat))))",
        ),
        // A clause inside another, in a parameter's parentheses.
        (
            "f is (((T) -> T for T in int) -> U for U in bool)",
            "(is f (for (-> ((for (-> (T) T) (T int))) U) (U bool)))",
        ),
        // `is` takes a union, so an unparenthesized clause does not parse.
        ("f is (T) -> T for T in int", "syntax"),
        ("f is ((T) -> T for T int)", "syntax"),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = sx(text);
            (got != want).then(|| format!("{text}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_variable_bounded_twice_in_one_clause_is_an_error() {
    let text = "f is ((T) -> T for T in int, T in f64)";
    assert!(sx(text).starts_with("error: "), "{}", sx(text));
    assert!(
        sx(text).contains("the type variable `T` is bounded twice"),
        "{}",
        sx(text)
    );
}

#[test]
fn the_formatter_writes_the_clause_and_parenthesizes_it_inside_tighter_forms() {
    for text in [
        TWICE,
        "f(g: (T, U) -> T for T in int | f64, U in String) = 0;\n",
        "f(g: (T -> T for T in int) -> U for U in bool) = 0;\n",
        "f(g: ((T -> T for T in int), int)) = 0;\n",
        "f(g: ((T -> T for T in rat),)) = 0;\n",
        "y = 1 is (T -> T for T in int) | int;\n",
    ] {
        assert_eq!(fmt(text), text);
    }
    // Parentheses the grammar needs stay; others go.
    assert_eq!(
        fmt("f(g: (((T) -> T) for T in int)) = 0;\n"),
        "f(g: T -> T for T in int) = 0;\n"
    );
    // A clause before a comma is parenthesized, so a reader sees where it ends.
    assert_eq!(
        fmt("f(g: (T -> T for T in int, int)) = 0;\n"),
        "f(g: ((T -> T for T in int), int)) = 0;\n"
    );
    assert_eq!(
        fmt("f(g: (T -> T for T in rat,)) = 0;\n"),
        "f(g: ((T -> T for T in rat),)) = 0;\n"
    );
}

#[test]
fn a_bounded_function_type_is_checked_at_each_call() {
    let neg = format!("{TWICE}neg(x) = -x;\ny = twice(3, g: neg);\n");
    assert!(type_errors(&neg).is_empty(), "{:?}", type_errors(&neg));
    assert_eq!(value(&neg, "y"), "3");
    // One carrier, and several variables.
    let one = "h(g: (x: T) -> T for T in rat) = 0;\n";
    assert!(type_errors(one).is_empty(), "{:?}", type_errors(one));
    let two = "h(g: (a: T, b: U) -> T for T in int | f64, U in String) = g(a: 2, b: \"s\");\n";
    assert!(type_errors(two).is_empty(), "{:?}", type_errors(two));
}

#[test]
fn a_call_outside_the_bound_is_an_error() {
    let errors = type_errors("h(g: (x: T) -> T for T in int | f64) = g(x: \"s\");\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].ends_with("[g(x: \"s\")]"), "{errors:?}");
    let errors = type_errors("h(g: (a: T, b: U) -> T for T in int, U in bool) = g(a: 2, b: 3);\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
}

#[test]
fn the_signature_holds_the_bound() {
    assert_eq!(
        sig(TWICE, "twice"),
        "(int, g: (x: T) -> T for T in int | f64) -> int"
    );
}

#[test]
fn an_unbounded_name_is_an_error() {
    assert_eq!(
        resolve_errors("f(g: (T) -> U for T in int) = 0;\n"),
        [
            "The type `U` is not defined. [U]; a type variable is bounded by the clause after its \
             type, as `for U in int | f64`; this clause does not bound `U` \
             [(T) -> U for T in int]"
        ]
    );
}

#[test]
fn a_bound_on_a_variable_the_type_does_not_hold_is_an_error() {
    assert_eq!(
        resolve_errors("f(g: (T) -> T for T in int, U in f64) = 0;\n"),
        [
            "the bound names `U`, and the type before `for` does not hold `U`, so the bound \
             constrains nothing. Remove the bound, or write `U` in the type. [U]; \
             the type [(T) -> T]"
        ]
    );
}

#[test]
fn a_repeated_variable_is_an_error() {
    assert_eq!(
        resolve_errors("f(g: ((T) -> T for T in int) -> T for T in f64) = 0;\n"),
        [
            "the type variable `T` is bounded twice, and a type variable has one bound. Remove one of the two bounds. [T]; the first bound of `T` [T]"
        ]
    );
}

#[test]
fn a_bound_that_is_no_union_of_carriers_is_an_error() {
    let cases = [
        (
            "f(g: (T) -> T for T in #a) = 0;\n",
            "the bound of `T` is not a union of carriers: `#a` is an atom, no carrier; \
             the carriers are int, f32, f64, rat, String, bool [#a]",
        ),
        (
            "f(g: (T) -> T for T in int | (int, int)) = 0;\n",
            "the bound of `T` is not a union of carriers: this type is no carrier; \
             the carriers are int, f32, f64, rat, String, bool [(int, int)]",
        ),
        (
            "f(g: (T) -> T for T in Lines) = 0;\n",
            "the bound of `T` is not a union of carriers: `Lines` is no carrier; \
             the carriers are int, f32, f64, rat, String, bool [Lines]",
        ),
        // A bound is read outside its clause, so a variable of the same clause is no name there.
        (
            "f(g: (T, U) -> T for T in int, U in T) = 0;\n",
            "the bound of `U` is not a union of carriers: `T` is no carrier; \
             the carriers are int, f32, f64, rat, String, bool [T]",
        ),
        (
            "f(g: ((U) -> U for U in T) -> T for T in int) = 0;\n",
            "the bound of `U` is not a union of carriers: `T` is a type variable; \
             the carriers are int, f32, f64, rat, String, bool [T]",
        ),
    ];
    for (text, want) in cases {
        let got = resolve_errors(text);
        assert_eq!(got.len(), 1, "{text}: {got:?}");
        assert!(got[0].starts_with(want), "{text}: {got:?}");
    }
}

#[test]
fn a_variable_outside_one_function_type_is_an_error() {
    let outside = resolve_errors("f(x: T for T in int) = x;\n");
    assert_eq!(outside.len(), 1, "{outside:?}");
    assert!(
        outside[0].starts_with("the bounded variable `T` stands outside a function type"),
        "{outside:?}"
    );
    let two = resolve_errors("f(g: ((T) -> T, (T) -> int) for T in int) = 0;\n");
    assert_eq!(two.len(), 1, "{two:?}");
    assert!(
        two[0].starts_with("the bounded variable `T` stands in two function types"),
        "{two:?}"
    );
}

#[test]
fn an_is_test_of_a_bounded_type_is_an_error() {
    let errors = elab_errors("f(x) = x;\ny = f is ((T) -> T for T in int);\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("this `is` test names a type with the bounded variable `T`; "),
        "{errors:?}"
    );
}

/// The elaboration errors of the unit `text`.
fn elab_errors(text: &str) -> Vec<String> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    match zedc::elab::elaborate(&stmts, &res) {
        Ok(_) => Vec::new(),
        Err(es) => es.iter().map(|e| e.message.clone()).collect(),
    }
}

#[test]
fn a_printed_bounded_type_reads_back() {
    // The printer writes a function type in parentheses only where the grammar needs them
    // (DESIGN.md sec:grammar); what it writes reads back to the same type.
    for (text, want) in [
        ("(T) -> T for T in int | f64", "T -> T for T in int | f64"),
        (
            "(T, U) -> T for T in int, U in String | bool",
            "(T, U) -> T for T in int, U in bool | String",
        ),
        (
            "((T) -> T for T in rat) -> int",
            "(T -> T for T in rat) -> int",
        ),
    ] {
        let first = parse_type(text).unwrap_or_else(|e| panic!("{e}"));
        let printed = first.to_string();
        assert_eq!(printed, want);
        let again = parse_type(&printed).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(again, first, "{text}");
        assert_eq!(again.to_string(), printed);
    }
}

#[test]
fn a_bounded_signature_printed_and_read_back_is_the_same_type() {
    for text in [
        // A clause of every carrier, one of a variable only in the result, and one per
        // signature of a tuple and of a union.
        "(a: T, b: T) -> bool for T in int | f32 | f64 | rat | String | bool",
        "() -> T for T in int | f64",
        "((x: T) -> T for T in rat, (y: U) -> String for U in String | bool)",
        "((x: T) -> T for T in int) | int",
        // A clause on a function parameter of a bounded signature, and two variables of one
        // clause in written order other than the printer's.
        "(g: ((x: U) -> U for U in f64), y: T) -> T for T in int | rat",
        "(b: U, a: T) -> U for U in bool, T in int",
    ] {
        let first = parse_type(text).unwrap_or_else(|e| panic!("{e}"));
        let printed = first.to_string();
        let again = parse_type(&printed).unwrap_or_else(|e| panic!("{text}: {printed}: {e}"));
        assert_eq!(again, first, "{text} printed {printed}");
        assert_eq!(again.to_string(), printed, "{text}");
    }
    // The checker's own signatures, bounded on a parameter, read back to one signature that
    // prints as the text printed (a type, unlike a signature alone, is printed in parentheses).
    for (src, name) in [(P, "p_wide"), (L, "two"), (L, "mix"), (R, "r2")] {
        let printed = sig(src, name);
        let again = parse_type(&printed).unwrap_or_else(|e| panic!("{printed}: {e}"));
        assert_eq!(again.fns.len(), 1, "{printed}");
        assert_eq!(again.fns[0].to_string(), printed, "{name}");
    }
}

/// A signature of `n` parameters, each of its own variable, with the clause bounding all `n`.
pub(super) fn many_bounds(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("x{i}: T{i}")).collect();
    let bs: Vec<String> = (0..n)
        .map(|i| format!("T{i} in {}", ["int | f64", "String", "rat | bool"][i % 3]))
        .collect();
    format!("({}) -> T0 for {}", ps.join(", "), bs.join(", "))
}

/// A signature of `n` parameters, parameter `i` taking `(Bi,) | (T,)` with `Bi` bounded to
/// `int | f64` and `T` free, one variable for all (written at least twice, so `n` is 2 or more), returning `(B{n-1},)`; and the signature that passes `(String,)`
/// to each parameter but the last, `(int,)` to the last, and returns `result`. A `(String,)`
/// is held by `(T,)` alone, since `Bi`'s bound does not hold `String`
/// (FAIL-types-overload-bounded-tuple), so the first fits the second exactly when `result`
/// holds `(int,)`.
pub(super) fn bounded_or_free(n: usize, result: &str) -> (String, String) {
    let ps: Vec<String> = (0..n).map(|i| format!("x{i}: (B{i},) | (T,)")).collect();
    let bs: Vec<String> = (0..n).map(|i| format!("B{i} in int | f64")).collect();
    let qs: Vec<String> = (0..n)
        .map(|i| format!("x{i}: ({},)", if i + 1 == n { "int" } else { "String" }))
        .collect();
    (
        format!("({}) -> (B{},) for {}", ps.join(", "), n - 1, bs.join(", ")),
        format!("({}) -> {result}", qs.join(", ")),
    )
}

/// `bounded_or_free` at small sizes: each `(String,)` skips the bounded shape for the free one,
/// and the last parameter binds `B{n-1}` to `int`, which the result `(f64,)` does not hold.
#[test]
fn a_bounded_variable_beside_a_free_one_takes_only_what_its_bound_holds() {
    use zedc::check::ty::{fits_sig, why_unfit};
    // From n = 2: `T` written once would not be read as a variable.
    for n in 2..=5 {
        for (result, fits) in [
            ("(int,)", true),
            ("(int,) | (String,)", true),
            ("(f64,)", false),
        ] {
            let (s, q) = bounded_or_free(n, result);
            let s = parse_type(&s).unwrap_or_else(|e| panic!("{e}"));
            let q = parse_type(&q).unwrap_or_else(|e| panic!("{e}"));
            let (s, q) = (&s.fns[0], &q.fns[0]);
            assert_eq!(fits_sig(s, q), fits, "{q} in {s}");
            if fits {
                assert_eq!(why_unfit(s, q), None, "{q} in {s}");
            }
        }
    }
}

/// A signature of `n` parameters, parameter `i` taking `(Ti,) | ({other},)` with `Ti` free,
/// returning `(T0, ..., T(n-1))`; and the same under the names `Ui`, with `{given}` for
/// `{other}`. The result puts a ceiling on each `Ti`, `Ui`, so `(Ui,)` binds `Ti` and
/// `({given},)` is left to `({other},)` where `{other}` holds it
/// (FAIL-types-first-shape-unbounded): the first fits the second exactly then.
pub(super) fn free_beside_a_carrier(n: usize, other: &str, given: &str) -> (String, String) {
    let sig = |v: &str, k: &str| {
        let ps: Vec<String> = (0..n)
            .map(|i| format!("x{i}: ({v}{i},) | ({k},)"))
            .collect();
        let rs: Vec<String> = (0..n).map(|i| format!("{v}{i}")).collect();
        let comma = if n == 1 { "," } else { "" };
        format!("({}) -> ({}{comma})", ps.join(", "), rs.join(", "))
    };
    (sig("T", other), sig("U", given))
}

/// One parameter taking `(T0, ..., T(n-1)) | ({other}, ..., {other})` with each `Ti` free,
/// returning `(T0, ..., T(n-1))`; and the same under the names `Ui`, with `{given}` for
/// `{other}`. As [`free_beside_a_carrier`], in one tuple of `n` places: one shape searched.
pub(super) fn free_in_one_tuple(n: usize, other: &str, given: &str) -> (String, String) {
    let sig = |v: &str, k: &str| {
        let comma = if n == 1 { "," } else { "" };
        let vs: Vec<String> = (0..n).map(|i| format!("{v}{i}")).collect();
        let ks = vec![k; n];
        let (vs, ks) = (vs.join(", "), ks.join(", "));
        format!("(x0: ({vs}{comma}) | ({ks}{comma})) -> ({vs}{comma})")
    };
    (sig("T", other), sig("U", given))
}

/// A signature of one parameter taking the atom `#p` of `n` components, component `i` the
/// variable `Bi` bounded to `int | f64`, returning `(B0, ..., B(n-1))`, and the same under
/// the names `Ci`, bounded to `bound`. Each `Ci` is read under a new name, in the payload too
/// (FAIL-types-payload-vars-unread), so the first fits the second exactly where `bound` is
/// within `int | f64`.
pub(super) fn bounded_in_a_payload(n: usize, bound: &str) -> (String, String) {
    let sig = |v: &str, m: &str| {
        let vs: Vec<String> = (0..n).map(|i| format!("{v}{i}")).collect();
        let bs: Vec<String> = (0..n).map(|i| format!("{v}{i} in {m}")).collect();
        let comma = if n == 1 { "," } else { "" };
        format!(
            "(x0: #p({})) -> ({}{comma}) for {}",
            vs.join(", "),
            vs.join(", "),
            bs.join(", ")
        )
    };
    (sig("B", "int | f64"), sig("C", bound))
}

/// `free_beside_a_carrier`, `free_in_one_tuple` and `bounded_in_a_payload` at small sizes, both
/// ways of each boundary.
#[test]
fn free_and_bounded_variables_fit_themselves_under_other_names() {
    use zedc::check::ty::fits_sig;
    let fits = |(s, q): (String, String)| {
        let s = parse_type(&s).unwrap_or_else(|e| panic!("{e}"));
        let q = parse_type(&q).unwrap_or_else(|e| panic!("{e}"));
        fits_sig(&s.fns[0], &q.fns[0])
    };
    for n in 1..=4 {
        for (other, given, want) in [
            ("int", "int", true),
            ("int", "1", true),
            ("int | String", "String", true),
            ("int", "String", false),
        ] {
            let pair = free_beside_a_carrier(n, other, given);
            assert_eq!(fits(pair.clone()), want, "{pair:?}");
            let pair = free_in_one_tuple(n, other, given);
            assert_eq!(fits(pair.clone()), want, "{pair:?}");
        }
        for (bound, want) in [("int | f64", true), ("int", true), ("int | String", false)] {
            let pair = bounded_in_a_payload(n, bound);
            assert_eq!(fits(pair.clone()), want, "{pair:?}");
        }
    }
}

#[test]
fn the_checker_reads_a_one_tuple_and_a_morphism_type() {
    let one = "f(p: (int,)) = p;\n";
    assert_eq!(sig(one, "f"), "(p: (int,)) -> (int,)");
    let morphism = "f(m: int .. int -> bool) = 0;\n";
    assert!(
        type_errors(morphism).is_empty(),
        "{:?}",
        type_errors(morphism)
    );
    let (info, _) = info(morphism);
    assert_eq!(info.sigs.len(), 1);
}

#[test]
fn an_argument_must_take_every_carrier_of_the_bound() {
    // A call of `twice` may bind `T` to int or to f64, so its argument takes both.
    let shout = format!("{TWICE}shout(x) = upper(x) ++ \"!\";\ny = twice(3, g: shout);\n");
    assert_eq!(
        type_errors(&shout),
        [
            "`shout` is `(x: String) -> String`, not `(x: T) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. [shout]"
        ]
    );
    let inc = format!("{TWICE}inc(x: int) = x + 1;\ny = twice(3, g: inc);\n");
    assert_eq!(
        type_errors(&inc),
        [
            "`inc` is `(x: int) -> int`, not `(x: T) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. [inc]"
        ]
    );
    let neg = format!("{TWICE}neg(x) = -x;\ny = twice(3, g: neg);\n");
    assert!(type_errors(&neg).is_empty(), "{:?}", type_errors(&neg));
}

/// A function whose parameter `g` takes `n` arguments, each of its own bounded variable, and
/// that calls `g` once.
pub(super) fn wide(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("x{i}: T{i}")).collect();
    let bs: Vec<String> = (0..n).map(|i| format!("T{i} in int | f64")).collect();
    let args: Vec<String> = (0..n)
        .map(|i| match i % 2 {
            0 => format!("x{i}: 1"),
            _ => format!("x{i}: 1.5"),
        })
        .collect();
    format!(
        "h(g: ({}) -> T0 for {}) = g({});\n",
        ps.join(", "),
        bs.join(", "),
        args.join(", ")
    )
}

/// `n` bounds clauses nested in the parameter of a function type.
pub(super) fn nested(n: usize) -> String {
    let mut t = "(".repeat(n - 1);
    t.push_str("T0 -> T0 for T0 in int");
    for i in 1..n {
        t.push_str(&format!(") -> T{i} for T{i} in f64"));
    }
    format!("h(g: {t}) = 0;\n")
}

/// A function that passes its argument, of `n` parameters each of its own variable bounded by
/// int and f64, where one bounded by int alone is expected.
pub(super) fn passed(n: usize) -> String {
    let ps = |v: &str| -> String {
        let ps: Vec<String> = (0..n).map(|i| format!("x{i}: {v}{i}")).collect();
        ps.join(", ")
    };
    let bs = |v: &str, b: &str| -> String {
        let bs: Vec<String> = (0..n).map(|i| format!("{v}{i} in {b}")).collect();
        bs.join(", ")
    };
    format!(
        "p(g: ({}) -> T0 for {}) = 0;\nq(f: ({}) -> U0 for {}) = p(g: f);\n",
        ps("T"),
        bs("T", "int"),
        ps("U"),
        bs("U", "int | f64")
    )
}

/// `p` calls its argument on an int; `p_wide` on an int and on an f64.
const P: &str = "p(g: (x: T) -> T for T in int) = g(x: 1);\n\
                 p_wide(g: (x: T) -> T for T in int | f64) = g(x: 1.5);\n";

#[test]
fn a_bounded_function_passes_where_its_bound_holds_the_expected_one() {
    // `f` takes int and f64, so it serves where only int is asked, whatever its variable's name.
    for q in [
        "q(f: (x: T) -> T for T in int | f64) = p(g: f);\n",
        "q(f: (x: U) -> U for U in int | f64) = p(g: f);\n",
        "q(f: (x: U) -> U for U in int | f64) = p_wide(g: f);\n",
        "q(f: (x: T) -> T for T in int | f64) = p_wide(g: f);\n",
    ] {
        let text = format!("{P}{q}");
        assert!(
            type_errors(&text).is_empty(),
            "{q}: {:?}",
            type_errors(&text)
        );
    }
    let text = format!("{P}q(f: (x: U) -> U for U in int | f64) = p_wide(g: f);\n");
    assert_eq!(
        sig(&text, "q"),
        "(f: (x: U) -> U for U in int | f64) -> f64"
    );
}

#[test]
fn a_bounded_function_does_not_pass_where_more_carriers_are_asked() {
    // `p_wide` calls `g` on an f64, which `f` does not take.
    for q in [
        "q(f: (x: T) -> T for T in int) = p_wide(g: f);\n",
        "q(f: (x: U) -> U for U in int) = p_wide(g: f);\n",
        "q(f: (x: U) -> U for U in int | rat) = p_wide(g: f);\n",
    ] {
        let text = format!("{P}{q}");
        let errors = type_errors(&text);
        assert_eq!(errors.len(), 1, "{q}: {errors:?}");
        assert!(errors[0].ends_with("[p_wide(g: f)]"), "{q}: {errors:?}");
    }
}

#[test]
fn a_function_of_one_carrier_is_the_function_bounded_by_it() {
    let q = format!("{P}q(f: (x: int) -> int) = p(g: f);\n");
    assert!(type_errors(&q).is_empty(), "{:?}", type_errors(&q));
    let inc = format!("{P}inc(x: int) = x + 1;\ny = p(g: inc);\n");
    assert!(type_errors(&inc).is_empty(), "{:?}", type_errors(&inc));
    assert_eq!(value(&inc, "y"), "2");
    // Of two carriers, a function of one does not do; nor does one that takes both but
    // returns either, since the caller's `T` is the carrier it passed.
    let narrow = format!("{P}q(f: (x: int) -> int) = p_wide(g: f);\n");
    assert_eq!(type_errors(&narrow).len(), 1, "{:?}", type_errors(&narrow));
    let either = format!("{P}q(f: (x: int | f64) -> int | f64) = p_wide(g: f);\n");
    assert_eq!(type_errors(&either).len(), 1, "{:?}", type_errors(&either));
    let test = "t(g: (x: T) -> bool for T in int | f64) = g(x: 2);\n\
                q(f: (x: int | f64) -> bool) = t(g: f);\n";
    assert!(type_errors(test).is_empty(), "{:?}", type_errors(test));
}

#[test]
fn a_bounded_variable_only_in_the_result_gives_its_whole_bound() {
    let text = "h(g: () -> T for T in int | f64) = g();\n";
    assert!(type_errors(text).is_empty(), "{:?}", type_errors(text));
    assert_eq!(
        sig(text, "h"),
        "(g: () -> T for T in int | f64) -> int | f64"
    );
}

#[test]
fn a_bounded_variable_in_a_parameter_that_is_a_function_is_checked_at_each_carrier() {
    // `p2` gives its argument a function on the carrier its caller picks.
    let p2 = "p2(g: ((x: T) -> T) -> T for T in int | f64) = 0;\n\
              p1(g: ((x: T) -> T) -> T for T in int) = 0;\n";
    let cases = [
        // Refused for now, though sound to take: `U` occurs only under a function parameter,
        // where `fits_sig` binds no variable of the outer function (STATUS, TYPE-forms).
        (
            "q(f: ((x: U) -> U) -> U for U in int | f64) = p2(g: f);\n",
            1,
        ),
        ("q(f: ((x: int) -> int) -> int) = p1(g: f);\n", 0),
        // At f64, `f` would get a function on f64, which it does not take.
        ("q(f: ((x: int) -> int) -> int) = p2(g: f);\n", 1),
        ("q(f: ((x: U) -> U) -> U for U in int) = p2(g: f);\n", 1),
        // A generic function with no bound takes every carrier.
        ("id(x) = x;\ny = p_wide(g: id);\n", 0),
    ];
    for (q, n) in cases {
        let text = format!("{P}{p2}{q}");
        assert_eq!(type_errors(&text).len(), n, "{q}: {:?}", type_errors(&text));
    }
}

/// Functions whose bounded variable no parameter holds: no argument fixes its carrier, so
/// each returns a value of some carrier of the bound.
const R: &str = "r(g: () -> T for T in int | f64) = g();\n\
                 r2(g: (x: T) -> U for T in int, U in int | f64) = 0;\n\
                 r3(g: (x: T) -> U for T in int, U in int) = 0;\n";

#[test]
fn a_function_whose_bounded_variable_is_only_in_its_result_passes_as_itself() {
    let cases = [
        // The value has exactly the expected type.
        ("k(f: () -> T for T in int | f64) = r(g: f);\n", 0),
        (
            "k(f: (x: T) -> U for T in int, U in int | f64) = r2(g: f);\n",
            0,
        ),
        // A narrower function: int is within int | f64.
        ("k(f: (x: int) -> int) = r2(g: f);\n", 0),
        ("k(f: () -> int) = r(g: f);\n", 0),
        ("k(f: () -> T for T in f64) = r(g: f);\n", 0),
        ("y = r(g: () -> 1);\n", 0),
        ("y = r(g: () -> 1.5);\n", 0),
        // A result outside the bound, and a bound wider than the expected one.
        ("k(f: () -> String) = r(g: f);\n", 1),
        ("y = r(g: () -> \"s\");\n", 1),
        ("k(f: () -> T for T in int | rat) = r(g: f);\n", 1),
        (
            "k(f: (x: T) -> U for T in int, U in int | f64) = r3(g: f);\n",
            1,
        ),
    ];
    for (k, n) in cases {
        let text = format!("{R}{k}");
        assert_eq!(type_errors(&text).len(), n, "{k}: {:?}", type_errors(&text));
    }
    let text = format!("{R}y = r(g: () -> 1);\n");
    assert_eq!(value(&text, "y"), "1");
}

#[test]
fn a_lambda_outside_a_result_only_bound_names_the_whole_bound() {
    let errors = type_errors(&format!("{R}y = r(g: () -> \"s\");\n"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("the lambda returns \"s\"") && errors[0].contains("returns int | f64"),
        "{errors:?}"
    );
}

/// `p` and `q` both take a function of type `t` nested `n` deep, `(h: … (x: int) -> int …)
/// -> int`, each level's result its own variable bounded by int when `bounded`; `q` passes its
/// argument to `p`.
pub(super) fn passed_deep(n: usize, bounded: bool) -> String {
    let mut t = String::from("(x: int) -> int");
    for i in 0..n {
        t = match bounded {
            false => format!("(h{i}: {t}) -> int"),
            true => format!("((h{i}: {t}) -> T{i} for T{i} in int)"),
        };
    }
    format!("p(g: {t}) = 0;\nq(f: {t}) = p(g: f);\n")
}

/// Functions with bounded variables passed where other bounded function types are expected.
const S: &str = "r(g: () -> T for T in int | f64) = g();\n\
                 need_int(x: int) = x;\n\
                 r4(g: (h: () -> T) -> int for T in int | f64) = 0;\n\
                 r5(g: (x: int) -> U for U in int | f64) = 0;\n";

#[test]
fn a_bounded_function_fits_only_where_each_carrier_it_returns_is_taken() {
    let cases = [
        // `r` returns an int or an f64, so its result is no int.
        ("z = need_int(x: r(g: () -> 1));\n", 1),
        ("k(f: () -> T for T in int | f64) = need_int(x: f());\n", 1),
        // The caller of `r4`'s argument passes `h` returning either carrier.
        ("k(f: (h: () -> int) -> int) = r4(g: f);\n", 1),
        // `f` returns the carrier it is given; `r5` asks for an int or an f64 back.
        ("k(f: (x: T) -> T for T in int | f64) = r5(g: f);\n", 0),
        ("k(f: (x: T) -> T for T in int | f64) = r(g: f);\n", 1),
        ("k(f: (x: int) -> String) = r5(g: f);\n", 1),
    ];
    for (k, n) in cases {
        let text = format!("{S}{k}");
        assert_eq!(type_errors(&text).len(), n, "{k}: {:?}", type_errors(&text));
    }
}

/// Functions whose parameter `g` has bounded variables, for lambdas passed as `g`: `t` calls
/// it on an int, `two` and `mix` on an f64 and an int.
const L: &str = "t(g: (x: T) -> bool for T in int | f64) = g(x: 2);\n\
                 two(g: (a: T, b: U) -> T for T in int | f64, U in int) = g(a: 1.5, b: 2);\n\
                 mix(g: (a: T, b: int) -> T for T in int | f64) = g(a: 1.5, b: 2);\n\
                 pz(g: (z: T) -> T for T in int) = g(z: 1);\n\
                 dbl(x) = x + x;\n";

#[test]
fn a_lambda_uses_its_bounded_parameters_as_a_declared_function_does() {
    // Each use is checked at each carrier of the bound: at int, and for `p_wide` at f64.
    let cases = [
        ("y = p(g: (x) -> x + 1);\n", "2"),
        // A literal without a suffix takes the carrier of `x` (step L1.26a).
        ("y = p_wide(g: (x) -> x + 1);\n", "2.5"),
        ("y = p_wide(g: (x) -> x + x);\n", "3.0"),
        ("y = p_wide(g: (x) -> -x);\n", "-1.5"),
        ("y = p_wide(g: (x) -> x - x);\n", "0.0"),
        ("y = t(g: (x) -> x < x + x);\n", "true"),
        ("y = p_wide(g: (x) -> dbl(x: x));\n", "3.0"),
        ("y = two(g: (a, b) -> a + a);\n", "3.0"),
        // Named parameters taken in another order, and one `g` is not passed, by its default.
        ("y = two(g: (b, a) -> a);\n", "1.5"),
        ("y = p_wide(g: (x, k = 2) -> x);\n", "1.5"),
        // A parameter of a plain type beside a bounded one.
        ("y = mix(g: (a, b) -> a);\n", "1.5"),
        // Nested lambdas, the inner one using the outer one's parameter.
        ("y = p(g: (x) -> pz(g: (z) -> z + x));\n", "2"),
        (
            "y = p(g: (x) -> x + p(g: (x) -> x + p(g: (x) -> x)));\n",
            "3",
        ),
        // `(x: int) -> int` has no bounded variable: the lambda is checked against it alone.
        (
            "q(g: (x: int) -> int) = g(x: 1);\ny = q(g: (x) -> x + 1);\n",
            "2",
        ),
    ];
    for (q, v) in cases {
        let text = format!("{P}{L}{q}");
        assert!(
            type_errors(&text).is_empty(),
            "{q}: {:?}",
            type_errors(&text)
        );
        assert_eq!(value(&text, "y"), v, "{q}");
    }
    let twice = format!("{TWICE}y = twice(3, g: (x) -> -x);\n");
    assert!(type_errors(&twice).is_empty(), "{:?}", type_errors(&twice));
    assert_eq!(value(&twice, "y"), "3");
}

#[test]
fn a_lambda_whose_uses_the_bound_does_not_allow_is_an_error() {
    let cases = [
        // `int(1)` makes `x` an int, and `p_wide` passes an f64 too.
        (
            "y = p_wide(g: (x) -> x + int(1));\n",
            "the lambda is `(x: int) -> int`, not `(x: T) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. \
             [(x) -> x + int(1)]",
        ),
        (
            "y = p_wide(g: (x, k = 2) -> x + k);\n",
            "the lambda is `(x: int) -> int`, not `(x: T) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. \
             [(x, k = 2) -> x + k]",
        ),
        (
            "y = p_wide(g: (x) -> upper(x));\n",
            "the lambda is `(x: String) -> String`, not `(x: T) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. \
             [(x) -> upper(x)]",
        ),
        (
            "y = p_wide(g: (x: int) -> x);\n",
            "the lambda is `(x: int) -> int`, not `(x: T) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. \
             [(x: int) -> x]",
        ),
        // A comparison gives a bool, not the carrier passed.
        (
            "y = p_wide(g: (x) -> x < x);\n",
            "the lambda is `(x: T) -> bool for T in int | f32 | f64 | rat | bool | String`, \
             not `(x: T) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. [(x) -> x < x]",
        ),
        // `a` and `b` take different carriers, so `a + b` is no sum of one carrier.
        (
            "y = two(g: (a, b) -> a + b);\n",
            "the lambda is `(a: T, b: T) -> T for T in int | f32 | f64 | rat`, \
             not `(a: T, b: U) -> T for T in int | f64, U in int`: it is passed where a function of that type is expected, and its own type does not fit that one. [(a, b) -> a + b]",
        ),
        // `b` and the result have one type at each call, a variable; it is named `U`, since
        // the message writes `T` for the type `mix` declares.
        (
            "y = mix(g: (a, b) -> b);\n",
            "the lambda is `(a: _, b: U) -> U`, not `(a: T, b: int) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. \
             [(a, b) -> b]",
        ),
        // The inner `p_wide` gives an f64, so `x` is an f64, and `p_wide` passes an int too.
        (
            "y = p_wide(g: (x) -> p_wide(g: (x) -> x + x) + x);\n",
            "the lambda is `(x: f64) -> f64`, not `(x: T) -> T for T in int | f64`: it is passed where a function of that type is expected, and its own type does not fit that one. \
             [(x) -> p_wide(g: (x) -> x + x) + x]",
        ),
    ];
    for (q, message) in cases {
        let text = format!("{P}{L}{q}");
        assert_eq!(type_errors(&text), [message], "{q}");
    }
}

#[test]
fn a_lambda_and_a_declared_function_of_the_same_body_give_the_same_result() {
    for body in [
        "x + 1",
        "x + x",
        "-x",
        "x - x",
        "x < x",
        "upper(x)",
        "dbl(x: x)",
        "x",
    ] {
        for (g, n) in [("p", "x"), ("p_wide", "x"), ("t", "x")] {
            let lambda = format!("{P}{L}y = {g}(g: ({n}) -> {body});\n");
            let named = format!("{P}{L}f({n}) = {body};\ny = {g}(g: f);\n");
            let shown = |errors: Vec<String>, what: &str, at: &str| -> Vec<String> {
                errors
                    .iter()
                    .map(|e| e.replace(what, "it").replace(at, "[]"))
                    .collect()
            };
            let from_lambda = shown(
                type_errors(&lambda),
                "the lambda",
                &format!("[({n}) -> {body}]"),
            );
            let from_named = shown(type_errors(&named), "`f`", "[f]");
            assert_eq!(from_lambda, from_named, "{g} with {body}");
            if from_lambda.is_empty() {
                assert_eq!(value(&lambda, "y"), value(&named, "y"), "{g} with {body}");
            }
        }
    }
}

/// `n` lambdas nested, each passed for a parameter bounded by int and using its own.
pub(super) fn nested_lambdas(n: usize) -> String {
    let mut body = String::from("x");
    for _ in 1..n {
        body = format!("x + p(g: (x) -> {body})");
    }
    format!("{P}y = p(g: (x) -> {body});\n")
}

/// A lambda of `n` parameters, each of its own bounded variable, passed to the `h` of
/// [`wide`].
pub(super) fn wide_lambda(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    format!("{}y = h(g: ({}) -> x0 + x0);\n", wide(n), xs.join(", "))
}

#[test]
fn bounds_on_two_rows_are_both_found() {
    // A union of tuple types of two lengths, each holding a bounded signature of its own, and
    // with a tuple of no components beside them: the reading finds each bound on its own
    // row's signature. A walk that took two rows for one would read one row's signature
    // alone and refuse the other's bound as on no signature that names it.
    for text in [
        "((x: T) -> T for T in rat,) | ((y: U) -> String for U in String | bool, int)",
        "() | ((x: T) -> T for T in rat,) | ((y: U) -> String for U in String | bool, int)",
    ] {
        let t = parse_type(text).unwrap_or_else(|e| panic!("{text}: {e}"));
        let mut bounds: Vec<String> = (t.tuples.iter())
            .flat_map(|r| r.iter())
            .flat_map(|c| &c.fns)
            .flat_map(|s| s.bounds.keys().map(|v| v.to_string()))
            .collect();
        bounds.sort();
        assert_eq!(bounds, ["T", "U"], "{text}");
    }
}

#[test]
fn bounds_on_two_payloads_are_both_found() {
    // As above for the payloads of two atoms, each holding a bounded signature of its own.
    let text = "#a((x: T) -> T for T in rat) | #b((y: U) -> String for U in String | bool)";
    let t = parse_type(text).unwrap_or_else(|e| panic!("{text}: {e}"));
    let mut bounds: Vec<String> = (t.payloads.values().flatten().flatten())
        .flat_map(|s| &s.items)
        .flat_map(|c| &c.fns)
        .flat_map(|s| s.bounds.keys().map(|v| v.to_string()))
        .collect();
    bounds.sort();
    assert_eq!(bounds, ["T", "U"], "{text}");
}

/// A printed type of `n` definitions, the first a tuple of one bounded signature and each
/// after it a tuple of two of the one before, ending with the last: the signature is reached
/// by `2^n` paths and read once.
pub(super) fn shared_bounded_chain(n: usize) -> String {
    let mut text = String::from("type T0 = ((x: T) -> T for T in int | f64,); ");
    for i in 1..=n {
        text += &format!("type T{i} = (T{}, T{});\n", i - 1, i - 1);
    }
    text + &format!("T{n}")
}

/// A printed type of `n` definitions, each a tuple of a bounded signature of its own and the
/// definition before it, ending with the last: each `for` clause is read against the parts
/// its definition names, which hold every definition before it.
pub(super) fn bounded_chain(n: usize) -> String {
    let mut text = String::from("type T0 = ((x: T) -> T for T in int | f64,);\n");
    for i in 1..=n {
        text += &format!(
            "type T{i} = ((x: T) -> T for T in int | f64, T{});\n",
            i - 1
        );
    }
    text + &format!("T{n}")
}

/// `bounded_chain` with `T0` bounding `W` in place of `T`, so that of the definitions only the
/// first, `n` deep, has a signature that names `W`.
fn chain_bounding_w_first(n: usize) -> String {
    bounded_chain(n).replacen(
        "type T0 = ((x: T) -> T for T in int | f64,);",
        "type T0 = ((x: W) -> W for W in int | f64,);",
        1,
    )
}

#[test]
fn a_bound_deep_in_a_chain_is_found_and_a_bound_on_no_signature_is_rejected() {
    // The benchmark `bench::bounds::reading_a_chain_of_bounded_definitions_scales` reads
    // chains of `bounded_chain` 200 and 1,600 long.
    let n = 3;
    let chain = chain_bounding_w_first(n);
    assert!(parse_type(&chain).is_ok(), "{chain}");
    let ending = |clause: &str| {
        chain.replacen(
            &format!("\nT{n}"),
            &format!("\ntype B = (int, T{n}) {clause};\nB"),
            1,
        )
    };
    // `U` is on no signature: not on one of `B`, which has none, nor on one of the definitions
    // it names, which bound `T` and, `n` deep, `W`.
    let err = parse_type(&ending("for U in int")).expect_err("a bound on no signature");
    assert!(
        err.ends_with("the bound of `U` is on no signature that names it"),
        "{err}"
    );
    // `W` is on the signature of `T0`, `n` deep, so the reading goes on, and the resolver
    // rejects the clause, since the type before `for` does not hold `W`.
    let err = parse_type(&ending("for W in int")).expect_err("a bound that holds nothing");
    assert!(
        err.contains("the bound names `W`, and the type before `for` does not hold `W`"),
        "{err}"
    );
}

/// A type of `n` bounded signatures, each for a variable of its own name (`X1` to `Xn`) and
/// each in a tuple with the one before, every one also taking `int | #x`, a part used `n`
/// times, so the checker prints it with a definition before the whole text.
pub(super) fn distinct_bounds_chain(n: usize) -> String {
    let mut text = String::from("type D0 = (int | #x,);\n");
    for k in 1..=n {
        text += &format!(
            "type D{k} = (((x: X{k}, y: int | #x) -> X{k} for X{k} in int | f64), D{});\n",
            k - 1
        );
    }
    text + &format!("D{n}")
}

#[test]
fn a_printed_type_has_each_bounds_clause_on_a_signature_of_its_last_part() {
    // The printer writes a bounds clause right after the signature it bounds, in the text of
    // the type itself; the definitions before it are kernel sets, which hold no clause. So each
    // clause of a printed type is on a signature its last part writes, and reading it back
    // finds each bound among the signatures that part meets first, with no search of the
    // definitions.
    let n = 5;
    let t = parse_type(&distinct_bounds_chain(n)).unwrap_or_else(|e| panic!("{e}"));
    let printed = t.to_string();
    let (defs, last): (Vec<&str>, Vec<&str>) =
        printed.lines().partition(|l| l.starts_with("type "));
    assert!(!defs.is_empty(), "{printed}");
    assert!(defs.iter().all(|d| !d.contains(" for ")), "{printed}");
    assert_eq!(last.len(), 1, "{printed}");
    assert_eq!(last[0].matches(" for ").count(), n, "{printed}");
    assert_eq!(parse_type(&printed).unwrap_or_else(|e| panic!("{e}")), t);
}

#[test]
fn a_signature_of_many_bounds_prints_and_reads_back() {
    // A small instance of the benchmarks
    // `bench::bounds::printing_a_signature_of_many_bounds_scales`
    // and `bench::bounds::reading_back_a_signature_of_many_bounds_scales`.
    let first = parse_type(&many_bounds(3)).unwrap_or_else(|e| panic!("{e}"));
    let printed = first.to_string();
    assert_eq!(
        printed,
        "(x0: T0, x1: T1, x2: T2) -> T0 for T0 in int | f64, T1 in String, T2 in rat | bool"
    );
    assert_eq!(
        parse_type(&printed).unwrap_or_else(|e| panic!("{e}")),
        first
    );
}

#[test]
fn many_bounded_variables_and_nested_clauses_are_checked() {
    // Small instances of the benchmarks `bench::bounds::many_bounded_variables_scale`,
    // `bench::bounds::passing_a_function_of_many_bounded_variables_scales`,
    // `bench::bounds::nested_bounds_clauses_scale`,
    // `bench::bounds::passing_a_deep_function_type_as_itself_scales`,
    // `bench::bounds::passing_a_deep_bounded_function_type_as_itself_scales` and
    // `bench::bounds::a_lambda_of_many_bounded_parameters_scales`.
    for text in [
        wide(3),
        passed(3),
        nested(3),
        passed_deep(3, false),
        passed_deep(3, true),
        wide_lambda(3),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    }
    assert_eq!(fmt(&wide(3)), wide(3));
    assert_eq!(fmt(&nested(3)), nested(3));
    assert!(resolve_errors(&nested(3)).is_empty());
    assert_eq!(value(&wide_lambda(3), "y"), "2");
}

#[test]
fn nested_lambdas_for_bounded_parameters_give_their_value() {
    // A small instance of the benchmark
    // `bench::bounds::nested_lambdas_for_bounded_parameters_scale`.
    assert_eq!(value(&nested_lambdas(3), "y"), "3");
}

#[test]
fn a_deep_function_type_prints() {
    // A small instance of the benchmark `bench::bounds::printing_a_deep_function_type_scales`.
    let (info, names) = info(&nested(3));
    let (_, s) = info
        .sigs
        .iter()
        .find(|(id, _)| names[**id] == "h")
        .expect("h");
    assert_eq!(
        s.to_string(),
        "(g: ((T0 -> T0 for T0 in int) -> T1 for T1 in f64) -> T2 for T2 in f64) -> 0"
    );
}

#[test]
fn chains_of_bounded_definitions_read_as_one_tuple() {
    // Small instances of the benchmarks
    // `bench::bounds::reading_a_chain_of_shared_bounded_parts_scales`,
    // `bench::bounds::reading_a_chain_of_bounded_definitions_scales` and
    // `bench::bounds::reading_back_a_printed_type_of_many_distinct_bounded_variables_scales`.
    for text in [shared_bounded_chain(3), bounded_chain(3)] {
        let t = parse_type(&text).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(t.tuples.len(), 1, "{text}");
        assert_eq!(
            parse_type(&t.to_string()).unwrap_or_else(|e| panic!("{e}")),
            t
        );
    }
    let t = parse_type(&distinct_bounds_chain(3)).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(
        parse_type(&t.to_string()).unwrap_or_else(|e| panic!("{e}")),
        t
    );
}
