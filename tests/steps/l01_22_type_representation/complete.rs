//! Completeness cases for L1.22 (TEST-complete-types, COMPLETENESS.md): the kernel type each
//! written form denotes (`zedc_types::kernel_type`, read through `declared_text`), and the `is`
//! test's rejections in every position a port name or a function bound can stand. Expected
//! results are DESIGN.md L1.22: a function type is curried one level per parameter, `->?` is
//! partial at each level, `() -> V` has the empty tuple as its one key, `()` is the empty
//! tuple's type, and `is` is rejected when its type admits some functions and not others or
//! names a port.

use zed_tests::step_helpers::l01_16_elaboration::elab;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

/// The text of the kernel type `text` denotes, `None` when it denotes none (a port name).
fn denotes(text: &str) -> Option<String> {
    let tokens = lex_fence(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    let tree = parse(text, &tokens, "Type", TOP).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    let t = zedc::ast::ty(text, &tokens, &tree).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    zedc::check::declared_text(&t)
}

const IS_FUNCTION: &str = "`is` tests a value against a type when the program runs, and a function value does not show its type then. Test against a type that is not a function type, or remove the `is`.";

fn port(name: &str) -> String {
    format!(
        "`{name}` is the type of a port, which only a port parameter has; no value has it, so it cannot be written here. To repair it, write the type of the values the port carries, such as `String`. [{name}]"
    )
}

#[test]
fn function_types_are_curried_and_partial_at_each_level() {
    for (written, kernel) in [
        // `() -> V` has the empty tuple as its one key.
        ("() -> int", "(()) -> int"),
        ("() ->? int", "(()) ->? int"),
        // One level per parameter; `->?` makes every level partial.
        ("(a: int, b: int) -> int", "int -> int -> int"),
        ("(a: int, b: int) ->? int", "int ->? int ->? int"),
        // One parameter that is a pair is one level whose key is the pair.
        ("((int, int)) -> int", "((int, int)) -> int"),
        // A partial level whose result is an exact function keeps each level's own arrow.
        ("(int) ->? (int) -> int", "int ->? int -> int"),
        ("int -> int -> int", "int -> int -> int"),
    ] {
        assert_eq!(denotes(written).as_deref(), Some(kernel), "{written}");
    }
}

#[test]
fn bounded_function_types_keep_both_bounds() {
    for (written, kernel) in [
        ("(#a | #c .. #a | #b -> int)", "#a | #c .. #a | #b -> int"),
        ("(#a .. #a | #b -> int)", "#a .. #a | #b -> int"),
        // A guarantee of nothing is a partial function; equal bounds an exact one.
        ("(Never .. int -> int)", "int ->? int"),
        ("(int .. int -> int)", "int -> int"),
    ] {
        assert_eq!(denotes(written).as_deref(), Some(kernel), "{written}");
    }
}

#[test]
fn the_connectives_and_the_extremes_denote_sets() {
    for (written, kernel) in [
        ("Never", "Never"),
        ("int & rat", "Never"),
        ("int \\ int", "Never"),
        ("(int, String) \\ (int, String)", "Never"),
        // Tuple types of one length are not met when built (L1.22).
        ("(int, String) & (int, bool)", "(int, String) & (int, bool)"),
        ("#a | #b", "#a | #b"),
        (
            "f32 | f64 | rat | bool | String",
            "f32 | f64 | rat | bool | String",
        ),
        ("#_", "#_"),
        ("(..)", "(..)"),
        ("{..}", "{..}"),
        ("()", "()"),
        ("(int,)", "(int,)"),
    ] {
        assert_eq!(denotes(written).as_deref(), Some(kernel), "{written}");
    }
}

#[test]
fn a_port_name_denotes_no_type_wherever_it_stands() {
    for written in [
        "Lines",
        "Files",
        "(Lines, Files)",
        "int | Lines",
        "(int) -> Files",
    ] {
        assert_eq!(denotes(written), None, "{written}");
    }
}

#[test]
fn is_rejects_a_port_in_every_position_in_written_order() {
    assert_eq!(elab("f(x) = x is Files;").unwrap_err(), [port("Files")]);
    assert_eq!(
        elab("f(x) = x is (Lines, Files);").unwrap_err(),
        [port("Lines"), port("Files")]
    );
    assert_eq!(
        elab("f(x) = x is int | Lines;").unwrap_err(),
        [port("Lines")]
    );
    assert_eq!(elab("f(x) = x is not Lines;").unwrap_err(), [port("Lines")]);
}

/// A port name in an intersection, on either side of a difference, and in either bound of
/// `L .. U -> V` denotes no type, so the type holding it denotes none either
/// (TEST-types-unreached-paths: each `?` of `kernel_form` on a refused part). Each port is named
/// once, in written order, and no other error stands beside it: a bound that holds a port is not
/// compared with the other.
#[test]
fn is_rejects_a_port_in_an_intersection_a_difference_and_a_bound() {
    for (written, ports) in [
        ("int & Lines", &["Lines"][..]),
        ("Lines & Files", &["Lines", "Files"]),
        ("Lines \\ int", &["Lines"]),
        ("int \\ Files", &["Files"]),
        ("Lines \\ Files", &["Lines", "Files"]),
        ("(Lines .. int -> int)", &["Lines"]),
        ("(int .. Files -> int)", &["Files"]),
        ("(Lines .. Files -> int)", &["Lines", "Files"]),
    ] {
        let want: Vec<String> = ports.iter().map(|p| port(p)).collect();
        assert_eq!(
            elab(&format!("f(x) = x is {written};")).unwrap_err(),
            want,
            "{written}"
        );
        assert_eq!(denotes(written), None, "{written}");
    }
}

#[test]
fn is_rejects_a_type_with_some_functions_in_every_position() {
    for (written, span) in [
        ("(int, (int) -> int)", "(int, (int) -> int)"),
        ("(() -> int)", "(() -> int)"),
    ] {
        assert_eq!(
            elab(&format!("f(x) = x is {written};")).unwrap_err(),
            [format!("{IS_FUNCTION} [{span}]")],
            "{written}"
        );
    }
    assert_eq!(
        elab("f(x) = x is not ((int) -> int);").unwrap_err(),
        [format!("{IS_FUNCTION} [((int) -> int)]")]
    );
}

#[test]
fn is_accepts_a_type_with_every_function_or_none() {
    let term = |text: &str| {
        let u = elab(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
        u.get("f").unwrap().to_string()
    };
    // A function type less itself admits no function: the test is one against `Never`.
    let t = term("f(x) = x is ((int) -> int) \\ ((int) -> int);");
    assert!(t.contains("is Never -> true, _ -> false"), "{t}");
    for (written, shown) in [
        ("int & rat", "is Never"),
        ("Never", "is Never"),
        ("#_", "is #_"),
        ("(..)", "is (..)"),
        ("()", "is ()"),
    ] {
        let t = term(&format!("f(x) = x is {written};"));
        assert!(t.contains(shown), "{written}: {t}");
    }
}

#[test]
fn a_bounds_error_and_a_port_error_both_stand_in_written_order() {
    let errs = elab("f(x) = x is (#a | #c .. #a | #b -> Lines);").unwrap_err();
    assert_eq!(errs.len(), 2, "{errs:?}");
    assert!(
        errs[0].starts_with("in a function type `L .. U -> V`, every function the guarantee `L`")
            && errs[0].contains("the guarantee allows functions the permission does not"),
        "{errs:?}"
    );
    assert_eq!(errs[1], port("Lines"));
}

/// A bounded function type admits some functions and not others, so `is` rejects it (L1.22);
/// the error names each bounded variable, which no run-time test can choose a carrier for.
#[test]
fn is_rejects_a_bounded_function_type_naming_its_variables() {
    let msg = |vars: &str, it: &str, span: &str| {
        format!(
            "this `is` test names a type with the bounded {vars}; a call of a function chooses which carrier of its bound {it} stands for, and a test has no call to choose it, so the test has no one type to check against. To repair it, test each carrier of the bound in turn, as `x is int`. [{span}]"
        )
    };
    assert_eq!(
        elab("f(x) = x is ((T) -> T for T in int);").unwrap_err(),
        [msg("variable `T`", "it", "((T) -> T for T in int)")]
    );
    assert_eq!(
        elab("f(x) = x is ((T, U) -> T for T in int, U in rat);").unwrap_err(),
        [msg(
            "variables `T`, `U`",
            "each one",
            "((T, U) -> T for T in int, U in rat)"
        )]
    );
    // In a tuple component, the span is the bounded type's own.
    assert_eq!(
        elab("f(x) = x is (int, (T) -> T for T in int | rat);").unwrap_err(),
        [msg("variable `T`", "it", "(T) -> T for T in int | rat")]
    );
    assert_eq!(denotes("(T) -> T for T in int"), None);
}

/// `#a(..)` is the atom `#a` with every payload.
#[test]
fn an_atom_with_every_payload_denotes_itself() {
    assert_eq!(denotes("#a(..)").as_deref(), Some("#a(..)"));
    assert_eq!(denotes("#a(..) | #b").as_deref(), Some("#a(..) | #b"));
}

/// Two literals of one value print by their carrier, in the order of the number types: `f32`,
/// `f64`, `rat` (DESIGN.md sec:diagnostics, "Types in a message"), however the union is built.
#[test]
fn literals_of_one_value_print_by_their_carrier() {
    use num_bigint::BigInt;
    use zed_kernel::types::Type;
    use zed_kernel::{Rat, Value};
    let lit = |v: Value| Type::lit(&v).unwrap();
    let (a, b, c) = (
        lit(Value::float32(1.5)),
        lit(Value::float(1.5)),
        lit(Value::rat(
            Rat::int(BigInt::from(3))
                .div(&Rat::int(BigInt::from(2)))
                .unwrap()
                .unwrap(),
        )),
    );
    for t in [&(&a | &b) | &c, &(&c | &b) | &a, &(&b | &c) | &a] {
        let text = t.surface().root;
        let parts: Vec<&str> = text.split(" | ").collect();
        assert_eq!(parts.len(), 3, "{text}");
        assert_eq!(parts[0], "1.5f32", "{text}");
        assert!(
            !parts[1].ends_with("f32") && !parts[1].ends_with('r'),
            "{text}"
        );
        assert!(parts[2].ends_with('r'), "{text}");
    }
}
