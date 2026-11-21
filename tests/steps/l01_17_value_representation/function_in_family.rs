//! A family whose entries hold functions (row FAIL-family-function-entry). DESIGN.md L1.17:
//! "A tuple, an array or a struct may hold a function at any depth"; sec:values_morphisms:
//! "Application is indexing", and `p(1)(2)` is valid for a function that returns a function.
//! So `b["a"]` reads the entry and `(2)` applies it. The reference evaluator keeps such a
//! family as a held value (`HeldFamily` in crates/zed-kernel/src/value.rs): its keys, and its
//! data entries, by the rules of a data family, and each entry that holds a function as a part
//! of its own. Each expected value is worked by hand from the program. The same programs run
//! by `zedc run` and by an executable are in `l03_02_map_run::functions`.

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Evaluator, KernelError, Prim, Term, Value, World};
use zed_tests::step_helpers::l01_16_elaboration::{errors, value};

/// Two functions at the keys "a" and "b": `b["a"](n)` is `n + 1`, `b["b"](n)` is `2 n`.
const B: &str = "b = { \"a\" -> (y -> y + 1), \"b\" -> (y -> y * 2) };\n";

/// The value of `a` in `B` followed by `body`.
fn a(body: &str) -> String {
    value(&format!("{B}{body}"), "a")
}

#[test]
fn a_function_read_from_a_family_display_is_applied() {
    let src = "b = { \"a\" -> (y -> y + 1) };\na = b[\"a\"](2);\n";
    assert_eq!(value(src, "a"), "3", "{src}");
    assert_eq!(a("a = b[\"a\"](2);\n"), "3");
    assert_eq!(a("a = b[\"b\"](2);\n"), "4");
}

#[test]
fn a_function_made_by_map_is_read_and_applied() {
    let src = "b = { \"a\" -> 1 }.map(r -> (y -> y + 1));\na = b[\"a\"](2);\n";
    assert_eq!(value(src, "a"), "3", "{src}");
    // The function captures the entry it was made from: 2 + 1.
    let src = "b = { \"a\" -> 1 }.map(r -> (y -> y + r));\na = b[\"a\"](2);\n";
    assert_eq!(value(src, "a"), "3", "{src}");
    // One function per entry, each with its own capture: 10 + 1 and 10 + 2.
    let src = "a = { \"a\" -> 1, \"b\" -> 2 }.map(r -> (y -> y + r)).map(f -> f(10));\n";
    assert_eq!(value(src, "a"), "{\"a\" -> 11, \"b\" -> 12}", "{src}");
}

/// The family passed to a function, which reads and applies an entry: `b["b"](10)` is 20.
#[test]
fn a_family_of_functions_passed_on_is_read_and_applied() {
    assert_eq!(
        a("ap(positional f, positional k) = f[k](10);\na = ap(b, \"b\");\n"),
        "20"
    );
    // Made inside a function, from its argument: 1 + 5.
    let src = "f(positional k) = { \"a\" -> (y -> y + k) };\na = f(5)[\"a\"](1);\n";
    assert_eq!(value(src, "a"), "6", "{src}");
}

/// Held by a tuple, an array, and a family of families. A struct holding one waits for
/// structs to compile (row TEST-family-function-struct-field).
#[test]
fn a_family_of_functions_held_by_another_value_is_read_and_applied() {
    assert_eq!(a("p = (b, 1);\na = p[0][\"a\"](2);\n"), "3");
    assert_eq!(a("a = [b, b][1][\"b\"](3);\n"), "6");
    assert_eq!(a("a = { 1 -> b, 2 -> b }[2][\"b\"](3);\n"), "6");
    assert_eq!(
        a("a = { 1 -> b, 2 -> b }.map(c -> c[\"a\"](1));\n"),
        "{1 -> 2, 2 -> 2}"
    );
    let src = "a = { \"a\" -> { \"b\" -> (y -> y + 1) } }[\"a\"][\"b\"](2);\n";
    assert_eq!(value(src, "a"), "3", "{src}");
}

/// A key that is not in the family gives `#notFound` (sec:type_language), and applying it
/// passes the failure on; `else` gives the default, a function or a number.
#[test]
fn a_missed_key_gives_not_found_and_else_its_default() {
    let ks = "ks = [\"a\", \"z\"];\n";
    assert_eq!(a(&format!("{ks}a = b[ks[1]];\n")), "#notFound");
    assert_eq!(a(&format!("{ks}a = b[ks[1]](2);\n")), "#notFound");
    assert_eq!(
        a(&format!("{ks}a = b[ks[1]](2) else #notFound -> -1;\n")),
        "-1"
    );
    assert_eq!(
        a(&format!("{ks}a = b[ks[0]](2) else #notFound -> -1;\n")),
        "3"
    );
    assert_eq!(
        a(&format!(
            "{ks}a = (b[ks[1]] else #notFound -> (y -> 0))(5);\n"
        )),
        "0"
    );
    assert_eq!(
        a(&format!(
            "{ks}a = (b[ks[0]] else #notFound -> (y -> 0))(5);\n"
        )),
        "6"
    );
    assert_eq!(a(&format!("{ks}a = ks[1] in b;\n")), "false");
}

/// An array of functions is a family keyed by position: `[…][1](5)` is 10.
#[test]
fn an_array_of_functions_is_read_and_applied() {
    let src = "a = [(x -> x + 1), (x -> x * 2)][1](5);\n";
    assert_eq!(value(src, "a"), "10", "{src}");
}

/// `map` applies each entry, and may make functions from functions: f(1) + 100 at "b" is 102.
#[test]
fn map_over_a_family_of_functions() {
    assert_eq!(a("a = b.map(f -> f(2));\n"), "{\"a\" -> 3, \"b\" -> 4}");
    assert_eq!(
        a("c = b.map(f -> (y -> f(y) + 100));\na = c[\"b\"](1);\n"),
        "102"
    );
    assert_eq!(a("a = b.map(f -> f)[\"a\"](5);\n"), "6");
    assert_eq!(a("a = b.map(f -> (f, 1))[\"a\"][0](5);\n"), "6");
}

/// `count`, `in`, `first` and `last` read the keys and the entries at the ends.
#[test]
fn count_in_first_and_last() {
    assert_eq!(a("a = b.count;\n"), "2");
    assert_eq!(a("a = \"a\" in b;\n"), "true");
    assert_eq!(a("c = b.first;\na = c(4);\n"), "5");
    assert_eq!(a("c = b.last;\na = c(4);\n"), "8");
}

/// Data entries beside function entries keep their values.
#[test]
fn data_entries_beside_function_entries() {
    let c = "c = { \"a\" -> (y -> y + 1), \"b\" -> 7 };\n";
    assert_eq!(value(&format!("{c}a = c[\"b\"];\n"), "a"), "7");
    assert_eq!(value(&format!("{c}a = c.last;\n"), "a"), "7");
    assert_eq!(value(&format!("{c}a = c.count;\n"), "a"), "2");
    assert_eq!(
        value(&format!("{c}a = c.map(v -> 0);\n"), "a"),
        "{\"a\" -> 0, \"b\" -> 0}"
    );
}

/// Two entries at one key collide as in a family of data (sec:corner_cases), and the run
/// stops with that message, not as a bug in zedc.
#[test]
fn two_function_entries_at_one_key_collide() {
    let src = "b = { \"a\" -> (y -> y + 1), \"a\" -> (y -> y) };\na = b[\"a\"](1);\n";
    let got = value(src, "a");
    assert!(
        got.contains("two entries were written at the same key path, [\"a\"]"),
        "{src}\n{got}"
    );
    assert!(!got.contains("a bug in zedc"), "{src}\n{got}");
}

/// `where` and a remap need no entry to be data (L1.17: only showing and `==` do), so they
/// keep the functions (row FAIL-held-family-operators). `b["a"](3)` is 4 and `b["b"](3)` is 6,
/// so `f(3) > 5` keeps "b" alone.
#[test]
fn where_and_a_remap_over_a_family_of_functions() {
    assert_eq!(a("a = b.where(f -> true).count;\n"), "2");
    assert_eq!(a("c = b.where(f -> true);\na = c[\"a\"](2);\n"), "3");
    assert_eq!(a("a = b.where(f -> f(3) > 5).count;\n"), "1");
    assert_eq!(a("c = b.where(f -> f(3) > 5);\na = c[\"b\"](3);\n"), "6");
    assert_eq!(
        a("c = b as (k -> v) into (k -> v);\na = c[\"a\"](2);\n"),
        "3"
    );
}

/// A family whose entries are functions is not data (row FAIL-check-family-of-functions-as-data).
/// DESIGN.md L1.17: "`Utf8String(x)` and interpolation show data, so a value that holds a
/// function is a type error there", and "`==` on functions is a type error until types give
/// the enumerable domain to compare them on". The checker rejects each use, so the run never
/// stops on it; and the repair offered for `len(b)` is not `len(String(b))`, which the same
/// rule rejects.
#[test]
fn a_family_of_functions_is_not_shown_or_compared() {
    for body in ["a = \"${b}\";\n", "a = b == b;\n"] {
        let src = format!("{B}{body}");
        let got = errors(&src);
        assert!(!got.is_empty(), "{src}");
    }
    let src = format!("{B}a = len(b);\n");
    let got = errors(&src).join("\n");
    assert!(!got.contains("String(b)"), "{src}\n{got}");
}

/// A use that needs data and meets a value that may hold a function is rejected with a
/// headline in code form (row MSG-data-code-form; DESIGN.md sec:diagnostics, "A short
/// headline, the detail in the notes"): the expression rejected, with its operand's type, and
/// no repair in words.
#[test]
fn a_family_of_functions_shown_is_rejected_in_code_form() {
    for (body, code) in [
        ("a = \"${b}\";\n", "`\"${b}\"`"),
        ("a = b == #c;\n", "`b == #c`"),
    ] {
        let src = format!("{B}{body}");
        let got = errors(&src);
        assert_eq!(got.len(), 1, "{src}\n{got:#?}");
        assert!(got[0].starts_with("Cannot "), "{src}\n{}", got[0]);
        assert!(got[0].contains(code), "{src}\n{}", got[0]);
        assert!(
            !got[0].contains("call the function before the value gets here"),
            "{src}\n{}",
            got[0]
        );
    }
}

/// The headline names what the use does, shows the operand with its type in the expression
/// of the use (of a map display, the entry `key -> value`; none where one expression would
/// be named in each of many errors, a string of several holes or a set), and ends with a
/// repair only where one is written as code that the checker accepts: a function of no
/// parameters whose result is data, shown, is called.
#[test]
fn a_value_that_may_hold_a_function_is_rejected_with_the_use_in_code() {
    let f = "f(positional y) = y + int(1);\nseed() = 42;\n";
    for (body, want, at) in [
        (
            "a = \"${f}\";\n",
            "Cannot show a value that may hold a function: `f : int -> int` in `\"${f}\"`.",
            "f",
        ),
        (
            "a = String(f);\n",
            "Cannot show a value that may hold a function: `f : int -> int` in `String(f)`.",
            "String(f)",
        ),
        (
            "a = (f, 1) == (f, 1);\n",
            "Cannot compare a value that may hold a function: `(f, 1) : (int -> int, 1)` in \
             `(f, 1) == (f, 1)`.",
            "(f, 1) == (f, 1)",
        ),
        (
            "a = { f -> 1 };\n",
            "Cannot use a value that may hold a function as a key: `f : int -> int` in \
             `f -> 1`.",
            "f",
        ),
        (
            "a = (f, 1) in { (1, 1) };\n",
            "Cannot use a value that may hold a function as a key: `(f, 1) : (int -> int, 1)` \
             in `(f, 1) in { (1, 1) }`.",
            "(f, 1)",
        ),
        (
            "a = \"${seed}\";\n",
            "Cannot show a value that may hold a function: `seed : () -> 42` in `\"${seed}\"`. \
             Try `\"${seed()}\"` instead.",
            "seed",
        ),
        // Of a string of several holes, each hole is named alone, and of a set its element.
        (
            "a = \"x${seed} ${2}\";\n",
            "Cannot show a value that may hold a function: `seed : () -> 42`. Try `seed()` \
             instead.",
            "seed",
        ),
        (
            "a = \"x${1} ${f}\";\n",
            "Cannot show a value that may hold a function: `f : int -> int`.",
            "f",
        ),
        (
            "a = { 1, (f, 2) };\n",
            "Cannot use a value that may hold a function as a key: `(f, 2) : (int -> int, 2)`.",
            "(f, 2)",
        ),
        (
            "a = String(seed);\n",
            "Cannot show a value that may hold a function: `seed : () -> 42` in \
             `String(seed)`. Try `String(seed())` instead.",
            "String(seed)",
        ),
        // `==` takes no repair: `seed() == 1` is a comparison of other values.
        (
            "a = seed == 1;\n",
            "Cannot compare a value that may hold a function: `seed : () -> 42` in \
             `seed == 1`.",
            "seed == 1",
        ),
    ] {
        let src = format!("{f}{body}");
        let got = errors(&src);
        assert_eq!(got, [format!("{want} [{at}]")], "{src}");
    }
    // Each repair offered is accepted, and shows what the function gives.
    for (body, shown) in [
        ("a = \"${seed()}\";\n", "\"42\""),
        ("a = String(seed());\n", "\"42\""),
        ("a = \"x${seed()} ${2}\";\n", "\"x42 2\""),
    ] {
        let src = format!("{f}{body}");
        assert_eq!(value(&src, "a"), shown, "{src}");
    }
}

/// A family finds an entry by comparing the key with its keys, so a key that holds a
/// function is rejected where the family is read, as a key of a display is (row
/// FAIL-generic-get-function-key): before, `get` was accepted and the run stopped with
/// "`[k]` applied to a value that holds a function", a bug in zedc. The plain read `c[(f, 1)]`
/// gives the same message, and not that the key is outside the family's keys. A function read
/// at a function, `ap(f, k) = f[k]`, takes any argument and stays accepted.
#[test]
fn a_key_that_holds_a_function_is_rejected_at_a_read() {
    let f = "f(positional y) = y + int(1);\n";
    let key = "Cannot use a value that may hold a function as a key: ";
    for (body, want, at) in [
        // The family and the key both parameters: the call meets the read with both types.
        (
            "get(positional c, positional k) = c[k] else #notFound -> 0;\na = get({ 1 -> 1 }, (f, 1));\n",
            "`(int -> int, 1)` in `get({ 1 -> 1 }, (f, 1))`.",
            "get({ 1 -> 1 }, (f, 1))",
        ),
        // The key a function itself.
        (
            "get(positional c, positional k) = c[k] else #notFound -> 0;\na = get({ 1 -> 1 }, f);\n",
            "`int -> int` in `get({ 1 -> 1 }, f)`.",
            "get({ 1 -> 1 }, f)",
        ),
        // The key built on its own, under a name.
        (
            "pair = (f, 1);\nget(positional c, positional k) = c[k] else #notFound -> 0;\n\
             a = get({ 1 -> 1 }, pair);\n",
            "`(int -> int, 1)` in `get({ 1 -> 1 }, pair)`.",
            "get({ 1 -> 1 }, pair)",
        ),
        // The family known, the key a parameter.
        (
            "c = { 1 -> 1 };\nget(positional k) = c[k] else #notFound -> 0;\na = get((f, 1));\n",
            "`(int -> int, 1)` in `get((f, 1))`.",
            "get((f, 1))",
        ),
        // The key on its own, read with no call between.
        (
            "c = { 1 -> 1 };\na = c[(f, 1)] else #notFound -> 0;\n",
            "`(f, 1) : (int -> int, 1)` in `c[(f, 1)]`.",
            "c[(f, 1)]",
        ),
        // A lambda applied at once.
        (
            "c = { 1 -> 1 };\na = ((k) -> c[k] else #notFound -> 0)((f, 1));\n",
            "`(int -> int, 1)` in `((k) -> c[k] else #notFound -> 0)((f, 1))`.",
            "((k) -> c[k] else #notFound -> 0)((f, 1))",
        ),
    ] {
        let src = format!("{f}{body}");
        let got = errors(&src);
        assert_eq!(got, [format!("{key}{want} [{at}]")], "{src}");
    }
    // A read of a function at a function is an application, and takes it.
    let src = format!("{f}ap(positional c, positional k) = c[k];\na = ap((x -> 1), f);\n");
    assert_eq!(value(&src, "a"), "1", "{src}");
    // A key of data in the same reads is found.
    let src = "get(positional c, positional k) = c[k] else #notFound -> 0;\na = get({ (1, 1) -> 5 }, (1, 1));\n";
    assert_eq!(value(src, "a"), "5", "{src}");
}

/// A display takes its arguments in pairs, a key then a value. Elaboration builds no other, but
/// a kernel term made elsewhere may give it an odd count, which the evaluator refuses with a
/// type error, never a stop, whether the arguments are all data or one holds a function, and
/// whatever the count (row FAIL-entries-held-odd-panic: one function as the only argument
/// stopped the evaluator at an `unreachable!`). A key that is no data is refused as a function
/// where data is needed, also when it is the last key, left without its value.
#[test]
fn a_display_with_a_key_left_without_a_value_is_refused() {
    let f = Term::Lam(vec!["y".into()], Term::Var("y".into()).into());
    let n = |i| lit(Value::Int(i));
    let function = "`{..}` applied to a function";
    let odd =
        |k: usize| format!("`{{..}}` takes its arguments in pairs, a key then a value, given {k}");
    for (what, args, expected) in [
        ("a function alone", vec![f.clone()], function.to_string()),
        (
            "an entry, then a function as a key",
            vec![n(1), n(2), f.clone()],
            function.to_string(),
        ),
        (
            "an entry whose value is a function, then a function as a key",
            vec![n(1), f.clone(), f.clone()],
            function.to_string(),
        ),
        (
            "an entry whose value is a function, then a key",
            vec![n(1), f.clone(), n(2)],
            odd(3),
        ),
        ("one key", vec![n(1)], odd(1)),
        (
            "two entries and a key",
            vec![n(1), n(2), n(3), n(4), n(5)],
            odd(5),
        ),
        ("two entries", vec![n(1), n(2), n(3), n(4)], String::new()),
    ] {
        let term = prim(Prim::Entries, args);
        match Evaluator::new(World::new()).run(&term) {
            Err(KernelError::Type(m)) => assert_eq!(m, expected, "{what}: {term}"),
            Ok(v) if expected.is_empty() => assert_eq!(v.to_string(), "{1 -> 2, 3 -> 4}"),
            other => panic!("{what}: {term}: no type error but {other:?}"),
        }
    }
}

/// The evaluator on its own, with no checker before it, never hashes or compares a key that
/// holds a function: a family is read, tested or built at such a key only to refuse it, with
/// a type error naming the step, and never a stop or an answer (row
/// FAIL-generic-get-function-key, "test hashing of a function-holding key on its own"). A
/// family is found by its keys' hashes (`Hash for Value`), which only data has, so the key is
/// refused before any lookup.
#[test]
fn the_evaluator_refuses_a_key_that_holds_a_function() {
    let f = Term::Lam(vec!["y".into()], Term::Var("y".into()).into());
    let key = prim(Prim::Tuple, vec![f.clone(), lit(Value::Int(1))]);
    let data = prim(Prim::Entries, vec![lit(Value::Int(1)), lit(Value::Int(2))]);
    let held = prim(Prim::Entries, vec![lit(Value::Int(1)), f.clone()]);
    for (what, term, expected) in [
        (
            "a family of data read at it",
            prim(Prim::Get, vec![data.clone(), key.clone()]),
            "`[k]` applied to a value that holds a function",
        ),
        (
            "a family of data tested at it",
            prim(Prim::Has, vec![key.clone(), data]),
            "`in` applied to a value that holds a function",
        ),
        (
            "a family holding a function read at it",
            prim(Prim::Get, vec![held.clone(), key.clone()]),
            "`[k]` at a function",
        ),
        (
            "a family holding a function tested at it",
            prim(Prim::Has, vec![key.clone(), held]),
            "`in` at a function",
        ),
        (
            "a display with it as a key",
            prim(Prim::Entries, vec![key.clone(), lit(Value::Int(1))]),
            "`{..}` applied to a function",
        ),
        (
            "a display with the function itself as a key",
            prim(Prim::Entries, vec![f, lit(Value::Int(1))]),
            "`{..}` applied to a function",
        ),
    ] {
        match Evaluator::new(World::new()).run(&term) {
            Err(KernelError::Type(m)) => assert_eq!(m, expected, "{what}: {term}"),
            other => panic!("{what}: {term}: no type error but {other:?}"),
        }
    }
}
