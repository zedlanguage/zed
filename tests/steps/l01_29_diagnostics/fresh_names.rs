//! A type variable a message prints is named apart from every name the program binds
//! (DESIGN.md sec:diagnostics, "Types in a message"): a type in a message is read in the
//! program's scope, so a program that binds `T` never sees a variable printed `T`, which a
//! reader would take for the program's own `T` (MSG-fresh-name-clash). The names are those of
//! the whole file, in any scope, so one numbering serves every message of the file.

use std::sync::Arc;

use zedc::check::read::parse_type;
use zedc::check::ty::{ProgramNames, Sig};

use super::rejected;

/// The type of the function the first line of the rejection of `src` says `==` cannot take.
fn compared(src: &str) -> String {
    let out = rejected(src);
    let first = out.lines().next().expect("a message");
    let (_, rest) = first
        .split_once("may hold a function, `")
        .unwrap_or_else(|| panic!("no function type shown:\n{out}"));
    rest[..rest.find('`').expect("the end of the type")].into()
}

/// That `text`, written as a parameter's type in a program that binds the names `defs` does,
/// reads back to the same text: the bounds clause binds its own variables, and the program's
/// names keep their meaning beside it. The only rejection is the call that passes nothing.
fn writes_back_beside(defs: &str, text: &str) {
    let src = format!("{defs}u(positional v: {text}) = 1;\nm(positional n: int) = u();\n");
    let out = rejected(&src);
    let errors: Vec<&str> = (out.lines())
        .filter(|l| !l.starts_with(char::is_whitespace))
        .collect();
    assert_eq!(errors.len(), 1, "`{text}` as a written type:\n{out}");
    assert!(
        errors[0].contains("this call of `u` gives no value to its parameter `v`"),
        "`{text}` as a written type:\n{out}"
    );
    assert!(
        out.contains(&format!(
            "the type the checker found for `u` is `({text}) -> 1`"
        )),
        "`{text}` does not read back as itself:\n{out}"
    );
}

/// The names the bounds clauses of `text` bind, in the order of the clauses.
fn bound_names(text: &str) -> Vec<Arc<str>> {
    let t = parse_type(text).unwrap_or_else(|why| panic!("{why}"));
    assert_eq!(t.fns.len(), 1, "{text}");
    t.fns[0].bounds.keys().cloned().collect()
}

#[test]
fn a_program_that_binds_t_and_u_sees_its_variable_named_v() {
    // The finding: with `T` and `U` bound to numbers, the message printed `(T) -> T for T in
    // …`, and a reader of `T` here could not tell the variable from the program's `T`.
    let defs = "T = 1;\nU = 2;\n";
    let shown = compared(&format!("{defs}inc = x -> x + 1;\nsame = inc == inc;\n"));
    assert_eq!(shown, "V -> V for V in int | f32 | f64 | rat");
    assert_eq!(bound_names(&shown), ["V".into()] as [Arc<str>; 1]);
    writes_back_beside(defs, &shown);
    // The same function in a program that binds neither keeps the first name.
    let shown = compared("inc = x -> x + 1;\nsame = inc == inc;\n");
    assert_eq!(shown, "T -> T for T in int | f32 | f64 | rat");
    writes_back_beside("", &shown);
}

#[test]
fn every_derivation_step_of_the_message_uses_the_same_free_name() {
    let out =
        rejected("T = 1;\nU = 2;\ninc = x -> x + 1;\nboxed = #box(inc);\nsame = boxed == boxed;\n");
    assert!(
        out.contains("`inc` is V -> V for V in int | f32 | f64 | rat here"),
        "{out}"
    );
    assert!(
        out.contains("`inc` is defined as this expression, V -> V for V in int | f32 | f64 | rat"),
        "{out}"
    );
    // No step names a variable `T` or `U`: each `T` or `U` of the message is the program's.
    assert!(
        !out.contains("(T)") && !out.contains("for T ") && !out.contains("for U "),
        "{out}"
    );
}

#[test]
fn the_names_after_w_are_skipped_too() {
    // `T`, `U`, `V`, `W` and `T5` are the program's; the next free name is `T6`.
    let defs = "T = 1;\nU = 2;\nV = 3;\nW = 4;\nT5 = 5;\n";
    let shown = compared(&format!("{defs}inc = x -> x + 1;\nsame = inc == inc;\n"));
    assert_eq!(shown, "T6 -> T6 for T6 in int | f32 | f64 | rat");
    writes_back_beside(defs, &shown);
}

#[test]
fn only_the_names_a_variable_could_take_are_skipped() {
    // Two variables: `U` is the program's, so they are `T` and `V`.
    let pair = "pair(positional x, positional y) = (x * 2, y * 2);\nsame = pair == pair;\n";
    let shown = compared(&format!("U = 1;\n{pair}"));
    assert_eq!(
        shown,
        "(T, V) -> (T, V) for T in int | f32 | f64 | rat, V in int | f32 | f64 | rat"
    );
    writes_back_beside("U = 1;\n", &shown);
    // `T1` to `T4` and `T05` are no variable's name, so binding them changes nothing; a
    // parameter `T` of another function is a name of the file too, and is skipped.
    let defs = "T1 = 1;\nT2 = 2;\nT4 = 4;\nT05 = 5;\n";
    let shown = compared(&format!("{defs}{pair}"));
    assert_eq!(
        shown,
        "(T, U) -> (T, U) for T in int | f32 | f64 | rat, U in int | f32 | f64 | rat"
    );
    writes_back_beside(defs, &shown);
    let shown = compared(&format!("g(positional T) = T;\n{pair}"));
    assert_eq!(
        shown,
        "(U, V) -> (U, V) for U in int | f32 | f64 | rat, V in int | f32 | f64 | rat"
    );
    // A field is in no scope: a struct's field `T` would leave `T` free (structs come at L2,
    // so this is the resolver's kind, not a program here).
}

/// The signature `(inner, T) -> T for T in int | rat` with `inner` as its first parameter's
/// type: an inner signature that bounds `T` again, which the printer renames.
fn shadowing(inner: &str) -> Sig {
    let outer = parse_type("(int, T) -> T for T in int | rat").unwrap();
    let inner = parse_type(inner).unwrap();
    let mut s = (*outer.fns[0]).clone();
    s.arrows[0].params[0] = inner;
    s
}

#[test]
fn the_printer_renames_an_inner_signature_apart_from_the_program_names() {
    let s = shadowing("(T) -> T for T in int");
    assert_eq!(
        s.to_string(),
        "(U -> U for U in int, T) -> T for T in int | rat"
    );
    {
        // While a program that binds `U` and `V` is checked, the inner `T` takes `W`.
        let _names = ProgramNames::hold(["U", "V", "x"]);
        assert_eq!(
            s.to_string(),
            "(W -> W for W in int, T) -> T for T in int | rat"
        );
        {
            // A check started inside it holds its own names, and gives the outer ones back.
            let _inner = ProgramNames::hold(["U"]);
            assert_eq!(
                s.to_string(),
                "(V -> V for V in int, T) -> T for T in int | rat"
            );
        }
        assert_eq!(
            s.to_string(),
            "(W -> W for W in int, T) -> T for T in int | rat"
        );
    }
    assert_eq!(
        s.to_string(),
        "(U -> U for U in int, T) -> T for T in int | rat"
    );
}

/// A program binding `T`, `U`, `V`, `W` and `T5` to `T(n + 4)`, with `n` generic functions and
/// one comparison of the first: each function's variable is named `T(n + 5)`.
pub(super) fn crowded(n: usize) -> String {
    let mut src = String::from("T = 0;\nU = 0;\nV = 0;\nW = 0;\n");
    for k in 5..n + 5 {
        src += &format!("T{k} = {k};\n");
    }
    for i in 0..n {
        src += &format!("g{i} = x -> x + {i};\n");
    }
    src + "same = g0 == g0;\n"
}

/// The type the comparison of [`crowded`]`(n)` shows: its variable named past the `n + 4`
/// names the program binds.
pub(super) fn first(n: usize) -> String {
    format!("T{m} -> T{m} for T{m} in int | f32 | f64 | rat", m = n + 5)
}

/// The rejection of [`crowded`]`(n)` names each function's variable past the program's names.
pub(super) fn variables_named_past_the_program_names(src: &str, n: usize) {
    let out = rejected(src);
    assert!(out.contains(&first(n)), "{out}");
}

#[test]
fn naming_variables_beside_many_program_names() {
    for n in [1, 3, 12] {
        let src = crowded(n);
        assert_eq!(compared(&src), first(n));
        variables_named_past_the_program_names(&src, n);
    }
}

/// `ap` takes a pair of two `int | #x`, so a message about it defines that part; the program
/// binds `defs` too.
fn defining(defs: &str) -> String {
    format!("{defs}ap(positional g: (int | #x, int | #x)) = 0;\nh() = ap(1);\nmain() = 0;\n")
}

#[test]
fn a_definition_skips_the_program_names_by_the_same_rule() {
    // The definitions (MSG-type-defs-layout) pick their names with the same function as the
    // variables, so the names the program binds are skipped there too.
    for (defs, name) in [
        ("", "T1"),
        ("T1 = 1;\nT2 = 2;\n", "T3"),
        ("T = 1;\nT2 = 2;\n", "T1"),
    ] {
        let out = rejected(&defining(defs));
        assert!(
            out.contains(&format!("    type {name} = int | #x;")),
            "{name} for {defs:?}:\n{out}"
        );
        assert!(
            out.contains(&format!("`ap` takes (({name}, {name})) -> 0")),
            "{out}"
        );
    }
}
