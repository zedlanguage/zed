//! A type variable a message prints is named apart from every name the program binds
//! (DESIGN.md sec:diagnostics, "Types in a message"): a type in a message is read in the
//! program's scope, so a program that binds `T` never sees a variable printed `T`, which a
//! reader would take for the program's own `T` (MSG-fresh-name-clash). The names are those of
//! the whole file, in any scope, so one numbering serves every message of the file. Since
//! QUESTIONS Q23 only a type variable has a name of the form `[A-Z][0-9]*`, so a program binds
//! such a name by writing it in a signature ([`holding`]).

use std::sync::Arc;

use zedc::check::read::parse_type;
use zedc::check::ty::{ProgramNames, Sig};

use super::rejected;

/// The type of the operand the first line of the rejection of `src` says `==` cannot compare,
/// shown as `` `name : type` in `code` ``.
fn compared(src: &str) -> String {
    let out = rejected(src);
    let first = out.lines().next().expect("a message");
    let (_, rest) = first
        .split_once("Cannot compare a value that may hold a function: `")
        .and_then(|(_, rest)| rest.split_once(" : "))
        .unwrap_or_else(|| panic!("no operand and type shown:\n{out}"));
    rest[..rest.find("` in `").expect("the end of the type")].into()
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

/// A function for each of `names` whose signature writes it twice, so the file binds it as a
/// type variable.
fn holding(names: &[&str]) -> String {
    (names.iter().enumerate())
        .map(|(i, n)| format!("k{i}(a: {n}, b: {n}) = 0;\n"))
        .collect()
}

/// The names the bounds clauses of `text` bind, in the order of the clauses.
fn bound_names(text: &str) -> Vec<Arc<str>> {
    let t = parse_type(text).unwrap_or_else(|why| panic!("{why}"));
    assert_eq!(t.fns.len(), 1, "{text}");
    t.fns[0].bounds.keys().cloned().collect()
}

#[test]
fn a_program_that_binds_t_and_u_sees_its_variable_named_v() {
    // The finding: with `T` and `U` bound (to numbers, before Q23), the message printed
    // `(T) -> T for T in …`, and a reader of `T` here could not tell the variable from the
    // program's `T`.
    let defs = &holding(&["T", "U"]);
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
    let out = rejected(&format!(
        "{}inc = x -> x + 1;\nboxed = #box(inc);\nsame = boxed == boxed;\n",
        holding(&["T", "U"])
    ));
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
    let defs = &holding(&["T", "U", "V", "W", "T5"]);
    let shown = compared(&format!("{defs}inc = x -> x + 1;\nsame = inc == inc;\n"));
    assert_eq!(shown, "T6 -> T6 for T6 in int | f32 | f64 | rat");
    writes_back_beside(defs, &shown);
}

#[test]
fn only_the_names_a_variable_could_take_are_skipped() {
    // Two variables: `U` is the program's, so they are `T` and `V`.
    let pair = "pair(positional x, positional y) = (x * 2, y * 2);\nsame = pair == pair;\n";
    let one = holding(&["U"]);
    let shown = compared(&format!("{one}{pair}"));
    assert_eq!(
        shown,
        "(T, V) -> (T, V) for T in int | f32 | f64 | rat, V in int | f32 | f64 | rat"
    );
    writes_back_beside(&one, &shown);
    // `T1` to `T4` and `T05` are no printed variable's name, so binding them changes nothing;
    // a variable `T` of another function's body is a name of the file too, and is skipped.
    let defs = &holding(&["T1", "T2", "T4", "T05"]);
    let shown = compared(&format!("{defs}{pair}"));
    assert_eq!(
        shown,
        "(T, U) -> (T, U) for T in int | f32 | f64 | rat, U in int | f32 | f64 | rat"
    );
    writes_back_beside(defs, &shown);
    let shown = compared(&format!(
        "g(positional x) = {{ h = (y: T, z: T) -> y; h(x, x) }};\n{pair}"
    ));
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

/// A program binding `T`, `U`, `V`, `W` and `T5` to `T(n + 4)` as type variables, each in a
/// signature of its own, with `n` generic functions and one comparison of the first: each
/// function's variable is named `T(n + 5)`.
pub(super) fn crowded(n: usize) -> String {
    let mut src = holding(&["T", "U", "V", "W"]);
    for k in 5..n + 5 {
        src += &format!("t{k}(a: T{k}, b: T{k}) = 0;\n");
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

/// The lines of `out` that hold `part`, for a failure message.
fn lines_with<'a>(out: &'a str, part: &str) -> Vec<&'a str> {
    out.lines().filter(|l| l.contains(part)).collect()
}

#[test]
fn a_type_variable_the_declaration_writes_prints_by_its_written_name() {
    // Plan row MSG-type-vars-printed-renamed: a variable the declaration writes is printed by
    // the name it wrote, which the names drawn for the other variables skip. Unbounded, it
    // stands twice in the type of `g`, which printed `(U, U) -> (U, U)`.
    let out = rejected(
        "g(positional y: T, positional z: T) = (y, z);\nmain(m: MainArgs) { m.stdout <- [g]; }\n",
    );
    assert!(
        out.contains("`m.stdout <- [g] : 0 -> (T, T) -> (T, T)`"),
        "{out}"
    );
    // Bounded by carriers, it printed `(U, U) -> U for U in int | f32 | f64 | rat`.
    let out = rejected(
        "f(positional a: T, positional b: T) = a + b;\n\
         main(m: MainArgs) { x = f(1, \"s\"); m.stdout <- [\"a\"]; }\n",
    );
    assert!(
        out.contains("`f` takes (T, T) -> T for T in int | f32 | f64 | rat"),
        "{out}"
    );
    // Control: the same functions with no variable written, in a program that writes `T`
    // elsewhere, still name theirs apart from it.
    let defs = holding(&["T"]);
    let out = rejected(&format!(
        "{defs}g(positional y, positional z) = (y, z);\nmain(m: MainArgs) {{ m.stdout <- [g]; }}\n"
    ));
    assert!(
        out.contains("`m.stdout <- [g] : 0 -> (U, V) -> (U, V)`"),
        "{out}"
    );
    let out = rejected(&format!(
        "{defs}f(positional a, positional b) = a + b;\n\
         main(m: MainArgs) {{ x = f(1, \"s\"); m.stdout <- [\"a\"]; }}\n"
    ));
    assert!(
        out.contains("`f` takes (U, U) -> U for U in int | f32 | f64 | rat"),
        "{out}"
    );
}

/// `k` writes `T` for two parameters and pushes both to `out`, which takes only text, and
/// `main` calls it with two numbers.
const PUSHES_T: &str = "k(positional z: T, positional w: T, out: Lines) { out <- [z, w]; }\n\
                        main(m: MainArgs) { k(5, 6, out: m.stdout); }\n";

#[test]
fn the_declared_step_and_the_note_print_the_written_name() {
    // The step on the declaration printed `(U, U, out: …)` (row
    // MSG-type-vars-printed-renamed), and the note on the pushed value, read after `k` ended,
    // printed its `T` as `_` (row MSG-headline-note-disagree).
    let out = rejected(PUSHES_T);
    let declared = "the type the checker found for `k` is `(T, T, out: Lines) -> ()`";
    assert!(out.contains(declared), "{out}");
    assert!(
        out.contains("this expression is (0 | 1) -> T"),
        "{:?}\n{out}",
        lines_with(&out, "this expression is")
    );
}

#[test]
fn the_note_on_a_push_prints_the_types_the_call_binds() {
    // DESIGN.md sec:diagnostics, "Types in a message": "the rejection of `h(x: "a", y: 5,
    // out: m.stdout)` writes the note `this expression is (0 | 1 | 2) -> 5 | String`, not
    // `(0 | 1 | 2) -> _`", while the declaration's type keeps `y: _`, "a type the parameter's
    // uses decide" (plan rows MSG-untyped-signature-placeholder,
    // MSG-signature-untyped-placeholder). The headline printed the bound type before; the
    // note printed the body's.
    let src = "h(x, y, out: Lines) { out <- [x, y, x.upper]; }\n\
               main(m: MainArgs) { h(x: \"a\", y: 5, out: m.stdout); }\n";
    let out = rejected(src);
    assert!(
        out.contains("this expression is (0 | 1 | 2) -> 5 | String"),
        "{:?}\n{out}",
        lines_with(&out, "this expression is")
    );
    assert!(!out.contains("-> _\n"), "{out}");
    assert!(out.contains("y: _, out: Lines) -> ()`"), "{out}");
}

/// The step on the declaration of `k` in `out`, from "the type the checker found" to the end
/// of its line.
fn declared_k(out: &str) -> String {
    let at = (out.find("the type the checker found for `k` is"))
        .unwrap_or_else(|| panic!("no declared step for `k`:\n{out}"));
    out[at..].lines().next().expect("a line").into()
}

#[test]
fn a_written_parameter_type_prints_as_written() {
    // Plan row MSG-written-param-type-printed: the declared step printed `out: Lines` as the
    // list type it denotes, `[String | #ioError(op: String, path: String, why: String)]`.
    // Probe k2 of row MSG-type-vars-printed-renamed:
    let k2 = "h0(positional f, positional m) = m.map(f);\n\
              h1(positional f, positional m) = h0(f, m).map(f);\n\
              h2(positional f, positional m) = h1(f, m).map(f);\n\
              g(positional f) = m -> h2(f, m);\n\
              k(positional y: U, positional z: T, positional w: T, positional f: U -> U, \
              out: Lines) { r = g(f)([y]); out <- r; out <- [z, w]; }\n\
              main(m: MainArgs) { a = \"a\" ++ \"\"; k(a, 5, 6, s -> s ++ \"!\", out: m.stdout); }\n";
    assert_eq!(
        declared_k(&rejected(k2)),
        "the type the checker found for `k` is `(U, T, T, U -> U, out: Lines) -> ()`"
    );
    // A written alias of a range prints as written, as it did by its range; the control, `v`
    // with no type written, prints the type the checker found for it.
    let some = "k(positional z: T, positional w: T, positional u: u8, positional v, \
                out: Lines) { out <- [z, w]; x = v + 1; }\n\
                main(m: MainArgs) { k(5, 6, 7, 8, out: m.stdout); }\n";
    assert_eq!(
        declared_k(&rejected(some)),
        "the type the checker found for `k` is `(T, T, u8, U, out: Lines) -> () for U in int | \
         f32 | f64 | rat`"
    );
}

#[test]
fn a_written_name_a_function_around_binds_is_printed_apart() {
    // In the body of `h`, which writes `T`, a `T` means `h`'s: the type of `g`, which writes
    // `T` too, is printed with another name there, and `h`'s own steps print its `T`.
    let out = rejected(
        "g(positional y: T, positional z: T) = (y, z);\n\
         h(positional a: T, positional b: T, out: Lines) { out <- [a]; out <- [g]; }\n\
         main(m: MainArgs) { h(1, 2, out: m.stdout); }\n",
    );
    assert!(
        out.contains("`out <- [g] : 0 -> (U, U) -> (U, U)`"),
        "{:?}\n{out}",
        lines_with(&out, "out <- [g]")
    );
    assert!(
        out.contains("the type the checker found for `h` is `(T, T, out:"),
        "{out}"
    );
    assert!(out.contains("this expression is 0 -> T"), "{out}");
}

#[test]
fn what_else_leaves_of_a_written_variable_prints_by_its_written_name() {
    // `r else #a -> 0` leaves `r` without `#a`, which is printed with `r`'s own variable
    // (`Scope::open` joins the two by the `Narrow` need) and the difference (DESIGN.md
    // sec:diagnostics; else1x1): `T -> (T \ (#a | #a(..))) | 0` with no variable written. With
    // `T` written, the variable is kept, and its leftover must still print `T`, not `_`, which
    // says the result takes every value (found by proofdoc4c, checking `Sig::standing_twice`
    // against 9ff4e6673). A `T` written once is refused, so the written form writes it for two
    // parameters.
    for (src, shown) in [
        (
            "g(positional r) = r else #a -> 0;\n",
            "0 -> T -> (T \\ (#a | #a(..))) | 0",
        ),
        (
            "g(positional r: T, positional s: T) = (r else #a -> 0, s);\n",
            "0 -> (T, T) -> ((T \\ (#a | #a(..))) | 0, T)",
        ),
    ] {
        let out = rejected(&format!("{src}main(m: MainArgs) {{ m.stdout <- [g]; }}\n"));
        assert!(
            out.contains(&format!("`m.stdout <- [g] : {shown}`")),
            "{src}{:?}\n{out}",
            lines_with(&out, "m.stdout <- [g]")
        );
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
    // variables, so the names the program binds are skipped there too. A type variable `T1`
    // is no definition's name, so it changes nothing.
    for (defs, name) in [
        ("", "Part1"),
        ("Part1 = 1;\nPart2 = 2;\n", "Part3"),
        ("Part2 = 2;\nk(a: T1, b: T1) = 0;\n", "Part1"),
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
