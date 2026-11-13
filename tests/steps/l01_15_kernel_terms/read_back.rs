//! The printer writes negation, `!`, a tuple component, a family entry and an atom as a
//! program writes them (`-x`, `!x`, `t[0]`, `f[k]`, `#err(code: 3)`), never as calls no program
//! can write (repair PRIM-hidden-names). Each printed term is read back by the parser and the
//! elaborator: the forms elaboration builds come back as the same term, and the rest as a term
//! with the same value.

use zed_kernel::term::build::{app, lam, lit, prim, var};
use zed_kernel::{Evaluator, Family, Prim, Term, Value, World};
use zed_tests::kernel::*;

use zed_tests::step_helpers::l01_16_elaboration::elab;

/// The term of the definition `x` of `text`.
fn x_of(text: &str) -> Term {
    let unit = elab(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    unit.defs
        .iter()
        .find(|d| d.name == "x")
        .unwrap_or_else(|| panic!("{text}: no `x`"))
        .term
        .as_ref()
        .clone()
}

/// `t` printed, then read back as the definition `x`.
fn read_back(t: &Term) -> Term {
    x_of(&format!("x = {t};\n"))
}

fn value(t: &Term) -> Value {
    Evaluator::new(World::new())
        .run(t)
        .unwrap_or_else(|e| panic!("{t}: {e:?}"))
}

/// Each source, elaborated and printed, prints as written and reads back as the same term.
#[test]
fn an_elaborated_term_reads_back_as_itself() {
    // A power takes a parameter, not a literal, as its other operand: a literal without a
    // suffix beside an operand of no fixed carrier takes that operand's carrier at run time,
    // and its elaboration binds the operand to a name no program can write (steps L1.26a). A
    // decimal base is such a literal since `f32` is a carrier: `2.0^-a` chooses `2.0f32` or
    // `2.0` by the carrier of `-a`.
    let cases = [
        ("(a) -> -a", "a -> -a"),
        ("(c) -> !c", "c -> !c"),
        ("(a, b) -> -(a + b)", "(a, b) -> -(a + b)"),
        ("(a, b) -> !(a < b)", "(a, b) -> !(a < b)"),
        ("(a) -> -(-a)", "a -> -(-a)"),
        ("(c) -> !(!c)", "c -> !(!c)"),
        ("(a, k) -> (-a)^k", "(a, k) -> ((-a)^k)"),
        ("(a, k) -> -a^k", "(a, k) -> -(a^k)"),
        ("(a, b, c) -> a^b^c", "(a, b, c) -> (a^(b^c))"),
        ("(a, b, c) -> (a^b)^c", "(a, b, c) -> ((a^b)^c)"),
        ("(a, b, k) -> (a + b)^k", "(a, b, k) -> ((a + b)^k)"),
        ("(a, b, k) -> a * b^k", "(a, b, k) -> (a * (b^k))"),
        ("(a, k) -> a ^ k", "(a, k) -> (a^k)"),
        ("(a, b) -> a - -b", "(a, b) -> (a - -b)"),
        ("(t) -> t[0]", "t -> t[0]"),
        ("(t) -> t[0][1]", "t -> t[0][1]"),
        ("(t) -> -t[1]", "t -> -t[1]"),
        ("(t) -> (t[0], t[1])[1]", "t -> (t[0], t[1])[1]"),
        ("(a) -> #err(a)", "a -> #err(a)"),
        (
            "(a, b) -> #err(code: a, msg: b)",
            "(a, b) -> #err(code: a, msg: b)",
        ),
        ("(a) -> #ok(-a, !true)", "a -> #ok(-a, !true)"),
    ];
    for (src, printed) in cases {
        let t = x_of(&format!("x = {src};\n"));
        assert_eq!(t.to_string(), printed, "{src}");
        assert_eq!(read_back(&t), t, "{src} printed {t}");
    }
}

/// Terms no elaboration builds in these shapes, built by hand, read back as the same term:
/// the printer parenthesizes an operand wherever the grammar would read it otherwise.
#[test]
fn a_built_term_reads_back_with_its_parentheses() {
    let neg = |t: Term| prim(Prim::Neg, vec![t]);
    let cases = [
        (neg(lit(-3)), "-(-3)"),
        (neg(neg(lit(3))), "-(-3)"),
        (
            prim(Prim::Not, vec![prim(Prim::Not, vec![lit(true)])]),
            "!(!true)",
        ),
        (prim(Prim::Pow, vec![neg(lit(2)), lit(2)]), "((-2)^2)"),
        (prim(Prim::Pow, vec![lit(2), neg(lit(-1))]), "(2^-(-1))"),
        (
            nth(
                app(
                    lam(&["p"], var("p")),
                    vec![prim(Prim::Tuple, vec![lit(5), lit(6)])],
                ),
                1,
            ),
            "(p -> p)((5, 6))[1]",
        ),
    ];
    for (t, printed) in cases {
        assert_eq!(t.to_string(), printed);
        let back = read_back(&t);
        // `-(-3)` written from a literal -3 reads back as two negations of 3: the same value.
        if t != back {
            assert_eq!(value(&back), value(&t), "{printed}");
        }
    }
    assert_eq!(read_back(&neg(neg(lit(3)))), neg(neg(lit(3))));
    // An index of a prefix operation keeps its parentheses. No well-typed program indexes a
    // negation, so this one is checked as printed only.
    let indexed = nth(neg(prim(Prim::Tuple, vec![lit(1), lit(2)])), 0);
    assert_eq!(indexed.to_string(), "(-(1, 2))[0]");
}

/// `get` comes only from the staging of lookup ports, and the primitives as values only from
/// hand-built terms: no program writes them as such, so their written forms read back as
/// other terms, `f[k]` as an application and `(x -> -x)` as a lambda, of the same value.
#[test]
fn an_entry_and_a_primitive_function_read_back_as_terms_of_the_same_value() {
    // Each is read back on its own and then applied, so the family argument is never printed.
    let family = || lit(Family::of([("qty", 3), ("price", 7)]));
    let pair = || prim(Prim::Tuple, vec![lit(10), lit(20)]);
    let entry = lam(&["f"], get(var("f"), lit("price")));
    assert_eq!(entry.to_string(), "f -> f[\"price\"]");
    let cases = [
        (entry, vec![family()], "f -> f[\"price\"]"),
        (Term::PrimFn(Prim::Neg), vec![lit(4)], "(x -> -x)"),
        (Term::PrimFn(Prim::Not), vec![lit(true)], "(x -> !x)"),
        (
            Term::PrimFn(Prim::Get),
            vec![family(), lit("qty")],
            "((f, k) -> f[k])",
        ),
    ];
    for (f, args, printed) in cases {
        assert_eq!(f.to_string(), printed);
        let back = read_back(&f);
        assert_eq!(
            value(&app(back, args.clone())),
            value(&app(f, args)),
            "{printed}"
        );
    }
    // DESIGN.md indexes a tuple as it indexes anything (`m[k]`), but elaboration builds
    // `tupleGet` only for a literal index (step L1.9) and an application otherwise, which the
    // evaluator refuses on a tuple. So this form is checked as printed only.
    let component = Term::PrimFn(Prim::TupleGet);
    assert_eq!(component.to_string(), "((t, i) -> t[i])");
    assert_eq!(value(&app(component, vec![pair(), lit(1)])), Value::Int(20));
}

/// An atom whose name or field names are not literals has no written form: its name is `#_`
/// and its payload positional. Elaboration never builds one.
#[test]
fn an_atom_with_no_literal_name_is_written_any_atom() {
    let named = prim(
        Prim::Atom,
        vec![var("n"), lit(Value::tuple(Vec::new())), var("a")],
    );
    assert_eq!(named.to_string(), "#_(a)");
    let fields = prim(Prim::Atom, vec![lit("err"), var("fs"), var("a"), var("b")]);
    assert_eq!(fields.to_string(), "#err(a, b)");
}
