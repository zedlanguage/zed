//! QUESTIONS A5, answer A (row A5-print): a printed type names each part it uses more than once
//! with a `type PartK = …;` definition, and the text, definitions included, reads back as the
//! same type. The kernel's tests of the text are `types::print::tests::
//! a_doubled_tuple_names_each_level_once`, and its benchmark `types::print::bench::
//! a_type_doubled_to_depth_n_prints_in_n_definitions`.

use zed_kernel::Value;
use zed_kernel::types::Type;
use zedc::check::read::parse_type;
use zedc::check::ty::Ty;

/// `t_0 = base` and `t_{k+1} = (t_k, t_k)`.
fn doubled(base: Type, d: usize) -> Type {
    (0..d).fold(base, |t, _| Type::tuple(vec![t.clone(), t]))
}

#[test]
fn a_doubled_tuple_reads_back_from_its_definitions() {
    let pair = Type::tuple(vec![Type::int(), Type::int()]);
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    for (base, d) in [
        (pair.clone(), 2),
        (pair, 12),
        (Type::tuple(vec![lit(1), lit(1)]), 5),
        (&Type::int() - &lit(1), 7),
    ] {
        let t = doubled(base, d);
        let s = t.surface();
        assert!(s.exact, "{s}");
        assert_eq!(s.defs.len(), d, "{s}");
        let back = parse_type(&s.to_string()).unwrap_or_else(|e| panic!("{s}: {e}"));
        assert!(back.subtype(&Ty::set(t.clone())), "{s}");
        assert!(Ty::set(t.clone()).subtype(&back), "{s}");
    }
}

/// Plan row TYPE-display-shared: the parity of the `c` overlapping one-tuples `(int \ i,)`, `i`
/// in `0..c`, built a literal at a time as `f & !x | !f & x`, whose clauses are `2^(c-1)`,
/// prints in at most `3c` definitions, one for each atom and two for each step
/// (`types::print::tests::the_parity_of_c_tuple_types_prints_in_o_c_definitions`, with the proof),
/// and the text, definitions included, reads back as the same type.
#[test]
fn the_parity_of_tuple_types_reads_back_from_its_definitions() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal");
    for c in [1usize, 2, 3, 5, 9] {
        let t = (0..c).fold(Type::empty(), |f, i| {
            let x = Type::tuple(vec![&Type::int() - &lit(i as i64)]);
            &(&f & &!&x) | &(&!&f & &x)
        });
        let s = t.surface();
        assert!(s.exact, "{s}");
        assert!(s.defs.len() <= 3 * c, "{c}: {s}");
        let back = parse_type(&s.to_string()).unwrap_or_else(|e| panic!("{s}: {e}"));
        assert!(back.subtype(&Ty::set(t.clone())), "{s}");
        assert!(Ty::set(t.clone()).subtype(&back), "{s}");
    }
}

/// A message names a part with a `type PartK` definition only where the message writes the
/// part more than once (row MSG-part-alias-written-once): a call of `f(x: int | rat)` with an
/// argument of a third carrier writes `int | rat` in place where it writes it once, and names
/// it where the note writes `f`'s type with the part twice, as `(x: Part1) -> Part1`.
#[test]
fn a_part_written_once_in_a_message_is_written_in_place() {
    use zed_tests::step_helpers::l01_29_diagnostics::rejected_with_main;
    for (src, named) in [
        ("f(x: int | rat) = 1;\ny = f(x: 1.5f64);\n", false),
        ("f(x: int | rat) = x;\ny = f(x: 1.5f64);\n", true),
        (
            "f(x: int | rat, z: int | rat) = 1;\ny = f(x: 1.5f64, z: 1);\n",
            true,
        ),
    ] {
        let e = rejected_with_main(src);
        assert!(
            e.contains("The suffix makes the literal `1.5f64` an `f64`, never `int | rat`."),
            "{e}"
        );
        assert_eq!(e.contains("type Part1 = int | rat;"), named, "{src}\n{e}");
        // Each name a definition gives is written at least twice in the message.
        if named {
            assert!(e.matches("Part1").count() >= 3, "{e}");
        }
    }
}

/// The text with each definition written out at each name for it: `(defs, text)` read back,
/// and the expanded text read back, as one type, each a subtype of the other and printed alike.
fn reads_as(shared: &str, expanded: &str) {
    let a = parse_type(shared).unwrap_or_else(|e| panic!("{shared}: {e}"));
    let b = parse_type(expanded).unwrap_or_else(|e| panic!("{expanded}: {e}"));
    assert!(a.subtype(&b), "{shared} <: {expanded}");
    assert!(b.subtype(&a), "{expanded} <: {shared}");
    assert_eq!(a.to_string(), b.to_string(), "{shared}");
}

/// Row PRINT-shared-part-exponential, case (a): a printed type reads a capitalized name as a
/// variable by the rule of a written type applied to the text with each definition written out
/// at each name for it (DESIGN.md sec:diagnostics, "Types in a message"), so the shared part of
/// `shared_rows(2)`, whose variables stand once in the definition and twice in the type, reads
/// back as the type written in full.
#[test]
fn a_definition_used_twice_counts_its_names_twice() {
    reads_as(
        "type Part1 = (T, (T, U));\n(T, U, V) -> (Part1, (Part1, V))",
        "(T, U, V) -> ((T, (T, U)), ((T, (T, U)), V))",
    );
    // A variable written only in the definition, which a definition used twice writes twice.
    reads_as(
        "type Part1 = (T, int);\n(Part1, Part1) -> int",
        "((T, int), (T, int)) -> int",
    );
}

/// Case (b): a definition used once writes each name of its body once, and a name written once
/// in all is an undefined name, as in a written type, so a misspelled type name is still caught.
/// The names are not of a type variable's form, `[A-Z][0-9]*`: every name of that form is a
/// variable whatever its count (DESIGN.md sec:type_resolution, rule 4), so only another
/// capitalized name is refused when written once.
#[test]
fn a_name_written_once_in_a_definition_used_once_is_refused() {
    for text in [
        "type Part1 = (Tx, int);\n(Part1) -> int",
        "type Part1 = (Tx, int);\n(T) -> (T, Part1)",
        "type Part1 = (Tx, int);\ntype Part2 = (Part1, int);\n(Part2) -> int",
        // A definition no name uses writes its body no time at all.
        "type Part1 = (Tx, Tx);\n(int) -> int",
    ] {
        let e = parse_type(text).expect_err(text);
        assert!(e.contains("Tx"), "{text}: {e}");
    }
}

/// Case (c): a definition used inside another writes its names as many times as the one that
/// uses it is used, times the uses there, and the outermost signature around a name for either
/// is the home of their variables.
#[test]
fn a_definition_used_inside_another_counts_through_it() {
    reads_as(
        "type Part1 = (T, int);\ntype Part2 = (Part1, int);\n(Part2, Part2) -> int",
        "(((T, int), int), ((T, int), int)) -> int",
    );
    reads_as(
        "type Part1 = (T, int);\ntype Part2 = (Part1, Part1);\n(Part2) -> int",
        "(((T, int), (T, int))) -> int",
    );
    reads_as(
        "type Part1 = (T, U);\ntype Part2 = (Part1, (Part1, U));\n(Part2, V) -> (V, T)",
        "(((T, U), ((T, U), U)), V) -> (V, T)",
    );
    // A type name used twice through a definition used once counts twice, so it is read as
    // the present rule reads the text written out; used once through it, it is refused.
    let twice = "type Part1 = (Tx, int);\ntype Part2 = (Part1, Part1);\n(Part2) -> int";
    let once = "type Part1 = (Tx, int);\ntype Part2 = (Part1, int);\n(Part2) -> int";
    assert_eq!(
        parse_type(twice).map(|t| t.to_string()),
        parse_type("(((Tx, int), (Tx, int))) -> int").map(|t| t.to_string()),
        "{twice}"
    );
    assert!(parse_type(once).is_err(), "{once}");
}

/// The count is found in one pass over the definitions, not by writing them out: a chain of 64
/// definitions each naming the one before twice writes `T` 2^64 times written out, which the
/// count holds saturated, and reads back in time linear in the text.
#[test]
fn a_chain_of_doubling_definitions_counts_without_writing_it_out() {
    let mut text = String::from("type Part1 = (T, int);\n");
    for k in 2..=64 {
        text.push_str(&format!("type Part{k} = (Part{}, Part{});\n", k - 1, k - 1));
    }
    text.push_str("(Part64) -> int");
    let start = std::time::Instant::now();
    let t = parse_type(&text).unwrap_or_else(|e| panic!("{e}"));
    assert!(start.elapsed() < std::time::Duration::from_secs(2));
    assert_eq!(t.fns.len(), 1, "{t}");
}
