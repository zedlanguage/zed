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
/// prints in at most `2c` definitions (`types::print::tests::the_parity_of_c_tuple_types_prints_in_o_c_definitions`),
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
        assert!(s.defs.len() <= 2 * c, "{c}: {s}");
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
