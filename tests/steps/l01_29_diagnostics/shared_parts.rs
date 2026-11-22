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
