//! Types of every form a type's `Debug` text holds, for the test that the text is the one the
//! derived `Debug`s wrote (debug_text.txt was written by them, before step T2-types-rest).

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::value::Value;

fn next(s: &mut u64) -> u64 {
    *s = s
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *s >> 33
}

/// A random type `d` deep.
fn random(s: &mut u64, d: u32) -> Type {
    let k = next(s);
    if d == 0 || k.is_multiple_of(7) {
        return match k % 6 {
            0 => Type::int(),
            1 => Type::string(),
            2 => Type::bool(),
            3 => Type::lit(&Value::Int((k % 5) as i64)).unwrap(),
            4 => Type::atom(["a", "b"][(k % 2) as usize]),
            _ => Type::empty(),
        };
    }
    let mut part = || random(s, d - 1);
    match k % 9 {
        0 => Type::tuple(vec![part(), part()]),
        1 => Type::tuple(vec![part()]),
        2 => Type::atom_with(["a", "b"][(k % 2) as usize], &Type::tuple(vec![part()])),
        3 => Type::exact(part(), part()),
        4 => Type::partial(part(), part()),
        5 => &part() | &part(),
        6 => &part() & &part(),
        7 => &part() - &part(),
        _ => !part(),
    }
}

/// Each scalar part, tuples of two lengths, atoms with and without payloads, morphisms,
/// complements, a tuple part kept as an expression, a recursive type, and random types, one with
/// a shared diagram node, and an xor chain whose expressions share operands.
pub fn samples() -> Vec<Type> {
    let lit = |i: i64| Type::lit(&Value::Int(i)).unwrap();
    let one = |t: Type| Type::tuple(vec![t]);
    let xor = |a: &Type, b: &Type| &(a - b) | &(b - a);
    let (w, x, y, z) = (one(lit(1)), one(lit(2)), one(lit(3)), one(lit(4)));
    let t = || Expr::Ref(0, vec![Expr::Param(0)]);
    let tree = Group::new(vec![Def {
        name: "Tree".into(),
        params: vec!["A".into()],
        body: Expr::Union(vec![
            Expr::Atom("leaf".into(), vec![Expr::Param(0)]),
            Expr::Atom("fork".into(), vec![t(), t()]),
        ]),
    }])
    .unwrap()
    .instance(vec![Type::string()])
    .remove(0);
    let mut out = vec![
        Type::empty(),
        Type::top(),
        Type::int(),
        &Type::bool() | &Type::string(),
        &lit(7) | &Type::rat(),
        Type::tuple(vec![Type::int(), Type::string()]),
        &one(Type::int()) | &Type::tuple(vec![Type::bool(), Type::bool()]),
        !one(Type::int()),
        &Type::atom_with("a", &one(lit(1))) | &Type::atom("b"),
        !Type::atom("b"),
        &Type::exact(Type::string(), Type::int()) | &Type::partial(Type::int(), Type::bool()),
        !Type::exact(Type::int(), Type::int()),
        &xor(&w, &y) & &xor(&x, &z),
        !(&xor(&w, &y) & &xor(&x, &z)),
        &(&w | &x) - &(&xor(&w, &y) & &xor(&x, &z)),
        Type::tuple(vec![tree, Type::int()]),
    ];
    let mut seed = 5;
    out.extend((0..12).map(|_| random(&mut seed, 3)));
    // A tuple part whose diagram has a node reached by two edges.
    let mut seed = 3;
    out.extend((0..=1172).map(|_| random(&mut seed, 5)).last());
    // An xor chain of four one-tuples, whose expressions share their operands.
    out.push((1..4).fold(one(lit(0)), |t, i| {
        &(&t - &one(lit(i))) | &(&one(lit(i)) - &t)
    }));
    out
}
