use super::*;

/// Every union of a subset of `lits`, and the complement of each within `within`.
fn subsets_and_complements(lits: &[Type], within: &Type) -> Vec<Type> {
    let finite: Vec<Type> = (0..1u32 << lits.len())
        .map(|mask| {
            Type::union_all(
                (0..lits.len())
                    .filter(|i| mask & (1 << i) != 0)
                    .map(|i| lits[i].clone()),
            )
        })
        .collect();
    let complements: Vec<Type> = finite.iter().map(|t| within - t).collect();
    finite.into_iter().chain(complements).collect()
}

/// `scalar_cell` decides a meet or a difference of two scalar-only types from their parts;
/// each answer must be what the explicit set operation and `is_empty` give.
fn agree(all: &[Type]) {
    // A type as an operand in a failure message, in the surface syntax.
    let op = |t: &Type| t.surface_operand();
    for a in all {
        for b in all {
            assert_eq!(
                a.scalar_cell(b, true),
                Some((a & b).is_empty()),
                "{} & {}",
                op(a),
                op(b)
            );
            assert_eq!(
                a.scalar_cell(b, false),
                Some((a - b).is_empty()),
                "{} \\ {}",
                a.surface_in_union(),
                op(b)
            );
        }
    }
}

#[test]
fn scalar_cells_agree_with_explicit_set_operations() {
    // The 32 types of the old review test: the subsets of 0..4 and their complements in int.
    let ints: Vec<Type> = (0..4).map(|i| Type::lit(&Value::Int(i)).unwrap()).collect();
    let all = subsets_and_complements(&ints, &Type::int());
    assert_eq!(all.len(), 32);
    agree(&all);
}

#[test]
fn scalar_cells_agree_with_explicit_set_operations_across_carriers() {
    // One or two literals of each carrier, so that every clause of `scalar_cell` decides
    // some pair: 128 types, finite and cofinite in each carrier.
    let half = Rat::decimal("0.5").expect("given").unwrap();
    let lits: Vec<Type> = [
        Value::Bool(true),
        Value::Int(0),
        Value::rat(half),
        Value::float(0.5),
        Value::str("a"),
        Value::str("b"),
    ]
    .iter()
    .map(|v| Type::lit(v).unwrap())
    .collect();
    let scalars = Type::union_all([
        Type::bool(),
        Type::int(),
        Type::rat(),
        Type::f64(),
        Type::string(),
    ]);
    let all = subsets_and_complements(&lits, &scalars);
    assert_eq!(all.len(), 128);
    agree(&all);
}

/// [`Atoms::zip`] by the walk over the smaller map alone, as it was before the diff.
fn zip_by_walk(a: &Atoms, b: &Atoms, op: Op) -> Atoms {
    let (large, small) = if a.names.len() >= b.names.len() {
        (a, b)
    } else {
        (b, a)
    };
    let mut out = match (op, small.cofinite) {
        (Op::Or, false) | (Op::And, true) => large.clone(),
        _ => Atoms::default(),
    };
    out.cofinite = match op {
        Op::Or => a.cofinite || b.cofinite,
        Op::And => a.cofinite && b.cofinite,
    };
    for (n, p) in &small.names {
        out.set(n, large.get(n).zip(p, op));
    }
    out
}

/// The diff of two maps that share nodes gives what the walk gives, for sets grown from
/// one another as a chain of merged failures grows them, for unrelated sets, for payloads
/// and bare atoms, for complements, and for both operations (ERRS-precise).
#[test]
fn atoms_combined_by_a_diff_agree_with_the_walk() {
    let atom = |i: usize| match i % 3 {
        0 => Type::atom(&format!("a{i}")),
        1 => Type::atom_with(&format!("a{i}"), &Type::tuple(vec![Type::int()])),
        _ => Type::atom(&format!("a{i}")) | Type::atom_with(&format!("a{i}"), &Type::top()),
    };
    let mut grown = vec![Type::empty()];
    for i in 0..200 {
        let last = grown.last().expect("one at least").clone();
        grown.push(&last | &atom(i));
    }
    let mut sets = grown.clone();
    // Grown again from a midpoint, so the two lines share their first nodes.
    let mut other = grown[100].clone();
    for i in 300..380 {
        other = &other | &atom(i);
        sets.push(other.clone());
    }
    sets.push(Type::union_all((0..150).step_by(2).map(atom)));
    let complements: Vec<Type> = sets.iter().step_by(17).map(|t| !t).collect();
    sets.extend(complements);
    for a in sets.iter().step_by(7) {
        for b in sets.iter().step_by(11) {
            for op in [Op::Or, Op::And] {
                let (x, y) = (&a.p().atoms, &b.p().atoms);
                assert_eq!(x.zip(y, op), zip_by_walk(x, y, op));
                assert_eq!(y.zip(x, op), zip_by_walk(y, x, op));
            }
        }
    }
}

/// `scalar` gives the one value of a type of one boolean or one literal, and nothing for any
/// other type: two values, a carrier, a type without a value, an atom or a tuple.
#[test]
fn scalar_is_the_one_value_of_a_literal_type() {
    let lit = |v: &Value| Type::lit(v).expect("a literal");
    for v in [
        Value::Bool(false),
        Value::Bool(true),
        Value::Int(3),
        Value::float(0.5),
        Value::str("x"),
    ] {
        assert_eq!(lit(&v).scalar(), Some(v.clone()), "{v:?}");
    }
    let one = lit(&Value::Int(1));
    for t in [
        &one | &lit(&Value::Int(2)),
        &one | &lit(&Value::str("x")),
        &one | &Type::atom("a"),
        Type::int(),
        Type::bool(),
        Type::string(),
        &Type::int() - &one,
        Type::empty(),
        Type::atom("a"),
        Type::tuple(vec![one.clone()]),
    ] {
        assert_eq!(t.scalar(), None, "{t}");
    }
}

/// `scalar`, read from the parts, is what comparing a type with the type of its first value
/// gives, on random unions, meets and differences of booleans, literals, carriers, atoms and
/// tuples, many of them one value.
#[test]
fn scalar_read_from_the_parts_is_that_of_comparing_types() {
    let by_lit = |t: &Type| {
        let p = t.p();
        let first = |l: &&Lits| (!l.cofinite).then(|| l.values.iter().next().cloned())?;
        let v = match p.bools {
            1 => Some(Value::Bool(false)),
            2 => Some(Value::Bool(true)),
            _ => [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
                .iter()
                .find_map(first),
        }?;
        (Type::lit(&v)? == *t).then_some(v)
    };
    let lit = |v: Value| Type::lit(&v).expect("a literal");
    let mut seed = crate::seed::seed("scalar_read_from_the_parts_is_that_of_comparing_types") | 1;
    let mut below = |n: u64| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % n
    };
    let (mut ones, mut others) = (0, 0);
    let piece = |below: &mut dyn FnMut(u64) -> u64| match below(12) {
        0 => lit(Value::Bool(below(2) == 0)),
        1 | 2 => lit(Value::Int(below(3) as i64)),
        3 => lit(Value::float([0.5, -0.0, 0.0][below(3) as usize])),
        4 => lit(Value::str(["x", "y"][below(2) as usize])),
        5 => Type::int(),
        6 => Type::bool(),
        7 => Type::f64(),
        8 => Type::atom("a"),
        9 => Type::tuple(vec![lit(Value::Int(1))]),
        10 => Type::empty(),
        _ => Type::string(),
    };
    for _ in 0..20_000 {
        let mut t = piece(&mut below);
        for _ in 0..below(3) {
            let p = piece(&mut below);
            t = match below(3) {
                0 => &t | &p,
                1 => &t & &p,
                _ => &t - &p,
            };
        }
        let scalar = t.scalar();
        assert_eq!(scalar, by_lit(&t), "{t}");
        match scalar {
            Some(_) => ones += 1,
            None => others += 1,
        }
    }
    println!("{ones} of one value, {others} not");
    assert!(ones > 2000 && others > 2000);
}

/// A tuple with a component that lists no value has no value, and is built as the empty type
/// itself, also nested, inside an atom's payload and in a union; a component empty only by a
/// tuple meet is kept as written, though `is_empty` still finds the tuple empty.
#[test]
fn a_tuple_with_an_empty_component_is_empty() {
    let (never, int, b) = (Type::empty(), Type::int(), Type::bool());
    let pair = Type::tuple(vec![never.clone(), int.clone()]);
    assert_eq!(pair, never);
    assert_eq!(Type::tuple(vec![int.clone(), never.clone()]), never);
    assert_eq!(Type::tuple(vec![pair.clone(), b.clone()]), never);
    assert_eq!(&pair | &b, b);
    assert_eq!(pair.surface().to_string(), "Never");
    let payload = Type::atom_with("a", &Type::tuple(vec![never.clone()]));
    assert_eq!(payload, never);
    assert_eq!(&payload | &Type::atom("b"), Type::atom("b"));
    // A tuple with no components is the one empty tuple, not the empty type.
    assert!(!Type::tuple(Vec::new()).is_empty());
    let met = &Type::tuple(vec![int.clone(), int.clone()]) & &Type::tuple(vec![b.clone(), int]);
    let kept = Type::tuple(vec![met.clone(), b]);
    assert!(met.is_empty() && kept.is_empty());
    assert_ne!(kept, never);
}

/// Equal types built apart hash alike under the kernel's hasher (`digest::Digest`), alone and
/// in the keys the type tables use: a group's number with its arguments, and a pair of ids; a
/// type that differs hashes apart.
#[test]
fn equal_types_built_apart_hash_alike() {
    use std::hash::{BuildHasher, BuildHasherDefault};
    let h = BuildHasherDefault::<crate::digest::Digest>::default();
    let build = |name: &str| {
        Type::tuple(vec![
            Type::int(),
            &Type::atom(name) | &Type::bool(),
            Type::tuple(vec![Type::atom("b")]),
        ])
    };
    let (a, b, c) = (build("a"), build("a"), build("c"));
    assert_eq!(a, b);
    assert_ne!(a, c);
    assert_eq!(h.hash_one(&a), h.hash_one(&b));
    assert_ne!(h.hash_one(&a), h.hash_one(&c));
    let args = |t: &Type| (7u64, vec![t.clone(), Type::int()]);
    assert_eq!(h.hash_one(args(&a)), h.hash_one(args(&b)));
    assert_ne!(h.hash_one(args(&a)), h.hash_one(args(&c)));
    assert_eq!(
        h.hash_one((a.digest(), 3u32)),
        h.hash_one((b.digest(), 3u32))
    );
}

#[test]
fn a_function_part_is_found_at_any_depth() {
    let (int, a) = (Type::int(), Type::atom("a"));
    let tuples = Type::universe(Universe::Tuple);
    let structs = Type::universe(Universe::Struct);
    let fns = Type::universe(Universe::Morphism);
    let pair = |x: &Type, y: &Type| Type::tuple(vec![x.clone(), y.clone()]);
    let shape = pair(&(&int | &a), &(&int | &a));
    // Scalars, atoms, every atom and a written shape hold no function; nor does a written
    // shape met with, or less, a kind-wide part.
    for t in [
        int.clone(),
        Type::universe(Universe::Scalar),
        shape.clone(),
        &shape & &(&tuples - &pair(&a, &a)),
        &shape - &pair(&a, &a),
        pair(&int, &shape),
        Type::empty(),
    ] {
        assert_eq!(t.function_part(), None, "{}", t.surface());
    }
    // A kind-wide part at the outer level or in a component, a tuple of a length outside the
    // shapes listed, a struct, a morphism, and an atom's payload that holds every tuple.
    let open = &tuples - &shape;
    for (t, part) in [
        (tuples.clone(), tuples.clone()),
        (&int | &tuples, tuples.clone()),
        (pair(&int, &(&a | &tuples)), tuples.clone()),
        (
            (&shape - &pair(&int, &int)) | pair(&a, &pair(&int, &tuples)),
            tuples.clone(),
        ),
        (open.clone(), open.clone()),
        (pair(&int, &structs), structs.clone()),
        (pair(&int, &fns), fns.clone()),
        (Type::atom_with("b", &pair(&int, &tuples)), tuples.clone()),
    ] {
        assert_eq!(t.function_part(), Some(part), "{}", t.surface());
    }
}

#[test]
fn a_function_part_follows_only_the_tuple_types_a_path_to_true_takes() {
    let (int, a) = (Type::int(), Type::atom("a"));
    let tuples = Type::universe(Universe::Tuple);
    let fns = Type::universe(Universe::Morphism);
    let pair = |x: &Type, y: &Type| Type::tuple(vec![x.clone(), y.clone()]);
    let wide_int = pair(&(&int | &tuples), &int);
    let shape = pair(&int, &(&int | &a));
    // A tuple type only subtracted is not walked: each of these holds pairs of data alone.
    let met = &(&tuples - &wide_int) & &shape;
    for t in [
        // Subtracted from a written pair.
        &pair(&int, &int) - &pair(&tuples, &int),
        // Subtracted from every tuple, then met with a pair of data: `(int, #a)` alone.
        met.clone(),
        // The same in a union with a pair of data, and met once more.
        &met | &pair(&a, &a),
        &met & &(&tuples - &pair(&int, &tuples)),
        // Two differences met, each subtracting a pair with a kind-wide component.
        &(&(&tuples - &pair(&tuples, &int)) & &(&tuples - &pair(&int, &tuples))) & &shape,
        // Under three complements, by `!`.
        &shape & &!&!&!&wide_int,
        // A subtracted function type.
        &pair(&int, &int) - &pair(&int, &fns),
    ] {
        assert_eq!(t.function_part(), None, "{}", t.surface());
    }
    // A tuple type with a kind-wide component under an even number of complements is kept,
    // and a function part that a difference leaves in place is found.
    for (t, part) in [
        // Twice subtracted: `(..) \ ((..) \ ((..), int))` is `((..), int)`.
        (&tuples - &(&tuples - &wide_int), tuples.clone()),
        (&shape | &!&!&wide_int, tuples.clone()),
        // A union in a difference: the subtracted pair takes away part of the kind-wide one.
        (
            &pair(&tuples, &tuples) - &pair(&tuples, &int),
            tuples.clone(),
        ),
        (&met | &pair(&a, &tuples), tuples.clone()),
        // The function part survives a difference that takes a function type away.
        (&pair(&int, &fns) - &pair(&int, &int), fns.clone()),
    ] {
        assert_eq!(t.function_part(), Some(part), "{}", t.surface());
    }
    // The tradeoff of `Type::function_part` (COMPLEXITY.md K103): a path to `true` that takes
    // two tuple types walks both, though their meet may leave no function. So the meet of
    // `(int, int)` with `(int | (..), int)`, which holds only pairs of `int`s, is read as
    // holding a function; and so is `s \ (r \ q)`, which is `s & (!r | q)`, whose path
    // `s & r & q` takes `r`, though its values are in `q = (int, int)`.
    for t in [
        &pair(&int, &int) & &wide_int,
        &shape - &(&wide_int - &pair(&int, &int)),
    ] {
        assert_eq!(t.function_part(), Some(tuples.clone()), "{}", t.surface());
    }
}

#[test]
fn a_function_part_is_found_in_a_recursive_type_once_per_node() {
    use rec::{Def, Expr, Group};
    // `name = () | (head, name)`: a list whose items are `head`, walked through its cycle once.
    let list = |name: &str, head: Type| {
        let body = Expr::Union(vec![
            Expr::Tuple(vec![]),
            Expr::Tuple(vec![Expr::Type(head), Expr::Ref(0, vec![])]),
        ]);
        let def = Def {
            name: name.to_string(),
            params: vec![],
            body,
        };
        let g = Group::new(vec![def]).expect("a recursive group");
        g.instance(vec![]).remove(0)
    };
    let (int, a) = (Type::int(), Type::atom("a"));
    let tuples = Type::universe(Universe::Tuple);
    let data = list("FunctionPartData", &int | &a);
    assert_eq!(data.function_part(), None);
    let less = &data - &Type::tuple(vec![a.clone(), Type::tuple(Vec::new())]);
    assert_eq!(less.function_part(), None);
    let wide = list("FunctionPartWide", &a | &tuples);
    assert_eq!(wide.function_part(), Some(tuples));
}

#[test]
fn an_empty_payload_is_a_member_apart_from_the_bare_atom() {
    // `#e` holds the bare atom only, `#e(())` the empty payload only, and `#e(..)` every
    // payload; a member test that read `#e()` as `#e` would answer each of the first two
    // wrong, and `lit`, which types scalars and bare atoms only, must not read `#e()` as `#e`.
    let (bare, empty) = (Value::atom("e"), Value::atom_with("e", Vec::new()));
    let bare_ty = Type::atom("e");
    let empty_ty = Type::atom_with("e", &Type::tuple(Vec::new()));
    let any = Type::atom_with("e", &Type::universe(Universe::Tuple));
    assert!(bare_ty.contains(&bare) && !bare_ty.contains(&empty));
    assert!(empty_ty.contains(&empty) && !empty_ty.contains(&bare));
    assert!(any.contains(&empty) && !any.contains(&bare));
    assert!(!any.contains(&Value::atom_with("f", Vec::new())));
    assert_eq!(Type::lit(&bare), Some(bare_ty.clone()));
    assert_eq!(Type::lit(&empty), None);
    assert!((&bare_ty & &empty_ty).is_empty());
}

/// A fixed b-cycle makes every state recursive; all states accept exactly the same words.
/// Distinct a-edges still give distinct named graphs. With eight-bit hashes, 257 such
/// graphs force a collision, so the fallback must compare their retained bodies.
#[cfg(feature = "short-addresses")]
#[test]
fn colliding_presentation_hashes_keep_named_graphs_apart() {
    use super::rec::{Def, Expr, Group};
    let mut first = std::collections::HashMap::<(u64, u64), (usize, Type)>::new();
    let mut primary = None;
    let mut collisions = 0;
    for pattern in 0..=256 {
        let mut digits = pattern;
        let defs = (0..5)
            .map(|i| {
                let a = digits % 5;
                digits /= 5;
                Def {
                    name: format!("CollisionState{i}"),
                    params: vec![],
                    body: Expr::Union(vec![
                        Expr::Atom("stop".into(), vec![]),
                        Expr::Tuple(vec![Expr::Atom("a".into(), vec![]), Expr::Ref(a, vec![])]),
                        Expr::Tuple(vec![
                            Expr::Atom("b".into(), vec![]),
                            Expr::Ref((i + 1) % 5, vec![]),
                        ]),
                    ]),
                }
            })
            .collect();
        let group = Group::new(defs).expect("a regular, contractive graph");
        let member = group.instance(vec![]).remove(0);
        assert_eq!(*primary.get_or_insert(member.digest()), member.digest());
        let hash = (member.digest(), member.name_digest());
        if let Some((prior, old)) = first.get(&hash) {
            collisions += 1;
            assert_ne!(&member, old, "named graphs {prior} and {pattern}");
        } else {
            first.insert(hash, (pattern, member));
        }
    }
    assert!(collisions > 0, "257 graphs must collide in eight bits");
}

/// `union_all` joins the types of atoms alone into one map before the pairs; the union must be
/// the one a fold of `|` gives, for every subset, in both orders, of bare atoms, payloads of one
/// name joined, a name repeated, a complement (cofinite, so joined in pairs), a type of atoms
/// and a tuple, and other kinds beside them.
#[test]
fn union_all_of_atom_types_is_the_union_joined_one_at_a_time() {
    let payload = |t: Type| Type::tuple(vec![t]);
    let ts = [
        Type::atom("a"),
        Type::atom_with("a", &payload(Type::int())),
        Type::atom_with("a", &payload(Type::bool())),
        Type::atom("b"),
        Type::atom("b"),
        !&Type::atom("c"),
        &Type::atom("d") | &payload(Type::int()),
        Type::bool(),
        Type::atom_with("e", &Type::top()),
    ];
    for mask in 0..1u32 << ts.len() {
        let chosen: Vec<Type> = (0..ts.len())
            .filter(|i| mask & (1 << i) != 0)
            .map(|i| ts[i].clone())
            .collect();
        let fold = chosen.iter().fold(Type::empty(), |u, t| &u | t);
        assert_eq!(Type::union_all(chosen.clone()), fold, "mask {mask:#b}");
        assert_eq!(
            Type::union_all(chosen.into_iter().rev()),
            fold,
            "mask {mask:#b}"
        );
    }
}
