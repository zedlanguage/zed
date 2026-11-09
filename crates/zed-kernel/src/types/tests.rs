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
    for a in sets.iter().step_by(3) {
        for b in sets.iter().step_by(5) {
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
            _ => [&p.ints, &p.rats, &p.floats, &p.strings]
                .iter()
                .find_map(first),
        }?;
        (Type::lit(&v)? == *t).then_some(v)
    };
    let lit = |v: Value| Type::lit(&v).expect("a literal");
    let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
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
