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

/// `a - b`, which reads only the names one of the two lists (BENCH-if-chain-other-paths), is
/// `a & !b`, which complements each name `b` lists: for finite and cofinite sets of every
/// size order, sets sharing names whose parts differ (bare, payload or both), and types with
/// parts beside their atoms.
#[test]
fn a_difference_of_types_is_the_meet_with_the_complement() {
    let atom = |i: usize| match i % 3 {
        0 => Type::atom(&format!("a{i}")),
        1 => Type::atom_with(&format!("a{i}"), &Type::tuple(vec![Type::int()])),
        _ => Type::atom(&format!("a{i}")) | Type::atom_with(&format!("a{i}"), &Type::top()),
    };
    // The other part a name can have, so that two sets list a name with different parts.
    let other_part = |i: usize| match i % 3 {
        0 => Type::atom_with(&format!("a{i}"), &Type::top()),
        _ => Type::atom(&format!("a{i}")),
    };
    let mut sets = vec![Type::empty(), Type::top()];
    for (lo, hi, step) in [(0, 1, 1), (0, 4, 1), (2, 9, 1), (0, 40, 3), (1, 40, 2)] {
        sets.push(Type::union_all((lo..hi).step_by(step).map(atom)));
        sets.push(Type::union_all((lo..hi).step_by(step).map(other_part)));
    }
    let complements: Vec<Type> = sets.iter().map(|t| !t).collect();
    sets.extend(complements);
    let mixed: Vec<Type> = sets
        .iter()
        .step_by(3)
        .map(|t| t | &Type::int() | Type::tuple(vec![Type::atom("a0")]))
        .collect();
    sets.extend(mixed);
    for a in &sets {
        for b in &sets {
            assert_eq!(
                a - b,
                a & &!b,
                "{} \\ {}",
                a.surface_operand(),
                b.surface_operand()
            );
            assert_eq!(
                a.p().atoms.minus(&b.p().atoms),
                a.p().atoms.zip(&b.p().atoms.not(), Op::And)
            );
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
    // `scalar` agrees with comparing types; whether it is one value.
    let scalar_agrees = |t: &Type| {
        let scalar = t.scalar();
        assert_eq!(scalar, by_lit(t), "{t}");
        scalar.is_some()
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
        match scalar_agrees(&t) {
            true => ones += 1,
            false => others += 1,
        }
    }
    println!("{ones} of one value, {others} not");
    // Both kinds on types built to give them, whatever the draws met (PROOF-test-count-
    // thresholds; until 2026-11-15 the test asserted more than 2000 of each among the draws):
    // the literal 1 is one value; `int` is many.
    assert!(scalar_agrees(&lit(Value::Int(1))));
    assert!(!scalar_agrees(&Type::int()));
}

/// A tuple with a component that lists no value has no value, and is built as the empty type
/// itself, also nested, inside an atom's payload and in a union; a component empty only by a
/// tuple meet is kept as written, though `is_empty` still finds the tuple empty.
/// `only_row` reads its answer from the parts (PERF-listing-each-row-met-first); it must agree
/// with building the tuple of the one row and comparing it with the type.
#[test]
fn only_row_agrees_with_building_the_tuple_of_the_row() {
    let (int, b) = (Type::int(), Type::bool());
    let one = Type::lit(&Value::Int(1)).expect("a literal");
    let odd = &int - &one;
    let pair = Type::tuple(vec![odd.clone(), b.clone()]);
    let other = Type::tuple(vec![int.clone(), int.clone()]);
    let unit = Type::tuple(Vec::new());
    let nested = Type::tuple(vec![pair.clone(), unit.clone()]);
    let all = [
        pair.clone(),
        other.clone(),
        unit.clone(),
        nested.clone(),
        Type::tuple(vec![one.clone()]),
        &pair | &other,
        &pair | &unit,
        &pair | &int,
        &pair | &Type::atom("a"),
        &pair | &b,
        &pair & &other,
        !&pair,
        &Type::top() - &pair,
        int.clone(),
        Type::top(),
        Type::empty(),
        Type::atom_with("a", &pair),
        Type::tuple(vec![Type::empty(), int.clone()]),
    ];
    for t in &all {
        let built = {
            let p = t.p();
            let lens = Vec::from_iter(&p.tuples.lens);
            match &lens[..] {
                [(_, part)] => match &part.distinct_atoms()[..] {
                    [row] => (Type::tuple(row.to_vec()) == *t).then(|| row.to_vec()),
                    _ => None,
                },
                _ => None,
            }
        };
        let read = only_row(t).map(|row| row.to_vec());
        assert_eq!(read, built, "{}", t.surface_operand());
    }
    for t in [&pair, &other, &unit, &nested] {
        assert!(only_row(t).is_some(), "{}", t.surface_operand());
    }
}

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

/// The part `Type::function_part` finds in a type whose pairs are `rows`, whose first components
/// are `tuples` or `structs` and whose other components hold no kind-wide part: the walk reads
/// the rows in their order (`Row`'s), so the components come in the order of the rows sorted,
/// each type once, as the walk pushes them; of those, the kind-wide one met last, which the walk
/// pops first. The rows are written out by the test, not read by the walk under test, so a walk
/// whose order followed the draw would fail (cross-review of PERF-xor-shape-free, round 3,
/// Claude R3-C4).
fn kind_wide_part_met_last(mut rows: Vec<Row>, tuples: &Type, structs: &Type) -> Type {
    rows.sort();
    let mut met: Vec<Type> = Vec::new();
    for r in &rows {
        for c in r.iter() {
            if !met.contains(c) {
                met.push(c.clone());
            }
        }
    }
    let wide = |c: &&Type| *c == tuples || *c == structs;
    met.iter()
        .rev()
        .find(wide)
        .expect("a kind-wide component")
        .clone()
}

/// The same part, read from the walk itself (`Part::taken_toward`), for a meet: the walk of a
/// meet reads its decision list, whose order of rows is neither `Row`'s nor fixed across atom
/// names (`r1` before `r2` for some names, after for others, under every draw), so the test
/// cannot write it out. This oracle uses the walk under test, so it checks that `function_part`
/// keeps each type once, at its first meeting, not that the walk's order is free of the draw;
/// that rests on the proof in `the_function_part_of_a_meet_of_unions_sharing_rows_is_fixed_by_the_type`
/// (cross-review of PERF-xor-shape-free, round 3, Claude R3-C4, Sol Q1(a)).
fn kind_wide_part_walked(t: &Type, tuples: &Type, structs: &Type) -> Type {
    let mut met: Vec<Type> = Vec::new();
    let mut paths = crate::digest::DigestSet::default();
    t.p().tuples.lens[&2].taken_toward(true, &mut paths, &mut |r| {
        for c in r.iter() {
            if !met.contains(c) {
                met.push(c.clone());
            }
        }
    });
    let wide = |c: &&Type| *c == tuples || *c == structs;
    met.iter()
        .rev()
        .find(wide)
        .expect("a kind-wide component")
        .clone()
}

/// The part found is fixed by the type, whatever the draw of the treap priorities: the tuple
/// types a path takes come in their order (`Bdd::taken_toward`), not in the shapes' order, which
/// gave `(..)` under some draws and `{..}` under others (PERF-xor-shape-free; the cross-review's
/// probe, run under 16 values of `ZED_TREAP_SEED`). Each type is pushed once, when first met,
/// so the part is the kind-wide component first met last.
#[test]
fn the_function_part_of_a_union_of_pairs_is_fixed_by_the_type() {
    let tuples = Type::universe(Universe::Tuple);
    let structs = Type::universe(Universe::Struct);
    let pair = |x: &Type, y: &Type| Type::tuple(vec![x.clone(), y.clone()]);
    let mut t = Type::empty();
    let mut rows = Vec::new();
    for i in 0..8 {
        let wide = if i % 2 == 0 { &tuples } else { &structs };
        t = &t | &pair(wide, &Type::atom(&format!("a{i}")));
        rows.push(Row::new(vec![wide.clone(), Type::atom(&format!("a{i}"))]));
    }
    let part = kind_wide_part_met_last(rows, &tuples, &structs);
    assert_eq!(t.function_part(), Some(part), "{}", t.surface());
}

/// The same for a meet of two unions that share rows, `X & Y` with `X = r1 | r2` and
/// `Y = r1 | r2 | r3`: the walk skips a subtree of `Y`'s set that it shares with `X`'s and
/// walks again a node that `Y`'s set rebuilt, and which subtrees the two sets share follows the
/// draw, so a row can be met twice under one draw and once under another. The order in which
/// the walk first meets each row is fixed: a skipped subtree was walked in full before, so
/// skipping it drops no first meeting, and the walk without skips reads each set in order.
/// Each type is pushed once, when first met, so the part is the kind-wide component first met
/// last (`kind_wide_part_walked`). Removing a type met again only when it was popped gave the
/// part of a row met a second time under some draws (cross-review of PERF-xor-shape-free,
/// round 2, Sol X2-F1; red under each of 16 values of `ZED_TREAP_SEED`, since one of the 16
/// types met a row twice under each).
#[test]
fn the_function_part_of_a_meet_of_unions_sharing_rows_is_fixed_by_the_type() {
    let tuples = Type::universe(Universe::Tuple);
    let structs = Type::universe(Universe::Struct);
    let pair = |x: &Type, y: &Type| Type::tuple(vec![x.clone(), y.clone()]);
    for i in 0..16 {
        let atom = |j: usize| Type::atom(&format!("m{i}_{j}"));
        let x = &pair(&tuples, &atom(1)) | &pair(&structs, &atom(2));
        let y = &x | &pair(&Type::int(), &atom(3));
        let t = &x & &y;
        let part = kind_wide_part_walked(&t, &tuples, &structs);
        assert_eq!(t.function_part(), Some(part), "{i}: {}", t.surface());
        // `(r1 | r2) & (r1 | r3)`, two sets sharing one row (round 2, Gemini R2-F1).
        let t = &x & &(&pair(&tuples, &atom(1)) | &pair(&Type::int(), &atom(3)));
        let part = kind_wide_part_walked(&t, &tuples, &structs);
        assert_eq!(t.function_part(), Some(part), "{i}: {}", t.surface());
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

/// `union_all` joins the types of tuples alone, each a union of tuple literals at each length,
/// at once, their literals sorted and one set of them built bottom up (PERF-equal-functions-
/// forms-ratio); the union must be the one a fold of `|` gives, for every subset, in both
/// orders, of tuples of two lengths, a union of several, a tuple repeated, a complement (every
/// other length, so joined in pairs), the empty type, and a tuple beside an atom; and for 300
/// tuples in a scrambled order, where the pairs and the fold made the set by many paths.
#[test]
fn union_all_of_tuple_types_is_the_union_joined_one_at_a_time() {
    let one = |t: Type| Type::tuple(vec![t]);
    let two = |a: &str, b: &str| Type::tuple(vec![Type::atom(a), Type::atom(b)]);
    let ts = [
        one(Type::int()),
        two("a", "b"),
        &two("b", "a") | &(&two("c", "c") | &one(Type::bool())),
        two("a", "b"),
        !&one(Type::atom("x")),
        Type::empty(),
        &two("d", "d") | &Type::atom("y"),
        one(Type::atom_with("p", &one(Type::int()))),
        Type::tuple(vec![]),
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
    // 300 tuples, the i-th taken at 7i mod 300, a repeat of each tenth.
    let many: Vec<Type> = (0..330usize)
        .map(|i| (i * 7) % 300)
        .map(|i| Type::tuple(vec![Type::atom(&format!("n{i}")), Type::int()]))
        .collect();
    let fold = many.iter().fold(Type::empty(), |u, t| &u | t);
    assert_eq!(Type::union_all(many.clone()), fold);
    assert_eq!(Type::union_all(many.into_iter().rev()), fold);
}

/// With no type of literals or atoms alone, `union_all` is the union the pairs make on its
/// types in the order they came, in form, though it joins the tuple types at once
/// (PROOF-union-all-expr-parts): for every subset, in both orders, of tuple types between
/// types whose functions, or whose tuples, are expressions (`Part::Expr`), whose form depends
/// on how they are bracketed. Before, the joined tuples went to the end and the other parts
/// were bracketed anew.
#[test]
fn union_all_is_the_union_joined_in_pairs_in_order() {
    let one = |t: Type| Type::tuple(vec![t]);
    let f = |k: Type, v: Type| Type::exact(k, v);
    let (int, bool, string) = (Type::int, Type::bool, Type::string);
    // `(a & !b) | (c & !d)` on four literals is no decision list, so an expression.
    let two_meets = |a: Type, b: Type, c: Type, d: Type| &(&a - &b) | &(&c - &d);
    let ts = [
        one(Type::atom("a")),
        two_meets(
            f(int(), bool()),
            f(bool(), int()),
            f(string(), bool()),
            f(int(), int()),
        ),
        one(Type::atom("b")),
        !&f(bool(), int()),
        one(int()),
        two_meets(
            f(bool(), bool()),
            f(string(), int()),
            f(int(), string()),
            f(bool(), string()),
        ),
        two_meets(
            one(&Type::atom("c") | &int()),
            one(&Type::atom("d") | &int()),
            one(&Type::atom("e") | &bool()),
            one(&Type::atom("f") | &bool()),
        ),
        Type::tuple(vec![Type::atom("a"), Type::atom("b")]),
        &Type::partial(int(), int()) | &one(bool()),
    ];
    let fn_expr = |t: &Type| matches!(t.p().morphisms, Part::Expr(_));
    let tuple_expr = |t: &Type| (t.p().tuples.lens.values()).any(|b| matches!(b, Part::Expr(_)));
    assert!(fn_expr(&ts[1]) && fn_expr(&ts[5]) && tuple_expr(&ts[6]));
    let (mut exprs, mut alone) = (0, 0);
    for mask in 0..1u32 << ts.len() {
        let chosen: Vec<Type> = (0..ts.len())
            .filter(|i| mask & (1 << i) != 0)
            .map(|i| ts[i].clone())
            .collect();
        for chosen in [chosen.clone(), chosen.into_iter().rev().collect()] {
            let pairs = Type::pairwise(chosen.clone(), Type::empty(), |a, b| a | b);
            let all = Type::union_all(chosen.clone());
            assert_eq!(all, pairs, "mask {mask:#b}");
            exprs += usize::from(fn_expr(&pairs) || tuple_expr(&pairs));
            let tuples = chosen.iter().filter(|t| t.tuple_literals_only()).count();
            alone += usize::from(
                tuples > 1
                    && chosen
                        .iter()
                        .all(|t| t.tuple_literals_only() || t.holds_no_tuple()),
            );
        }
    }
    assert!(
        exprs > 100 && alone > 50,
        "{exprs} unions with an expression, {alone} with the tuples joined at once"
    );
}

/// A union of tuple literals met with the complement of another, or joined to it, is made at
/// once from the two blocks (`Bdd::zip_chain`, PERF-equal-functions-forms-ratio); it must be
/// the type that taking the tuples away, or adding the complements, one at a time gives: for
/// sets that overlap, one inside the other, equal, apart, of one tuple against many, and a set
/// with the complement of a tuple, whose atom the other set takes.
#[test]
fn a_union_of_tuples_less_another_is_the_tuples_taken_away_one_at_a_time() {
    let row = |i: usize| Type::tuple(vec![Type::atom(&format!("r{i}")), Type::int()]);
    let union = |rows: &[usize]| Type::union_all(rows.iter().map(|&i| row(i)));
    let ranges: [(&[usize], &[usize]); 7] = [
        (&[0, 1, 2, 3, 4, 5, 6, 7], &[4, 5, 6, 7, 8, 9, 10, 11]),
        (&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], &[2, 3, 4]),
        (&[2, 3, 4], &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
        (&[1, 2, 3, 4, 5], &[1, 2, 3, 4, 5]),
        (&[0, 2, 4, 6, 8], &[1, 3, 5, 7, 9]),
        (&[7], &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
        (&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], &[7, 12]),
    ];
    for (a, b) in ranges {
        let (ta, tb) = (union(a), union(b));
        let less = b.iter().fold(ta.clone(), |u, &i| &u - &row(i));
        assert_eq!(&ta - &tb, less, "{a:?} less {b:?}");
        // `ta | !tb` is `!(tb - ta)`, with `tb - ta` taken one tuple at a time.
        let more = !&a.iter().fold(tb.clone(), |u, &i| &u - &row(i));
        assert_eq!(&ta | &!&tb, more, "{a:?} with the complement of {b:?}");
        // The complement of one tuple beside the others: an atom taken by one block and
        // refused by the other.
        let with_not = &union(&b[1..]) | &!&row(b[0]);
        let less = b[1..].iter().fold(&ta - &!&row(b[0]), |u, &i| &u - &row(i));
        assert_eq!(&ta - &with_not, less, "{a:?} less {b:?} with a complement");
    }
}

/// `union_all` joins the types of finitely many booleans, numbers and strings alone into the
/// sets of the largest before the pairs; the union must be the one a fold of `|` gives, for every
/// subset, in both orders, of literals of each kind, a set of several, a value repeated, a
/// complement (cofinite, so joined in pairs), the empty type, and literals beside other kinds.
#[test]
fn union_all_of_literal_types_is_the_union_joined_one_at_a_time() {
    let lit = |v: Value| Type::lit(&v).unwrap();
    let ts = [
        lit(Value::Int(1)),
        (0..5).fold(Type::empty(), |u, i| &u | &lit(Value::Int(i))),
        lit(Value::Int(1)),
        lit(Value::Bool(true)),
        lit(Value::float(0.5)),
        lit(Value::str("s")),
        !&lit(Value::Int(7)),
        Type::empty(),
        &lit(Value::Int(9)) | &Type::atom("a"),
        Type::tuple(vec![Type::int()]),
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

/// A change of one row of an exclusive or of the `c` one-tuples `(i | (i, i))` reaches a number
/// of nodes of the listing's graph that does not grow with `c` (PERF-kernel-ratios-9-to-10_5).
/// The exclusive or of two literals is a union of two lists of two rows each, `!a & b` and
/// `a & !b`, and of one row a list with its literal taken or not taken; read as choices, the
/// chain of unions and meets that builds the exclusive or of the `c` terms is one exclusive or
/// ([`Graph::parities`]). Read as unions and meets, a change reached 81 nodes at `c = 64`; read
/// as one exclusive or, 4 at both sizes.
#[test]
fn a_change_of_a_row_of_an_exclusive_or_reaches_few_nodes() {
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).unwrap();
    for c in [64, 512] {
        let t = (0..c)
            .map(|i| Type::tuple(vec![&lit(i) | &Type::tuple(vec![lit(i), lit(i)])]))
            .fold(Type::empty(), |x, t| &(&x - &t) | &(&t - &x));
        let p = t.p();
        let part = &p.tuples.lens[&1];
        let mut rows = part.distinct_atoms();
        rows.sort();
        let graph = Graph::new(&rows, part);
        let most = (0..rows.len()).map(|i| graph.reach(i)).max();
        assert!(most <= Some(6), "c = {c}: a change reaches {most:?} nodes");
    }
}

/// `ints_listed` gives exactly the ints a type holds, whatever made the type
/// (PROOF-ints-listed-complete): for types made by `|`, `&`, `-` and `!` from int literals, a
/// big int, `int`, a range's worth of literals, and types of other kinds, each int of a window
/// and the big ints is listed exactly when `contains` holds it; and where nothing is listed,
/// the type holds all but finitely many ints, so a far int it does not list is held.
#[test]
fn ints_listed_are_the_ints_the_type_holds() {
    let lit = |v: Value| Type::lit(&v).expect("a literal");
    let big = Value::int(num_bigint::BigInt::from(1u8) << 70usize);
    let far = Value::int(num_bigint::BigInt::from(1u8) << 90usize);
    let mut seed = crate::seed::seed("ints_listed_are_the_ints_the_type_holds") | 1;
    let mut below = |n: u64| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % n
    };
    let piece = |below: &mut dyn FnMut(u64) -> u64| match below(9) {
        0..=2 => lit(Value::Int(below(9) as i64 - 4)),
        3 => lit(big.clone()),
        4 => Type::int(),
        5 => (2..5).fold(Type::empty(), |u, i| &u | &lit(Value::Int(i))),
        6 => lit(Value::Bool(true)),
        7 => Type::tuple(vec![lit(Value::Int(1))]),
        _ => Type::empty(),
    };
    let (mut listed, mut cofinite) = (0, 0);
    for _ in 0..5_000 {
        let mut t = piece(&mut below);
        for _ in 0..below(4) {
            let p = piece(&mut below);
            t = match below(4) {
                0 => &t | &p,
                1 => &t & &p,
                2 => &t - &p,
                _ => !&t,
            };
        }
        let window = (-6..7).map(Value::Int).chain([big.clone(), far.clone()]);
        match t.ints_listed() {
            Some(ints) => {
                listed += 1;
                for v in window {
                    assert_eq!(ints.contains(&v), t.contains(&v), "{t} at {v:?}");
                }
            }
            None => {
                cofinite += 1;
                // A type cofinite in the ints that is made from these pieces names none
                // beyond 2^70, so it holds 2^90.
                assert!(t.contains(&far), "{t}");
            }
        }
    }
    assert!(listed > 1000 && cofinite > 1000, "{listed} {cofinite}");
}

/// `lists_values_of(b)` says what listing the meet with base type `b` says, that it lists one
/// value or more (CHECK-literal-union-cost), for types made by `|`, `&`, `-` and `!` from
/// literals and whole base types of each base, tuples and atoms.
#[test]
fn lists_values_of_agrees_with_listing_the_meet() {
    let lit = |v: Value| Type::lit(&v).expect("a literal");
    let half = Rat::decimal("0.5").expect("given").unwrap();
    let bases = [
        Type::bool(),
        Type::int(),
        Type::rat(),
        Type::f64(),
        Type::string(),
        Type::f32(),
    ];
    let mut seed = crate::seed::seed("lists_values_of_agrees_with_listing_the_meet") | 1;
    let mut below = |n: u64| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % n
    };
    let piece = |below: &mut dyn FnMut(u64) -> u64| match below(12) {
        0 => lit(Value::Int(below(3) as i64)),
        1 => lit(Value::rat(half.clone())),
        2 => lit(Value::float([0.5, 1.0][below(2) as usize])),
        3 => lit(Value::float32(0.5)),
        4 => lit(Value::str(["x", "y"][below(2) as usize])),
        5 => lit(Value::Bool(below(2) == 0)),
        6 => bases[below(6) as usize].clone(),
        7 => Type::tuple(vec![lit(Value::Int(1))]),
        8 => Type::atom("a"),
        _ => Type::empty(),
    };
    let (mut yes, mut no) = (0, 0);
    for _ in 0..5_000 {
        let mut t = piece(&mut below);
        for _ in 0..below(4) {
            let p = piece(&mut below);
            t = match below(4) {
                0 => &t | &p,
                1 => &t & &p,
                2 => &t - &p,
                _ => !&t,
            };
        }
        for (b, base) in bases.iter().enumerate() {
            let want = (&t & base).values_listed().is_some_and(|vs| !vs.is_empty());
            assert_eq!(t.lists_values_of(b), want, "{t} at base {b}");
            let part = &t & base;
            let unlisted = !part.is_empty() && part.values_listed().is_none();
            assert_eq!(t.holds_unlisted_values_of(b), unlisted, "{t} at base {b}");
            if want {
                yes += 1;
            } else {
                no += 1;
            }
        }
    }
    assert!(yes > 1000 && no > 1000, "{yes} {no}");
}

/// The members of the order, `==`, `Debug` and `Display` families that only delegate, which no
/// caller in the workspace calls directly (llvm-cov over the whole local suite,
/// TEST-types-unreached-paths-2): `partial_cmp` of literal sets is `Some` of `cmp`, as `Ord`
/// requires; `==` of two arrows is their three types equal; the text `{:?}` writes for a node
/// or a morphism type is the text a type holding it writes for it, which `debug_samples` holds
/// to the derived `Debug`s; and a refusal's `Display` is its message.
#[test]
fn the_delegating_orders_and_texts_of_types_agree_with_what_they_delegate_to() {
    let lit = |i: i64| Type::lit(&Value::Int(i)).unwrap();
    let ints = |t: &Type| match &*t.0 {
        Node::Parts(p, _) => p.ints.clone(),
        Node::Rec(_) => panic!("{t:?} is not recursive"),
    };
    let sets = [
        lit(0),
        lit(1),
        &lit(0) | &lit(1),
        Type::int(),
        Type::string(),
    ]
    .map(|t| ints(&t));
    for a in &sets {
        for b in &sets {
            assert_eq!(a.partial_cmp(b), Some(a.cmp(b)), "{a:?}, {b:?}");
        }
    }
    let arrows = [
        Morphism::new(Type::int(), Type::int(), Type::string()),
        Morphism::new(Type::empty(), Type::int(), Type::string()),
        Morphism::new(Type::int(), Type::int(), Type::bool()),
    ];
    for a in &arrows {
        for b in &arrows {
            let same =
                a.guarantee == b.guarantee && a.permission == b.permission && a.value == b.value;
            assert_eq!(**a == **b, same, "{a:?}, {b:?}");
        }
    }
    for t in [Type::int(), Type::tuple(vec![lit(0), Type::string()])] {
        assert_eq!(format!("{t:?}"), format!("Type({:?})", *t.0));
    }
    let m = Type::exact(Type::int(), Type::string());
    assert!(
        format!("{m:?}").contains(&format!("{:?}", arrows[0])),
        "{m:?} writes {:?}",
        arrows[0]
    );
    use Refusal::*;
    let all = [
        Fork,
        Residues,
        TupleSplit,
        SharedCells(1),
        MorphismSplit,
        NoWitness,
        Group,
    ];
    for r in all {
        assert_eq!(r.to_string(), r.message(), "{r:?}");
    }
}
