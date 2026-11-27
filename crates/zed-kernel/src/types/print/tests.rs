//! The text of a type does not depend on the order of its atoms (step BDD-atom-order).
//! The order follows the digests, which differ between the full build and the
//! short-addresses build; the test hook `SALT` changes every digest of a thread, so a type
//! built on a thread of its own with a salt has its atoms in another order.

use super::super::bdd::Part;
use super::super::{Op, Row, SALT, Type, Universe};
use super::defs::{collect, lift, plain};
use crate::seed::Rng;
use crate::value::Value;

pub(super) fn lit(i: u64) -> Type {
    Type::lit(&Value::Int(i as i64)).expect("an integer literal type")
}

fn leaf(rng: &mut Rng, depth: u32) -> Type {
    let k = rng.next_u64();
    match k % 7 {
        0 => Type::top(),
        1 | 2 => lit(k / 7 % 4),
        3 => Type::atom(&format!("a{}", k / 7 % 3)),
        4 if depth > 0 => ty(rng, depth - 1),
        5 => Type::exact(lit(k / 7 % 3), Type::int()),
        _ => Type::int(),
    }
}

/// A random type of unions, intersections, differences and complements of tuple types,
/// some of them an atom's payload.
fn ty(rng: &mut Rng, depth: u32) -> Type {
    let k = rng.next_u64();
    if depth == 0 || k.is_multiple_of(7) {
        let n = 1 + (k / 7 % 2) as usize;
        let t = Type::tuple((0..n).map(|_| leaf(rng, depth.saturating_sub(2))).collect());
        return match k / 14 % 5 {
            0 => Type::atom_with("p", &t),
            _ => t,
        };
    }
    let a = ty(rng, depth - 1);
    match k % 4 {
        0 => &a | &ty(rng, depth - 1),
        1 => &a & &ty(rng, depth - 1),
        2 => &a - &ty(rng, depth - 1),
        _ => !&a,
    }
}

/// The parts of `t` kept as expressions.
fn exprs(t: &Type) -> usize {
    let p = t.p();
    p.tuples.lens.values().filter(|q| q.view().is_err()).count()
        + usize::from(p.morphisms.view().is_err())
}

/// On a thread with `salt`: the texts of `n` random types drawn from `base` in both
/// printers, the number of their parts kept as expressions, and how 64 pairs of tuple types
/// are ordered.
fn texts(salt: u64, base: u64, n: u64) -> (Vec<(String, String)>, usize, Vec<bool>) {
    std::thread::spawn(move || {
        SALT.set(salt);
        let mut kept = 0;
        let texts = (0..n)
            .map(|i| {
                let t = ty(&mut Rng::new(base.wrapping_add(i * 7919)), 5);
                kept += exprs(&t);
                (t.to_string(), t.surface().to_string())
            })
            .collect();
        let order = (0..64)
            .map(|i| Row::new(vec![lit(i)]) < Row::new(vec![lit(i + 1)]))
            .collect();
        (texts, kept, order)
    })
    .join()
    .expect("the thread prints without panicking")
}

#[test]
fn random_types_print_alike_in_every_order_of_their_atoms() {
    let n = 600;
    let base = crate::seed::seed("random_types_print_alike_in_every_order_of_their_atoms");
    let (want, kept, order) = texts(0, base, n);
    eprintln!("{kept} parts kept as expressions");
    // A type that keeps a part as an expression, built, prints alike on every salt whatever
    // the draws met (PROOF-test-count-thresholds; until 2026-11-15 the test asserted that the
    // 600 drawn types kept more than 10 parts as expressions): its tuples of one component
    // are the one part, `xor_part`, kept as an expression.
    let built = |salt: u64| {
        std::thread::spawn(move || {
            SALT.set(salt);
            let t = Type::with(|q| {
                q.tuples.lens.insert(1, xor_part());
            });
            (exprs(&t), t.to_string(), t.surface().to_string())
        })
        .join()
        .expect("the thread prints without panicking")
    };
    let first = built(0);
    assert_eq!(first.0, 1, "{first:?}");
    for salt in [0x5555_aaaa_1234_9876, 0x0123_4567_89ab_cdef, u64::MAX] {
        assert_eq!(built(salt), first, "salt {salt:#x}");
    }
    for salt in [0x5555_aaaa_1234_9876, 0x0123_4567_89ab_cdef, u64::MAX] {
        let (got, _, other) = texts(salt, base, n);
        assert_ne!(order, other, "salt {salt:#x} orders the atoms otherwise");
        let differ: Vec<_> = (0..n as usize).filter(|&i| want[i] != got[i]).collect();
        assert!(
            differ.is_empty(),
            "salt {salt:#x}: {} of {n} types print otherwise, first {:?} and {:?}",
            differ.len(),
            want[differ[0]],
            got[differ[0]],
        );
    }
}

/// The type that `ZED_TEST_SEED=11060904907146018957` drew in
/// [`random_types_print_alike_in_every_order_of_their_atoms`] (FAIL-print-alias-atom-order),
/// built: `_ \ ((int,) & ((int,) | ((3,) \ (int,)) | (#a0,) & (2,)))`, whose tuples are kept as
/// an expression in which `(int,)` is made twice, as the complement of `(_,) \ (int,)`. Printed,
/// the first `(int,)` made was freed before the second was made, or not, by the order of the
/// walk, which follows the order of the atoms: at salt `u64::MAX` the two were two nodes,
/// each written out, and at salt 0 one node with a definition.
#[test]
fn a_part_made_twice_while_printing_is_one_part_in_every_order_of_the_atoms() {
    let built = |salt: u64| {
        std::thread::spawn(move || {
            SALT.set(salt);
            let one = |t: Type| Type::tuple(vec![t]);
            // Every value but `(int,)`: its tuples of one component are the one literal.
            let n = !&one(Type::int());
            let d = &one(lit(3)) - &one(Type::int());
            let e = &one(Type::atom("a0")) & &one(lit(2));
            let t = &n | &(&n & &!&(&d | &e));
            (exprs(&t), t.to_string(), t.surface().to_string())
        })
        .join()
        .expect("the thread prints without panicking")
    };
    let first = built(0);
    assert_eq!(
        first.0, 1,
        "the tuples are kept as an expression: {first:?}"
    );
    assert_eq!(
        first.2,
        "type Part1 = (int,);\n_ \\ (Part1 & (Part1 | ((3,) \\ (int,)) | (#a0,) & (2,)))"
    );
    for salt in [0x5555_aaaa_1234_9876, 0x0123_4567_89ab_cdef, u64::MAX] {
        assert_eq!(built(salt), first, "salt {salt:#x}");
    }
}

#[test]
fn a_union_of_tuple_types_less_another_prints_alike_in_every_order() {
    // The case of L1.37a repair#1: the two builds printed `((0, #a0) | (1, #a1)) \ (1, _)`
    // and `(0, #a0) & ((_, _) \ (1, _)) | ((1, #a1) \ (1, _) \ (0, #a0))`.
    for salt in [0, 0x5555_aaaa_1234_9876, 0x0123_4567_89ab_cdef, u64::MAX] {
        let (display, surface) = std::thread::spawn(move || {
            SALT.set(salt);
            let a = Type::tuple(vec![lit(0), Type::atom("a0")]);
            let b = Type::tuple(vec![lit(1), Type::atom("a1")]);
            let t = &(&a | &b) - &Type::tuple(vec![lit(1), Type::top()]);
            (t.to_string(), t.surface().to_string())
        })
        .join()
        .expect("the thread prints without panicking");
        assert_eq!(surface, "((0, #a0) | (1, #a1)) \\ (1, _)", "salt {salt:#x}");
        assert_eq!(
            display, "(| (& (tuple 0 #a0) (! (tuple 1 _))) (& (tuple 1 #a1) (! (tuple 1 _))))",
            "salt {salt:#x}"
        );
    }
}

/// `((x0 | x1) \ x2 \ x3 | x4 | x5) \ x6 …` on `m` atoms: blocks of two literals, values
/// alternating, each new literal first in the order, so the diagram is one node per atom.
pub(super) fn decision_list(m: usize) -> Type {
    let mut xs: Vec<Row> = (0..m as u64).map(|i| Row::new(vec![lit(i)])).collect();
    xs.sort();
    let mut f = Part::literal(xs[m - 1].clone());
    for (i, x) in xs[..m - 1].iter().rev().enumerate() {
        f = match i / 2 % 2 {
            0 => f.zip(&Part::literal(x.clone()).not(), Op::And),
            _ => f.zip(&Part::literal(x.clone()), Op::Or),
        };
    }
    Type::with(|p| {
        p.tuples.lens.insert(1, f);
    })
}

/// The text of [`decision_list`]`(m)` has no definition and one connective between each
/// two literals; the benchmark `the_text_of_a_long_decision_list_scales` in `bench.rs`
/// checks the same at 1,024 and 8,192 atoms.
#[test]
fn the_text_of_a_decision_list_has_a_connective_between_each_two_literals() {
    for m in [1, 2, 3, 4, 5, 9, 64] {
        let s = decision_list(m).surface();
        assert!(s.defs.is_empty(), "{m}");
        assert_eq!(
            s.root.matches(" \\ ").count() + s.root.matches(" | ").count(),
            m - 1,
            "{m}: {}",
            s.root
        );
    }
}

/// The exclusive or of the one-tuples `(0,)` to `(c - 1,)`, built a literal at a time as
/// `f & !x | !f & x`: the tuples with an odd number of the `c` atoms, whose clauses as a sum of
/// products are the `2^(c-1)` odd subsets (docs/thresholds.md, the display of type diagrams).
pub(super) fn parity(c: u64) -> Type {
    let f = (0..c).fold(Part::leaf(false), |f, i| {
        let x = Part::literal(Row::new(vec![lit(i)]));
        let left = f.zip(&x.not(), Op::And);
        left.zip(&f.not().zip(&x, Op::And), Op::Or)
    });
    Type::with(|p| {
        p.tuples.lens.insert(1, f);
    })
}

/// The bounds on the text of [`parity`]`(c)`: at most `3c` definitions and `c (64 + 12 L)`
/// bytes, `L = 4 + digits(3c)` the length of the longest name `PartK`. Proof: the diagram has
/// at most `c` atoms `(i,)` and two nodes for each step of the fold, `(A | B) \ (A & C)` and
/// `(A \ B) | (C \ A)`, at most `2c`, and the display writes each once, as a definition where it
/// is used more than once and in place otherwise; so at most `3c` definitions. A step's
/// definition `type P = (A | B) \ (A & C);` and its newline take `23 + 5L` bytes, an atom's
/// `type P = (i,);` at most `13 + 2L` (`i < c` has fewer digits than `L`), and a node written in
/// place takes no more than its definition (it drops `type P = ;` and the newline, `10 + L`
/// bytes, and adds two parentheses). So the text is at most `c (2 (23 + 5L) + 13 + 2L) = c (59 +
/// 12 L)` bytes. Measured (2026-11-27): 40 definitions and 1,708 bytes at `c = 16`, where a
/// bound of `2c` definitions, written first, failed.
/// The text is `O(c log c)` bytes because the names are `O(log c)` long, and it is linear in the
/// nodes.
pub(super) fn parity_text_bounds(c: usize) -> (usize, usize) {
    let l = 4 + (3 * c).to_string().len();
    (3 * c, c * (64 + 12 * l))
}

/// Plan row TYPE-display-shared: the parity of `c` tuple types, whose diagram has `2^(c-1)`
/// paths, prints within [`parity_text_bounds`], at most `3c` definitions, so it does not list
/// its clauses: at `c = 16` they would be 32,768. It prints the counts for the record. The
/// benchmark `the_parity_of_c_tuple_types_prints_in_linear_text` in `bench.rs` checks the
/// work at 1,000 and 8,000 atoms, and `l01_29_diagnostics::shared_parts::
/// the_parity_of_tuple_types_reads_back_from_its_definitions` that the text reads back as the
/// same type.
#[test]
fn the_parity_of_c_tuple_types_prints_in_o_c_definitions() {
    for c in [1usize, 2, 3, 4, 5, 8, 16, 64] {
        let s = parity(c as u64).surface();
        let text = s.to_string();
        println!(
            "parity of {c}: {} definitions, {} bytes",
            s.defs.len(),
            text.len()
        );
        let (defs, bytes) = parity_text_bounds(c);
        assert!(s.exact, "{c}: {text}");
        assert!(s.defs.len() <= defs, "{c}: {text}");
        assert!(text.len() <= bytes, "{c}: {} bytes: {text}", text.len());
    }
}

/// `R1 = R0 \ Never` with `R0 = (#a0, #a0 | (#a1, #a1 | … (#a{k-1}, #a{k-1} | R0)))`.
/// Written by name, `R1` unfolds once, and so does each part `#ai | …` kept unevaluated,
/// whose unfolding holds the next and the last of which holds the first again: a cycle of
/// `k` parts, none of them a member with a name of its own.
pub(super) fn part_cycle(k: usize) -> Type {
    use super::super::rec::{Def, Expr, Group};
    let one = |name: &str, body| {
        let def = Def {
            name: name.into(),
            params: vec![],
            body,
        };
        Group::new(vec![def])
            .expect("accepted")
            .instance(vec![])
            .remove(0)
    };
    let mut body = Expr::Ref(0, vec![]);
    for i in (0..k).rev() {
        let a = || Expr::Type(Type::atom(&format!("a{i}")));
        body = Expr::Tuple(vec![a(), Expr::Union(vec![a(), body])]);
    }
    let r0 = Expr::Type(one("R0", body));
    one(
        "R1",
        Expr::Diff(Box::new(r0), Box::new(Expr::Type(Type::empty()))),
    )
}

/// `R = R0 \ Never` with `Ri = (#ai, #ai | R{i+1})` for `i < k`, `Rk` being `R0`: written by
/// name, `R` unfolds once, and so does each part `#ai | R{i+1}`, whose unfolding holds the
/// next part, the last the first: a cycle of `k` parts, each name a few words long.
pub(super) fn part_ring(k: usize) -> Type {
    use super::super::rec::{Def, Expr, Group};
    let defs = (0..k)
        .map(|i| {
            let a = || Expr::Type(Type::atom(&format!("a{i}")));
            let next = Expr::Ref((i + 1) % k, vec![]);
            Def {
                name: format!("R{i}"),
                params: vec![],
                body: Expr::Tuple(vec![a(), Expr::Union(vec![a(), next])]),
            }
        })
        .collect();
    let r0 = Group::new(defs)
        .expect("accepted")
        .instance(vec![])
        .remove(0);
    let def = Def {
        name: "R".into(),
        params: vec![],
        body: Expr::Diff(
            Box::new(Expr::Type(r0)),
            Box::new(Expr::Type(Type::empty())),
        ),
    };
    Group::new(vec![def])
        .expect("accepted")
        .instance(vec![])
        .remove(0)
}

/// Item PERF-print-by-name-after-plain: a type prints the same text wherever its diagrams were
/// made. [`part_cycle`] made on a thread of its own, or [`part_ring`] printed again on a later
/// thread after the end of the unit that unfolded it, holds equal diagrams made on two threads,
/// whose interned ids differ; the printer keyed a diagram by its id, so the type's root and the
/// equal row inside its cycle were two items, the root left without a definition.
#[test]
fn a_type_prints_the_same_wherever_its_diagrams_were_made() {
    let on_a_thread = |f: &(dyn Fn() -> String + Sync)| {
        std::thread::scope(|s| s.spawn(f).join()).expect("printed")
    };
    let by_name = |t: &Type| t.surface_by_name(super::At::Any).to_string();
    for k in [1, 2, 3, 5] {
        let here = by_name(&part_cycle(k));
        let apart = std::thread::scope(|s| s.spawn(|| part_cycle(k)).join()).expect("made");
        assert_eq!(on_a_thread(&|| by_name(&apart)), here, "{k}");
        let ring = part_ring(k);
        let first = on_a_thread(&|| by_name(&ring));
        assert_eq!(on_a_thread(&|| by_name(&ring)), first, "{k}");
        assert_eq!(by_name(&ring), first, "{k}");
    }
}

/// Item FAIL-print-height-cycle-seed: [`part_cycle`] and [`part_ring`] written by name end,
/// each part on the cycle defined; before, the printer stopped in `heights`, which found a
/// cycle with no recursive type with a definition on it. The benchmark
/// `a_long_cycle_of_parts_written_by_name_scales` in `bench.rs` checks the same on a ring of
/// more parts.
#[test]
fn a_cycle_of_parts_written_by_name_is_defined() {
    // `type Part1 = Part2 | #a0; type Part2 = (#a0, Part1);` and `Part2` for one part, of either
    // family.
    for (k, t) in [1, 2, 3, 5]
        .into_iter()
        .flat_map(|k| [(k, part_cycle(k)), (k, part_ring(k))])
    {
        let s = t.surface_by_name(super::At::Any);
        assert_eq!(s.defs.len(), k + 1, "{k}: {s}");
        assert!(s.defs.iter().any(|(name, _)| *name == s.root), "{k}: {s}");
        for i in 0..k {
            let atom = format!("#a{i}");
            let uses: usize = s.defs.iter().map(|(_, b)| b.matches(&atom).count()).sum();
            assert_eq!(uses, 2, "{k}: {atom} in {s}");
        }
    }
}

/// Item TEST-kernel-unreached-paths-4: a member of a group of two parameters, written by name,
/// separates its arguments by a comma and a space.
#[test]
fn a_member_of_two_parameters_written_by_name_lists_its_arguments() {
    use super::super::rec::{Def, Expr, Group};
    // `type P(T, U) = #nil | #c(T, U, P(T, U))`.
    let def = Def {
        name: "PrintTwoParams".into(),
        params: vec!["T".into(), "U".into()],
        body: Expr::Union(vec![
            Expr::Type(Type::atom("nil")),
            Expr::Atom(
                "c".into(),
                vec![
                    Expr::Param(0),
                    Expr::Param(1),
                    Expr::Ref(0, vec![Expr::Param(0), Expr::Param(1)]),
                ],
            ),
        ]),
    };
    let t = Group::new(vec![def])
        .expect("accepted")
        .instance(vec![Type::int(), Type::bool()])
        .remove(0);
    assert_eq!(
        t.surface_by_name(super::At::Any).to_string(),
        "PrintTwoParams(int, bool)"
    );
}

/// `0 | 0.5 | 2r/3r | 1 | 1.5 | 5r/3r | …`: `m` literals of each of int, f64 and rat, which
/// the fixed order interleaves by value (DESIGN.md sec:diagnostics, decision A92).
pub(super) fn three_carriers(m: usize) -> Type {
    Type::with(|p| {
        for i in 0..m as i64 {
            p.ints.insert(&Value::Int(i));
            p.floats.insert(&Value::float(i as f64 + 0.5));
            let r = crate::num::Rat::new((3 * i + 2).into(), 3.into()).expect("a ratio");
            p.rats.insert(&Value::rat(r));
        }
    })
}

/// The literals of [`three_carriers`] print ascending, one `|` between each two; the
/// benchmark `a_union_of_many_numeric_literals_prints_ascending_in_m_log_m` in `bench.rs`
/// checks the count at 1,024 and 8,192 literals of each carrier.
#[test]
fn a_union_of_numeric_literals_of_three_carriers_prints_ascending() {
    assert_eq!(
        three_carriers(1).surface().root.to_string(),
        "0 | 0.5 | 2r/3r"
    );
    assert_eq!(
        three_carriers(2).surface().root.to_string(),
        "0 | 0.5 | 2r/3r | 1 | 1.5 | 5r/3r"
    );
    for m in [3, 7, 64] {
        let s = three_carriers(m).surface();
        assert_eq!(s.root.matches(" | ").count(), 3 * m - 1, "{m}");
    }
}

fn defs_abc() -> Type {
    Type::atom("a") | Type::atom("b") | Type::atom("c")
}

#[test]
fn a_shared_part_is_a_reference_while_collecting_and_reads_alone_as_before() {
    let t = Type::tuple(vec![defs_abc(), defs_abc(), defs_abc()]);
    let alone = t.surface().to_string();
    assert_eq!(alone, "type Part1 = #a | #b | #c;\n(Part1, Part1, Part1)");
    let _on = collect();
    let s = t.surface();
    assert!(s.defs.is_empty());
    assert_ne!(s.root, alone, "the root holds a reference");
    assert_eq!(plain(&s.root), alone);
    // A union used once is a reference too, since a later step of the message may use it
    // twice (MSG-derive-print-union-names); the message writes it in full until then.
    let once = defs_abc().surface().root;
    assert_ne!(once, "#a | #b | #c");
    assert_eq!(plain(&once), "#a | #b | #c");
}

#[test]
fn one_message_has_one_numbering_and_each_definition_once() {
    let _on = collect();
    let x = Type::tuple(vec![defs_abc(), defs_abc()]).surface().root;
    let y = Type::tuple(vec![defs_abc(), defs_abc(), defs_abc()])
        .surface()
        .root;
    let ab = Type::atom("a") | Type::atom("b");
    let z = Type::tuple(vec![ab.clone(), ab]).surface().root;
    let mut message = format!("`f` does not take ({x}, {y})");
    let mut note = format!("`f` takes {z}");
    let defs = lift(&mut [&mut message, &mut note], &|_| false);
    assert_eq!(
        message,
        "`f` does not take ((Part1, Part1), (Part1, Part1, Part1))"
    );
    assert_eq!(note, "`f` takes (Part2, Part2)");
    assert_eq!(
        defs,
        [
            ("Part1".to_string(), "#a | #b | #c".to_string()),
            ("Part2".to_string(), "#a | #b".to_string())
        ]
    );
}

/// Each type printed in one table after the others, as the messages of one checked unit
/// are, and lifted as a message of its own.
fn printed_in_turn(ts: &[Type]) -> Vec<(String, Vec<(String, String)>)> {
    let _on = collect();
    let roots: Vec<String> = ts.iter().map(|t| t.surface().root).collect();
    roots
        .into_iter()
        .map(|mut root| {
            let defs = lift(&mut [&mut root], &|_| false);
            (root, defs)
        })
        .collect()
}

#[test]
fn a_part_printed_before_is_taken_again_only_where_it_names_the_union_it_holds_alike() {
    // Step MSG-derive-print-unions. `u = 1 | 2`, `a = (u, 0)`, `c = (a, 0)`: in `a` and
    // `c` the union is written once and not named. `(c, 0)` takes `c` again as printed.
    // In `(a, u)` and `(c, u)` the union is written twice and named, so the part printed
    // before, which writes it out, is not taken again: each prints as in a table of its own.
    let u = lit(1) | lit(2);
    let a = Type::tuple(vec![u.clone(), lit(0)]);
    let c = Type::tuple(vec![a.clone(), lit(0)]);
    let ts = [
        a.clone(),
        c.clone(),
        Type::tuple(vec![c.clone(), lit(0)]),
        Type::tuple(vec![a, u.clone()]),
        Type::tuple(vec![c, u]),
    ];
    let alone: Vec<_> = ts
        .iter()
        .map(|t| printed_in_turn(std::slice::from_ref(t))[0].clone())
        .collect();
    let t1 = || vec![("Part1".to_string(), "1 | 2".to_string())];
    assert_eq!(
        alone,
        [
            ("(1 | 2, 0)".to_string(), vec![]),
            ("((1 | 2, 0), 0)".to_string(), vec![]),
            ("(((1 | 2, 0), 0), 0)".to_string(), vec![]),
            ("((Part1, 0), Part1)".to_string(), t1()),
            ("(((Part1, 0), 0), Part1)".to_string(), t1()),
        ]
    );
    assert_eq!(printed_in_turn(&ts), alone);
}

#[test]
fn a_name_the_message_or_the_program_holds_is_skipped() {
    let _on = collect();
    let x = Type::tuple(vec![defs_abc(), defs_abc()]).surface().root;
    let mut message = format!("`Part1` does not take {x}");
    let defs = lift(&mut [&mut message], &|w| w == "Part2");
    assert_eq!(message, "`Part1` does not take (Part3, Part3)");
    assert_eq!(defs[0].0, "Part3");
}

#[test]
fn a_difference_of_differences_prints_as_written() {
    // `A \ (B \ C)` is `A & ((all \ B) | C)`, which needs the top type `_` of L10 to write;
    // it prints as written, in the forms of L1 (READ-atom-meet).
    let a = Type::exact(Type::atom("a"), Type::int());
    let b = Type::partial(Type::atom("b"), Type::bool());
    let c = Type::exact(Type::int(), Type::empty());
    let t = &a - &(&b - &c);
    assert_eq!(
        t.surface().to_string(),
        "(#a -> int) \\ ((#b ->? bool) \\ (int -> Never))"
    );
    let d = Type::exact(Type::string(), Type::string());
    let t = &(&a - &d) - &(&b - &c);
    assert_eq!(
        t.surface().to_string(),
        "(#a -> int) \\ ((String -> String) | ((#b ->? bool) \\ (int -> Never)))"
    );
    // Tuples of one length the same.
    let row = |x: Type, y: Type| Type::tuple(vec![x, y]);
    let t = &row(a.clone(), a.clone()) - &(&row(b.clone(), a.clone()) - &row(b.clone(), c.clone()));
    assert_eq!(
        t.surface().to_string(),
        "type Part1 = #a -> int;\ntype Part2 = #b ->? bool;\n(Part1, Part1) \\ ((Part2, Part1) \\ (Part2, int -> Never))"
    );
    // Every morphism but some is no type of L1, and keeps `_`.
    let t = &Type::universe(super::super::Universe::Morphism) - &a;
    assert_eq!(t.surface().to_string(), "(_ ->? _) \\ (#a -> int)");
}

/// A random part of 1-tuples over six rows, from literals, their complements, meets,
/// unions and complements.
fn random_part(rng: &mut Rng, depth: u32) -> Part<Row> {
    let k = rng.next_u64();
    if depth == 0 || k.is_multiple_of(5) {
        let l = Part::literal(Row::new(vec![lit(k / 5 % 6)]));
        return if (k / 30).is_multiple_of(2) {
            l
        } else {
            l.not()
        };
    }
    let a = random_part(rng, depth - 1);
    match k % 3 {
        0 => a.zip(&random_part(rng, depth - 1), Op::And),
        1 => a.zip(&random_part(rng, depth - 1), Op::Or),
        _ => a.not(),
    }
}

#[test]
fn only_a_part_holding_values_outside_every_atom_prints_the_top_type() {
    // Item PRINT-kept-meet-all: a part prints `_` exactly when it holds the values outside
    // every atom it names, which no other text can write; a kept meet or complement whose
    // operand holds them, and that does not hold them itself, is written without `_`.
    let mut kept = 0;
    let base =
        crate::seed::seed("only_a_part_holding_values_outside_every_atom_prints_the_top_type");
    for i in 0..4000u64 {
        let mut rng = Rng::new(base.wrapping_add(i * 7919));
        kept += usize::from(prints_top_when_outside(&random_part(&mut rng, 6)).0);
    }
    eprintln!("{kept} of 4000 kept as expressions");
    // Kept expressions built, whatever the draws met (PROOF-test-count-thresholds; until
    // 2026-11-15 the test asserted more than 800 among the 4,000 drawn): `xor_part`, which
    // holds no value outside its atoms (with both false it is false), and its complement,
    // which holds them all.
    let x = xor_part();
    assert_eq!(prints_top_when_outside(&x), (true, false), "{x:?}");
    assert_eq!(prints_top_when_outside(&x.not()), (true, true), "{x:?}");
}

/// Checks that the type of the one-tuples of `p` prints `_` exactly when `p` holds the values
/// outside every atom it names; gives whether `p` is kept as an expression, and whether it
/// holds those values.
fn prints_top_when_outside(p: &Part<Row>) -> (bool, bool) {
    let outside = p.eval3(&|_| Some(false)).expect("every atom is known");
    let t = Type::with(|q| {
        q.tuples.lens.insert(1, p.clone());
    });
    let s = t.surface().to_string();
    assert_eq!(s.contains('_'), outside, "{s}");
    (p.view().is_err(), outside)
}

/// `(0,) ^ (2,)`, written `(0,) & !(2,) | !(0,) & (2,)`: an exclusive or is no decision list,
/// so `zip` keeps it as an expression
/// (`two_exclusive_ors_on_disjoint_atoms_meet_in_an_expression` in `bdd/tests.rs`).
fn xor_part() -> Part<Row> {
    let a = Part::literal(Row::new(vec![lit(0)]));
    let c = Part::literal(Row::new(vec![lit(2)]));
    (a.zip(&c.not(), Op::And)).zip(&a.not().zip(&c, Op::And), Op::Or)
}

/// A type printed apart (`Type::surfaces_apart`, `Printer::write_out`) is written out where it
/// stands, parenthesized when its place does not admit its text, never by a name of its own,
/// even when another type printed with it names the same part.
#[test]
fn a_type_printed_apart_is_written_out_and_parenthesized_by_its_place() {
    use super::super::TextPlace as At;
    let d = &Type::int() - &lit(1);
    let pair = Type::tuple(vec![d.clone(), d.clone()]);
    let print = |ts: &[(Type, At)], apart: &[bool]| {
        let s = Type::surfaces_apart(ts, apart, None);
        (s.defs, s.roots)
    };
    let part1 = vec![("Part1".to_string(), "int \\ 1".to_string())];
    assert_eq!(
        print(&[(d.clone(), At::Union)], &[true]),
        (vec![], vec!["(int \\ 1)".into()])
    );
    assert_eq!(
        print(&[(d.clone(), At::Any)], &[true]),
        (vec![], vec!["int \\ 1".into()])
    );
    let both = [(pair.clone(), At::Any), (d.clone(), At::Union)];
    assert_eq!(
        print(&both, &[false, true]),
        (
            part1.clone(),
            vec!["(Part1, Part1)".into(), "(int \\ 1)".into()]
        )
    );
    assert_eq!(
        print(&both, &[false, false]),
        (part1.clone(), vec!["(Part1, Part1)".into(), "Part1".into()])
    );
    assert_eq!(
        print(&[(pair, At::Union)], &[true]),
        (part1, vec!["(Part1, Part1)".into()])
    );
}

/// Item TEST-kernel-unreached-paths-4 (kernel13): a message collecting the definitions of a
/// cycle (`Printer::collect`): a definition whose body waits on one not placed yet gets a place
/// first and its body after the others; a union named by count that waits is written where it
/// stands; a tuple that waits and is not named is written where it stands; a node whose text
/// is the tuple's name is an alias, given the tuple's reference.
#[test]
fn a_message_collects_the_definitions_of_a_cycle() {
    use super::super::rec::{Def, Expr, Group};
    let mutual = Group::new(vec![
        Def {
            name: "KM0".into(),
            params: vec![],
            body: Expr::Union(vec![
                Expr::Type(Type::atom("ma")),
                Expr::Atom("ml".into(), vec![Expr::Ref(1, vec![])]),
            ]),
        },
        Def {
            name: "KM1".into(),
            params: vec![],
            body: Expr::Union(vec![
                Expr::Type(Type::atom("mb")),
                Expr::Atom("mm".into(), vec![Expr::Ref(0, vec![])]),
            ]),
        },
    ])
    .expect("a group")
    .instance(vec![])
    .remove(0);
    let tl = Group::new(vec![Def {
        name: "KT".into(),
        params: vec![],
        body: Expr::Union(vec![
            Expr::Type(Type::atom("stop")),
            Expr::Tuple(vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])]),
        ]),
    }])
    .expect("a group")
    .instance(vec![])
    .remove(0);
    let tn = Group::new(vec![Def {
        name: "KN".into(),
        params: vec![],
        body: Expr::Tuple(vec![
            Expr::Type(Type::int()),
            Expr::Union(vec![Expr::Type(Type::atom("stop")), Expr::Ref(0, vec![])]),
        ]),
    }])
    .expect("a group")
    .instance(vec![])
    .remove(0);
    let in_a_message = |t: &Type| {
        let _on = collect();
        let mut root = t.surface().root;
        let defs = lift(&mut [&mut root], &|_| false);
        (root, defs)
    };
    let def = |name: &str, body: &str| (name.to_string(), body.to_string());
    // `#ml(KM1)` waits on `KM0`, and `KM1`'s union, named by count, waits too: it is written
    // where it stands, inside `KM0`'s body.
    assert_eq!(
        in_a_message(&mutual),
        (
            "Part2".to_string(),
            vec![
                def("Part1", "#mb | #mm(Part2)"),
                def("Part2", "#ma | #ml(Part1)")
            ]
        )
    );
    // The tuple `(int, KT)` waits on `KT` and is not named: written in `KT`'s body.
    let one = in_a_message(&tl);
    assert_eq!(
        one,
        (
            "Part1".to_string(),
            vec![def("Part1", "(int, Part1) | #stop")]
        )
    );
    // The same inside a tuple: the tuple holding the cycle is placed after it.
    assert_eq!(
        in_a_message(&Type::tuple(vec![lit(1), tl.clone()])),
        ("(1, Part1)".to_string(), one.1)
    );
    // `KN`'s node is one name, the tuple's: an alias of it, given the tuple's reference.
    assert_eq!(
        in_a_message(&tn),
        (
            "Part2".to_string(),
            vec![def("Part1", "Part2 | #stop"), def("Part2", "(int, Part1)")]
        )
    );
}

/// Item TEST-kernel-unreached-paths-4 (kernel14, `Printer::collect`'s arm `(false, false)`): a
/// recursive type whose body is a tuple, `KP0 = (int, KP1)` with `KP1 = #pa | #pb(KP0)`. `KP1`'s
/// union waits on `KP0` and gets a place first; the tuple `(int, Part1)` then waits on nothing
/// and gets its reference, so `KP0`'s node, a recursive type with a definition (no alias, not
/// named by count), has a body that waits on nothing: the arm, which puts it in the table,
/// merged with an equal definition there. In a message of two types it is defined once.
/// Control (kernel14): the arm given a place of its own, as a body that waits gets
/// (`defs::reserve`), defines `Part3 = Part2` and `Part4 = Part2` in the message of `KP0` and
/// `(KP0, 1)`, and the test fails. Writing the body itself in place of the arm's reference (as
/// an alias is written) passes, since the body here is one reference, the tuple's.
#[test]
fn a_recursive_type_whose_body_is_a_tuple_is_defined_by_the_tuple() {
    use super::super::rec::{Def, Expr, Group};
    let g = Group::new(vec![
        Def {
            name: "KP0".into(),
            params: vec![],
            body: Expr::Tuple(vec![Expr::Type(Type::int()), Expr::Ref(1, vec![])]),
        },
        Def {
            name: "KP1".into(),
            params: vec![],
            body: Expr::Union(vec![
                Expr::Type(Type::atom("pa")),
                Expr::Atom("pb".into(), vec![Expr::Ref(0, vec![])]),
            ]),
        },
    ])
    .expect("a group")
    .instance(vec![]);
    let in_a_message = |t: &Type| {
        let _on = collect();
        let mut root = t.surface().root;
        let defs = lift(&mut [&mut root], &|_| false);
        (root, defs)
    };
    let def = |name: &str, body: &str| (name.to_string(), body.to_string());
    assert_eq!(
        in_a_message(&g[0]),
        (
            "Part2".to_string(),
            vec![
                def("Part1", "#pa | #pb(Part2)"),
                def("Part2", "(int, Part1)")
            ]
        )
    );
    assert_eq!(
        in_a_message(&g[1]),
        (
            "Part2".to_string(),
            vec![
                def("Part1", "(int, Part2)"),
                def("Part2", "#pa | #pb(Part1)")
            ]
        )
    );
    let in_turn = |ts: &[&Type]| {
        let _on = collect();
        let mut roots: Vec<String> = ts.iter().map(|t| t.surface().root).collect();
        let mut refs: Vec<&mut String> = roots.iter_mut().collect();
        let defs = lift(&mut refs, &|_| false);
        (roots, defs)
    };
    let words = |ws: &[&str]| ws.iter().map(|w| w.to_string()).collect::<Vec<_>>();
    let two = Type::tuple(vec![g[0].clone(), lit(1)]);
    let kp0 = vec![
        def("Part1", "#pa | #pb(Part2)"),
        def("Part2", "(int, Part1)"),
    ];
    assert_eq!(
        in_turn(&[&g[0], &two]),
        (words(&["Part2", "(Part2, 1)"]), kp0.clone())
    );
    assert_eq!(
        in_turn(&[&two, &g[0]]),
        (words(&["(Part2, 1)", "Part2"]), kp0)
    );
    assert_eq!(
        in_turn(&[&g[1], &g[0], &two]),
        (
            words(&["Part2", "Part1", "(Part1, 1)"]),
            vec![
                def("Part1", "(int, Part2)"),
                def("Part2", "#pa | #pb(Part1)")
            ]
        )
    );
}

/// One recursive type written by two types of one message is defined once: the later print
/// takes the reference the earlier one gave the cycle (FAIL-print-cycle-defined-twice), in
/// either order of the two types, and so does a pair of types defined by each other.
#[test]
fn a_cycle_written_by_two_types_of_a_message_is_defined_once() {
    use super::super::rec::{Def, Expr, Group};
    let tl = Group::new(vec![Def {
        name: "KT".into(),
        params: vec![],
        body: Expr::Union(vec![
            Expr::Type(Type::atom("stop")),
            Expr::Tuple(vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])]),
        ]),
    }])
    .expect("a group")
    .instance(vec![])
    .remove(0);
    let pair = Type::tuple(vec![tl.clone(), tl.clone()]);
    let in_turn = |ts: &[&Type]| {
        let _on = collect();
        let mut roots: Vec<String> = ts.iter().map(|t| t.surface().root).collect();
        let mut refs: Vec<&mut String> = roots.iter_mut().collect();
        let defs = lift(&mut refs, &|_| false);
        (roots, defs)
    };
    let def = |name: &str, body: &str| (name.to_string(), body.to_string());
    let words = |ws: &[&str]| ws.iter().map(|w| w.to_string()).collect::<Vec<_>>();
    let kt = vec![def("Part1", "(int, Part1) | #stop")];
    assert_eq!(
        in_turn(&[&tl, &pair]),
        (words(&["Part1", "(Part1, Part1)"]), kt.clone())
    );
    assert_eq!(
        in_turn(&[&pair, &tl]),
        (words(&["(Part1, Part1)", "Part1"]), kt.clone())
    );
    assert_eq!(
        in_turn(&[&tl, &tl, &pair]),
        (words(&["Part1", "Part1", "(Part1, Part1)"]), kt)
    );
    let mutual = Group::new(vec![
        Def {
            name: "KM0".into(),
            params: vec![],
            body: Expr::Union(vec![
                Expr::Type(Type::atom("ma")),
                Expr::Atom("ml".into(), vec![Expr::Ref(1, vec![])]),
            ]),
        },
        Def {
            name: "KM1".into(),
            params: vec![],
            body: Expr::Union(vec![
                Expr::Type(Type::atom("mb")),
                Expr::Atom("mm".into(), vec![Expr::Ref(0, vec![])]),
            ]),
        },
    ])
    .expect("a group")
    .instance(vec![]);
    let (m0, m1) = (&mutual[0], &mutual[1]);
    assert_eq!(
        in_turn(&[m0, &Type::tuple(vec![m0.clone(), lit(1)])]),
        (
            words(&["Part2", "(Part2, 1)"]),
            vec![
                def("Part1", "#mb | #mm(Part2)"),
                def("Part2", "#ma | #ml(Part1)")
            ]
        )
    );
    // `KM1` is a definition of the first print, written here by its reference.
    let (roots, defs) = in_turn(&[m0, m1]);
    assert_eq!(defs.len(), 2, "{roots:?} {defs:?}");
    // A later type that holds a union and a part printed before is printed again with every
    // part printed anew (`Printer::print`); the cycle is still defined once.
    let ab = Type::tuple(vec![lit(1), lit(2)]);
    let both = Type::union_all([ab.clone(), Type::tuple(vec![ab.clone(), tl.clone()])]);
    let (roots, defs) = in_turn(&[&Type::tuple(vec![ab.clone(), tl.clone()]), &both]);
    let cycles = defs
        .iter()
        .filter(|(_, body)| body.contains("#stop"))
        .count();
    assert_eq!(cycles, 1, "{roots:?} {defs:?}");
}

/// `Printer::meet_of_literals` walks an `&` whose operands share a part: `x & (m & x)`, with
/// `x` an exclusive or and `m` a meet of two morphism literals, is kept as that form. When the
/// digests put `m & x` on top of the stack, `x` is pushed twice and popped the second time
/// decided; otherwise `x` is decided first and not pushed again. Either way the meet `m` is
/// folded to one arrow. The order follows the digests, which differ between builds, so the
/// test runs over many `x` (TEST-kernel-unreached-paths-4, kernel13).
#[test]
fn a_meet_whose_operands_share_a_part_folds_the_meet_in_it() {
    let (int, b, never) = (Type::int(), Type::bool(), Type::empty());
    let ar = |l: Type, u: Type, v: Type| Type::morphism(l, u, v);
    let any = |v: Type| Type::morphism(Type::empty(), Type::top(), v);
    let m = &ar(never.clone(), int, lit(1)) & &ar(never, b, lit(1));
    let x = |p: &Type, q: &Type| &(p - q) | &(q - p);
    for k in 2..40 {
        let xk = x(&any(lit(k)), &any(lit(k + 1)));
        let text = (&xk & &(&m & &xk)).surface().to_string();
        assert!(text.contains("(Never ->? 1)"), "{k}: {text}");
    }
}

/// A text with no syntax is printed while a message collects its parts, and `remember` keeps
/// none of it: `#a` with every tuple as its payload prints `#a(tuple)`, which is not exact, so
/// `Printer::remember` returns at once. The control, `#a` with any payload, prints `#a(..)`,
/// exact (TEST-kernel-unreached-paths-14: no test printed an inexact text while collecting).
#[test]
fn an_inexact_text_is_printed_while_collecting() {
    let _on = collect();
    let s = Type::atom_with("a", &Type::universe(Universe::Tuple)).surface();
    assert!(!s.exact, "{s}");
    assert_eq!(plain(&s.root), "#a(tuple)");
    let c = Type::atom_with("a", &Type::top()).surface();
    assert!(c.exact, "{c}");
    assert_eq!(plain(&c.root), "#a(..)");
}

/// The two edges of the texts that reach a type no node holds, in the proof at
/// `Printer::force_cycles` (PROOF-sweep-zed-kernel): the complement arm of `Printer::ty`, and
/// the atom parts turned over in `Printer::items`, each turning over the payload `(ForceL,)`
/// of `#a`, whose column is a recursive type. Each prints, with names and without, so
/// `Printer::heights`, which panics on a cycle through no recursive type with a definition,
/// passes.
#[test]
fn a_cycle_of_parts_inside_every_value_but_one_atom_payload_is_defined() {
    use super::super::rec::{Def, Expr, Group};
    // `type ForceL = #nil | #c(ForceL); type ForceM = #a(ForceL);`.
    let defs = vec![
        Def {
            name: "ForceL".into(),
            params: vec![],
            body: Expr::Union(vec![
                Expr::Type(Type::atom("nil")),
                Expr::Atom("c".into(), vec![Expr::Ref(0, vec![])]),
            ]),
        },
        Def {
            name: "ForceM".into(),
            params: vec![],
            body: Expr::Atom("a".into(), vec![Expr::Ref(0, vec![])]),
        },
    ];
    let m = Group::new(defs)
        .expect("accepted")
        .instance(vec![])
        .remove(1);
    // Every value but `#a(ForceL)` takes the complement arm of `Printer::ty`; without the
    // structs it does not, and its atoms are written `#_ \ #a(ForceL)` by `Printer::items`,
    // each atom part turned over.
    let not_m = !&m;
    let no_structs = &not_m - &Type::universe(super::super::Universe::Struct);
    for (t, want) in [
        (&not_m, "_ \\ #a(ForceL)"),
        (&!&not_m, "#a(ForceL)"),
        (&no_structs, "#_ \\ #a(ForceL)"),
    ] {
        let named = t.surface_by_name(super::At::Any).to_string();
        let plain = t.surface().to_string();
        assert!(named.contains(want), "{named}");
        assert!(plain.contains("#c("), "{plain}");
    }
}

#[test]
fn a_doubled_tuple_names_each_level_once() {
    // QUESTIONS A5, answer A (A5-print): the example of the row.
    let pair = Type::tuple(vec![Type::int(), Type::int()]);
    assert_eq!(
        doubled(pair.clone(), 2).surface().to_string(),
        "type Part1 = (int, int);\ntype Part2 = (Part1, Part1);\n(Part2, Part2)"
    );
    // `2^d` copies of the base, `d` definitions: the text grows with `d`, whatever the base
    // (a tuple of types, of literals, or a difference).
    for base in [
        pair,
        Type::tuple(vec![lit(1), lit(1)]),
        &Type::int() - &lit(1),
    ] {
        for d in 1..=12 {
            let s = doubled(base.clone(), d).surface();
            assert_eq!(s.defs.len(), d, "d = {d}");
            assert_eq!(s.root, format!("(Part{d}, Part{d})"), "d = {d}");
        }
    }
}

/// `t_0 = base` and `t_{k+1} = (t_k, t_k)`, so `t_d`: `2^d` copies of `base` on `d + 1`
/// distinct parts.
pub(super) fn doubled(base: Type, d: usize) -> Type {
    (0..d).fold(base, |t, _| Type::tuple(vec![t.clone(), t]))
}
