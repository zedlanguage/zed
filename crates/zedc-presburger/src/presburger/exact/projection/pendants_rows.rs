use super::*;

fn row(t: &[(&str, i64)], c: i64, rel: Rel) -> Con {
    Con {
        lin: Lin {
            terms: t
                .iter()
                .map(|(n, k)| (Atom::Sym((*n).into()), Int::from(*k)))
                .collect(),
            constant: Int::from(c),
        },
        rel,
    }
}

/// The rows of `exact::tests::an_unbounded_conjunction_needs_one_cell`, projected at once:
/// every `w <= -31`, and -29 (-30 needs `a == -14`, `b == 2`, so `z2 >= -8 > -9`).
#[test]
fn the_whole_pendants_part_is_one_projection() {
    let rows = vec![
        row(&[("a", -1)], -14, Rel::Ge),
        row(&[("b", 1)], -1, Rel::Ge),
        row(&[("b", -1)], 8, Rel::Ge),
        row(&[("z2", -1)], -9, Rel::Ge),
        row(&[("z3", -1)], 2, Rel::Ge),
        row(&[("a", -2), ("b", -1), ("c", -1), ("z2", 1)], -7, Rel::Ge),
        row(&[("a", -1), ("b", -2), ("z2", 1)], -2, Rel::Ge),
        row(&[("a", -1), ("c", -1), ("z3", 1)], -5, Rel::Eq),
        row(&[("a", 1), ("b", 1), ("c", 1), ("z2", -1)], 6, Rel::Ge),
        row(&[("z2", -1), ("z3", 1)], -11, Rel::Ge),
        row(&[("w", -1), ("a", 2), ("b", -1)], 0, Rel::Eq),
        row(&[("w", -1)], -29, Rel::Ge),
    ];
    let mut w = Work {
        used: 0,
        limit: 10_000_000,
        solver: super::super::super::SOLVER,
    };
    let parts = pugh(&rows, &Atom::Sym("w".into()), &IntervalSet::top(), &mut w).unwrap();
    let (got, tails) = ranges(&parts, &mut w).unwrap();
    eprintln!("PARTS {parts:?} WORK {}", w.used);
    assert!(tails.is_empty());
    assert_eq!(
        got,
        IntervalSet::from_pieces(vec![
            (End::NegInf, End::from(-31i64)),
            (End::from(-29i64), End::from(-29i64))
        ])
    );
}
