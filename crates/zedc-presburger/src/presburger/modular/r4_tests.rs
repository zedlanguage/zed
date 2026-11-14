use super::*;
use crate::scaling;
mod bench;

#[test]
fn pncx_affine_alias_names_match() {
    let mut answers = Vec::new();
    for (name, sign) in [
        ("a", 1),
        ("z", 1),
        ("b", -1),
        ("y", -1),
        ("w", 1),
        ("xa", -1),
    ] {
        let xa = Atom::Sym("x".into());
        let alias = Atom::Sym(name.into());
        let x = Lin::atom(xa.clone());
        let mut parts = vec![
            Formula::Con(Con::eq(
                &Lin::atom(alias.clone()),
                &if sign > 0 {
                    x.minus(&Lin::constant(8))
                } else {
                    Lin::constant(8).minus(&x)
                },
            )),
            Formula::Con(Con::ge(&x, &Lin::constant(-8))),
            Formula::Con(Con::ge(&Lin::constant(26), &x)),
        ];
        let mut point = Model::from([(xa, Int::from(9)), (alias, Int::from(sign))]);
        let mut rs = Vec::new();
        for (i, (m, off, width)) in [(10i64, 1i64, 1i64), (4, -5, 1), (8, 0, 7)]
            .into_iter()
            .enumerate()
        {
            let qa = Atom::Aux(2 * i as u32);
            let ra = Atom::Aux(2 * i as u32 + 1);
            let q = Lin::atom(qa.clone());
            let r = Lin::atom(ra.clone());
            parts.push(Formula::Con(Con::eq(
                &x.plus(&Lin::constant(off)),
                &q.times(m).plus(&r),
            )));
            parts.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
            parts.push(Formula::Con(Con::ge(&Lin::constant(width), &r)));
            point.insert(qa, Int::from((9 + off).div_euclid(m)));
            point.insert(ra, Int::from((9 + off).rem_euclid(m)));
            rs.push(r);
        }
        let eq = |i: usize, v: i64| Formula::Con(Con::eq(&rs[i], &Lin::constant(v)));
        parts.push(Formula::or(vec![
            eq(1, 2),
            eq(1, 1),
            Formula::Con(Con::ge(&Lin::constant(12), &x)),
        ]));
        parts.push(Formula::or(vec![
            Formula::negate(eq(0, 5)),
            Formula::negate(eq(2, 7)),
        ]));
        let f = Formula::and(parts);
        assert!(f.holds(&point));
        let answer = (
            crate::presburger::decide(&f),
            crate::presburger::satisfiable(&f).map(|m| m.is_some()),
        );
        println!("AFFINE_RENAME {name} {sign} answer={answer:?}");
        answers.push(answer);
    }
    assert!(answers.iter().all(|a| *a == answers[0]), "{answers:?}");
}

fn prefix_formula(n: usize) -> Formula {
    let x = Lin::atom(Atom::Sym("x".into()));
    let mut defs = vec![Formula::Con(Con::ge(&x, &Lin::constant(1)))];
    let mut rs = Vec::new();
    for (i, m) in [3i64, 5].into_iter().enumerate() {
        let q = Lin::atom(Atom::Aux(2 * i as u32));
        let r = Lin::atom(Atom::Aux(2 * i as u32 + 1));
        defs.push(Formula::Con(Con::eq(&x, &q.times(m).plus(&r))));
        defs.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
        defs.push(Formula::Con(Con::ge(&Lin::constant(m - 1), &r)));
        rs.push(r);
    }
    let mut prefix = Formula::top();
    for i in 0..n {
        let clause = Formula::or(vec![
            Formula::Con(Con::eq(&rs[0], &Lin::constant(0))),
            Formula::Con(Con::eq(&rs[1], &Lin::constant(0))),
            Formula::Con(Con::ge(&x, &Lin::constant(i as i64 + 2))),
        ]);
        prefix = Formula::And(crate::presburger::Shared::new(vec![prefix, clause]));
    }
    defs.push(prefix);
    Formula::And(crate::presburger::Shared::new(defs))
}

fn pure_constraints(n: usize, modular: bool) -> Formula {
    let x = Lin::atom(Atom::Sym("x".into()));
    let q = Lin::atom(Atom::Aux(0));
    let r = Lin::atom(Atom::Aux(1));
    let m = if modular { 2 * n as i64 + 1 } else { 3 };
    let mut parts = vec![Formula::Con(Con::ge(&x, &Lin::constant(1)))];
    if modular {
        parts.push(Formula::Con(Con::eq(&x, &q.times(m).plus(&r))));
        parts.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
        parts.push(Formula::Con(Con::ge(&Lin::constant(m - 1), &r)));
    } else {
        parts.push(Formula::Con(Con::eq(
            &x.minus(&q.times(m)),
            &Lin::constant(1),
        )));
    }
    for i in 0..n {
        parts.push(Formula::negate(Formula::Con(Con::eq(
            if modular { &r } else { &x },
            &Lin::constant(if modular {
                2 * i as i64 + 1
            } else {
                3 * i as i64 + 1
            }),
        ))));
    }
    Formula::and(parts)
}

#[test]
fn pncx_domain_membership_matches_scan() {
    let domain = Domain::from_pieces(vec![
        (None, Some(Int::from(-3))),
        (Some(Int::from(1)), Some(Int::from(4))),
        (Some(Int::from(8)), None),
    ]);
    let ends: Vec<_> = std::iter::once(None)
        .chain((-10..=10).map(|v| Some(Int::from(v))))
        .collect();
    for lo in &ends {
        for hi in &ends {
            if matches!((lo, hi), (Some(a), Some(b)) if a > b) {
                continue;
            }
            let expected = domain.pieces.iter().any(|(l, h)| {
                l.as_ref()
                    .is_none_or(|l| lo.as_ref().is_some_and(|v| l <= v))
                    && h.as_ref()
                        .is_none_or(|h| hi.as_ref().is_some_and(|v| h >= v))
            });
            assert_eq!(domain.contains_span(lo, hi), expected);
        }
    }
}

#[test]
fn pncx_case4609_keeps_its_answer() {
    let x = Lin::atom(Atom::Sym("x".into()));
    let mut parts = vec![Formula::Con(Con::ge(&x, &Lin::constant(18)))];
    let mut rs = Vec::new();
    let mut point = Model::from([(Atom::Sym("x".into()), Int::from(25))]);
    for (i, (m, off)) in [(30i64, 0i64), (5, -1), (27, 2), (25, -3), (15, 5)]
        .into_iter()
        .enumerate()
    {
        let qa = Atom::Aux(2 * i as u32);
        let ra = Atom::Aux(2 * i as u32 + 1);
        let q = Lin::atom(qa.clone());
        let r = Lin::atom(ra.clone());
        parts.push(Formula::Con(Con::eq(
            &x.plus(&Lin::constant(off)),
            &q.times(m).plus(&r),
        )));
        parts.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
        parts.push(Formula::Con(Con::ge(&Lin::constant(m - 1), &r)));
        point.insert(qa, Int::from((25 + off).div_euclid(m)));
        point.insert(ra, Int::from((25 + off).rem_euclid(m)));
        rs.push(r);
    }
    let eq = |i: usize, c: i64| Formula::Con(Con::eq(&rs[i], &Lin::constant(c)));
    parts.push(Formula::or(vec![
        eq(4, 0),
        eq(4, 7),
        Formula::Con(Con::ge(&Lin::constant(16), &x)),
    ]));
    parts.push(Formula::negate(eq(3, 20)));
    parts.push(Formula::or(vec![
        Formula::negate(eq(3, 14)),
        Formula::negate(eq(2, 12)),
    ]));
    parts.push(Formula::negate(Formula::and(vec![
        eq(2, 1),
        Formula::Con(Con::ge(&x, &Lin::constant(13))),
    ])));
    parts.push(Formula::negate(eq(4, 11)));
    let f = Formula::and(parts);
    assert!(f.holds(&point));
    assert_eq!(crate::presburger::decide(&f), Ok(true));
    let model = crate::presburger::satisfiable(&f)
        .expect("answered")
        .expect("point");
    assert!(f.holds(&model));
}

#[test]
fn pncx_batch_remainders_match() {
    let mut x = Int::ONE;
    for i in 0..512 {
        x = &(&x * &Int::from(2)) + &Int::from(i % 7);
        let mut ms: Vec<_> = (2..30).map(Int::from).collect();
        ms.push(&x + &Int::ONE);
        for point in [x.clone(), -&x] {
            let want: Vec<_> = ms.iter().map(|m| point.mod_floor_wide(m)).collect();
            assert_eq!(batch_remainders(&point, &ms), want);
        }
    }
}

#[test]
fn pncx_scalar_validation_matches_full_models() {
    let x = Atom::Sym("x".into());
    let q = Atom::Aux(0);
    let r = Atom::Aux(1);
    let mut uf = UnitUf::new();
    for a in [&x, &q, &r] {
        uf.ensure(a);
    }
    let atoms = BTreeSet::from([x.clone(), q.clone(), r.clone()]);
    let fixed = HashMap::new();
    let local = HashMap::new();
    let mut point = Int::ONE;
    for i in 0..512 {
        point = &(&point * &Int::from(2)) + &Int::from(i % 11);
        let m = Int::from(2 + i % 29);
        let rem = HashMap::from([(
            r.clone(),
            FullRemDef {
                c_r: -1,
                x_root: x.clone(),
                c_x: Int::ONE,
                q_root: q.clone(),
                c_q: -&m,
                k: Int::ZERO,
            },
        )]);
        let global = HashMap::from([(
            q.clone(),
            GlobalQuot {
                s_x: 1,
                c_lo: Int::ZERO,
                sigma_q: 1,
                m: m.clone(),
                w: &m - &Int::ONE,
            },
        )]);
        for xv in [point.clone(), -&point] {
            let w = ScalarWitness {
                x_root: &x,
                x_val: &xv,
                fixed: &fixed,
                uf: &uf,
                rem_defs: &rem,
                global_quots: &global,
                local_windows: &local,
            };
            let model = build_model(&x, &xv, &atoms, &fixed, &uf, &rem, &global, &local);
            for kq in [-1, 1, 2] {
                let lin = Lin::atom(x.clone())
                    .minus(&Lin::atom(q.clone()).times(&m * &Int::from(kq)))
                    .minus(&Lin::atom(r.clone()));
                for rel in [Rel::Eq, Rel::Ge] {
                    let f = Formula::Con(Con {
                        lin: lin.clone(),
                        rel,
                    });
                    assert_eq!(w.holds(&f), f.holds(&model));
                }
            }
        }
    }
}

#[test]
fn pncx_affine_images_match_enumeration() {
    for q in 2..40i64 {
        for m in [1, q + 1, q - 1] {
            for shift in -3..=3i64 {
                for (a, b) in [(0, 0), (0, q - 2), (q - 1, q - 1)] {
                    let input = vec![(Int::from(a), Int::from(b))];
                    let image =
                        map_affine_mod(&input, &Int::from(m), &Int::from(shift), &Int::from(q))
                            .expect("unit step");
                    for r in 0..q {
                        let expected = (a..=b).any(|y| (shift + m * y).rem_euclid(q) == r);
                        assert_eq!(
                            res_contains(&image, &Int::from(r)),
                            expected,
                            "q={q} m={m} shift={shift} [{a},{b}] r={r}"
                        );
                    }
                }
            }
        }
    }
}

fn color_system(
    n: usize,
) -> (
    Vec<BaseInfo>,
    Vec<ResidueSet>,
    Vec<BTreeMap<usize, ResidueSet>>,
) {
    let info: Vec<_> = shared_moduli(3 * n)
        .into_iter()
        .map(|m| {
            let p = m.div_floor_wide(&Int::from(2));
            BaseInfo {
                max_q: p.clone(),
                u: Int::ZERO,
                stride: Int::ONE,
                z_max_q: p,
            }
        })
        .collect();
    let allowed = vec![vec![(Int::ZERO, Int::from(2))]; info.len()];
    let mut clauses = Vec::new();
    for start in (0..3 * n).step_by(3) {
        for (a, b) in [
            (start, start + 1),
            (start + 1, start + 2),
            (start, start + 2),
        ] {
            for c in 0..3 {
                let color = Int::from(c);
                clauses.push(BTreeMap::from([
                    (
                        a,
                        res_diff(
                            &allowed[a],
                            &[(color.clone(), color.clone())],
                            &info[a].max_q,
                        ),
                    ),
                    (
                        b,
                        res_diff(&allowed[b], &[(color.clone(), color)], &info[b].max_q),
                    ),
                ]));
            }
        }
    }
    (info, allowed, clauses)
}

fn connected_color_system(
    n: usize,
) -> (
    Vec<BaseInfo>,
    Vec<ResidueSet>,
    Vec<BTreeMap<usize, ResidueSet>>,
) {
    let (info, allowed, mut clauses) = color_system(n);
    for b in (3..3 * n).step_by(3) {
        for c in 0..3 {
            clauses.push(BTreeMap::from([
                (
                    b - 1,
                    res_diff(
                        &allowed[b - 1],
                        &[(Int::from(c), Int::from(c))],
                        &info[b - 1].max_q,
                    ),
                ),
                (
                    b,
                    res_diff(&allowed[b], &[(Int::from(c), Int::from(c))], &info[b].max_q),
                ),
            ]));
        }
    }
    (info, allowed, clauses)
}

#[test]
fn pncx_coloring_small_graphs_match_enumeration() {
    let (mut info, mut allowed, _) = color_system(2);
    info.truncate(5);
    allowed.truncate(5);
    let edges: Vec<_> = (0..5)
        .flat_map(|a| (a + 1..5).map(move |b| (a, b)))
        .collect();
    let mut found = 0;
    for mask in 0..(1usize << edges.len()) {
        let selected: Vec<_> = edges
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, &e)| e)
            .collect();
        let clauses: Vec<_> = selected
            .iter()
            .flat_map(|&(a, b)| (0..3).map(move |c| (a, b, c)))
            .map(|(a, b, c)| {
                BTreeMap::from([
                    (
                        a,
                        res_diff(&allowed[a], &[(Int::from(c), Int::from(c))], &info[a].max_q),
                    ),
                    (
                        b,
                        res_diff(&allowed[b], &[(Int::from(c), Int::from(c))], &info[b].max_q),
                    ),
                ])
            })
            .collect();
        let brute = (0..243usize).any(|mut code| {
            let mut colors = [0; 5];
            for color in &mut colors {
                *color = code % 3;
                code /= 3;
            }
            selected.iter().all(|&(a, b)| colors[a] != colors[b])
        });
        let candidate = graph_coloring_witness(&info, &allowed, &clauses);
        assert_eq!(
            candidate.is_some(),
            brute && !selected.is_empty(),
            "mask={mask}"
        );
        if let Some(point) = candidate {
            found += 1;
            assert!(brute, "mask={mask}");
            assert!(
                holds_coprime_point(&point, &info, &allowed, &clauses),
                "mask={mask}"
            );
        }
    }
    assert!(found > 500);
    println!("COLOR_ORACLE graphs=1024 found={found}");
}

#[test]
fn pncx_coloring_relabelings() {
    let (info, allowed, clauses) = connected_color_system(4);
    for sign in [-1, 1] {
        for shift in [-19, -1, 0, 7, 20] {
            let relabeled = allowed
                .iter()
                .zip(&info)
                .map(|(s, b)| {
                    s.iter()
                        .flat_map(|(a, z)| {
                            shift_residue_interval(a, z, sign, &Int::from(shift), &b.max_q)
                        })
                        .collect()
                })
                .zip(&info)
                .map(|(s, b)| res_normalize(s, &b.max_q))
                .collect::<Vec<_>>();
            let transformed = clauses
                .iter()
                .map(|cl| {
                    cl.iter()
                        .map(|(&i, s)| {
                            let values = s
                                .iter()
                                .flat_map(|(a, z)| {
                                    shift_residue_interval(
                                        a,
                                        z,
                                        sign,
                                        &Int::from(shift),
                                        &info[i].max_q,
                                    )
                                })
                                .collect();
                            (i, res_normalize(values, &info[i].max_q))
                        })
                        .collect()
                })
                .collect::<Vec<_>>();
            let point = graph_coloring_witness(&info, &relabeled, &transformed)
                .expect("same coloring problem");
            assert!(holds_coprime_point(&point, &info, &relabeled, &transformed));
        }
    }
    // One extra forbidden pair spoils the matching; the recognizer must not claim this witness.
    let mut other = clauses.clone();
    other.push(BTreeMap::from([
        (
            0,
            res_diff(&allowed[0], &[(Int::ZERO, Int::ZERO)], &info[0].max_q),
        ),
        (
            1,
            res_diff(&allowed[1], &[(Int::ONE, Int::ONE)], &info[1].max_q),
        ),
    ]));
    assert!(graph_coloring_witness(&info, &allowed, &other).is_none());
}

#[test]
fn pncx_independent_components_keep_their_witnesses() {
    for n in 1..20 {
        let (info, allowed, clauses) = color_system(n);
        let RegimeOut::Found(point) =
            solve_coprime_system(&None, &None, &info, allowed.clone(), clauses.clone(), true)
        else {
            panic!("coloring missed");
        };
        assert!(holds_coprime_point(&point, &info, &allowed, &clauses));
    }
}

fn shared_moduli(n: usize) -> BTreeSet<Int> {
    let mut ms = BTreeSet::new();
    let mut p = 3i64;
    while ms.len() < n {
        if (3..)
            .step_by(2)
            .take_while(|d| d * d <= p)
            .all(|d| p % d != 0)
        {
            ms.insert(Int::from(2 * p));
        }
        p += 2;
    }
    ms
}

#[test]
fn pncx_common_factors_reconstruct_inputs() {
    for n in 1..50 {
        let ms = shared_moduli(n);
        let facs = coprime_factorization(&ms).unwrap();
        let bases: BTreeSet<_> = facs.values().flatten().map(|(b, _)| b).collect();
        for a in &bases {
            for b in bases.iter().filter(|b| *b < a) {
                assert_eq!(a.gcd_recursive(b), Int::ONE);
            }
        }
        for m in &ms {
            assert_eq!(facs[m].iter().fold(Int::ONE, |v, (_, q)| &v * q), *m);
        }
    }
}

fn holes(n: usize) -> Vec<Domain> {
    (0..n)
        .map(|i| Domain::single(Int::from(3 * i as i64)).complement())
        .collect()
}

#[test]
fn pncx_lower_witness_enumeration() {
    for m in 2..50i64 {
        for lo in -50..50i64 {
            let s = vec![(Int::from(1), Int::from(m - 1))];
            let first = first_residue_at(&Int::from(lo), &Int::from(m), &s);
            let want = (lo..lo + m).find(|x| x.rem_euclid(m) != 0).map(Int::from);
            assert_eq!(first, want);
        }
    }
}

#[test]
fn pncx_bound_merge_enumeration() {
    for n in 0..40 {
        let ds = holes(n);
        let want = ds.iter().fold(Domain::all(), |a, b| a.intersect(b));
        let got = intersect_domains(ds);
        assert_eq!(got, want);
        for x in -2..3 * n as i64 + 2 {
            let point = Some(Int::from(x));
            assert_eq!(
                got.contains_span(&point, &point),
                x < 0 || x % 3 != 0 || x >= 3 * n as i64
            );
        }
    }
}

/// The formula of the bound-merging benchmark: `x >= 1`, `x mod 3` and `x mod 5` named by
/// remainders, and `n` clauses each allowing either remainder to be 0 or `x != 3i + 1`.
fn bound_merge_formula(n: usize) -> Formula {
    let x = Lin::atom(Atom::Sym("x".into()));
    let mut fs = vec![Formula::Con(Con::ge(&x, &Lin::constant(1)))];
    let mut residues = Vec::new();
    for (i, m) in [3, 5].into_iter().enumerate() {
        let q = Lin::atom(Atom::Aux(2 * i as u32));
        let r = Lin::atom(Atom::Aux(2 * i as u32 + 1));
        fs.push(Formula::Con(Con::eq(&x, &q.times(m).plus(&r))));
        fs.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
        fs.push(Formula::Con(Con::ge(&Lin::constant(m - 1), &r)));
        residues.push(Formula::Con(Con::eq(&r, &Lin::constant(0))));
    }
    for i in 0..n {
        let mut cl = residues.clone();
        cl.push(Formula::negate(Formula::Con(Con::eq(
            &x,
            &Lin::constant(3 * i + 1),
        ))));
        fs.push(Formula::or(cl));
    }
    Formula::and(fs)
}

/// The input of the bound-partition benchmark: `n` disjoint global pieces `[10i, 10i + 4]` and
/// a clause `x >= 10i + 2` for each, which cuts every piece in two.
fn bound_partition_input(n: usize) -> (Domain, Vec<FlatClause>) {
    let global = Domain::from_pieces(
        (0..n)
            .map(|i| {
                let x = Int::from(10 * i as i64);
                (Some(x.clone()), Some(&x + &Int::from(4)))
            })
            .collect(),
    );
    let clauses = (0..n)
        .map(|i| FlatClause {
            bounds: Domain::ge(Int::from(10 * i as i64 + 2)),
            mods: BTreeMap::new(),
        })
        .collect();
    (global, clauses)
}

/// The small instances of the benchmarks in `bench.rs`, with the answers they assert, and the
/// answers of the two routines that the benchmarks only time: membership in disjoint bound
/// intervals, and the first `x >= 1000003` that no modulus `2..n+2` divides.
#[test]
fn the_benchmark_inputs_have_their_answers_at_small_sizes() {
    for n in 1..=6 {
        for residues in [false, true] {
            let f = pure_constraints(n, residues);
            assert!(matches!(solve_modular(&f, false), Some(Some(_))), "{n}");
        }
        assert!(
            matches!(solve_modular(&prefix_formula(n), false), Some(Some(_))),
            "{n}"
        );
        let f = bound_merge_formula(n);
        assert!(matches!(solve_modular(&f, false), Some(Some(_))), "{n}");
        let (info, allowed, clauses) = connected_color_system(n);
        assert!(
            graph_coloring_witness(&info, &allowed, &clauses).is_some(),
            "{n}"
        );
        let (info, allowed, clauses) = color_system(n);
        assert!(
            !matches!(
                solve_coprime_system(&None, &None, &info, allowed, clauses, true),
                RegimeOut::Empty
            ),
            "{n}"
        );
        let domain = Domain::from_pieces(
            (0..n)
                .map(|i| (Some(Int::from(3 * i as i64)), Some(Int::from(3 * i as i64))))
                .collect(),
        );
        for i in 0..n {
            let yes = Some(Int::from(3 * i as i64));
            let no = Some(Int::from(3 * i as i64 + 1));
            assert!(domain.contains_span(&yes, &yes), "{n} {i}");
            assert!(!domain.contains_span(&no, &no), "{n} {i}");
        }
        let units = (2..n + 2)
            .map(|m| (Int::from(m), vec![(Int::ONE, Int::from(m - 1))]))
            .collect::<BTreeMap<_, _>>();
        let lo = 1_000_003usize;
        let first = (lo..).find(|x| (2..n + 2).all(|m| x % m != 0));
        assert_eq!(
            lower_witness(&Int::from(lo), &None, &units, &[]),
            first.map(Int::from),
            "{n}"
        );
        let (global, clauses) = bound_partition_input(n);
        assert_eq!(
            partition_into_regimes(&global, &clauses).len(),
            2 * n,
            "{n}"
        );
    }
}
