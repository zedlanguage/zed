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
            let want: Vec<_> = ms.iter().map(|m| point.mod_floor(m)).collect();
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
            let p = m.div_floor(&Int::from(2));
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

/// A coloring question: the bases, the residues each vertex allows, and the clauses (the
/// arguments of `graph_coloring_choices`).
pub(super) type Coloring = (
    Vec<BaseInfo>,
    Vec<ResidueSet>,
    Vec<BTreeMap<usize, ResidueSet>>,
);

/// The size of the coloring benchmarks of `r4_tests` and `r6_tests` (PNCX-coloring-crt-scale).
/// At 16,000 the prism cores took a phase past the 20 s limit on a 12-core VM (2026-11-22), and
/// the other four families 17 to 35 s a piece, ratios 8.16 to 8.22.
pub(super) const COLORS: usize = 8_000;

/// The most work a whole coloring question may take, as a multiple of its two parts measured
/// apart: the coloring and the CRT that joins its witness (PNCX-coloring-crt-scale).
pub(super) const CRT_SHARE: f64 = 1.5;

/// Panics unless `run`, a whole question over `system` whose witness is the coloring's, takes
/// at most [`CRT_SHARE`] times the work of its coloring ([`graph_coloring_choices`]) and of
/// [`Int::crt`] on the residues it chooses. The witness is one integer modulo the
/// product of all the moduli, `N` bits for `k` moduli, which no point avoids: the product of
/// the moduli is its period, and a point of a system whose moduli are all needed has no
/// smaller representative in general. Its CRT costs `O(M(N) log k)`, which grows faster than the
/// limit of 10.5 at 8n once the integers are wide, so the coloring is measured apart, without
/// the CRT (`graph_coloring_choices`, by `scaling::check_order`), and the whole question here
/// against its two parts, as `pncx_fibonacci_crt_scale` measures its question against one gcd:
/// a replay of the bases or clauses on top of the CRT (Stage C's repeated scans) shows here
/// as a share past the bound.
///
/// The two are compared by `scaling::compare_costs_work_only`, which counts instructions
/// wherever a benchmark can: on the hardware counter, or under DynamoRIO in a new process of
/// the test when it runs with other tests on a machine with no counter (`Meter.elsewhere`,
/// BENCH-time-only-checks-by-instructions). Until 2026-11-24 this read one `Meter::work` of
/// each part, which off `--exact` on a Colab VM is processor time: 1.72 and 1.93 times under
/// load against 1.30 alone (FAIL-r4-crt-share-processor-time). Where only processor time can
/// be read, it takes the first of up to `scaling::TRIES` measurements under the bound. The
/// bytes are not held to the bound, which is on work: the question allocates for its own steps
/// beside the two parts, 1.64 times their bytes on hm4 (2026-11-24) against 1.30 times their
/// instructions, and a replay of the bases or clauses would show in the instructions.
pub(super) fn against_its_crt(what: &str, system: &Coloring, run: impl Fn() + Sync) {
    let (info, allowed, clauses) = system;
    let parts = || {
        let choices = graph_coloring_choices(info, allowed, clauses).expect("a coloring");
        std::hint::black_box(Int::crt(choices));
    };
    scaling::compare_costs_work_only(
        &format!("{what}: the whole question against its coloring and its CRT"),
        "a replay of the bases or clauses on top of the coloring and its CRT shows as a share \
         past 1.5 (PNCX-coloring-crt-scale)",
        CRT_SHARE,
        parts,
        run,
    );
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

/// [`connected_color_system`]'s triangles joined in a path are three-colorable, and
/// `solve_coprime_system` finds a point that every residue clause holds (from the probe
/// `pncx_color_components` of PERF-negated-chain-unsolved, which ran it on these clauses).
#[test]
fn pncx_connected_components_keep_their_witnesses() {
    for n in 1..20 {
        let (info, allowed, clauses) = connected_color_system(n);
        let RegimeOut::Found(point) =
            solve_coprime_system(&None, &None, &info, allowed.clone(), clauses.clone(), true)
        else {
            panic!("coloring of {n} connected triangles missed");
        };
        assert!(holds_coprime_point(&point, &info, &allowed, &clauses));
    }
}

/// `x = q_i (2 p_i) + 2 i` for the first `n` odd primes `p_i`: every modulus shares the
/// factor 2 and every remainder is even, so the system has a point.
fn shared_formula(n: usize) -> Formula {
    let x = Lin::atom(Atom::Sym("x".into()));
    let parts = (shared_moduli(n).into_iter().enumerate())
        .map(|(i, m)| {
            let q = Lin::atom(Atom::Aux(i as u32));
            Formula::Con(Con::eq(&x.minus(&q.times(m)), &Lin::constant(2 * i as i64)))
        })
        .collect();
    Formula::and(parts)
}

/// `solve_modular` gives [`shared_formula`] a model that it holds, at 1 to 40 moduli.
#[test]
fn pncx_shared_formula_models() {
    for n in 1..=40 {
        let f = shared_formula(n);
        let Some(Some(model)) = solve_modular(&f, true) else {
            panic!("no model at {n} moduli");
        };
        assert!(f.holds(&model), "{n} moduli");
    }
}

/// The edges of a graph on `3 n` vertices: `n` disjoint triangles, the triangles joined in a
/// path (`connected`), or the square of a cycle (`square`, each vertex joined to the next two).
fn color_edges(n: usize, connected: bool, square: bool) -> Vec<(usize, usize)> {
    if square {
        let mut unique = BTreeSet::new();
        for a in 0..3 * n {
            for step in [1, 2] {
                let b = (a + step) % (3 * n);
                unique.insert((a.min(b), a.max(b)));
            }
        }
        return unique.into_iter().collect();
    }
    let mut edges = Vec::new();
    for start in (0..3 * n).step_by(3) {
        edges.extend([
            (start, start + 1),
            (start + 1, start + 2),
            (start, start + 2),
        ]);
        if connected && start > 0 {
            edges.push((start - 1, start));
        }
    }
    edges
}

/// A three-coloring of [`color_edges`] as a formula: `x = q_i p_i + r_i`, `0 <= r_i <= 2`,
/// over one prime `p_i` per vertex ([`color_system`]'s), and for each edge `(a, b)` and color
/// `c`, `r_a != c or r_b != c`. With a model: `x` the CRT point of the colors `i mod 3`, which
/// colors every one of the three graphs properly: an edge joins `i` to `i + 1` or `i + 2`
/// (each triangle `3 k, 3 k + 1, 3 k + 2`; a joining edge `(3 k - 1, 3 k)`; the square's edges,
/// taken mod `3 n`, a multiple of 3), so its ends' colors differ by 1 or 2 mod 3.
fn color_formula(n: usize, connected: bool, square: bool) -> (Formula, Model) {
    let (info, _, _) = color_system(n);
    let xa = Atom::Sym("x".into());
    let x = Lin::atom(xa.clone());
    let choices = (info.iter().enumerate())
        .map(|(i, b)| (Int::from(i as i64 % 3), b.max_q.clone()))
        .collect();
    let (witness, _) = Int::crt(choices).expect("coprime primes");
    let mut model = Model::from([(xa, witness.clone())]);
    let (mut parts, mut remainders) = (Vec::new(), Vec::new());
    for (i, base) in info.iter().enumerate() {
        let qa = Atom::Aux(2 * i as u32);
        let ra = Atom::Aux(2 * i as u32 + 1);
        let q = Lin::atom(qa.clone());
        let r = Lin::atom(ra.clone());
        parts.push(Formula::Con(Con::eq(
            &x,
            &q.times(base.max_q.clone()).plus(&r),
        )));
        parts.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
        parts.push(Formula::Con(Con::ge(&Lin::constant(2), &r)));
        model.insert(qa, witness.div_floor(&base.max_q));
        model.insert(ra, witness.mod_floor(&base.max_q));
        remainders.push(r);
    }
    for (a, b) in color_edges(n, connected, square) {
        for color in 0..3 {
            parts.push(Formula::or(vec![
                Formula::negate(Formula::Con(Con::eq(&remainders[a], &Lin::constant(color)))),
                Formula::negate(Formula::Con(Con::eq(&remainders[b], &Lin::constant(color)))),
            ]));
        }
    }
    (Formula::and(parts), model)
}

/// `solve_modular` on [`color_formula`] never says there is no point (each graph is
/// three-colorable, and the model built by `i mod 3` holds, checked first), and a model it
/// gives holds. From the probe `pncx_color_formula_axis` of PERF-negated-chain-unsolved,
/// which allowed a refusal (`None`) and printed the work.
#[test]
fn pncx_color_formulas_are_never_refuted() {
    for n in 1..=6 {
        for (connected, square) in [(false, false), (true, false), (false, true)] {
            let what = format!("{n} triangles, connected {connected}, square {square}");
            let (f, model) = color_formula(n, connected, square);
            assert!(f.holds(&model), "{what}: the built model");
            match solve_modular(&f, true) {
                Some(None) => panic!("{what}: refuted"),
                Some(Some(m)) => assert!(f.holds(&m), "{what}: the model given"),
                None => {}
            }
        }
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
        let facs = coprime_factorization(&ms);
        let bases: BTreeSet<_> = facs.values().flatten().map(|(b, _)| b).collect();
        for a in &bases {
            for b in bases.iter().filter(|b| *b < a) {
                assert_eq!(a.gcd(b), Int::ONE);
            }
        }
        for m in &ms {
            assert_eq!(facs[m].iter().fold(Int::ONE, |v, (_, q)| &v * q), *m);
        }
    }
}

/// Whether `vals` (each at least 1) are on the table side of the kernel's
/// `num::coprime::shares_a_factor`.
fn on_the_table_side(vals: &[Int]) -> bool {
    coprime::dense_values(&uint_leaves(vals)).is_some()
}

/// `coprime_factorization` gives the same factors on the table side and on the tree side of
/// the kernel's `shares_a_factor`, with a shared factor and without one, each modulus's
/// factors by increasing base. (The methods of `shares_a_factor` and where it changes from one
/// to the other are tested in zed-kernel, `num::coprime::tests`, since DRY-coprime-bases-one.)
#[test]
fn pncx_coprime_factorization_has_its_answers() {
    let int = |v: i64| Int::from(v);
    let ints = |vs: &[i64]| vs.iter().map(|v| Int::from(*v)).collect::<Vec<_>>();
    // A shared factor 2 over coprime cofactors.
    for (cofactors, table) in [
        (vec![3, 5, 7, 11, 13], true),
        (vec![1009, 1013, 1019], false),
    ] {
        assert_eq!(on_the_table_side(&ints(&cofactors)), table);
        let ms: BTreeSet<Int> = cofactors.iter().map(|p| int(2 * p)).collect();
        let want: ModBase = cofactors
            .iter()
            .map(|p| (int(2 * p), vec![(int(2), int(2)), (int(*p), int(*p))]))
            .collect();
        assert_eq!(coprime_factorization(&ms), want);
    }
    // No shared factor: 6, 10 and 15 are factored over 2, 3 and 5, and each of the others is
    // its own base.
    for (others, table) in [(vec![7, 11, 13], true), (vec![7, 11, 1013], false)] {
        let all: Vec<i64> = [6, 10, 15].into_iter().chain(others.clone()).collect();
        assert_eq!(on_the_table_side(&ints(&all)), table);
        let ms: BTreeSet<Int> = all.iter().map(|m| int(*m)).collect();
        let mut want: ModBase = others
            .iter()
            .map(|p| (int(*p), vec![(int(*p), int(*p))]))
            .collect();
        for (m, a, b) in [(6, 2, 3), (10, 2, 5), (15, 3, 5)] {
            want.insert(int(m), vec![(int(a), int(a)), (int(b), int(b))]);
        }
        assert_eq!(coprime_factorization(&ms), want);
    }
}

/// The cofactors in the bench `pncx_common_factor_scale` are on the table side of
/// `shares_a_factor` at both of its sizes, so its pair of runs measures one method (A96).
#[test]
fn pncx_common_factor_bench_inputs_are_on_the_table_side() {
    for n in [512, 4096] {
        let cofactors: Vec<Int> = odd_primes(n).into_iter().collect();
        assert!(on_the_table_side(&cofactors));
    }
}

/// The first `n` odd primes: the cofactors of `shared_moduli(n)`.
fn odd_primes(n: usize) -> BTreeSet<Int> {
    shared_moduli(n)
        .iter()
        .map(|m| m.div_floor(&Int::from(2)))
        .collect()
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

/// [`intersect_domains`] against the fold of `Domain::intersect` on three domains of every
/// shape, in every order: none, every integer, bounded on either side or both, one point, and
/// the complements of these, of two pieces; they overlap, nest and touch. None at all is every
/// integer.
#[test]
fn pncx_bound_merge_of_mixed_domains_matches_the_fold() {
    let i = |v: i64| Int::from(v);
    let mut shapes = vec![Domain::empty(), Domain::all()];
    for (lo, hi) in [(-3, 2), (0, 0), (1, 5), (3, 3), (6, 9)] {
        shapes.push(Domain::range(i(lo), i(hi)));
        shapes.push(Domain::ge(i(lo)));
        shapes.push(Domain::le(i(hi)));
    }
    let complements: Vec<Domain> = shapes.iter().map(Domain::complement).collect();
    shapes.extend(complements);
    for a in &shapes {
        for b in &shapes {
            for c in &shapes {
                let ds = vec![a.clone(), b.clone(), c.clone()];
                let want = ds.iter().fold(Domain::all(), |x, y| x.intersect(y));
                assert_eq!(intersect_domains(ds), want, "{a:?} {b:?} {c:?}");
            }
        }
    }
    assert_eq!(intersect_domains(Vec::new()), Domain::all());
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

/// `Int::crt` on pairwise coprime moduli (the tree path: odd counts carry a node up)
/// and on moduli sharing a factor (the pairwise path), against the congruences themselves;
/// a conflicting pair gives `None`.
#[test]
fn the_crt_tree_solves_its_congruences() {
    // The odd primes from 3, the first of them times a wide value, so one modulus is past 128
    // bits; the moduli are checked pairwise coprime below.
    let big = &(&Int::from(i128::MAX) * &Int::from(i128::from(u64::MAX) + 14));
    let primes: Vec<Int> = (3i64..200)
        .filter(|p| (2..*p).all(|d| p % d != 0))
        .map(Int::from)
        .collect();
    for k in [1usize, 2, 3, 5, 16, 17] {
        for wide in [false, true] {
            let ms: Vec<Int> = (primes[..k].iter())
                .enumerate()
                .map(|(i, p)| if wide && i == 0 { p * big } else { p.clone() })
                .collect();
            for (i, a) in ms.iter().enumerate() {
                for b in &ms[i + 1..] {
                    assert_eq!(a.gcd(b), Int::ONE, "moduli {a} and {b}");
                }
            }
            let pairs: Vec<(Int, Int)> = (ms.iter().enumerate())
                .map(|(i, m)| (Int::from(i as i64 * 7 + 1).mod_floor(m), m.clone()))
                .collect();
            let (x, m) = Int::crt(pairs.clone()).expect("coprime");
            assert_eq!(m, ms.iter().fold(Int::ONE, |a, v| &a * v), "k {k}");
            assert!(!x.is_negative() && x < m, "k {k}");
            for (r, mi) in &pairs {
                assert_eq!(x.mod_floor(mi), *r, "k {k}");
            }
        }
    }
    // The first 3,001 odd primes (distinct primes, so coprime): a product of about 600 words,
    // so the kernel's cofactor tree runs its scaled remainder tree near the root and the exact
    // descent below, at the level its costs choose (`trees::remainders`), with carried nodes at
    // odd levels.
    let ms: Vec<Int> = (3u64..)
        .step_by(2)
        .filter(|&p| zed_numtheory::is_prime(p))
        .take(3001)
        .map(|p| Int::from(i128::from(p)))
        .collect();
    let pairs: Vec<(Int, Int)> = (ms.iter().enumerate())
        .map(|(i, m)| (Int::from(i as i64 * 7 + 1).mod_floor(m), m.clone()))
        .collect();
    let (x, m) = Int::crt(pairs.clone()).expect("distinct primes");
    assert_eq!(m, ms.iter().fold(Int::ONE, |a, v| &a * v), "3,001 primes");
    assert!(!x.is_negative() && x < m, "3,001 primes");
    for (r, mi) in &pairs {
        assert_eq!(x.mod_floor(mi), *r, "3,001 primes, modulus {mi}");
    }
    let shared = vec![(Int::from(1), Int::from(6)), (Int::from(3), Int::from(10))];
    assert_eq!(Int::crt(shared), Some((Int::from(13), Int::from(30))));
    let conflict = vec![(Int::from(1), Int::from(6)), (Int::from(2), Int::from(10))];
    assert_eq!(Int::crt(conflict), None);
}

/// The kernel's trees as this file uses them, on wide values (40 words each): remainders of
/// `x` and `-x` against `mod_floor`, `x` a multiple of one value so a remainder 0 occurs on
/// the negative side. (Its other half, shared factors of wide values against the pairwise
/// answer, is zed-kernel's `the_shared_factors_of_wide_values_are_the_pairwise_ones` since
/// DRY-coprime-bases-one.)
#[test]
fn the_kernel_trees_agree_on_wide_values() {
    // xorshift64 (zed-hash's, where its source is).
    let mut rng = zed_hash::Xorshift64::new(0x9e37_79b9_7f4a_7c15);
    let mut next = move || rng.next_u64();
    let word = Int::from(i128::from(u64::MAX) + 1);
    let mut wide = || {
        let mut v = Int::from(i128::from(next() >> 20) | 1);
        for _ in 0..40 {
            v = &(&v * &word) + &Int::from(i128::from(next()));
        }
        v
    };
    for k in [1usize, 2, 3, 16, 17] {
        let vals: Vec<Int> = (0..k).map(|_| wide()).collect();
        let x = &vals.iter().fold(Int::ONE, |a, v| &(&a * v) + &Int::from(3)) * &vals[0];
        for point in [x.clone(), -&x, Int::ZERO] {
            let want: Vec<_> = vals.iter().map(|m| point.mod_floor(m)).collect();
            assert_eq!(batch_remainders(&point, &vals), want, "k {k}");
        }
    }
}

#[test]
fn private_quotients_agree_with_enumeration_and_skip_shared_variables() {
    let x = Lin::atom(Atom::Sym("x".into()));
    let row = |q: u32, m: i64, r: i64| {
        Con::eq(
            &x.minus(&Lin::atom(Atom::Aux(q)).times(m)),
            &Lin::constant(r),
        )
    };
    for (m, n) in [(4, 8), (8, 4), (12, 18), (9, 10), (4, 4)] {
        for a in -2..m {
            for b in -2..n {
                let left = row(0, m, a);
                let right = row(1, -n, b);
                let expected = (0..m * n).any(|x| (x - a) % m == 0 && (x - b) % n == 0);
                assert_eq!(
                    private_quotient_consistency(&[&left, &right]),
                    Some(expected)
                );
                let f = Formula::and(vec![Formula::Con(left), Formula::Con(right)]);
                assert_eq!(
                    solve_modular(&f, false).map(|m| m.is_some()),
                    Some(expected)
                );
            }
        }
    }
    let left = row(0, 2, 0);
    let right = row(0, 6, 2);
    assert_eq!(private_quotient_consistency(&[&left, &right]), None);
    let bounded = Con::ge(&Lin::constant(1), &x);
    assert_eq!(private_quotient_consistency(&[&left, &bounded]), None);
    let fixed = Con::eq(&Lin::constant(1), &x);
    let input = Formula::and(vec![Formula::Con(left), Formula::Con(fixed)]);
    assert_eq!(
        solve_modular(&input, false).map(|m| m.is_some()),
        Some(false)
    );
}

#[test]
fn private_quotients_match_concrete_models_on_small_systems() {
    let x = Lin::atom(Atom::Sym("x".into()));
    let row = |q, m, r| {
        Con::eq(
            &x.minus(&Lin::atom(Atom::Aux(q)).times(m)),
            &Lin::constant(r),
        )
    };
    let check = |rows: Vec<Con>, expected: bool| {
        let f = Formula::and(rows.into_iter().map(Formula::Con).collect());
        let decided = solve_modular(&f, false)
            .map(|m| m.is_some())
            .unwrap_or_else(|| crate::presburger::decide(&f).unwrap());
        let found =
            solve_modular(&f, true).unwrap_or_else(|| crate::presburger::satisfiable(&f).unwrap());
        assert_eq!(decided, expected, "{f}");
        assert_eq!(found.is_some(), expected, "{f}");
        if let Some(model) = found {
            assert!(f.holds(&model), "{f}");
        }
    };
    let options: Vec<_> = (1..=12i64)
        .flat_map(|m| (0..m).map(move |r| (m, r)))
        .collect();
    let mut count = 1;
    check(vec![], true);
    for (i, &(a, r)) in options.iter().enumerate() {
        check(vec![row(0, a, r)], true);
        count += 1;
        for (j, &(b, s)) in options.iter().enumerate().skip(i) {
            let agrees = |x| (x - r) % a == 0 && (x - s) % b == 0;
            check(vec![row(0, a, r), row(1, -b, s)], (0..a * b).any(agrees));
            count += 1;
            for &(c, t) in &options[j..] {
                // Generalized CRT says that all pairwise gcd conditions suffice. Compute each
                // condition independently by enumerating a period of the two relevant rows.
                let expected = (0..a * b).any(agrees)
                    && (0..a * c).any(|x| (x - r) % a == 0 && (x - t) % c == 0)
                    && (0..b * c).any(|x| (x - s) % b == 0 && (x - t) % c == 0);
                check(vec![row(0, a, r), row(1, -b, s), row(2, c, t)], expected);
                count += 1;
            }
        }
    }
    assert_eq!(count, 85_320);
    check(vec![row(0, 4, 2), Con::ge(&x, &Lin::constant(0))], true);
    check(vec![row(0, 4, 2), Con::ge(&Lin::constant(1), &x)], true);
    check(
        vec![
            row(0, 4, 2),
            Con::ge(&x, &Lin::constant(0)),
            Con::ge(&Lin::constant(1), &x),
        ],
        false,
    );
    check(vec![row(0, 2, 0), row(0, 6, 2)], false);
    check(vec![row(0, 2, 0), row(0, 6, 4)], true);
}

/// The verdict-only path of `solve_modular` agrees with its model path, and both with the truth,
/// on every system of two congruences `x = m q + r` with `1 <= m1 <= m2 <= 12`, of three with
/// `2 <= m1 <= m2 <= m3 <= 6`, and on three triples whose moduli share factors, at every residue;
/// the two-row systems also with the alias `y = 7 - x`. The truth is enumeration of `x` over one
/// period, the product of the moduli. A mode that declines (`None`) falls back to the general
/// solver, as the callers do. Then the edge forms: empty, modulus 1, one-sided and two-sided
/// bounds with and without an alias, homogeneous rows, a quotient shared by two rows, a
/// disjunction and a negated point. Taken from the R2 Gemini seat of XR-negated-chain-crt-tree
/// (2026-11-21, `unit_witness_matches_full_crt_exhaustively`), with the fallback, the enumerated
/// truth, the two-sided verdicts and the exact count added by num1.
#[test]
fn verdict_and_model_paths_agree_exhaustively_and_on_edge_forms() {
    let x = Lin::atom(Atom::Sym("x".into()));
    let y = Lin::atom(Atom::Sym("y".into()));
    let mk_eq = |qi: u32, m: i64, r: i64| -> Formula {
        let q = Lin::atom(Atom::Aux(qi));
        Formula::Con(Con::eq(&x.minus(&q.times(m)), &Lin::constant(r)))
    };
    let verdict = |f: &Formula, tag: &str| -> bool {
        let decided = solve_modular(f, false)
            .map(|m| m.is_some())
            .unwrap_or_else(|| crate::presburger::decide(f).unwrap());
        let found =
            solve_modular(f, true).unwrap_or_else(|| crate::presburger::satisfiable(f).unwrap());
        assert_eq!(
            decided,
            found.is_some(),
            "verdict and model disagree on {tag}: {f}"
        );
        if let Some(model) = found {
            assert!(f.holds(&model), "model fails {tag}: {f}");
        }
        decided
    };
    let truth = |rows: &[(i64, i64)]| {
        let period: i64 = rows.iter().map(|&(m, _)| m).product();
        (0..period).any(|v| rows.iter().all(|&(m, r)| (v - r).rem_euclid(m) == 0))
    };
    let system = |rows: &[(i64, i64)]| {
        Formula::and(
            rows.iter()
                .enumerate()
                .map(|(i, &(m, r))| mk_eq(i as u32, m, r))
                .collect(),
        )
    };

    let mut checked = 0usize;
    for m1 in 1..=12i64 {
        for m2 in m1..=12i64 {
            for r1 in 0..m1 {
                for r2 in 0..m2 {
                    let rows = [(m1, r1), (m2, r2)];
                    let want = truth(&rows);
                    let tag = format!("({r1}%{m1}, {r2}%{m2})");
                    assert_eq!(verdict(&system(&rows), &tag), want, "flat {tag}");
                    let alias = Formula::and(vec![
                        Formula::Con(Con::eq(&y, &Lin::constant(7).minus(&x))),
                        mk_eq(0, m1, r1),
                        mk_eq(1, m2, r2),
                    ]);
                    assert_eq!(verdict(&alias, &tag), want, "alias {tag}");
                    checked += 2;
                }
            }
        }
    }
    let mut triples = Vec::new();
    for m1 in 2..=6i64 {
        for m2 in m1..=6i64 {
            for m3 in m2..=6i64 {
                triples.push((m1, m2, m3));
            }
        }
    }
    triples.extend([(4, 6, 10), (6, 9, 12), (4, 8, 12)]);
    for (m1, m2, m3) in triples {
        for r1 in 0..m1 {
            for r2 in 0..m2 {
                for r3 in 0..m3 {
                    let rows = [(m1, r1), (m2, r2), (m3, r3)];
                    let tag = format!("({r1}%{m1}, {r2}%{m2}, {r3}%{m3})");
                    assert_eq!(verdict(&system(&rows), &tag), truth(&rows), "{tag}");
                    checked += 1;
                }
            }
        }
    }
    // 2 * 3,367 two-row systems (the sum of m1 m2 over 1 <= m1 <= m2 <= 12 is (78^2 + 650) / 2),
    // 2,380 three-row systems on 2..6 and 240 + 648 + 384 on the three shared-factor triples.
    assert_eq!(checked, 10_386);

    assert!(verdict(&Formula::and(vec![]), "empty"));
    assert!(verdict(&mk_eq(0, 1, 3), "modulus 1 alone"));
    assert!(verdict(
        &Formula::and(vec![mk_eq(0, 1, 3), mk_eq(1, 6, 5)]),
        "modulus 1 paired"
    ));
    // x = 4 (6) and x = 2 (10) meet at x = 22 (30); x = 0 (6) and x = 1 (10) never meet. A
    // one-sided bound leaves the verdict of the congruences alone.
    for (r1, r2, want) in [(4, 2, true), (0, 1, false)] {
        for bound in [
            Formula::Con(Con::ge(&x, &Lin::constant(100))),
            Formula::Con(Con::ge(&Lin::constant(-100), &x)),
            Formula::Con(Con::ge(&x.times(2), &Lin::constant(11))),
        ] {
            let flat = Formula::and(vec![mk_eq(0, 6, r1), mk_eq(1, 10, r2), bound.clone()]);
            assert_eq!(verdict(&flat, "one-sided"), want);
            let alias = Formula::and(vec![
                Formula::Con(Con::eq(&y, &x.plus(&Lin::constant(3)))),
                mk_eq(0, 6, r1),
                mk_eq(1, 10, r2),
                bound,
            ]);
            assert_eq!(verdict(&alias, "one-sided alias"), want);
        }
    }
    // On 0 <= x <= hi the class 22 (30) has a point exactly when hi >= 22.
    for hi in [10i64, 21, 22, 25] {
        let bounds = || {
            vec![
                Formula::Con(Con::ge(&x, &Lin::constant(0))),
                Formula::Con(Con::ge(&Lin::constant(hi), &x)),
            ]
        };
        let mut flat = vec![mk_eq(0, 6, 4), mk_eq(1, 10, 2)];
        flat.extend(bounds());
        assert_eq!(
            verdict(&Formula::and(flat), "two-sided"),
            hi >= 22,
            "hi {hi}"
        );
        let mut alias = vec![
            Formula::Con(Con::eq(&y, &x.plus(&Lin::constant(1)))),
            mk_eq(0, 6, 4),
            mk_eq(1, 10, 2),
        ];
        alias.extend(bounds());
        assert_eq!(
            verdict(&Formula::and(alias), "two-sided alias"),
            hi >= 22,
            "hi {hi}"
        );
    }
    assert!(verdict(
        &Formula::and(vec![mk_eq(0, 6, 0), mk_eq(1, 10, 0)]),
        "homogeneous"
    ));
    assert!(verdict(
        &Formula::and(vec![
            mk_eq(0, 6, 0),
            mk_eq(1, 10, 0),
            Formula::Con(Con::ge(&x, &Lin::constant(1))),
        ]),
        "homogeneous, x >= 1"
    ));
    // One quotient q in two rows: x = 2q and x = 3q + 1 at q = -1, x = -2; x = 2q and
    // x = 2q + 1 never; x = 2q + 1 and x = 6q + 2 force 4q = -1.
    let q = Lin::atom(Atom::Aux(0));
    let shared = |m1: i64, c1: i64, m2: i64, c2: i64| {
        Formula::and(vec![
            Formula::Con(Con::eq(&x.minus(&q.times(m1)), &Lin::constant(c1))),
            Formula::Con(Con::eq(&x.minus(&q.times(m2)), &Lin::constant(c2))),
        ])
    };
    assert!(verdict(&shared(2, 0, 3, 1), "shared quotient"));
    assert!(!verdict(
        &shared(2, 0, 2, 1),
        "shared quotient, same modulus"
    ));
    assert!(!verdict(&shared(2, 1, 6, 2), "shared quotient, parity"));
    // x = 1 (4) meets x = 3 (6) at x = 9; x = 4 (6) with x != 4 holds at x = 10.
    assert!(verdict(
        &Formula::and(vec![
            mk_eq(0, 4, 1),
            Formula::or(vec![mk_eq(1, 6, 3), mk_eq(2, 6, 5)]),
        ]),
        "disjunction"
    ));
    assert!(verdict(
        &Formula::and(vec![
            mk_eq(0, 6, 4),
            Formula::negate(Formula::Con(Con::eq(&x, &Lin::constant(4)))),
        ]),
        "negated point"
    ));
}

/// `Int::crt` agrees with a left fold of `Int::crt_pair` on moduli that are not
/// pairwise coprime: equal moduli, powers of 2 and of 3 out of order, a divisibility chain with
/// duplicates, repeated coprime moduli and moduli sharing factors without a chain, each also
/// with a conflict. Taken unchanged from the R2 Gemini seat of XR-negated-chain-crt-tree
/// (2026-11-21), where it tested that seat's chain and repeated-moduli fast paths; on main it
/// tests the general tree on the same inputs.
#[test]
fn crt_tree_chain_and_repeated_moduli_match_pairwise() {
    let ref_crt = |pairs: &[(Int, Int)]| -> Option<(Int, Int)> {
        let mut cur = (Int::ZERO, Int::ONE);
        for (r, m) in pairs {
            cur = Int::crt_pair(&cur.0, &cur.1, r, m)?;
        }
        Some(cur)
    };
    let cases: Vec<Vec<(i64, i64)>> = vec![
        // Equal moduli (consistent and conflicting)
        vec![(3, 12), (15, 12), (-9, 12)],
        vec![(3, 12), (4, 12)],
        // Powers of 2 (consistent, unsorted, and conflicting)
        vec![(13, 16), (1, 2), (5, 8), (1, 4), (29, 32)],
        vec![(1, 2), (2, 4), (5, 8)],
        // Powers of 3 (consistent and conflicting)
        vec![(14, 27), (2, 3), (5, 9), (41, 81)],
        vec![(2, 3), (4, 9), (14, 27)],
        // General divisibility chain with duplicates
        vec![(5, 6), (11, 12), (11, 36), (11, 36), (1, 2), (47, 72)],
        vec![(5, 6), (11, 12), (23, 36)],
        // Repeated coprime moduli (consistent and conflicting)
        vec![(1, 3), (2, 5), (4, 7), (7, 3), (12, 5), (4, 7)],
        vec![(1, 3), (2, 5), (2, 3)],
        // Non-chain sharing factors (min divides max, middle doesn't: `{2, 4, 6, 12}`)
        vec![(1, 2), (1, 4), (5, 6), (5, 12)],
        vec![(1, 2), (3, 4), (5, 6), (5, 12)],
    ];
    for raw in cases {
        let pairs: Vec<(Int, Int)> = raw
            .iter()
            .map(|&(r, m)| (Int::from(r), Int::from(m)))
            .collect();
        assert_eq!(Int::crt(pairs.clone()), ref_crt(&pairs), "raw={raw:?}");
    }
}

/// One row `x = r (mod m)` with its own quotient `q`: `x - m q = r`, or `m q - x = -r` when
/// `flip`, so both signs of `x` are covered.
fn congruence_row(q: u32, m: i64, r: i64, flip: bool) -> Con {
    let x = Lin::atom(Atom::Sym("x".into()));
    let mq = Lin::atom(Atom::Aux(q)).times(m);
    if flip {
        Con::eq(&mq.minus(&x), &Lin::constant(-r))
    } else {
        Con::eq(&x.minus(&mq), &Lin::constant(r))
    }
}

/// Whether some `x` in `lo..=hi` meets every `x = r (mod m)`, by enumeration.
fn some_x_meets(rows: &[(i64, i64)], lo: i64, hi: i64) -> bool {
    (lo..=hi).any(|x| rows.iter().all(|&(m, r)| (x - r).rem_euclid(m) == 0))
}

/// `private_quotient_consistency` with step 4 of its proof broken: the requirement of the first
/// power of each base is kept, not that of the larger one. The negative control below shows
/// the enumeration catches it.
fn broken_private_quotient_consistency(cons: &[&Con]) -> Option<bool> {
    let x = Atom::Sym("x".into());
    let mut rows = Vec::new();
    let mut moduli = BTreeSet::new();
    for c in cons {
        let s = c.lin.terms.get(&x)?;
        let (_, k) = c.lin.terms.iter().find(|(a, _)| **a != x)?;
        let r = if s.is_negative() {
            c.lin.constant.clone()
        } else {
            -&c.lin.constant
        };
        moduli.insert(k.abs());
        rows.push((k.abs(), r));
    }
    let factors = coprime_factorization(&moduli);
    let mut first: HashMap<Int, (Int, Int)> = HashMap::new();
    for (m, r) in rows {
        for (base, power) in &factors[&m] {
            let residue = r.mod_floor(power);
            let (p0, r0) = first
                .entry(base.clone())
                .or_insert((power.clone(), residue.clone()));
            let small = if *power < *p0 { power } else { &*p0 };
            if r0.mod_floor(small) != residue.mod_floor(small) {
                return Some(false);
            }
        }
    }
    Some(true)
}

/// Every system of 1 to 3 rows `x = r_i (mod m_i)` with `2 <= m_1 <= m_2 <= m_3 <= 12` and every
/// residue `0 <= r_i < m_i` (103,103 systems of 3 rows), each with its own quotient. Calls
/// `check` with the rows, the formula, and the answer by enumeration over one period.
fn for_each_small_system(mut check: impl FnMut(&[(i64, i64)], &[Con], bool)) {
    let mut systems: Vec<Vec<i64>> = Vec::new();
    for a in 2..=12i64 {
        systems.push(vec![a]);
        for b in a..=12 {
            systems.push(vec![a, b]);
            for c in b..=12 {
                systems.push(vec![a, b, c]);
            }
        }
    }
    for ms in systems {
        let period: i64 = ms.iter().product();
        let count: i64 = period;
        for code in 0..count {
            let mut rest = code;
            let rows: Vec<(i64, i64)> = (ms.iter())
                .map(|&m| {
                    let r = rest % m;
                    rest /= m;
                    (m, r)
                })
                .collect();
            let cons: Vec<Con> = (rows.iter().enumerate())
                .map(|(i, &(m, r))| congruence_row(i as u32, m, r, (code + i as i64) % 2 == 1))
                .collect();
            check(&rows, &cons, some_x_meets(&rows, 0, period - 1));
        }
    }
}

/// `private_quotient_consistency` and the whole `solve_modular(f, false)` agree with
/// enumeration on every small system, and so does `solve_modular(f, true)`, whose model `f`
/// holds; the broken variant disagrees at least once (negative control). Then the edges of the
/// proof: modulus 1, a bound added (`x >= 0`, `x <= c`), a quotient shared by two rows, and the
/// empty conjunction. Taken unchanged from the R2 Opus seat of XR-negated-chain-crt-tree
/// (2026-11-21); beside `private_quotients_match_concrete_models_on_small_systems` it adds rows
/// with `x` of coefficient -1, the routine called directly, a negative control kept in the test
/// and a quotient shared by rows of any two moduli.
#[test]
fn private_quotients_match_enumeration_and_the_model_path() {
    let mut systems = 0usize;
    let mut broken_wrong = 0usize;
    for_each_small_system(|rows, cons, expected| {
        systems += 1;
        let refs: Vec<&Con> = cons.iter().collect();
        assert_eq!(
            private_quotient_consistency(&refs),
            Some(expected),
            "{rows:?}"
        );
        if broken_private_quotient_consistency(&refs) != Some(expected) {
            broken_wrong += 1;
        }
        let f = Formula::and(cons.iter().cloned().map(Formula::Con).collect());
        assert_eq!(
            solve_modular(&f, false).map(|m| m.is_some()),
            Some(expected),
            "{rows:?}"
        );
        match solve_modular(&f, true) {
            Some(Some(model)) => assert!(expected && f.holds(&model), "{rows:?}"),
            Some(None) => assert!(!expected, "{rows:?}"),
            None => panic!("no verdict from the model path at {rows:?}"),
        }
    });
    assert_eq!(systems, 77 + 3289 + 103_103);
    assert!(broken_wrong > 0, "the negative control was not caught");

    let x = Lin::atom(Atom::Sym("x".into()));
    // Both paths give the same verdict, or both none; a verdict matches `want`; a model holds.
    // Counts the formulas with no verdict, for each edge.
    let mut silent = [0usize; 3];
    let mut check = |f: &Formula, want: bool, edge: usize| {
        let d = solve_modular(f, false).map(|m| m.is_some());
        let w = solve_modular(f, true);
        if let Some(Some(model)) = &w {
            assert!(f.holds(model));
        }
        let w = w.map(|m| m.is_some());
        assert_eq!(d, w);
        match d {
            Some(v) => assert_eq!(v, want),
            None => silent[edge] += 1,
        }
    };
    for m in 2..=12i64 {
        for r in 0..m {
            // Modulus 1: `x - q = 0` holds for every `x`; the routine gives no verdict.
            let unit = congruence_row(1, 1, 0, false);
            let row = congruence_row(0, m, r, false);
            assert_eq!(private_quotient_consistency(&[&row, &unit]), None);
            let f = Formula::and(vec![Formula::Con(row.clone()), Formula::Con(unit)]);
            check(&f, true, 0);
            // A bound added later: the routine gives no verdict; both paths agree with
            // enumeration over the bounded range.
            for c in 0..12i64 {
                let lo = Con::ge(&x, &Lin::constant(0));
                let hi = Con::ge(&Lin::constant(c), &x);
                assert_eq!(private_quotient_consistency(&[&row, &hi]), None);
                let f = Formula::and(vec![
                    Formula::Con(row.clone()),
                    Formula::Con(lo),
                    Formula::Con(hi),
                ]);
                let want = some_x_meets(&[(m, r)], 0, c);
                check(&f, want, 1);
            }
            // One quotient in two rows: `m q + r = n q + s` needs `(m - n) q = s - r`.
            for n in 2..=12i64 {
                for s in 0..n {
                    let shared = Con::eq(
                        &x.minus(&Lin::atom(Atom::Aux(0)).times(n)),
                        &Lin::constant(s),
                    );
                    assert_eq!(private_quotient_consistency(&[&row, &shared]), None);
                    let want = if m == n {
                        r == s
                    } else {
                        (s - r) % (m - n) == 0
                    };
                    let f = Formula::and(vec![Formula::Con(row.clone()), Formula::Con(shared)]);
                    check(&f, want, 2);
                }
            }
        }
    }
    assert_eq!(private_quotient_consistency(&[]), None);
    eprintln!("no verdict (modulus 1, bounds, shared quotient): {silent:?}");
}
