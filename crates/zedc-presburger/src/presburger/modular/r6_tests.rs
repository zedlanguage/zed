use super::*;
use crate::scaling;
use num_bigint::BigInt;
mod bench;

#[test]
fn pncx_fast_bezout_matches_euclid() {
    let mut pairs = Vec::new();
    for n in [0, 1, 2, 3, 63, 127, 128, 129, 255, 512, 1024, 2048] {
        let x: BigInt = (BigInt::from(1) << n) + 3;
        let y: BigInt = (BigInt::from(1) << (n / 2)) + 5;
        for a in [&x, &-&x] {
            for b in [&y, &-&y] {
                pairs.push((Int::from(a.clone()), Int::from(b.clone())));
            }
        }
        pairs.push((Int::from(x), Int::ZERO));
        pairs.push((Int::ZERO, Int::from(y)));
    }
    let (mut a, mut b) = (Int::ONE, Int::ONE);
    // Fibonacci pairs, the longest run of Euclid's steps for their width, to 2780 bits: below
    // the lift width of the half gcd (`LIFT_BITS`, 29376 bits as built), as the 8300 bits of
    // 12000 steps were, at an eighth of the reference's quadratic work.
    for i in 0..4000 {
        (a, b) = (b.clone(), &a + &b);
        if i % 61 == 0 {
            pairs.push((a.clone(), b.clone()));
            pairs.push((&a * &Int::from(12), &b * &Int::from(12)));
        }
    }
    for (a, b) in pairs {
        let (g, s, t) = a.extended_gcd(&b).expect("arithmetic check");
        assert_eq!(&(&s * &a) + &(&t * &b), g);
        let expected = a.abs().euclid_bezout(&b).0;
        assert_eq!(g, expected);
    }
}

#[test]
fn pncx_wide_floor_division_matches_integer_division() {
    for n in [129, 256, 1024, 4096, 16_384] {
        let a: BigInt = (BigInt::from(1) << n) + 17;
        for m in [3, 127, n / 2, n - 1] {
            let b: BigInt = (BigInt::from(1) << m) + 3;
            for a in [&a, &-&a] {
                for b in [&b, &-&b] {
                    let mut q = a / b;
                    let mut r = a % b;
                    if r != BigInt::from(0) && a.sign() != b.sign() {
                        q -= 1;
                        r += b;
                    }
                    let (ia, ib) = (Int::from(a.clone()), Int::from(b.clone()));
                    assert_eq!(ia.div_floor(&ib), Int::from(q));
                    assert_eq!(ia.mod_floor(&ib), Int::from(r));
                }
            }
        }
    }
}

fn bipartite_core(
    n: usize,
) -> (
    Vec<BaseInfo>,
    Vec<ResidueSet>,
    Vec<BTreeMap<usize, ResidueSet>>,
) {
    let mut info = Vec::new();
    let mut p = 5i64;
    while info.len() < n + 3 {
        if (2..).take_while(|d| d * d <= p).all(|d| p % d != 0) {
            let modulus = Int::from(p);
            info.push(BaseInfo {
                max_q: modulus.clone(),
                u: Int::ZERO,
                stride: Int::ONE,
                z_max_q: modulus,
            });
        }
        p += 1;
    }
    let allowed = vec![vec![(Int::ZERO, Int::from(2))]; info.len()];
    let mut clauses = Vec::new();
    for a in 0..3 {
        for b in 3..n + 3 {
            for color in 0..3 {
                let c = Int::from(color);
                clauses.push(BTreeMap::from([
                    (
                        a,
                        res_diff(&allowed[a], &[(c.clone(), c.clone())], &info[a].max_q),
                    ),
                    (b, res_diff(&allowed[b], &[(c.clone(), c)], &info[b].max_q)),
                ]));
            }
        }
    }
    (info, allowed, clauses)
}

#[test]
fn pncx_bipartite_core() {
    for n in 3..16 {
        let (info, allowed, clauses) = bipartite_core(n);
        let point = graph_coloring_witness(&info, &allowed, &clauses).expect("bipartite core");
        assert!(holds_coprime_point(&point, &info, &allowed, &clauses));
    }
}

#[test]
fn pncx_coprime_base_exhaustive_small_inputs() {
    for a in 2..24 {
        for b in a..32 {
            for c in b..40 {
                let inputs = BTreeSet::from([Int::from(a), Int::from(b), Int::from(c)]);
                let fs = coprime_factorization(&inputs);
                let bases: BTreeSet<_> = fs.values().flatten().map(|(b, _)| b).collect();
                for &a in &bases {
                    for &b in &bases {
                        if b < a {
                            assert_eq!(a.gcd(b), Int::ONE);
                        }
                    }
                }
                for m in &inputs {
                    assert_eq!(
                        prod_slice(&fs[m].iter().map(|(_, q)| q.clone()).collect::<Vec<_>>()),
                        *m
                    );
                }
            }
        }
    }
}

#[test]
fn pncx_bound_matching_is_order_independent() {
    let vertices: Vec<_> = (0..3).map(Int::from).collect();
    for mask in 0..512usize {
        let mut pairs = Vec::new();
        for a in 0..3 {
            for b in 0..3 {
                if mask & (1 << (3 * a + b)) != 0 {
                    pairs.push((&vertices[a], &vertices[b]));
                }
            }
        }
        let brute = [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ]
        .iter()
        .any(|p| (0..3).all(|a| mask & (1 << (3 * a + p[a])) != 0));
        assert_eq!(three_disjoint_pairs(&pairs), brute, "mask={mask}");
        pairs.reverse();
        assert_eq!(three_disjoint_pairs(&pairs), brute, "reversed mask={mask}");
    }
    let make = |a, b| FlatClause {
        bounds: Domain::ge(Int::from(100)),
        mods: BTreeMap::from([
            (Int::from(5), vec![(Int::from(a), Int::from(a))]),
            (Int::from(7), vec![(Int::from(b), Int::from(b))]),
        ]),
    };
    let mut clauses: Vec<_> = [(0, 0), (0, 1), (1, 0), (2, 2)]
        .into_iter()
        .map(|(a, b)| make(a, b))
        .collect();
    assert_eq!(forced_pair_bounds(&clauses), Domain::ge(Int::from(100)));
    clauses.reverse();
    assert_eq!(forced_pair_bounds(&clauses), Domain::ge(Int::from(100)));
}

fn power_inputs(bits: usize) -> (BTreeMap<Int, ResidueSet>, Int) {
    let mut k = 0usize;
    while (k + 1) * (k + 1) <= bits {
        k += 1;
    }
    let mut q = Int::ONE;
    let mut sets = BTreeMap::new();
    for _ in 0..k {
        q = &q * &Int::from(2);
        let r = &q - &Int::ONE;
        sets.insert(q.clone(), vec![(r.clone(), r)]);
    }
    (sets, q)
}

#[test]
fn pncx_power_propagation_oracle() {
    for seed in 0..512u64 {
        let mut rng = crate::seed::Rng::new(seed);
        let mut sets = BTreeMap::new();
        let mut q = 1i64;
        for i in 0..6 {
            q *= 2;
            let a = rng.int(0, q - 1);
            let b = if i == 4 { a } else { (a + 1).min(q - 1) };
            sets.insert(Int::from(q), vec![(Int::from(a), Int::from(b))]);
        }
        let points: Vec<_> = (0..q)
            .filter(|&x| {
                sets.iter()
                    .all(|(m, s)| res_contains(s, &Int::from(x).mod_floor(m)))
            })
            .collect();
        match consolidate_prime_powers(&sets, &Int::from(q)) {
            ConsolidateOut::Empty => assert!(points.is_empty(), "seed={seed}"),
            ConsolidateOut::Ok(info, allowed) => {
                let found: Vec<_> = (0..q)
                    .filter(|&x| {
                        info.z_from_x(&Int::from(x))
                            .is_some_and(|z| res_contains(&allowed, &z))
                    })
                    .collect();
                assert_eq!(found, points, "seed={seed}");
            }
            ConsolidateOut::Undecided => {}
        }
    }
}

fn boolean_info(n: usize) -> Vec<BaseInfo> {
    let mut out = Vec::new();
    let mut p = 3i64;
    while out.len() < n {
        if (2..).take_while(|d| d * d <= p).all(|d| p % d != 0) {
            let m = Int::from(p);
            out.push(BaseInfo {
                max_q: m.clone(),
                u: Int::ZERO,
                stride: Int::ONE,
                z_max_q: m,
            });
        }
        p += 1;
    }
    out
}

#[test]
fn pncx_score_witness_oracle() {
    let info = boolean_info(3);
    let allowed = vec![vec![(Int::ZERO, Int::ONE)]; 3];
    let mut gained = 0;
    for mask in 0..256usize {
        let clauses: Vec<BTreeMap<usize, ResidueSet>> = (0..8)
            .filter(|cl| mask & (1 << cl) != 0)
            .map(|cl| {
                (0..3)
                    .map(|i| {
                        let v = Int::from((cl >> i) & 1);
                        (i, vec![(v.clone(), v)])
                    })
                    .collect()
            })
            .collect();
        let truth = (0..8).any(|a| {
            clauses.iter().all(|cl| {
                cl.iter()
                    .any(|(&i, s)| res_contains(s, &Int::from((a >> i) & 1)))
            })
        });
        let found = score_witness(&info, &allowed, &clauses);
        if let Some(x) = &found {
            gained += 1;
            assert!(truth);
            assert!(holds_coprime_point(x, &info, &allowed, &clauses));
        }
        for flips in 0..8 {
            let transformed: Vec<BTreeMap<usize, ResidueSet>> = clauses
                .iter()
                .map(|cl| {
                    cl.iter()
                        .map(|(&i, s)| {
                            let v = if flips & (1 << i) != 0 {
                                &Int::ONE - &s[0].0
                            } else {
                                s[0].0.clone()
                            };
                            (i, vec![(v.clone(), v)])
                        })
                        .collect()
                })
                .collect();
            let got = score_witness(&info, &allowed, &transformed);
            assert_eq!(got.is_some(), found.is_some(), "mask={mask} flips={flips}");
            if let Some(x) = got {
                assert!(holds_coprime_point(&x, &info, &allowed, &transformed));
            }
        }
    }
    println!("score oracle: {gained} satisfiable systems recognized of 256");
    assert!(gained > 0);
}

#[test]
fn pncx_wide_arithmetic_random_oracle() {
    use num_bigint::Sign;
    // A new seed each run, printed. Every fifth case of 1200: as 5 is prime to 2, 3, 71 and
    // 91, the signs and shifts still take every value they took, and the lengths, 17 to 516
    // bytes, every fifth.
    let (mut rng, _) = crate::seed::Rng::fresh("pncx_wide_arithmetic_random_oracle");
    for i in (0..1200usize).step_by(5) {
        let mut make = |n: usize| {
            let bytes: Vec<u8> = (0..n).map(|_| rng.next_u64() as u8).collect();
            BigInt::from_bytes_le(Sign::Plus, &bytes)
        };
        let a: BigInt = make(17 + i % 500) << (i % 91);
        let b: BigInt = (make(17 + (i * 37) % 500) + 1) << ((i * 11) % 71);
        let a = if i % 2 == 0 { a } else { -a };
        let b = if i % 3 == 0 { b } else { -b };
        let (ia, ib) = (Int::from(a.clone()), Int::from(b.clone()));
        let (g, s, t) = ia.extended_gcd(&ib).expect("nonzero pair");
        assert_eq!(&(&s * &ia) + &(&t * &ib), g, "case={i}");
        assert_eq!(g, ia.abs().euclid_bezout(&ib).0, "case={i}");
        assert_eq!(ia.gcd(&ib), g, "case={i}");
        assert_eq!(ia.gcd(&ib), g, "case={i}");
        let mut q = &a / &b;
        let mut r = &a % &b;
        if r != BigInt::from(0) && a.sign() != b.sign() {
            q -= 1;
            r += &b;
        }
        assert_eq!(ia.div_floor(&ib), Int::from(q), "case={i}");
        assert_eq!(ia.mod_floor(&ib), Int::from(r), "case={i}");
    }
}

#[test]
fn pncx_brooks_subcubic_oracle() {
    let mut checked = 0;
    for mask in 0..(1usize << 15) {
        let mut graph = vec![Vec::new(); 6];
        let mut bit = 0;
        for a in 0..6 {
            for b in a + 1..6 {
                if mask & (1 << bit) != 0 {
                    graph[a].push(b);
                    graph[b].push(a);
                }
                bit += 1;
            }
        }
        if graph.iter().any(|r| r.len() > 3) {
            continue;
        }
        let brute = (0..729usize).any(|mut code| {
            let mut c = [0; 6];
            for v in &mut c {
                *v = code % 3;
                code /= 3;
            }
            graph
                .iter()
                .enumerate()
                .all(|(a, row)| row.iter().all(|&b| c[a] != c[b]))
        });
        let found = brooks::color(&graph);
        assert_eq!(found.is_some(), brute, "mask={mask}");
        if let Some(c) = found {
            assert!(
                graph
                    .iter()
                    .enumerate()
                    .all(|(a, row)| row.iter().all(|&b| c[a] != c[b]))
            );
        }
        checked += 1;
    }
    println!("Brooks oracle: {checked} subcubic graphs on six vertices");
}

fn prism_core(
    n: usize,
) -> (
    Vec<BaseInfo>,
    Vec<ResidueSet>,
    Vec<BTreeMap<usize, ResidueSet>>,
) {
    let k = 2 * n + 1;
    let info = boolean_info(2 * k);
    let allowed = vec![vec![(Int::ZERO, Int::from(2))]; 2 * k];
    let mut edges = Vec::new();
    for i in 0..k {
        edges.push((i, (i + 1) % k));
        edges.push((k + i, k + (i + 1) % k));
        edges.push((i, k + i));
    }
    let mut clauses = Vec::new();
    for (a, b) in edges {
        for color in 0..3 {
            let c = Int::from(color);
            clauses.push(BTreeMap::from([
                (
                    a,
                    res_diff(&allowed[a], &[(c.clone(), c.clone())], &info[a].max_q),
                ),
                (b, res_diff(&allowed[b], &[(c.clone(), c)], &info[b].max_q)),
            ]));
        }
    }
    (info, allowed, clauses)
}

#[test]
fn pncx_prism_models() {
    for n in 1..40 {
        let (info, allowed, clauses) = prism_core(n);
        let x = graph_coloring_witness(&info, &allowed, &clauses).expect("prism");
        assert!(holds_coprime_point(&x, &info, &allowed, &clauses));
    }
}

/// [`prism_core`] as a formula: `x = q_i p_i + r_i`, `0 <= r_i <= 2`, and each residue clause
/// `r_i not in s` written as `r_i != c` for the one color `c` of `0..3` its set leaves out;
/// `decide` finds it satisfiable, and the point of `graph_coloring_witness` is a model of it
/// (from the probe `pncx_prism_formula_axis` of PERF-negated-chain-unsolved).
#[test]
fn pncx_prism_formulas_are_true() {
    for n in 1..=8 {
        let (info, allowed, clauses) = prism_core(n);
        let point = graph_coloring_witness(&info, &allowed, &clauses).expect("prism");
        let xa = Atom::Sym("x".into());
        let x = Lin::atom(xa.clone());
        let mut model = Model::from([(xa, point.clone())]);
        let (mut parts, mut rs) = (Vec::new(), Vec::new());
        for (i, base) in info.iter().enumerate() {
            let qa = Atom::Aux((2 * i) as u32);
            let ra = Atom::Aux((2 * i + 1) as u32);
            let q = Lin::atom(qa.clone());
            let r = Lin::atom(ra.clone());
            parts.push(Formula::Con(Con::eq(
                &x,
                &q.times(base.max_q.clone()).plus(&r),
            )));
            parts.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
            parts.push(Formula::Con(Con::ge(&Lin::constant(2), &r)));
            model.insert(qa, point.div_floor(&base.max_q));
            model.insert(ra, point.mod_floor(&base.max_q));
            rs.push(r);
        }
        for clause in clauses {
            let literals = (clause.into_iter())
                .map(|(i, s)| {
                    let c = (0..3).map(Int::from).find(|c| !res_contains(&s, c));
                    let c = c.expect("a clause's set leaves out a color");
                    Formula::negate(Formula::Con(Con::eq(&rs[i], &Lin::constant(c))))
                })
                .collect();
            parts.push(Formula::or(literals));
        }
        let f = Formula::and(parts);
        assert!(f.holds(&model), "{n}: the coloring's point");
        assert_eq!(crate::presburger::decide(&f), Ok(true), "{n}");
    }
}

fn wheel_core(
    n: usize,
) -> (
    Vec<BaseInfo>,
    Vec<ResidueSet>,
    Vec<BTreeMap<usize, ResidueSet>>,
) {
    let k = 2 * n;
    let info = boolean_info(k + 1);
    let allowed = vec![vec![(Int::ZERO, Int::from(2))]; k + 1];
    let mut clauses = Vec::new();
    for a in 0..k {
        for b in [(a + 1) % k, k] {
            for color in 0..3 {
                let c = Int::from(color);
                clauses.push(BTreeMap::from([
                    (
                        a,
                        res_diff(&allowed[a], &[(c.clone(), c.clone())], &info[a].max_q),
                    ),
                    (b, res_diff(&allowed[b], &[(c.clone(), c)], &info[b].max_q)),
                ]));
            }
        }
    }
    (info, allowed, clauses)
}

#[test]
fn pncx_wheel_models() {
    for n in 2..30 {
        let (info, allowed, clauses) = wheel_core(n);
        let point = graph_coloring_witness(&info, &allowed, &clauses).expect("even wheel");
        assert!(holds_coprime_point(&point, &info, &allowed, &clauses));
    }
}

#[test]
fn pncx_empty_pair_implication() {
    for mask in 0..512usize {
        let clauses: Vec<_> = (0..3)
            .flat_map(|a| (0..3).map(move |b| (a, b)))
            .filter(|(a, b)| mask & (1 << (3 * a + b)) != 0)
            .map(|(a, b)| FlatClause {
                bounds: Domain::empty(),
                mods: BTreeMap::from([
                    (Int::from(5), vec![(Int::from(a), Int::from(a))]),
                    (Int::from(7), vec![(Int::from(b), Int::from(b))]),
                ]),
            })
            .collect();
        if forced_pair_bounds(&clauses).is_empty() {
            assert!(
                !(0..35).any(|x| clauses.iter().all(|cl| cl.mods.iter().any(|(m, s)| {
                    let r = Int::from(x).mod_floor(m);
                    s.iter().any(|(a, b)| a <= &r && &r <= b)
                }))),
                "mask={mask}"
            );
        }
    }
    let clauses: Vec<_> = (0..3)
        .map(|a| FlatClause {
            bounds: Domain::empty(),
            mods: BTreeMap::from([
                (Int::from(5), vec![(Int::from(a), Int::from(a))]),
                (Int::from(7), vec![(Int::from(a), Int::from(a))]),
            ]),
        })
        .collect();
    assert!(forced_pair_bounds(&clauses).is_empty());
}

fn alias_chain(n: usize) -> (UnitUf, Vec<Atom>, Formula) {
    let atoms: Vec<_> = (0..=n)
        .map(|i| Atom::Sym(format!("n{:06}", n - i).into()))
        .collect();
    let mut uf = UnitUf::new();
    let mut parts = Vec::new();
    for pair in atoms.windows(2) {
        uf.union(&pair[0], &pair[1], 1, &Int::ONE)
            .expect("consistent chain");
        parts.push(Formula::Con(Con::eq(
            &Lin::atom(pair[0].clone()),
            &Lin::atom(pair[1].clone()).plus(&Lin::constant(1)),
        )));
    }
    let x = Lin::atom(atoms[0].clone());
    let q = Lin::atom(Atom::Aux(0));
    let r = Lin::atom(Atom::Aux(1));
    parts.extend([
        Formula::Con(Con::eq(&x, &q.times(3).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(2), &r)),
        Formula::Con(Con::eq(&r, &Lin::constant(2))),
        Formula::Con(Con::ge(&x, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(10000), &x)),
    ]);
    let f = Formula::And(crate::presburger::Shared::new(parts));
    (uf, atoms, f)
}

/// The small instances of the benchmarks in `bench.rs` that no test above holds, with the answers
/// they assert: the matched pair clauses force no bound, with the shared bounds `x >= 100` or
/// empty; the highest fixed residue reaches every lower power; and the alias chain has its
/// unit-union-find answer, a witness, and a point found by both solvers. The graph cores are
/// held by `pncx_bipartite_core`, `pncx_prism_models` and `pncx_wheel_models`.
#[test]
fn the_benchmark_inputs_have_their_answers_at_small_sizes() {
    for n in 1..=8 {
        for bounds in [Domain::ge(Int::from(100)), Domain::empty()] {
            let clauses: Vec<_> = (0..n)
                .map(|i| FlatClause {
                    bounds: bounds.clone(),
                    mods: BTreeMap::from([
                        (
                            Int::from(100_003),
                            vec![(Int::from(i % 2), Int::from(i % 2))],
                        ),
                        (Int::from(100_019), vec![(Int::from(i), Int::from(i))]),
                    ]),
                })
                .collect();
            assert_eq!(forced_pair_bounds(&clauses), Domain::all(), "{n}");
        }
        let (sets, max) = power_inputs(n * n);
        let ConsolidateOut::Ok(info, _) = consolidate_prime_powers(&sets, &max) else {
            panic!("fixed residue at {n}");
        };
        assert_eq!(info.u, &max - &Int::ONE, "{n}");
        let (uf, atoms, f) = alias_chain(n);
        assert_eq!(
            uf.get(&atoms[0]),
            (atoms[n].clone(), 1, Int::from(n)),
            "{n}"
        );
        let mut witness = Model::new();
        for (i, a) in atoms.iter().enumerate() {
            witness.insert(a.clone(), Int::from(2i64 - i as i64));
        }
        witness.insert(Atom::Aux(0), Int::ZERO);
        witness.insert(Atom::Aux(1), Int::from(2));
        assert!(f.holds(&witness), "{n}");
        assert!(matches!(solve_modular(&f, false), Some(Some(_))), "{n}");
        assert_eq!(crate::presburger::decide(&f), Ok(true), "{n}");
    }
}

/// The alias chain of `alias_chain(n)` whose last link carries one `64·n`-bit written offset
/// (U3 of PERF-negated-chain-unsolved).
fn wide_alias_chain(n: usize) -> Formula {
    let (_, atoms, f) = alias_chain(n);
    let huge = Int::from(num_bigint::BigInt::from(1) << (64 * n));
    let f = f.map_cons(&|c| {
        let mut c = c.clone();
        if c.lin.terms.contains_key(&atoms[n - 1]) && c.lin.terms.contains_key(&atoms[n]) {
            c.lin.constant = -&huge;
        }
        Formula::Con(c)
    });
    let mut model = Model::new();
    for (i, a) in atoms.iter().enumerate() {
        let value = if i == n {
            &Int::from(3i64 - n as i64) - &huge
        } else {
            Int::from(2i64 - i as i64)
        };
        model.insert(a.clone(), value);
    }
    model.insert(Atom::Aux(0), Int::ZERO);
    model.insert(Atom::Aux(1), Int::from(2));
    assert!(f.holds(&model));
    f
}

/// The answers `bench::pncx_wide_affine_alias_scale` checks at 128 and 1024, at small sizes.
#[test]
fn pncx_wide_affine_alias_is_satisfiable_at_small_sizes() {
    for n in [1, 2, 8, 16] {
        assert!(
            matches!(solve_modular(&wide_alias_chain(n), false), Some(Some(_))),
            "n={n}"
        );
    }
}

/// Builds a chain where the single `64*n`-bit offset sits in the middle (`n/2`) AND appears first
/// in the conjunction, with alternating signs and an unbounded primary variable (exercising
/// Kruskal bit-weight ordering, LCA cancellation, and `min_offsets_of`).
fn wide_middle_first_chain(n: usize) -> Formula {
    let mid = n / 2;
    let atoms: Vec<_> = (0..=n)
        .map(|i| Atom::Sym(format!("m{:06}", n - i).into()))
        .collect();
    let huge = Int::from(num_bigint::BigInt::from(1) << (64 * n));
    let mut parts = Vec::with_capacity(n + 5);
    // Place the wide middle edge FIRST to defeat naive FIFO orderings.
    // Sign-alternating chain: a_i = -a_{i+1} + c_i (except wide edge a_{mid-1} = -a_mid + huge).
    parts.push(Formula::Con(Con::eq(
        &Lin::atom(atoms[mid - 1].clone()),
        &Lin::atom(atoms[mid].clone())
            .times(-1)
            .plus(&Lin::constant(huge.clone())),
    )));
    for i in (0..n).rev() {
        if i == mid - 1 {
            continue;
        }
        parts.push(Formula::Con(Con::eq(
            &Lin::atom(atoms[i].clone()),
            &Lin::atom(atoms[i + 1].clone())
                .times(-1)
                .plus(&Lin::constant(1)),
        )));
    }
    let x = Lin::atom(atoms[0].clone());
    let q = Lin::atom(Atom::Aux(0));
    let r = Lin::atom(Atom::Aux(1));
    parts.extend([
        Formula::Con(Con::eq(&x, &q.times(3).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(2), &r)),
        Formula::Con(Con::eq(&r, &Lin::constant(2))),
    ]);
    Formula::And(crate::presburger::Shared::new(parts))
}

#[test]
fn pncx_wide_affine_alias_adversarial_shapes() {
    // 1. Verify exact model construction and `min_offsets_of` on middle-wide-first alternating-sign
    //    unbounded chains, plus renaming invariance.
    for n in [4usize, 7, 16] {
        let f = wide_middle_first_chain(n);
        assert!(matches!(solve_modular(&f, false), Some(Some(_))), "n={n}");
        let model = solve_modular(&f, true)
            .expect("accepted")
            .expect("satisfiable");
        assert!(f.holds(&model), "model failed at n={n}");

        // Rename every symbol in reverse order and confirm identical verdict.
        let renamed = f.map_cons(&|c| {
            let mut terms = BTreeMap::new();
            for (a, k) in &c.lin.terms {
                let na = match a {
                    Atom::Sym(s) => Atom::Sym(format!("z_{s}").into()),
                    other => other.clone(),
                };
                terms.insert(na, k.clone());
            }
            Formula::Con(Con {
                lin: Lin {
                    terms,
                    constant: c.lin.constant.clone(),
                },
                rel: c.rel,
            })
        });
        assert!(
            matches!(solve_modular(&renamed, false), Some(Some(_))),
            "renamed n={n}"
        );
    }

    // 2. Verify `UnitUf::min_offsets_of` matches naive `tree_get` over a mixed-sign forest.
    let mut uf = UnitUf::new();
    let atoms: Vec<_> = (0..12)
        .map(|i| Atom::Sym(format!("v{i:02}").into()))
        .collect();
    for i in 0..11 {
        let sign = if i % 3 == 0 { -1 } else { 1 };
        let offset = if i == 5 {
            Int::from(num_bigint::BigInt::from(1) << 256)
        } else {
            Int::from((i as i64) * 7 - 11)
        };
        uf.union(&atoms[i], &atoms[i + 1], sign, &offset)
            .expect("consistent");
    }
    let root = uf.tree_root(&atoms[0]);
    let mut expected: [Option<Int>; 2] = [None, None];
    for a in &atoms {
        let (r, s, d) = uf.tree_get(a);
        assert_eq!(r, root);
        let slot = &mut expected[usize::from(s < 0)];
        if slot.as_ref().is_none_or(|l| d < *l) {
            *slot = Some(d);
        }
    }
    assert_eq!(uf.min_offsets_of(&root), expected);
    // 3. The cost of the chain at 128 and 1024 is
    //    `bench::pncx_wide_affine_alias_adversarial_scale`.
}
