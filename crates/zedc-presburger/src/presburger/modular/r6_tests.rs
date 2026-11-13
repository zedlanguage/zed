use super::*;
use crate::scaling;
use num_bigint::BigInt;

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
    for i in 0..12_000 {
        (a, b) = (b.clone(), &a + &b);
        if i % 197 == 0 {
            pairs.push((a.clone(), b.clone()));
            pairs.push((&a * &Int::from(12), &b * &Int::from(12)));
        }
    }
    for (a, b) in pairs {
        let (g, s, t) = a.extended_gcd(&b).expect("arithmetic check");
        assert_eq!(&(&s * &a) + &(&t * &b), g);
        let expected = crate::presburger::bezout(&a.abs(), &b).0;
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

fn fibonacci_pair(n: usize) -> (Int, Int) {
    let (mut a, mut b) = (Int::ONE, Int::ONE);
    for _ in 0..n {
        (a, b) = (b.clone(), &a + &b);
    }
    (a, b)
}

#[test]
#[ignore = "open: R7-CLAUDE-4, num-bigint products below the NTT crossover allocate about w^1.8 bytes (18.4x bytes, 15.8x work per 8x steps)"]
fn pncx_fibonacci_scale() {
    let inputs = scaling::inputs(4096, fibonacci_pair);
    scaling::check_order("half-GCD coefficients on Fibonacci inputs", 4096, 1, |n| {
        let (a, b) = &inputs[&n];
        let (g, s, t) = a.extended_gcd(b).expect("coprime");
        assert_eq!(g, Int::ONE);
        assert_eq!(&(&s * a) + &(&t * b), Int::ONE);
    });
}

#[test]
// A hand-run probe, not a test (PERF-negated-chain-unsolved: prints the work at the sizes
// PNCX_SIZES): built only with `--cfg zed_probes`; see [workspace.lints.rust] in the top
// Cargo.toml.
#[cfg(zed_probes)]
fn pncx_gcd_axis() {
    let mut meter = scaling::Meter::new();
    for n in std::env::var("PNCX_SIZES")
        .unwrap()
        .split(',')
        .map(|s| s.parse().unwrap())
    {
        let (a, b) = fibonacci_pair(n);
        let mut result = None;
        let work = meter.work(|| result = a.extended_gcd(&b));
        let (g, s, t) = result.expect("coprime");
        assert_eq!(&(&s * &a) + &(&t * &b), g);
        println!(
            "GCD n={n} work={} bytes={} unit={}",
            work.units,
            work.bytes,
            meter.unit()
        );
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
fn pncx_bipartite_core_scale() {
    let inputs = scaling::inputs(32, bipartite_core);
    scaling::check_order("color a bipartite three-core", 32, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_witness(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_coprime_base_exhaustive_small_inputs() {
    for a in 2..24 {
        for b in a..32 {
            for c in b..40 {
                let inputs = BTreeSet::from([Int::from(a), Int::from(b), Int::from(c)]);
                let fs = coprime_factorization(&inputs).unwrap();
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

#[test]
fn pncx_bound_matching_scale() {
    let inputs = scaling::inputs(128, |n| {
        (0..n)
            .map(|i| FlatClause {
                bounds: Domain::ge(Int::from(100)),
                mods: BTreeMap::from([
                    (
                        Int::from(100_003),
                        vec![(Int::from(i % 2), Int::from(i % 2))],
                    ),
                    (Int::from(100_019), vec![(Int::from(i), Int::from(i))]),
                ]),
            })
            .collect::<Vec<_>>()
    });
    scaling::check_order("three-pair implication by matching", 128, 1, |n| {
        assert_eq!(forced_pair_bounds(&inputs[&n]), Domain::all());
    });
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
fn pncx_power_propagation_scale() {
    let inputs = scaling::inputs(65_536, power_inputs);
    scaling::check_order("propagate the highest fixed residue once", 65_536, 1, |n| {
        let (sets, max) = &inputs[&n];
        let ConsolidateOut::Ok(info, _) = consolidate_prime_powers(sets, max) else {
            panic!("fixed residue");
        };
        assert_eq!(info.u, max - &Int::ONE);
    });
}

#[test]
fn pncx_power_propagation_oracle() {
    for seed in 0..512u64 {
        let mut state = seed;
        let mut sets = BTreeMap::new();
        let mut q = 1i64;
        for i in 0..6 {
            q *= 2;
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let a = (state % q as u64) as i64;
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

#[ignore = "PRES-scaling-10_5: 10.5 times the work at 64 and 512 and 12.9 times the bytes at 512 and 4096, over the limit of 10.5; open"]
#[test]
fn pncx_score_witness_scale() {
    let inputs = scaling::inputs(64, |n| {
        let info = boolean_info(n);
        let allowed = vec![vec![(Int::ZERO, Int::ONE)]; n];
        let clauses: Vec<BTreeMap<usize, ResidueSet>> = (0..n)
            .map(|i| {
                [i, (i + 1) % n, (i + 2) % n]
                    .into_iter()
                    .map(|j| (j, vec![(Int::ZERO, Int::ZERO)]))
                    .collect()
            })
            .collect();
        (info, allowed, clauses)
    });
    scaling::check_order("preferred residue values by endpoint sweep", 64, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(score_witness(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_wide_arithmetic_random_oracle() {
    use num_bigint::Sign;
    let mut state = 0x36ab_94f1_2d6e_1a39u64;
    for i in 0..1200usize {
        let mut make = |n: usize| {
            let mut bytes = Vec::with_capacity(n);
            for _ in 0..n {
                state = state
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                bytes.push((state >> 32) as u8);
            }
            BigInt::from_bytes_le(Sign::Plus, &bytes)
        };
        let a: BigInt = make(17 + i % 500) << (i % 91);
        let b: BigInt = (make(17 + (i * 37) % 500) + 1) << ((i * 11) % 71);
        let a = if i % 2 == 0 { a } else { -a };
        let b = if i % 3 == 0 { b } else { -b };
        let (ia, ib) = (Int::from(a.clone()), Int::from(b.clone()));
        let (g, s, t) = ia.extended_gcd(&ib).expect("nonzero pair");
        assert_eq!(&(&s * &ia) + &(&t * &ib), g, "case={i}");
        assert_eq!(g, crate::presburger::bezout(&ia.abs(), &ib).0, "case={i}");
        assert_eq!(ia.gcd(&ib), g, "case={i}");
        assert_eq!(ia.gcd_recursive(&ib), g, "case={i}");
        let mut q = &a / &b;
        let mut r = &a % &b;
        if r != BigInt::from(0) && a.sign() != b.sign() {
            q -= 1;
            r += &b;
        }
        assert_eq!(ia.div_floor_wide(&ib), Int::from(q.clone()), "case={i}");
        assert_eq!(ia.div_floor(&ib), Int::from(q), "case={i}");
        assert_eq!(ia.mod_floor_wide(&ib), Int::from(r.clone()), "case={i}");
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
fn pncx_prism_core_scale() {
    let inputs = scaling::inputs(32, prism_core);
    scaling::check_order("Brooks coloring on odd prism cores", 32, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_witness(info, allowed, clauses).is_some());
    });
}

#[test]
fn pncx_prism_models() {
    for n in 1..40 {
        let (info, allowed, clauses) = prism_core(n);
        let x = graph_coloring_witness(&info, &allowed, &clauses).expect("prism");
        assert!(holds_coprime_point(&x, &info, &allowed, &clauses));
    }
}

#[test]
// A hand-run probe, not a test (PERF-negated-chain-unsolved: prints the work at the sizes
// PNCX_SIZES): built only with `--cfg zed_probes`; see [workspace.lints.rust] in the top
// Cargo.toml.
#[cfg(zed_probes)]
fn pncx_prism_formula_axis() {
    let mut meter = scaling::Meter::new();
    for n in std::env::var("PNCX_SIZES")
        .unwrap()
        .split(',')
        .map(|s| s.parse().unwrap())
    {
        let (info, allowed, clauses) = prism_core(n);
        let point = graph_coloring_witness(&info, &allowed, &clauses).expect("prism");
        let xa = Atom::Sym("x".into());
        let x = Lin::atom(xa.clone());
        let mut model = Model::from([(xa, point.clone())]);
        let mut parts = Vec::new();
        let mut rs = Vec::new();
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
            let literals = clause
                .into_iter()
                .map(|(i, s)| {
                    let c = (0..3)
                        .map(Int::from)
                        .find(|c| !res_contains(&s, c))
                        .unwrap();
                    Formula::negate(Formula::Con(Con::eq(&rs[i], &Lin::constant(c))))
                })
                .collect();
            parts.push(Formula::or(literals));
        }
        let f = Formula::and(parts);
        assert!(f.holds(&model));
        let mut answer = None;
        let work = meter.work(|| answer = Some(crate::presburger::decide(&f)));
        assert_eq!(answer, Some(Ok(true)));
        println!(
            "PRISM n={n} work={} bytes={} unit={}",
            work.units,
            work.bytes,
            meter.unit()
        );
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
fn pncx_wheel_core_scale() {
    let inputs = scaling::inputs(32, wheel_core);
    scaling::check_order("a universal vertex and a bipartite remainder", 32, 1, |n| {
        let (info, allowed, clauses) = &inputs[&n];
        assert!(graph_coloring_witness(info, allowed, clauses).is_some());
    });
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
                    let r = Int::from(x).mod_floor_wide(m);
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

#[test]
fn pncx_empty_pair_bound_scale() {
    let inputs = scaling::inputs(128, |n| {
        (0..n)
            .map(|i| FlatClause {
                bounds: Domain::empty(),
                mods: BTreeMap::from([
                    (
                        Int::from(100003),
                        vec![(Int::from(i % 2), Int::from(i % 2))],
                    ),
                    (Int::from(100019), vec![(Int::from(i), Int::from(i))]),
                ]),
            })
            .collect::<Vec<_>>()
    });
    scaling::check_order("empty shared bounds tested by matching", 128, 1, |n| {
        assert_eq!(forced_pair_bounds(&inputs[&n]), Domain::all());
    });
}

#[test]
// A hand-run probe, not a test (PERF-negated-chain-unsolved: prints the work at four sizes, against
// no limit): built only with `--cfg zed_probes`; see [workspace.lints.rust] in the top Cargo.toml.
#[cfg(zed_probes)]
fn pncx_preparation_axis() {
    let mut meter = scaling::Meter::new();
    for n in [512, 1024, 2048, 4096] {
        let (info, _, _) = bipartite_core(n);
        let ms: BTreeSet<_> = info
            .iter()
            .take(n)
            .map(|b| &b.max_q * &Int::from(2))
            .collect();
        let bits: u32 = ms
            .iter()
            .map(|m| 128 - m.to_i128().unwrap().unsigned_abs().leading_zeros())
            .sum();
        let work = meter.work(|| {
            std::hint::black_box(coprime_factorization(&ms));
        });
        println!(
            "PREP n={n} input_bits={bits} work={} bytes={}",
            work.units, work.bytes
        );
    }
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

#[test]
fn pncx_alias_chain_axis() {
    let mut meter = scaling::Meter::new();
    for n in [256, 512, 1024, 2048] {
        let (uf, atoms, f) = alias_chain(n);
        assert_eq!(uf.get(&atoms[0]), (atoms[n].clone(), 1, Int::from(n)));
        let work = meter.work(|| {
            for a in &atoms {
                std::hint::black_box(uf.get(a));
            }
        });
        let printed = f.to_string().len();
        let mut witness = Model::new();
        for (i, a) in atoms.iter().enumerate() {
            witness.insert(a.clone(), Int::from(2i64 - i as i64));
        }
        witness.insert(Atom::Aux(0), Int::ZERO);
        witness.insert(Atom::Aux(1), Int::from(2));
        assert!(f.holds(&witness));
        println!(
            "ALIAS_GET n={n} input_bytes={printed} work={} bytes={}",
            work.units, work.bytes
        );
        let mut result = None;
        let work = meter.work(|| result = solve_modular(&f, false));
        assert!(matches!(result, Some(Some(_))));
        println!(
            "ALIAS_FORMULA n={n} input_bytes={printed} work={} bytes={}",
            work.units, work.bytes
        );
        let mut d = None;
        let work = meter.work(|| d = Some(crate::presburger::decide(&f)));
        assert_eq!(d, Some(Ok(true)));
        println!(
            "ALIAS_DECIDE n={n} input_bytes={printed} work={} bytes={}",
            work.units, work.bytes
        );
    }
}

#[test]
fn pncx_affine_alias_chain_scale() {
    let inputs = scaling::inputs(256, |n| alias_chain(n).2);
    scaling::check_order("affine aliases before one remainder", 256, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}
