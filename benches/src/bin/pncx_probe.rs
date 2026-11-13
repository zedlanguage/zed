//! Hand-run probes of PERF-negated-chain-unsolved (docs/handoff/PERF-negated-chain-unsolved.md),
//! moved out of `tests/steps/l01_38_presburger/pncx_probe.rs`, where they were ignored tests:
//! each prints times or work for the sizes or cases its environment variables name and asserts
//! nothing, or takes past what a run of the tests may spend. `pncx_probe <name>` runs one; the
//! names are those of the functions below, `chain8`, `scaling`, `six_axis`, `pairs_enumeration`,
//! `sat_reduction`, `crt_bit_axis`, `fibonacci_parts` and `profile`. Example:
//! `PNCX_AXIS=moduli PNCX_SIZES=64,512 pncx_probe scaling`.

use std::process::ExitCode;
use std::time::Instant;

use zed_tests::step_helpers::l01_16_elaboration::elab;
use zed_tests::step_helpers::l01_38_presburger::pncx::*;

/// Chain 8 of
/// `one_scope::no_question_of_a_random_chain_with_negations_is_refused_where_its_relation_is_decided`.
const CHAIN8: &str = include_str!("../../../tests/steps/l01_38_presburger/pncx_chain8.zed");

/// Prints the time of each question of chain 8 (or of the source at `PNC_SRC`); checks the
/// answers only with `PNCX_CHECK`.
fn pncx_chain8() {
    let src = std::env::var("PNC_SRC")
        .map(|p| std::fs::read_to_string(p).unwrap())
        .unwrap_or_else(|_| CHAIN8.to_string());
    println!("{src}");
    // PNCX_CHECK: each empty answer of the modular solver asked again of the general path,
    // inside the timed calls (so the times are not those of the solver alone).
    if std::env::var_os("PNCX_CHECK").is_some() {
        let ((), c) = zedc::store::presburger::with_modular_empty_checked(|| run(&src, 1));
        report(&c);
    } else {
        run(&src, 1);
    }
}

/// Prints the work of the axis `PNCX_AXIS` at each size of `PNCX_SIZES`.
fn pncx_scaling() {
    let axis = std::env::var("PNCX_AXIS").unwrap();
    let sizes: Vec<usize> = std::env::var("PNCX_SIZES")
        .unwrap()
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    let mut meter = zed_tests::scaling::Meter::new();
    for n in sizes {
        let src = axis_src(&axis, n);
        if std::env::var_os("PNCX_SHOW").is_some() {
            println!("{src}");
        }
        let stmts = zed_tests::deep::statements(&src);
        let tokens = zedc::lex::lex_fence(&src).unwrap();
        let unit = elab(&src).unwrap();
        let mut refused = 0;
        let t = Instant::now();
        let w = meter.work(|| {
            refused = zedc::front::linear_questions(&src, &tokens, &stmts, &unit).len();
        });
        println!(
            "PNCXS {axis} n {n} instr {} bytes {} refused {refused} {:.4}s",
            w.units,
            w.bytes,
            t.elapsed().as_secs_f64()
        );
    }
}

/// The work, bytes and answer of `satisfiable` (or `decide`, with `PNCX_DECIDE`) on the formula
/// of the axis `PNCX_AXIS` at size `PNCX_N`.
fn pncx_six_axis() {
    use zed_tests::scaling::Meter;
    use zedc::store::presburger::satisfiable;
    let axis = std::env::var("PNCX_AXIS").unwrap();
    let n: usize = std::env::var("PNCX_N").unwrap().parse().unwrap();
    let f = pncx_formula(&axis, n);
    let mut meter = Meter::new();
    let mut ans = None;
    // `PNCX_DECIDE` set: `decide`, which builds no model, in place of `satisfiable`.
    let only_decide = std::env::var("PNCX_DECIDE").is_ok();
    let w = meter.work(|| {
        ans = Some(if only_decide {
            zedc::store::presburger::decide(&f).map(|b| b.then(zedc::store::presburger::Model::new))
        } else {
            satisfiable(&f)
        });
    });
    if !only_decide && let Some(Ok(Some(model))) = &ans {
        assert!(f.holds(model));
    }
    println!(
        "AXIS {axis} n={n} work={} bytes={} unit={} answer={:?}",
        w.units,
        w.bytes,
        meter.unit(),
        ans.as_ref().unwrap().as_ref().map(|m| m.is_some())
    );
}

/// Enumerates the pair cases `PNCX_CASES` (default `0..3000`, past 60 s).
fn pncx_pairs_enumeration() {
    use std::sync::Arc;
    use zedc::store::int::Int;
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, decide, satisfiable};
    let spec = std::env::var("PNCX_CASES").unwrap_or_else(|_| "0..3000".into());
    let (a, b) = spec.split_once("..").unwrap();
    let (a, b): (usize, usize) = (a.parse().unwrap(), b.parse().unwrap());
    let mut rng = zed_tests::instances::Rng::new(0x9284);
    let mut refused = 0;
    let mut checked = 0;
    let ((), c) = zedc::store::presburger::with_modular_empty_checked(|| {
        for case in 0..b {
            let mods = [3i64, 4, 5, 7, 11, 13, 16, 25];
            let pairs = 2 + rng.below(3);
            let ms: Vec<_> = (0..2 * pairs)
                .map(|_| mods[rng.below(mods.len())])
                .collect();
            let lo = match case % 3 {
                0 => -120,
                1 => -20,
                _ => 10000,
            } + rng.int(0, 20);
            let hi = lo + rng.int(0, 150);
            let x = Lin::atom(Atom::Sym(Arc::from("x")));
            let mut fs = vec![
                Formula::Con(Con::ge(&x, &Lin::constant(lo))),
                Formula::Con(Con::ge(&Lin::constant(hi), &x)),
            ];
            let mut rs = Vec::new();
            for (i, &m) in ms.iter().enumerate() {
                let q = Lin::atom(Atom::Aux((2 * i) as u32));
                let r = Lin::atom(Atom::Aux((2 * i + 1) as u32));
                fs.push(Formula::Con(Con::eq(
                    &x.minus(&q.times(m)).minus(&r),
                    &Lin::constant(0),
                )));
                fs.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
                fs.push(Formula::Con(Con::ge(&Lin::constant(m - 1), &r)));
                rs.push(r);
            }
            for j in 0..pairs {
                for _ in 0..2 {
                    let mut ds = Vec::new();
                    for i in [2 * j, 2 * j + 1] {
                        let v = rng.int(0, ms[i] - 1);
                        let f = Formula::Con(Con::eq(&rs[i], &Lin::constant(v)));
                        ds.push(if rng.below(4) == 0 {
                            Formula::negate(f)
                        } else {
                            f
                        });
                    }
                    fs.push(Formula::or(ds));
                }
            }
            if case < a {
                continue;
            }
            let f = Formula::and(fs);
            let brute = (lo..=hi).any(|v| {
                let mut model = Model::from([(Atom::Sym(Arc::from("x")), Int::from(v))]);
                for (i, &m) in ms.iter().enumerate() {
                    model.insert(Atom::Aux((2 * i) as u32), Int::from(v.div_euclid(m)));
                    model.insert(Atom::Aux((2 * i + 1) as u32), Int::from(v.rem_euclid(m)));
                }
                f.holds(&model)
            });
            let d = decide(&f);
            let s = satisfiable(&f);
            if let Ok(v) = &d {
                assert_eq!(*v, brute, "case {case}: {f}");
                checked += 1;
            } else {
                refused += 1;
            }
            if let Ok(m) = &s {
                assert_eq!(m.is_some(), brute, "case {case}: {f}");
                if let Some(m) = m {
                    assert!(f.holds(m));
                }
                checked += 1;
            } else {
                refused += 1;
            }
        }
    });
    report(&c);
    println!(
        "PAIR_ORACLE cases={} checked={checked} refused={refused}",
        b - a
    );
}

/// 3-SAT as one-variable residue constraints (the reduction of Garey and Johnson AN2): variable
/// `j` is `x mod p_j` in `{0, 1}` for the `j`-th prime `p_j`; a clause excludes the one residue
/// modulo the product of its three primes at which all three literals are false. `x` is bounded
/// to `0..P` for `P` the product of all the primes. `PNCX_SAT_RANDOM=v,c,seed` builds `c` random
/// clauses over `v` variables; each line prints `decide` and, for at most 7 variables
/// (`P <= 510510`), the truth by enumeration over `0..P`.
fn pncx_sat_reduction() {
    use std::sync::Arc;
    use zedc::store::int::Int;
    use zedc::store::presburger::{Atom, Con, Formula, Lin, decide};
    let spec = std::env::var("PNCX_SAT_RANDOM").unwrap();
    let v: Vec<u64> = spec.split(',').map(|s| s.parse().unwrap()).collect();
    let (nv, nc, seed) = (v[0] as usize, v[1] as usize, v[2]);
    let easy = std::env::var_os("PNCX_SAT_EASY").is_some();
    let mut rng = zed_tests::instances::Rng::new(seed);
    let mut primes = Vec::new();
    let mut p = 2i64;
    while primes.len() < nv {
        if (2..).take_while(|d| d * d <= p).all(|d| p % d != 0) {
            primes.push(p);
        }
        p += 1;
    }
    let plant: Vec<bool> = (0..nv).map(|_| rng.below(2) == 0).collect();
    let mut clauses: Vec<[(usize, bool); 3]> = Vec::new();
    while clauses.len() < nc {
        let a = rng.below(nv);
        let b = rng.below(nv);
        let c = rng.below(nv);
        if a == b || b == c || a == c {
            continue;
        }
        // `PNCX_SAT_EASY`: the first literal of every clause agrees with the planted assignment
        // `plant`, so `plant` satisfies every clause (an easy instance of the same shape, not
        // satisfied by `x = 1` unless `plant` is all ones).
        let mut cl = [
            (a, rng.below(2) == 0),
            (b, rng.below(2) == 0),
            (c, rng.below(2) == 0),
        ];
        if easy {
            cl[0].1 = plant[a];
        }
        clauses.push(cl);
    }
    let x = Lin::atom(Atom::Sym(Arc::from("x")));
    let mut fs = Vec::new();
    let mut aux = 0u32;
    let mut residue = |fs: &mut Vec<Formula>, m: i64| {
        let q = Lin::atom(Atom::Aux(aux));
        let r = Lin::atom(Atom::Aux(aux + 1));
        aux += 2;
        fs.push(Formula::Con(Con::eq(
            &x.minus(&q.times(Int::from(m))).minus(&r),
            &Lin::constant(0),
        )));
        fs.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
        fs.push(Formula::Con(Con::ge(&Lin::constant(m - 1), &r)));
        r
    };
    for &pj in &primes {
        let r = residue(&mut fs, pj);
        fs.push(Formula::Con(Con::ge(&Lin::constant(1), &r)));
    }
    let mut excluded = Vec::new();
    for cl in &clauses {
        let (m, c) = pncx_sat_residue(&primes, cl);
        let r = residue(&mut fs, m);
        fs.push(Formula::negate(Formula::Con(Con::eq(
            &r,
            &Lin::constant(c),
        ))));
        excluded.push((m, c));
    }
    // The product of the primes overflows i64 past 15 primes, so the bound is an `Int`.
    let big_p = primes
        .iter()
        .fold(Int::from(1i64), |acc, p| &acc * &Int::from(*p));
    fs.push(Formula::Con(Con::ge(&x, &Lin::constant(0))));
    fs.push(Formula::Con(Con::ge(
        &Lin::constant(&big_p - &Int::from(1i64)),
        &x,
    )));
    let f = Formula::and(fs);
    let t = std::time::Instant::now();
    println!("PNCXSAT_READY v={nv} c={nc}");
    let got = decide(&f);
    let dt = t.elapsed().as_secs_f64();
    let small_p: Option<i64> = (nv <= 7).then(|| primes.iter().product());
    let truth = small_p.map(|big_p| {
        (0..big_p)
            .any(|x| primes.iter().all(|p| x % p <= 1) && excluded.iter().all(|(m, c)| x % m != *c))
    });
    let shown = match &got {
        Ok(b) => b.to_string(),
        Err(e) => format!("refused {e:?}").chars().take(120).collect(),
    };
    println!(
        "PNCXSAT v={nv} c={nc} seed={seed} easy={easy} decide={shown} truth={truth:?} {dt:.4}s"
    );
    if let Err(why) = got {
        let divisors: std::collections::BTreeSet<_> = primes
            .iter()
            .copied()
            .chain(excluded.iter().map(|&(m, _)| m))
            .collect();
        let written: Vec<_> = divisors.iter().map(ToString::to_string).collect();
        let names: Vec<_> = written.iter().map(String::as_str).collect();
        println!("PNCXSAT_MESSAGE {}", why.said(&["x"], &names));
    }
    if let Ok(path) = std::env::var("PNCX_SAT_SOURCE") {
        let mut conditions: Vec<_> = primes.iter().map(|p| format!("x mod {p} <= 1")).collect();
        conditions.extend(excluded.iter().map(|(m, c)| format!("x mod {m} != {c}")));
        conditions.extend(["x >= 0".into(), format!("x < {big_p}")]);
        let source = format!(
            "ok(x:int)={};\nmain(m:MainArgs) {{ a=int(m.stdin[0] else \"0\") else 0; r=if ok(x:a) {{ \"in\" }} else {{ \"out\" }}; m.stdout <- \"${{r}}\"; }}\n",
            conditions.join(" && ")
        );
        std::fs::write(path, source).expect("probe source file");
    }
}

/// Sizes from `PNCX_SIZES`.
fn pncx_crt_bit_axis() {
    use zedc::store::presburger::satisfiable;
    let sizes = std::env::var("PNCX_SIZES").unwrap();
    let mut meter = zed_tests::scaling::Meter::new();
    for n in sizes.split(',').map(|n| n.parse::<usize>().unwrap()) {
        let f = pncx_crt_bits(n);
        let modulus_bits = f
            .cons()
            .iter()
            .flat_map(|c| c.lin.terms.values())
            .map(|k| {
                zedc::store::int::Num::from(k)
                    .built()
                    .expect("written integer")
                    .bits()
            })
            .max()
            .unwrap_or(0);
        let mut result = None;
        let t = Instant::now();
        let w = meter.work(|| result = Some(satisfiable(&f)));
        let model = result.unwrap().expect("answer").expect("point");
        assert!(f.holds(&model));
        println!(
            "CRTBITS {n} modulus_bits {modulus_bits} instr {} bytes {} wall {:.6}",
            w.units,
            w.bytes,
            t.elapsed().as_secs_f64()
        );
    }
}

/// The kernel's inverse and gcd alone on the moduli of [`pncx_crt_bits`], for `PNCX_SIZES`: the
/// part of `pncx_crt_bit_axis`'s work they take.
/// Sizes from `PNCX_SIZES`.
fn pncx_fibonacci_parts() {
    use zedc::store::int::Num;
    let sizes = std::env::var("PNCX_SIZES").unwrap();
    let mut meter = zed_tests::scaling::Meter::new();
    for n in sizes.split(',').map(|n| n.parse::<usize>().unwrap()) {
        let f = pncx_crt_bits(n);
        let ms: Vec<num_bigint::BigUint> = f
            .cons()
            .iter()
            .flat_map(|c| c.lin.terms.values())
            .map(|k| Num::from(k).built().expect("written").magnitude().clone())
            .filter(|m| m.bits() > 64)
            .collect();
        let (a, b) = (&ms[0], &ms[1]);
        let mut inv = None;
        let wi = meter.work(|| inv = zed_kernel::num::inverse_mod_uint(a, b));
        assert!((a * inv.expect("coprime") % b) == num_bigint::BigUint::from(1u32));
        let mut g = None;
        let wg = meter.work(|| g = Some(zed_kernel::num::gcd_uint(a, b)));
        assert!(g.expect("run") == num_bigint::BigUint::from(1u32));
        let mut p = None;
        let wp = meter.work(|| p = Some(zed_kernel::num::rem_uint(&(a * b), b)));
        let _ = std::hint::black_box(p);
        println!(
            "FIBPARTS {n} bits {} inverse {} {} gcd {} {} product+rem {} {}",
            b.bits(),
            wi.units,
            wi.bytes,
            wg.units,
            wg.bytes,
            wp.units,
            wp.bytes
        );
    }
}

/// The front's linear questions of the axis `PNCX_AXIS` at size `PNCX_N`, eight times, for a
/// profiler.
fn pncx_profile() {
    let axis = std::env::var("PNCX_AXIS").unwrap();
    let n: usize = std::env::var("PNCX_N").unwrap().parse().unwrap();
    let src = axis_src(&axis, n);
    let stmts = zed_tests::deep::statements(&src);
    let tokens = zedc::lex::lex_fence(&src).unwrap();
    let unit = elab(&src).unwrap();
    println!("PROFILE input built");
    for _ in 0..8 {
        std::hint::black_box(zedc::front::linear_questions(&src, &tokens, &stmts, &unit));
    }
}

fn main() -> ExitCode {
    let name = std::env::args().nth(1).unwrap_or_default();
    match name.as_str() {
        "chain8" => pncx_chain8(),
        "scaling" => pncx_scaling(),
        "six_axis" => pncx_six_axis(),
        "pairs_enumeration" => pncx_pairs_enumeration(),
        "sat_reduction" => pncx_sat_reduction(),
        "crt_bit_axis" => pncx_crt_bit_axis(),
        "fibonacci_parts" => pncx_fibonacci_parts(),
        "profile" => pncx_profile(),
        _ => {
            eprintln!(
                "pncx_probe: the probe is one of chain8, scaling, six_axis, pairs_enumeration, \
                 sat_reduction, crt_bit_axis, fibonacci_parts, profile; not `{name}`"
            );
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}
