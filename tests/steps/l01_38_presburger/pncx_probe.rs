//! Questions of random chains with negations and of the named axes of formulas
//! (PERF-negated-chain-unsolved): answers against enumeration, and their scaling. The helpers
//! are in `zed_tests::step_helpers::l01_38_presburger::pncx`, shared with the hand-run probes
//! of `benches/src/bin/pncx_probe.rs`.

use std::time::Instant;

use zed_kernel::Term;
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zed_tests::step_helpers::l01_38_presburger::pncx::*;
use zedc::store::preimage::Scoped;
use zedc::store::presburger::extend::Extending;

/// PNCX_SEEDS=a..b: random chains; each answer, faced and plain, in both orders, against
/// points. Prints one line per question and MISMATCH lines.
#[test]
fn pncx_random() {
    let seeds = std::env::var("PNCX_SEEDS").unwrap_or_else(|_| "0..20".into());
    let (a, b) = seeds.split_once("..").unwrap();
    let (a, b): (u64, u64) = (a.parse().unwrap(), b.parse().unwrap());
    let (mut refused, mut answered, mut bad) = (0, 0, 0);
    let check = std::env::var_os("PNCX_CHECK").is_some();
    let ((), c) = zedc::store::presburger::with_modular_empty_checked(|| {
        for seed in a..b {
            let mut rng = zed_tests::instances::Rng::new(seed);
            let src = std::env::var("PNC_SRC").map_or_else(
                |_| chain(&mut rng),
                |path| std::fs::read_to_string(path).expect("probe source"),
            );
            if std::env::var_os("PNCX_SHOW").is_some() {
                println!("PNCXSRC {seed}\n{src}\nPNCXEND");
            }
            let Ok(unit) = elab(&src) else { continue };
            let lets = lets(&unit);
            let fs: Vec<_> = unit
                .defs
                .iter()
                .filter_map(|d| match &*d.term {
                    Term::Lam(ps, body) => Some((d.name.as_str(), ps.as_slice(), &**body)),
                    _ => None,
                })
                .collect();
            for (o, order) in [
                (0..fs.len()).collect::<Vec<_>>(),
                (0..fs.len()).rev().collect(),
            ]
            .into_iter()
            .enumerate()
            {
                let mut scoped = Scoped::new(&lets);
                let (mut faced, mut plain) = (Extending::new(), Extending::new());
                for i in order {
                    let (name, ps, body) = fs[i];
                    let Some(r) = scoped.relation(body, ps, ps, true) else {
                        continue;
                    };
                    let t = Instant::now();
                    let mut ask = || {
                        let x =
                            faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
                        (x, plain.defined(&r, &|n| scoped.def(n)))
                    };
                    // Without PNCX_CHECK, the answers are asked outside the check.
                    let (x, y) = if check {
                        ask()
                    } else {
                        zedc::store::presburger::without_modular_empty_check(ask)
                    };
                    let dt = t.elapsed().as_secs_f64();
                    let w = scoped.written(&r);
                    let truth = enumerated(&w);
                    let show = |a: &Result<bool, _>| match a {
                        Ok(v) => v.to_string(),
                        Err(_) => "R".to_string(),
                    };
                    let tr = truth.map_or("?".to_string(), |(h, f)| format!("{h}/{f}"));
                    println!(
                        "PNCXR {seed} {o} {name} holds {}/{} fails {}/{} truth {tr} {dt:.4}s",
                        show(&x.holds),
                        show(&y.holds),
                        show(&x.fails),
                        show(&y.fails)
                    );
                    for (got, want) in [
                        (&x.holds, truth.map(|t| t.0)),
                        (&y.holds, truth.map(|t| t.0)),
                        (&x.fails, truth.map(|t| t.1)),
                        (&y.fails, truth.map(|t| t.1)),
                    ] {
                        match (got, want) {
                            (Ok(g), Some(w)) if *g != w => {
                                bad += 1;
                                println!("MISMATCH {seed} {o} {name}\n{src}");
                            }
                            (Ok(_), _) => answered += 1,
                            (Err(_), _) => refused += 1,
                        }
                    }
                }
            }
        }
    });
    report(&c);
    println!("PNCXR total answered {answered} refused {refused} mismatches {bad}");
    assert_eq!(bad, 0);
}

#[test]
fn pncx_distinct_moduli_scale() {
    use zedc::store::presburger::satisfiable;
    let inputs = zed_tests::scaling::inputs(32, |n| pncx_formula("moduli", n));
    zed_tests::scaling::check_order("one-variable distinct moduli", 32, 1, |n| {
        let ans = satisfiable(&inputs[&n]);
        assert!(ans.is_ok());
        let _ = std::hint::black_box(ans);
    });
}

#[test]
fn pncx_easy_pairs_scale() {
    use zedc::store::presburger::satisfiable;
    let inputs = zed_tests::scaling::inputs(2, |n| pncx_formula("pairs", n));
    zed_tests::scaling::check_order("separate remainder pairs", 2, 1, |n| {
        let ans = satisfiable(&inputs[&n]);
        assert!(matches!(ans, Ok(Some(_))));
        let _ = std::hint::black_box(ans);
    });
}

#[test]
fn pncx_sat_crt_construction_scale() {
    let inputs = zed_tests::scaling::inputs(8, |n| {
        let mut ps = Vec::new();
        let mut p = 2i64;
        while ps.len() < n {
            if (2..).take_while(|d| d * d <= p).all(|d| p % d != 0) {
                ps.push(p);
            }
            p += 1;
        }
        let cl = [(n - 3, true), (n - 2, false), (n - 1, true)];
        (ps, cl)
    });
    zed_tests::scaling::check_order("construct SAT image residues by CRT", 8, 1, |n| {
        let (ps, cl) = &inputs[&n];
        let residues: Vec<_> = (0..n).map(|_| pncx_sat_residue(ps, cl)).collect();
        std::hint::black_box(residues);
    });
}

#[test]
fn pncx_large_literals_keep_the_question() {
    for literal in [
        "9223372036854775807",
        "9223372036854775808",
        "18446744073709551616",
    ] {
        let src = format!("q(x: int) = x < {literal};");
        let unit = elab(&src).unwrap();
        let scope = lets(&unit);
        let mut scoped = Scoped::new(&scope);
        let d = &unit.defs[0];
        let Term::Lam(ps, body) = &*d.term else {
            panic!("lambda");
        };
        assert!(
            scoped.relation(body, ps, ps, true).is_some(),
            "{literal}: question dropped"
        );
    }
}

// A divisor written in decimal past `i128` keeps the question (R5-CLAUDE-4): read as an
// `i128`, `2^127` and up were read as no constant and the question was dropped.
#[test]
fn pncx_divisor_past_i128_is_read() {
    let two = num_bigint::BigInt::from(2);
    for bits in [64u32, 126, 127, 128, 200, 10_000] {
        let d = two.pow(bits).to_string();
        let src = format!("q(x: int) = x mod {d} == 1 && x div {d} == 0;");
        let unit = elab(&src).unwrap();
        let scope = lets(&unit);
        let mut scoped = Scoped::new(&scope);
        let Term::Lam(ps, body) = &*unit.defs[0].term else {
            panic!("lambda");
        };
        assert!(
            scoped.relation(body, ps, ps, true).is_some(),
            "2^{bits}: question dropped"
        );
    }
}

/// Two consecutive Fibonacci moduli, the slowest case of the Euclidean extended gcd: the whole
/// question costs at most 10 times the kernel's gcd of the same two moduli, at F(80001) (55,540
/// bits) and F(750001) (520,682 bits). Measured 5.8 and 6.5 times with the half gcd; 190 times
/// at F(80001) with the Euclidean `bezout` (R6-CLAUDE-7). A scaling test cannot hold it: the
/// kernel's gcd alone on these numbers grows 17.5 times in instructions and 13.9 times in bytes
/// from F(750001) to F(6000001), above the limit of 13. Ignored for its time,
/// about 3 seconds.
#[test]
fn pncx_fibonacci_crt_scale() {
    use zedc::store::int::Num;
    use zedc::store::presburger::satisfiable;
    let mut meter = zed_tests::scaling::Meter::new();
    for n in [80_000, 750_000] {
        let f = pncx_crt_bits(n);
        let ms: Vec<num_bigint::BigUint> = f
            .cons()
            .iter()
            .flat_map(|c| c.lin.terms.values())
            .map(|k| Num::from(k).built().expect("written").magnitude().clone())
            .filter(|m| m.bits() > 64)
            .collect();
        let mut ans = None;
        let question = meter.work(|| ans = Some(satisfiable(&f)));
        let model = ans.expect("run").expect("answer").expect("a point");
        assert!(f.holds(&model));
        let mut g = None;
        let gcd = meter.work(|| g = Some(zed_kernel::num::gcd_uint(&ms[0], &ms[1])));
        assert!(g.expect("run") == num_bigint::BigUint::from(1u32));
        let ratio = question.units as f64 / gcd.units as f64;
        println!(
            "FIBCRT {n} question {} gcd {} ratio {ratio:.2}",
            question.units, gcd.units
        );
        assert!(
            ratio <= 10.0,
            "F({}): the question is {ratio:.2} gcds",
            n + 1
        );
    }
}

#[test]
fn pncx_disj_scale() {
    pncx_front_scale("disj");
}

#[test]
fn pncx_pairs_scale() {
    pncx_front_scale("pairs");
}
#[test]
fn pncx_t8_enum_suite_sign12() {
    t8_enum_suite(1, 0..1200, 33);
}

#[test]
fn pncx_t8_enum_suite_padic() {
    t8_enum_suite(2, 0..1200, 33);
}

#[test]
fn pncx_t8_enum_suite_pairs_0() {
    t8_enum_suite(3, 0..300, 7);
}

#[test]
fn pncx_t8_enum_suite_pairs_1() {
    t8_enum_suite(3, 300..600, 5);
}

#[test]
fn pncx_t8_enum_suite_pairs_2() {
    t8_enum_suite(3, 600..900, 16);
}

#[test]
fn pncx_t8_enum_suite_pairs_3() {
    t8_enum_suite(3, 900..1200, 6);
}

#[test]
fn pncx_renamed_parameters_and_case56_match() {
    let names = ["A", "a", "b", "w", "x", "y", "z", "zz"];
    let condition = "x >= (0 - 8) && x <= 26 && (x + 1) mod 10 <= 1 && (x - 5) mod 4 <= 1 && ((x - 5) mod 4 == 2 || (x - 5) mod 4 == 1 || x <= 12) && ((x + 1) mod 10 != 5 || x mod 8 != 7)";
    let mut sources = Vec::new();
    for x in names {
        let condition = condition.replace('x', x);
        sources.push(format!("p{}({x}: int) = {condition};", sources.len()));
        for alias in names {
            if alias == x {
                continue;
            }
            sources.push(format!(
                "p{}({x}: int, {alias}: int) = {alias} == {x} - 8 && {condition};",
                sources.len()
            ));
        }
    }
    let ask = |src: &str, reverse: bool| {
        let unit = elab(src).unwrap();
        let scope = lets(&unit);
        let mut scoped = Scoped::new(&scope);
        let (mut faced, mut plain) = (Extending::new(), Extending::new());
        let mut indices: Vec<_> = (0..unit.defs.len()).collect();
        if reverse {
            indices.reverse();
        }
        let mut out = std::collections::BTreeMap::new();
        for i in indices {
            let d = &unit.defs[i];
            let Term::Lam(ps, body) = &*d.term else {
                continue;
            };
            let r = scoped
                .relation(body, ps, ps, true)
                .expect("the numeric question is translated");
            let a = faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            let b = plain.defined(&r, &|n| scoped.def(n));
            let written = scoped.written(&r);
            use zedc::store::presburger::{Formula, decide, satisfiable};
            let holds = Formula::and(vec![written.defined(), written.body.clone()]);
            let fails = Formula::and(vec![written.defined(), Formula::negate(written.body)]);
            out.insert(
                d.name.clone(),
                (
                    a.holds.ok(),
                    a.fails.ok(),
                    b.holds.ok(),
                    b.fails.ok(),
                    decide(&holds).ok(),
                    decide(&fails).ok(),
                    satisfiable(&holds).ok().map(|m| m.is_some()),
                    satisfiable(&fails).ok().map(|m| m.is_some()),
                ),
            );
        }
        out
    };
    let batch = sources.join("\n");
    let first = ask(&batch, false);
    assert_eq!(first, ask(&batch, true));
    let mut by_arity = std::collections::BTreeMap::new();
    for src in &sources {
        let single = ask(src, false);
        for (name, answer) in single {
            assert_eq!(first[&name], answer, "batch/single {src}");
            let alias = src.contains(" - 8 &&");
            if let Some(old) = by_arity.insert(alias, answer) {
                assert_eq!(old, answer, "renamed {src}");
            }
            if alias {
                assert_eq!(
                    answer,
                    (
                        Some(true),
                        Some(true),
                        Some(true),
                        Some(true),
                        Some(true),
                        Some(true),
                        Some(true),
                        Some(true)
                    ),
                    "{src}"
                );
            }
        }
    }
}

#[test]
fn pncx_wide_divisor_translation_scale() {
    use zedc::store::int::Int;
    let inputs = zed_tests::scaling::inputs(128, |n| {
        let mut m = Int::ONE;
        for _ in 0..n {
            m = &m + &m;
        }
        let src = format!("f(x: int) = x mod {} == 1;", &m + &Int::ONE);
        let unit = elab(&src).unwrap();
        let scope = lets(&unit);
        (unit, scope)
    });
    zed_tests::scaling::check_order("translate written wide divisors", 128, 1, |n| {
        let (unit, scope) = &inputs[&n];
        let mut scoped = Scoped::new(scope);
        let Term::Lam(ps, body) = &*unit.defs[0].term else {
            panic!("one function")
        };
        let r = scoped
            .relation(body, ps, ps, true)
            .expect("wide divisor retains its question");
        let got = Extending::new().defined(&r, &|i| scoped.def(i));
        assert_eq!(got.holds, Ok(true));
        assert_eq!(got.fails, Ok(true));
    });
}
