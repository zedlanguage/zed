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
/// points. Prints one line per question and MISMATCH lines. Without PNCX_SEEDS, seeds 0 to 3
/// (about 0.3 s at load 35); seeds 0 to 19 (1.7 s at load 35, 3.1 s at load 25 with the
/// other tests) are in `bench::pncx_probe`.
#[test]
fn pncx_random() {
    pncx_random_over(0..4);
}

/// [`pncx_random`] over the seeds of PNCX_SEEDS, or `default` without it.
pub(super) fn pncx_random_over(default: std::ops::Range<u64>) {
    let (a, b) = match std::env::var("PNCX_SEEDS") {
        Ok(seeds) => {
            let (a, b) = seeds.split_once("..").unwrap();
            (a.parse().unwrap(), b.parse().unwrap())
        }
        Err(_) => (default.start, default.end),
    };
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

// The three families of `t8_enum_suite` at their first formulas: 40 of families 1 and 2, which
// take each of the four kinds of range family 1 picks by its index, and 6 of family 3, which take
// both kinds of offset it picks by its index; none is refused. All 1,200 of each family are many
// cases, so they run in `bench::pncx_probe` (author P178).
#[test]
fn pncx_t8_enum_suite_sign12_first_formulas() {
    t8_enum_suite(1, 0..40, 0);
}

#[test]
fn pncx_t8_enum_suite_padic_first_formulas() {
    t8_enum_suite(2, 0..40, 0);
}

#[test]
fn pncx_t8_enum_suite_pairs_first_formulas() {
    t8_enum_suite(3, 0..6, 0);
}

/// A condition of one variable, written under four names (capital, small, other letter, two
/// letters), alone and beside an alias 8 below it under each other name: asked in one batch in
/// both orders and one by one, each gives the same answers, and the aliased forms are all
/// answered and both sides hold. All eight names (64 functions, 1.9 s at load 25) are in
/// `bench::pncx_probe`.
#[test]
fn pncx_renamed_parameters_and_case56_match() {
    renamed_parameters_match(&["A", "a", "x", "zz"]);
}

/// [`pncx_renamed_parameters_and_case56_match`] over the names `names`.
pub(super) fn renamed_parameters_match(names: &[&str]) {
    let condition = "x >= (0 - 8) && x <= 26 && (x + 1) mod 10 <= 1 && (x - 5) mod 4 <= 1 && ((x - 5) mod 4 == 2 || (x - 5) mod 4 == 1 || x <= 12) && ((x + 1) mod 10 != 5 || x mod 8 != 7)";
    let mut sources = Vec::new();
    for &x in names {
        let condition = condition.replace('x', x);
        sources.push(format!("p{}({x}: int) = {condition};", sources.len()));
        for &alias in names {
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
