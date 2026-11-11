//! PERF-negated-chain-xr probe, not committed: times each question of chain 8 of
//! `one_scope::no_question_of_a_random_chain_with_negations_is_refused_where_its_relation_is_decided`.

use std::time::Instant;

use zed_kernel::{Shared, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zedc::elab::Unit;
use zedc::interp::prelude;
use zedc::store::preimage::Scoped;
use zedc::store::presburger::extend::Extending;

fn lets(unit: &Unit) -> Term {
    prelude(unit.defs.iter().rev().fold(Term::Lit(Value::Bool(true)), |body, d| {
        Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
    }))
}

fn run(src: &str, reps: usize) {
    let unit = elab(src).unwrap();
    let lets = lets(&unit);
    let fs: Vec<_> = unit
        .defs
        .iter()
        .filter_map(|d| match &*d.term {
            Term::Lam(ps, body) => Some((d.name.as_str(), ps.as_slice(), &**body)),
            _ => None,
        })
        .collect();
    let orders: Vec<Vec<usize>> = match std::env::var("PNC_ORDER").as_deref() {
        Ok("rev") => vec![(0..fs.len()).rev().collect()],
        Ok("fwd") => vec![(0..fs.len()).collect()],
        _ => vec![(0..fs.len()).collect(), (0..fs.len()).rev().collect()],
    };
    for _ in 0..reps {
        for order in &orders {
            let mut scoped = Scoped::new(&lets);
            let (mut faced, mut plain) = (Extending::new(), Extending::new());
            for &i in order {
                let (name, ps, body) = fs[i];
                let Some(r) = scoped.relation(body, ps, ps, true) else { continue };
                let t = Instant::now();
                let a = faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
                let ta = t.elapsed();
                let t = Instant::now();
                let b = plain.defined(&r, &|n| scoped.def(n));
                let tb = t.elapsed();
                println!(
                    "PNC {name} faced {:.4}s plain {:.4}s holds {:?}/{:?} fails {:?}/{:?}",
                    ta.as_secs_f64(),
                    tb.as_secs_f64(),
                    a.holds.as_ref().map_err(|_| "refused"),
                    b.holds.as_ref().map_err(|_| "refused"),
                    a.fails.as_ref().map_err(|_| "refused"),
                    b.fails.as_ref().map_err(|_| "refused"),
                );
            }
        }
    }
}

const CHAIN8: &str = include_str!("pncx_chain8.zed");

#[test]
#[ignore]
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

/// Prints the record of the check of the modular solver's empty answers; asserts none wrong.
fn report(c: &zedc::store::presburger::EmptyCheck) {
    for w in &c.wrong {
        println!("EMPTYWRONG {w}");
    }
    println!(
        "EMPTYCHECK agreed {} wrong {} refused {}",
        c.agreed,
        c.wrong.len(),
        c.refused.len()
    );
    assert!(c.wrong.is_empty());
}

fn lit(n: i64) -> String {
    match n < 0 {
        true => format!("(0 - {})", -n),
        false => n.to_string(),
    }
}

const MODS: [i64; 16] = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 25, 27];

fn modulus(rng: &mut zed_tests::instances::Rng) -> i64 {
    MODS[rng.below(MODS.len())]
}

fn case(rng: &mut zed_tests::instances::Rng) -> String {
    let m = modulus(rng);
    match rng.below(5) {
        0 => format!("x mod {m} == {}", rng.int(0, m)),
        1 => format!("x mod {m} != {}", rng.int(0, m - 1)),
        2 => format!("x < {}", lit(rng.int(-40, 120))),
        3 => format!("x > {}", lit(rng.int(-40, 120))),
        _ => format!("!(x mod {m} == {} && x > {})", rng.int(0, m - 1), lit(rng.int(-40, 120))),
    }
}

/// A random chain of the shape of `random_negated_chain`, with more moduli (primes, prime
/// powers, composites) and bounds that may be negative.
fn chain(rng: &mut zed_tests::instances::Rng) -> String {
    let a = rng.int(-60, 60);
    let b = a + rng.int(-2, 160);
    let q = format!("{} && ({} || {}) && ({} || {})", case(rng), case(rng), case(rng), case(rng), case(rng));
    let mut src = format!(
        "q(x: int) = {q} && x > {} && x < {};\np0(x: int) = x > {};\n",
        lit(a),
        lit(b),
        lit(rng.int(-80, 80)),
    );
    for i in 1..rng.int(2, 12) {
        let own = match rng.below(3) {
            0 => format!(" && {}", case(rng)),
            1 => format!(" && ({} || {})", case(rng), case(rng)),
            _ => String::new(),
        };
        src.push_str(&format!(
            "p{i}(x: int) = q(x: x) && p{}(x: x + {}) && x < {}{own};\n",
            i - 1,
            lit(rng.int(-7, 7)),
            lit(rng.int(-60, 300)),
        ));
    }
    src
}

fn enumerated(w: &zedc::store::presburger::Relation) -> Option<(bool, bool)> {
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Rel, satisfiable};
    let syms: Vec<Atom> = (w.body.atoms().into_iter())
        .chain(w.defined().atoms())
        .filter(|a| matches!(a, Atom::Sym(_)))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    let [x] = &syms[..] else { return None };
    let (mut lo, mut hi) = (None::<i64>, None::<i64>);
    let mut top = vec![&w.body];
    while let Some(p) = top.pop() {
        if let Formula::And(parts) = p {
            top.extend(parts.iter());
            continue;
        }
        let Formula::Con(c) = p else { continue };
        let k = c.lin.terms.get(x).map(|k| i64::try_from(k.to_i128().unwrap()).unwrap());
        let b = i64::try_from(c.lin.constant.to_i128().unwrap()).unwrap();
        match (c.rel, c.lin.terms.len(), k) {
            (Rel::Ge, 1, Some(1)) => lo = Some(lo.map_or(-b, |l| l.max(-b))),
            (Rel::Ge, 1, Some(-1)) => hi = Some(hi.map_or(b, |h| h.min(b))),
            _ => {}
        }
    }
    let (lo, hi) = (lo?, hi?);
    let defined = w.defined();
    let (mut holds, mut fails) = (false, false);
    for v in lo.min(hi + 1)..=hi + 1 {
        let fixed = Formula::Con(Con::eq(&Lin::atom(x.clone()), &Lin::constant(v)));
        let m = satisfiable(&Formula::and(vec![defined.clone(), fixed.clone()])).ok()??;
        let b = w.body.holds(&m);
        (holds, fails) = (holds || b, fails || !b);
    }
    Some((holds, fails))
}

/// PNCX_SEEDS=a..b: random chains; each answer, faced and plain, in both orders, against
/// points. Prints one line per question and MISMATCH lines.
#[test]
#[ignore]
fn pncx_random() {
    let seeds = std::env::var("PNCX_SEEDS").unwrap_or_else(|_| "0..20".into());
    let (a, b) = seeds.split_once("..").unwrap();
    let (a, b): (u64, u64) = (a.parse().unwrap(), b.parse().unwrap());
    let (mut refused, mut answered, mut bad) = (0, 0, 0);
    let check = std::env::var_os("PNCX_CHECK").is_some();
    let ((), c) = zedc::store::presburger::with_modular_empty_checked(|| {
    for seed in a..b {
        let mut rng = zed_tests::instances::Rng::new(seed);
        let src = chain(&mut rng);
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
        for (o, order) in [(0..fs.len()).collect::<Vec<_>>(), (0..fs.len()).rev().collect()]
            .into_iter()
            .enumerate()
        {
            let mut scoped = Scoped::new(&lets);
            let (mut faced, mut plain) = (Extending::new(), Extending::new());
            for i in order {
                let (name, ps, body) = fs[i];
                let Some(r) = scoped.relation(body, ps, ps, true) else { continue };
                let t = Instant::now();
                let mut ask = || {
                    let x = faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
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

fn primes(n: usize) -> Vec<i64> {
    let mut ps = Vec::new();
    let mut k = 2i64;
    while ps.len() < n {
        if ps.iter().all(|p| k % p != 0) {
            ps.push(k);
        }
        k += 1;
    }
    ps
}

/// `2^n + d` in decimal, for `n >= 1` and `d` in -1..=1 (the last digit of `2^n` is 2, 4, 6
/// or 8).
fn pow2(n: usize, d: i8) -> String {
    let mut digits = vec![1u8];
    for _ in 0..n {
        let mut carry = 0;
        for x in &mut digits {
            let v = *x * 2 + carry;
            (*x, carry) = (v % 10, v / 10);
        }
        if carry > 0 {
            digits.push(carry);
        }
    }
    digits[0] = (digits[0] as i8 + d) as u8;
    digits.iter().rev().map(|x| char::from(b'0' + x)).collect()
}

/// The source of size `n` on axis `axis`.
fn axis_src(axis: &str, n: usize) -> String {
    let ps = primes(2 * n + 8);
    match axis {
        // Links of the negated modular chain of one_scope.
        "links" => {
            let mut src = String::from(
                "q(x: int) = !(x mod 3 == 2 && x > 11) && (x mod 4 == 1 || x > (0 - 5)) && x > 0 && x < 1000000;\n\
                 p0(x: int) = x > (0 - 4);\n",
            );
            for i in 1..n {
                let shift = ["(0 - 1)", "60", "(0 - 2)", "3"][i % 4];
                let extra = match i % 3 { 0 => " && !(x mod 5 == 2 && x > 49)", 1 => " && (x mod 7 != 3 || x < 20)", _ => "" };
                src.push_str(&format!("p{i}(x: int) = q(x: x) && p{}(x: x + {shift}) && x < {}{extra};\n", i - 1, 2000 + 1000 * i));
            }
            src
        }
        // Distinct coprime moduli, one excluded residue each.
        "moduli" => {
            let lits: Vec<String> = ps[..n].iter().map(|p| format!("x mod {p} != 1")).collect();
            format!("q(x: int) = {} && x > 0 && x < 1000000000;\n", lits.join(" && "))
        }
        // Primes in one disjunction.
        "disj" => {
            let lits: Vec<String> = ps[..n].iter().map(|p| format!("x mod {p} == 0")).collect();
            format!("q(x: int) = ({}) && x mod 2 == 1 && x > 0 && x < 1000000000;\n", lits.join(" || "))
        }
        // Easy pairs over distinct primes.
        "pairs" => {
            let lits: Vec<String> = (0..n)
                .map(|i| {
                    let (a, b) = (ps[2 * i + 1], ps[2 * i + 2]);
                    format!("(x mod {a} == 0 || x mod {b} == 0) && (x mod {a} == 1 || x mod {b} == 1)")
                })
                .collect();
            format!("q(x: int) = {};\n", lits.join(" && "))
        }
        // Clauses with distinct bounds: n regimes.
        "regimes" => {
            let lits: Vec<String> = (0..n)
                .map(|i| format!("!(x mod {} == {} && x > {})", ps[1 + i % 4], i % 3, 100 * (i + 1)))
                .collect();
            format!("q(x: int) = {} && x > 0 && x < 100000000;\n", lits.join(" && "))
        }
        // Two-modulus clauses with distinct bounds: n real regimes.
        "regimes2" => {
            let lits: Vec<String> = (0..n)
                .map(|i| format!("(x mod 5 == {} || x mod 7 == {} || x < {})", i % 5, (i / 5) % 7, 100 * (i + 1)))
                .collect();
            format!("q(x: int) = {} && x > 0 && x < 100000000;\n", lits.join(" && "))
        }
        // Nested cutting: level j excludes the residue w / 2^j modulo w / 2^(j-1) + 1, and three
        // clauses over 5 and 7 that hold nowhere.
        "nest" => {
            let w: i128 = 10 << n;
            let mut lits: Vec<String> = (1..=n)
                .map(|j| format!("x mod {} != {}", (w >> (j - 1)) + 1, w >> j))
                .collect();
            lits.push("(x mod 5 == 0 || x mod 7 == 0) && (x mod 5 == 1 || x mod 7 == 1) && (x mod 5 == 2 || x mod 7 == 2)".into());
            format!("q(x: int) = {} && x >= 0 && x <= {w};\n", lits.join(" && "))
        }
        // Two-modulus clauses that hold only above their bounds, with three clauses over 11
        // and 13 that hold nowhere below the top bound: every regime is walked.
        "regimes3" => {
            let mut lits: Vec<String> = (0..n)
                .map(|i| format!("(x mod 31 == {} || x mod 37 == {} || x > {})", i % 31, (i / 31) % 37, 100 * (i + 1)))
                .collect();
            for r in 0..3 {
                lits.push(format!("(x mod 11 == {r} || x mod 13 == {r} || x > {})", 100 * (n + 1)));
            }
            format!("q(x: int) = {} && x > 0 && x < 100000000;\n", lits.join(" && "))
        }
        // Bits of the bounds (n bits), fixed formula.
        "boundbits" => {
            let b = pow2(n, 0);
            format!(
                "q(x: int) = !(x mod 3 == 2 && x > 11) && (x mod 5 != 0 || x mod 7 != 0) && x mod 4 != 3 && x > 0 && x < {b};\n"
            )
        }
        // Bits of the moduli (n bits).
        "modbits" => {
            let (m1, m2) = (pow2(n, 1), pow2(n, -1));
            format!(
                "q(x: int) = x mod {m1} != 0 && (x mod {m2} != 1 || x mod 3 != 0) && x mod 5 == 2 && x > 0 && x < 1000000000;\n"
            )
        }
        _ => panic!("axis {axis}"),
    }
}

#[test]
#[ignore]
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

// From Codex's round-2 probe (library/r2-codex-pncx_probe.rs).
fn pncx_formula(axis: &str, n: usize) -> zedc::store::presburger::Formula {
    use std::sync::Arc;
    use zedc::store::int::Int;
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    let x = Lin::atom(Atom::Sym(Arc::from("x")));
    let mut fs = Vec::new();
    let mut primes = Vec::new();
    let mut p = 2i64;
    while primes.len() < 2 * n.max(1) {
        if (2..).take_while(|d| d * d <= p).all(|d| p % d != 0) {
            primes.push(p);
        }
        p += 1;
    }
    let count = match axis {
        "bounds" | "bits" => 1,
        "pairs" => 2 * n,
        _ => n,
    };
    let big = (0..n).fold(Int::ONE, |a, _| &a * &Int::from(2));
    let mut rs = Vec::new();
    for i in 0..count {
        let q = Lin::atom(Atom::Aux((2 * i) as u32));
        let r = Lin::atom(Atom::Aux((2 * i + 1) as u32));
        let m = if axis == "bits" {
            &big + &Int::ONE
        } else {
            Int::from(if axis == "links" { 5 } else { primes[i] })
        };
        let y = if axis == "links" {
            let y = Lin::atom(Atom::Sym(Arc::from(format!("x{i}"))));
            fs.push(Formula::Con(Con::eq(
                &y,
                &x.plus(&Lin::constant((i % 5) as i64)),
            )));
            y
        } else {
            x.clone()
        };
        fs.push(Formula::Con(Con::eq(
            &y.minus(&q.times(m.clone())).minus(&r),
            &Lin::constant(0),
        )));
        fs.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
        fs.push(Formula::Con(Con::ge(&Lin::constant(&m - &Int::ONE), &r)));
        rs.push(r);
    }
    if axis == "or" {
        fs.push(Formula::or(
            rs.iter()
                .map(|r| Formula::Con(Con::eq(r, &Lin::constant(1))))
                .collect(),
        ));
    } else if axis == "pairs" {
        for pair in rs.chunks(2) {
            for v in [0, 1] {
                fs.push(Formula::or(
                    pair.iter()
                        .map(|r| Formula::Con(Con::eq(r, &Lin::constant(v))))
                        .collect(),
                ));
            }
        }
    } else {
        for r in &rs {
            fs.push(Formula::negate(Formula::Con(Con::eq(r, &Lin::constant(0)))));
        }
    }
    if axis == "bounds" {
        fs.push(Formula::Con(Con::ge(&x, &Lin::constant(big.clone()))));
        fs.push(Formula::Con(Con::ge(
            &Lin::constant(&big + &Int::from(17)),
            &x,
        )));
    } else {
        fs.push(Formula::Con(Con::ge(&x, &Lin::constant(1))));
    }
    Formula::and(fs)
}

#[test]
#[ignore]
fn pncx_six_axis() {
    use zed_tests::scaling::Meter;
    use zedc::store::presburger::satisfiable;
    let axis = std::env::var("PNCX_AXIS").unwrap();
    let n: usize = std::env::var("PNCX_N").unwrap().parse().unwrap();
    let f = pncx_formula(&axis, n);
    let mut meter = Meter::new();
    let mut ans = None;
    let w = meter.work(|| {
        ans = Some(satisfiable(&f));
    });
    println!(
        "AXIS {axis} n={n} work={} bytes={} unit={} answer={:?}",
        w.units,
        w.bytes,
        meter.unit(),
        ans.as_ref().unwrap().as_ref().map(|m| m.is_some())
    );
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
#[ignore]
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
