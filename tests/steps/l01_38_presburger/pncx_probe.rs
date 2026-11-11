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
    prelude(
        unit.defs
            .iter()
            .rev()
            .fold(Term::Lit(Value::Bool(true)), |body, d| {
                Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
            }),
    )
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
                let Some(r) = scoped.relation(body, ps, ps, true) else {
                    continue;
                };
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
        _ => format!(
            "!(x mod {m} == {} && x > {})",
            rng.int(0, m - 1),
            lit(rng.int(-40, 120))
        ),
    }
}

/// A random chain of the shape of `random_negated_chain`, with more moduli (primes, prime
/// powers, composites) and bounds that may be negative.
fn chain(rng: &mut zed_tests::instances::Rng) -> String {
    let a = rng.int(-60, 60);
    let b = a + rng.int(-2, 160);
    let q = format!(
        "{} && ({} || {}) && ({} || {})",
        case(rng),
        case(rng),
        case(rng),
        case(rng),
        case(rng)
    );
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
        let k = c
            .lin
            .terms
            .get(x)
            .map(|k| i64::try_from(k.to_i128().unwrap()).unwrap());
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
        // Every integer in [0,n) has one impossible active clause. All
        // unrelated unit domains hold throughout that interval. This forces
        // a separate contradiction at each leaf of the regime walk (I3.3).
        "regimes-empty" => {
            let ps: Vec<_> = primes(3 * n + 8)
                .into_iter()
                .filter(|p| *p > n as i64 + 2)
                .take(n)
                .collect();
            assert_eq!(ps.len(), n);
            let mut lits = Vec::new();
            for (i, p) in ps.into_iter().enumerate() {
                lits.push(format!("x mod {p} < {}", p - 1));
                lits.push(format!("(x mod {p} == {} || x < {i} || x > {i})", p - 1));
            }
            format!("q(x: int) = {} && x >= 0 && x < {n};\n", lits.join(" && "))
        }
        // Links of the negated modular chain of one_scope.
        "links" => {
            let mut src = String::from(
                "q(x: int) = !(x mod 3 == 2 && x > 11) && (x mod 4 == 1 || x > (0 - 5)) && x > 0 && x < 1000000;\n\
                 p0(x: int) = x > (0 - 4);\n",
            );
            for i in 1..n {
                let shift = ["(0 - 1)", "60", "(0 - 2)", "3"][i % 4];
                let extra = match i % 3 {
                    0 => " && !(x mod 5 == 2 && x > 49)",
                    1 => " && (x mod 7 != 3 || x < 20)",
                    _ => "",
                };
                src.push_str(&format!(
                    "p{i}(x: int) = q(x: x) && p{}(x: x + {shift}) && x < {}{extra};\n",
                    i - 1,
                    2000 + 1000 * i
                ));
            }
            src
        }
        // Distinct coprime moduli, one excluded residue each.
        "moduli" => {
            let lits: Vec<String> = ps[..n].iter().map(|p| format!("x mod {p} != 1")).collect();
            format!(
                "q(x: int) = {} && x > 0 && x < 1000000000;\n",
                lits.join(" && ")
            )
        }
        // Primes in one disjunction.
        "disj" => {
            let lits: Vec<String> = ps[..n].iter().map(|p| format!("x mod {p} == 0")).collect();
            format!(
                "q(x: int) = ({}) && x mod 2 == 1 && x > 0 && x < 1000000000;\n",
                lits.join(" || ")
            )
        }
        // Easy pairs over distinct primes.
        "pairs" => {
            let lits: Vec<String> = (0..n)
                .map(|i| {
                    let (a, b) = (ps[2 * i + 1], ps[2 * i + 2]);
                    format!(
                        "(x mod {a} == 0 || x mod {b} == 0) && (x mod {a} == 1 || x mod {b} == 1)"
                    )
                })
                .collect();
            format!("q(x: int) = {};\n", lits.join(" && "))
        }
        // Clauses with distinct bounds: n regimes.
        "regimes" => {
            let lits: Vec<String> = (0..n)
                .map(|i| {
                    format!(
                        "!(x mod {} == {} && x > {})",
                        ps[1 + i % 4],
                        i % 3,
                        100 * (i + 1)
                    )
                })
                .collect();
            format!(
                "q(x: int) = {} && x > 0 && x < 100000000;\n",
                lits.join(" && ")
            )
        }
        // Two-modulus clauses with distinct bounds: n real regimes.
        "regimes2" => {
            let lits: Vec<String> = (0..n)
                .map(|i| {
                    format!(
                        "(x mod 5 == {} || x mod 7 == {} || x < {})",
                        i % 5,
                        (i / 5) % 7,
                        100 * (i + 1)
                    )
                })
                .collect();
            format!(
                "q(x: int) = {} && x > 0 && x < 100000000;\n",
                lits.join(" && ")
            )
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
        // `regimes-offset` and `regimes-wide` are Codex's round-3 axes (PEER_R3_CODEX.diff):
        // the three closing clauses have distinct bounds, and in `regimes-wide` the moduli grow
        // with n.
        "regimes3" | "regimes-offset" => {
            let mut lits: Vec<String> = (0..n)
                .map(|i| {
                    format!(
                        "(x mod 31 == {} || x mod 37 == {} || x > {})",
                        i % 31,
                        (i / 31) % 37,
                        100 * (i + 1)
                    )
                })
                .collect();
            for r in 0..3 {
                let off = if axis == "regimes-offset" { r } else { 0 };
                lits.push(format!(
                    "(x mod 11 == {r} || x mod 13 == {r} || x > {})",
                    100 * (n + 1) + off
                ));
            }
            format!(
                "q(x: int) = {} && x > 0 && x < 100000000;\n",
                lits.join(" && ")
            )
        }
        "regimes-wide" => {
            let m = (2 * n + 1).next_power_of_two();
            let mut lits: Vec<String> = (0..n)
                .map(|i| {
                    format!(
                        "(x mod {m} == {i} || x mod {} == {i} || x > {})",
                        m + 1,
                        100 * (i + 1)
                    )
                })
                .collect();
            for r in 0..3 {
                lits.push(format!(
                    "(x mod 11 == {r} || x mod 13 == {r} || x > {})",
                    100 * (n + 1) + r
                ));
            }
            format!(
                "q(x: int) = {} && x > 0 && x < {};\n",
                lits.join(" && "),
                100 * (n + 2)
            )
        }
        // The walk's bad case (T4): n contiguous segments of 50, each empty for its own reason
        // (`x mod 4 == 1` and `x mod 6 == 2` on it), and n global residues `x mod p != 0`, so
        // every node of the tree has a point under the global constraints and is descended.
        "walkrn" => {
            let mut lits: Vec<String> = (0..n)
                .map(|j| {
                    let (a, b) = (50 * j + 1, 50 * j + 50);
                    format!("(x mod 4 == 1 || x < {a} || x > {b}) && (x mod 6 == 2 || x < {a} || x > {b})")
                })
                .collect();
            lits.extend((0..n).map(|i| format!("x mod {} != 0", ps[2 + i])));
            format!(
                "q(x: int) = {} && x >= 1 && x <= {};\n",
                lits.join(" && "),
                50 * n
            )
        }
        // As `walkrn`, with the n global constraints two-literal clauses with no bounds, which
        // sit on the root of the walk's tree and so are in every node's solve.
        "walkrn2" => {
            let mut lits: Vec<String> = (0..n)
                .map(|j| {
                    let (a, b) = (50 * j + 1, 50 * j + 50);
                    format!("(x mod 4 == 1 || x < {a} || x > {b}) && (x mod 6 == 2 || x < {a} || x > {b})")
                })
                .collect();
            lits.extend((0..n).map(|i| {
                format!(
                    "(x mod {} == 1 || x mod {} == 1)",
                    ps[2 + 2 * i],
                    ps[3 + 2 * i]
                )
            }));
            format!(
                "q(x: int) = {} && x >= 1 && x <= {};\n",
                lits.join(" && "),
                50 * n
            )
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
        "crtbits" => 8,
        _ => n,
    };
    let big = (0..n).fold(Int::ONE, |a, _| &a * &Int::from(2));
    // `crtbits`: `m_i = 840 2^n (i + 1) + 1` for `i < 8`, pairwise coprime since a common
    // factor of two of them divides `840 2^n (i - j)` and is coprime to `840 2^n`.
    let wide = &big * &Int::from(840);
    let mut rs = Vec::new();
    for i in 0..count {
        let q = Lin::atom(Atom::Aux((2 * i) as u32));
        let r = Lin::atom(Atom::Aux((2 * i + 1) as u32));
        let m = if axis == "bits" {
            &big + &Int::ONE
        } else if axis == "crtbits" {
            &(&wide * &Int::from(i as i64 + 1)) + &Int::ONE
        } else if axis == "crtshared" {
            // `m_i = 2 p_{i+1}`: every pair shares the factor 2.
            Int::from(2 * primes[i + 1])
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
    } else if axis == "crtshared" {
        // Odd residues `2 i + 3`, consistent modulo 2, distinct otherwise.
        for (i, r) in rs.iter().enumerate() {
            fs.push(Formula::Con(Con::eq(
                r,
                &Lin::constant((2 * i as i64 + 3) % (2 * primes[i + 1])),
            )));
        }
    } else if axis == "crt" || axis == "crtbits" {
        // One residue fixed per modulus, `i + 2` (below each modulus): one CRT over all of
        // them, and `x = 1` is not a point.
        for (i, r) in rs.iter().enumerate() {
            let c = if axis == "crt" {
                (i as i64 + 2) % primes[i]
            } else {
                i as i64 + 2
            };
            fs.push(Formula::Con(Con::eq(r, &Lin::constant(c))));
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

fn pncx_sat_residue(primes: &[i64], cl: &[(usize, bool); 3]) -> (i64, i64) {
    let m: i64 = cl.iter().map(|(j, _)| primes[*j]).product();
    // The falsifying value of each literal: 0 for a positive literal, 1 for a negative one.
    // Complexity tradeoff: enumerating 0..m to build a CRT residue costs
    // O(m), exponential in the written modulus bits, before the timed call.
    // Three Euclidean inverses construct the same residue in O(log m)
    // word operations. Nothing is given up. Test: pncx_sat_crt_construction_scale.
    let mut c = 0i128;
    for &(j, pos) in cl {
        let p = i128::from(primes[j]);
        let part = i128::from(m) / p;
        let (mut r, mut next) = (p, part.rem_euclid(p));
        let (mut u, mut nu) = (0i128, 1i128);
        while next != 0 {
            let q = r / next;
            (r, next) = (next, r - q * next);
            (u, nu) = (nu, u - q * nu);
        }
        c = (c + part * u.rem_euclid(p) * i128::from(!pos)).rem_euclid(i128::from(m));
    }
    let c = i64::try_from(c).unwrap();
    assert!(
        cl.iter()
            .all(|(j, pos)| c % primes[*j] == if *pos { 0 } else { 1 })
    );
    (m, c)
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

/// 3-SAT as one-variable residue constraints (the reduction of Garey and Johnson AN2): variable
/// `j` is `x mod p_j` in `{0, 1}` for the `j`-th prime `p_j`; a clause excludes the one residue
/// modulo the product of its three primes at which all three literals are false. `x` is bounded
/// to `0..P` for `P` the product of all the primes. `PNCX_SAT_RANDOM=v,c,seed` builds `c` random
/// clauses over `v` variables; each line prints `decide` and, for at most 7 variables
/// (`P <= 510510`), the truth by enumeration over `0..P`.
#[test]
#[ignore]
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
            "ok(x:int)={};\nmain(m:MainArgs) {{ a=int(m.stdin[1] else \"0\") else 0; r=if ok(x:a) {{ \"in\" }} else {{ \"out\" }}; m.stdout <- \"${{r}}\"; }}\n",
            conditions.join(" && ")
        );
        std::fs::write(path, source).expect("probe source file");
    }
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

// Consecutive Fibonacci moduli force Euclid's long quotient sequence. Both
// residue requirements are needed; x = 0 or 1 cannot witness the formula.
fn pncx_crt_bits(n: usize) -> zedc::store::presburger::Formula {
    use zedc::store::int::Int;
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    // `(F(k), F(k + 1))` by doubling: `F(2k) = F(k) (2 F(k + 1) - F(k))`,
    // `F(2k + 1) = F(k)^2 + F(k + 1)^2`; `a = F(n + 1)`, `b = F(n + 2)`.
    let (mut a, mut b) = (Int::ZERO, Int::ONE);
    let k = n + 1;
    for i in (0..usize::BITS - k.leading_zeros()).rev() {
        let two_b = &b + &b;
        let c = &a * &(&two_b - &a);
        let d = &(&a * &a) + &(&b * &b);
        (a, b) = match (k >> i) & 1 {
            1 => (d.clone(), &c + &d),
            _ => (c, d),
        };
    }
    let x = Lin::atom(Atom::Sym("x".into()));
    let mut fs = vec![Formula::Con(Con::ge(&x, &Lin::constant(0)))];
    for (i, (m, d)) in [(a, 1), (b, 2)].into_iter().enumerate() {
        let q = Lin::atom(Atom::Aux(i as u32));
        fs.push(Formula::Con(Con::eq(
            &x.minus(&q.times(m.clone())),
            &Lin::constant(&m - &Int::from(d)),
        )));
    }
    Formula::and(fs)
}

#[test]
#[ignore]
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
#[test]
#[ignore]
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

/// Two consecutive Fibonacci moduli, the slowest case of the Euclidean extended gcd: the whole
/// question costs at most 10 times the kernel's gcd of the same two moduli, at F(80001) (55,540
/// bits) and F(750001) (520,682 bits). Measured 5.8 and 6.5 times with the half gcd; 190 times
/// at F(80001) with the Euclidean `bezout` (R6-CLAUDE-7). `check_log_squared` cannot hold it:
/// the kernel's gcd alone on these numbers grows 17.5 times in instructions and 13.9 times in
/// bytes from F(750001) to F(6000001), above the 11.7 that rule allows. Ignored for its time,
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
#[ignore]
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

fn pncx_front_scale(axis: &str) {
    let inputs = zed_tests::scaling::inputs(512, |n| {
        let src = axis_src(axis, n);
        let stmts = zed_tests::deep::statements(&src);
        let tokens = zedc::lex::lex_fence(&src).unwrap();
        let unit = elab(&src).unwrap();
        (src, stmts, tokens, unit)
    });
    zed_tests::scaling::check_order(axis, 512, 1, |n| {
        let (src, stmts, tokens, unit) = &inputs[&n];
        assert!(zedc::front::linear_questions(src, tokens, stmts, unit).is_empty());
    });
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
#[ignore]
fn pncx_t8_enum_suite() {
    use std::sync::Arc;
    use zedc::store::int::Int;
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, decide, satisfiable};
    let negctl = std::env::var_os("PNCX_ENUM_NEGCTL").is_some();
    let mut rng = zed_tests::instances::Rng::new(0x3141_5926);
    let mut total_checked = 0usize;
    let mut total_sat = 0usize;
    let mut total_unsat = 0usize;
    let mut total_refused = 0usize;

    // Family 1 (1,200 formulas): generalized `sign12` / prime-power / composite shifted remainder
    // systems (`(x + s1) mod m1 <= w1 && ((x - c) mod m2 == r1 || (x - c) mod m2 == r2)`):
    let m_pool = [
        4i64, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 36,
    ];
    for idx in 0..1200usize {
        let m1 = m_pool[rng.below(m_pool.len())];
        let m2 = m_pool[rng.below(m_pool.len())];
        let s1 = rng.int(-15, 15);
        let c2 = rng.int(-15, 15);
        let w1 = rng.int(0, (m1 - 1).min(5));
        let r2a = rng.int(0, m2 - 1);
        let r2b = rng.int(0, m2 - 1);
        let base_lo = match idx % 4 {
            0 => 10_020 + rng.int(0, 20),
            1 => -500 + rng.int(0, 40),
            2 => -15 + rng.int(0, 30),
            _ => rng.int(0, 200),
        };
        let hi = base_lo + rng.int(0, 90);
        let x0 = Atom::Sym(Arc::from("x"));
        let x = Lin::atom(x0.clone());
        let q0 = Atom::Aux(0);
        let r0 = Atom::Aux(1);
        let q1 = Atom::Aux(2);
        let r1 = Atom::Aux(3);
        let fs = vec![
            Formula::Con(Con::ge(&x, &Lin::constant(base_lo))),
            Formula::Con(Con::ge(&Lin::constant(hi), &x)),
            Formula::Con(Con::eq(
                &x.plus(&Lin::constant(s1))
                    .minus(&Lin::atom(q0.clone()).times(m1))
                    .minus(&Lin::atom(r0.clone())),
                &Lin::constant(0),
            )),
            Formula::Con(Con::ge(&Lin::atom(r0.clone()), &Lin::constant(0))),
            Formula::Con(Con::ge(&Lin::constant(m1 - 1), &Lin::atom(r0.clone()))),
            Formula::Con(Con::ge(&Lin::constant(w1), &Lin::atom(r0.clone()))),
            Formula::Con(Con::eq(
                &x.plus(&Lin::constant(-c2))
                    .minus(&Lin::atom(q1.clone()).times(m2))
                    .minus(&Lin::atom(r1.clone())),
                &Lin::constant(0),
            )),
            Formula::Con(Con::ge(&Lin::atom(r1.clone()), &Lin::constant(0))),
            Formula::Con(Con::ge(&Lin::constant(m2 - 1), &Lin::atom(r1.clone()))),
            Formula::or(vec![
                Formula::Con(Con::eq(&Lin::atom(r1.clone()), &Lin::constant(r2a))),
                Formula::Con(Con::eq(&Lin::atom(r1.clone()), &Lin::constant(r2b))),
            ]),
        ];
        let f = Formula::and(fs);
        let brute = (base_lo..=hi).any(|xv| {
            (xv + s1).rem_euclid(m1) <= w1
                && ((xv - c2).rem_euclid(m2) == r2a || (xv - c2).rem_euclid(m2) == r2b)
        });
        let (Ok(mut dec), Ok(sat)) = (decide(&f), satisfiable(&f)) else {
            total_refused += 1;
            continue;
        };
        if negctl && idx == 17 {
            dec = !dec;
        }
        assert_eq!(
            dec, brute,
            "sign12-family idx={idx}: dec={dec} brute={brute}\n{f}"
        );
        assert_eq!(sat.is_some(), brute, "sign12-family sat idx={idx}");
        if let Some(ref m) = sat {
            assert!(f.holds(m), "sign12-family model invalid idx={idx}");
            total_sat += 1;
        } else {
            total_unsat += 1;
        }
        total_checked += 1;
    }

    // Family 2 (1,200 formulas): `R2_CLAUDE` regimes3 + prime-power p-adic hierarchies (`2,4,8,16`, `3,9,27`, `5,25`):
    let pp_pool = [2i64, 4, 8, 16, 3, 9, 27, 5, 25, 6, 12, 18];
    for idx in 0..1200usize {
        let lo = rng.int(-80, 120);
        let hi = lo + rng.int(0, 140);
        let x0 = Atom::Sym(Arc::from("x"));
        let x = Lin::atom(x0.clone());
        let mut fs = vec![
            Formula::Con(Con::ge(&x, &Lin::constant(lo))),
            Formula::Con(Con::ge(&Lin::constant(hi), &x)),
        ];
        let k_divs = 3 + rng.below(3);
        let mut divs = Vec::new();
        for d in 0..k_divs {
            let m = pp_pool[rng.below(pp_pool.len())];
            let sh = rng.int(-6, 6);
            let qa = Atom::Aux((2 * d) as u32);
            let ra = Atom::Aux((2 * d + 1) as u32);
            fs.push(Formula::Con(Con::eq(
                &x.plus(&Lin::constant(sh))
                    .minus(&Lin::atom(qa.clone()).times(m))
                    .minus(&Lin::atom(ra.clone())),
                &Lin::constant(0),
            )));
            fs.push(Formula::Con(Con::ge(
                &Lin::atom(ra.clone()),
                &Lin::constant(0),
            )));
            fs.push(Formula::Con(Con::ge(
                &Lin::constant(m - 1),
                &Lin::atom(ra.clone()),
            )));
            divs.push((qa, ra, m, sh));
        }
        let n_cls = 2 + rng.below(5);
        for _ in 0..n_cls {
            let (_, ref ra1, m1, _) = divs[rng.below(divs.len())];
            let (_, ref ra2, m2, _) = divs[rng.below(divs.len())];
            let cut = lo + rng.int(-5, 145);
            let r1 = rng.int(0, m1 - 1);
            let r2 = rng.int(0, m2 - 1);
            let l1 = if rng.below(2) == 0 {
                Formula::Con(Con::eq(&Lin::atom(ra1.clone()), &Lin::constant(r1)))
            } else {
                Formula::negate(Formula::Con(Con::eq(
                    &Lin::atom(ra1.clone()),
                    &Lin::constant(r1),
                )))
            };
            let l2 = if rng.below(2) == 0 {
                Formula::Con(Con::eq(&Lin::atom(ra2.clone()), &Lin::constant(r2)))
            } else {
                Formula::negate(Formula::Con(Con::eq(
                    &Lin::atom(ra2.clone()),
                    &Lin::constant(r2),
                )))
            };
            let l3 = if rng.below(2) == 0 {
                Formula::Con(Con::ge(&x, &Lin::constant(cut)))
            } else {
                Formula::Con(Con::ge(&Lin::constant(cut), &x))
            };
            fs.push(Formula::or(vec![l1, l2, l3]));
        }
        let f = Formula::and(fs);
        let brute = (lo..=hi).any(|xv| {
            let mut m = Model::from([(x0.clone(), Int::from(xv))]);
            for (qa, ra, mod_m, sh) in &divs {
                m.insert(qa.clone(), Int::from((xv + *sh).div_euclid(*mod_m)));
                m.insert(ra.clone(), Int::from((xv + *sh).rem_euclid(*mod_m)));
            }
            f.holds(&m)
        });
        let (Ok(dec), Ok(sat)) = (decide(&f), satisfiable(&f)) else {
            total_refused += 1;
            continue;
        };
        assert_eq!(
            dec, brute,
            "padic-regimes3 idx={idx}: dec={dec} brute={brute}\n{f}"
        );
        assert_eq!(sat.is_some(), brute, "padic-regimes3 sat idx={idx}");
        if let Some(ref m) = sat {
            assert!(f.holds(m), "padic-regimes3 model invalid idx={idx}");
            total_sat += 1;
        } else {
            total_unsat += 1;
        }
        total_checked += 1;
    }

    // Family 3 (1,200 formulas): `R2_CODEX` multi-pair + large-offset/quotient systems:
    let pair_mods = [3i64, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 25];
    for idx in 0..1200usize {
        let base_off: i64 = if idx % 2 == 0 {
            1_000_000_000 + rng.int(0, 500)
        } else {
            -1_000_000_000 + rng.int(0, 500)
        };
        let lo = base_off;
        let hi = base_off + rng.int(0, 160);
        let x0 = Atom::Sym(Arc::from("x"));
        let x = Lin::atom(x0.clone());
        let mut fs = vec![
            Formula::Con(Con::ge(&x, &Lin::constant(lo))),
            Formula::Con(Con::ge(&Lin::constant(hi), &x)),
        ];
        let pairs = 2 + rng.below(2);
        let mut divs = Vec::new();
        for i in 0..2 * pairs {
            let m = pair_mods[rng.below(pair_mods.len())];
            let qa = Atom::Aux((2 * i) as u32);
            let ra = Atom::Aux((2 * i + 1) as u32);
            fs.push(Formula::Con(Con::eq(
                &x.minus(&Lin::atom(qa.clone()).times(m))
                    .minus(&Lin::atom(ra.clone())),
                &Lin::constant(0),
            )));
            fs.push(Formula::Con(Con::ge(
                &Lin::atom(ra.clone()),
                &Lin::constant(0),
            )));
            fs.push(Formula::Con(Con::ge(
                &Lin::constant(m - 1),
                &Lin::atom(ra.clone()),
            )));
            divs.push((qa, ra, m));
        }
        for p in 0..pairs {
            for _ in 0..2 {
                let (_, ref ra, ma) = divs[2 * p];
                let (_, ref rb, mb) = divs[2 * p + 1];
                let va = rng.int(0, ma - 1);
                let vb = rng.int(0, mb - 1);
                let la = if rng.below(3) == 0 {
                    Formula::negate(Formula::Con(Con::eq(
                        &Lin::atom(ra.clone()),
                        &Lin::constant(va),
                    )))
                } else {
                    Formula::Con(Con::eq(&Lin::atom(ra.clone()), &Lin::constant(va)))
                };
                let lb = if rng.below(3) == 0 {
                    Formula::negate(Formula::Con(Con::eq(
                        &Lin::atom(rb.clone()),
                        &Lin::constant(vb),
                    )))
                } else {
                    Formula::Con(Con::eq(&Lin::atom(rb.clone()), &Lin::constant(vb)))
                };
                fs.push(Formula::or(vec![la, lb]));
            }
        }
        let f = Formula::and(fs);
        let brute = (lo..=hi).any(|xv| {
            let mut m = Model::from([(x0.clone(), Int::from(xv))]);
            for (qa, ra, mod_m) in &divs {
                m.insert(qa.clone(), Int::from(xv.div_euclid(*mod_m)));
                m.insert(ra.clone(), Int::from(xv.rem_euclid(*mod_m)));
            }
            f.holds(&m)
        });
        let (Ok(dec), Ok(sat)) = (decide(&f), satisfiable(&f)) else {
            total_refused += 1;
            continue;
        };
        assert_eq!(
            dec, brute,
            "codex-pairs idx={idx}: dec={dec} brute={brute}\n{f}"
        );
        assert_eq!(sat.is_some(), brute, "codex-pairs sat idx={idx}");
        if let Some(ref m) = sat {
            assert!(f.holds(m), "codex-pairs model invalid idx={idx}");
            total_sat += 1;
        } else {
            total_unsat += 1;
        }
        total_checked += 1;
    }

    println!(
        "T8_ENUM_SUITE total=3600 checked={total_checked} sat={total_sat} unsat={total_unsat} refused={total_refused}"
    );
    assert!(total_checked >= 3500);
}

#[test]
fn pncx_renamed_parameters_and_case56_match() {
    let names = ["A", "a", "b", "w", "x", "y", "z", "zz"];
    let condition = "x >= (0 - 8) && x <= 26 && (x + 1) mod 10 <= 1 && (x - 5) mod 4 <= 1 && ((x - 5) mod 4 == 2 || (x - 5) mod 4 == 1 || x <= 12) && ((x + 1) mod 10 != 5 || x mod 8 != 7)";
    let mut sources = Vec::new();
    for x in names {
        let condition = condition.replace('x', x);
        sources.push(format!("f{}({x}: int) = {condition};", sources.len()));
        for alias in names {
            if alias == x {
                continue;
            }
            sources.push(format!(
                "f{}({x}: int, {alias}: int) = {alias} == {x} - 8 && {condition};",
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
