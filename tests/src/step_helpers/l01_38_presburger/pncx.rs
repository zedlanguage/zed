//! Helpers of `tests/steps/l01_38_presburger/pncx_probe.rs` shared with the hand-run probes of
//! PERF-negated-chain-unsolved (`benches/src/bin/pncx_probe.rs`, docs/handoff/
//! PERF-negated-chain-unsolved.md): the random chains with negations, the named axes of
//! formulas, the timing of one source's questions, and the one-variable modular formulas of
//! `one_scope.rs`.

use std::sync::Arc;
use std::time::Instant;

use crate::step_helpers::l01_16_elaboration::elab;
use zed_kernel::{Shared, Term, Value};
use zedc::elab::Unit;
use zedc::interp::prelude;
use zedc::store::preimage::Scoped;
use zedc::store::presburger::extend::Extending;

/// The definitions of `unit` as nested lets around `true`, under the prelude: the scope the
/// questions of `unit` are read in.
pub fn lets(unit: &Unit) -> Term {
    prelude(
        unit.defs
            .iter()
            .rev()
            .fold(Term::Lit(Value::Bool(true)), |body, d| {
                Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
            }),
    )
}

/// Times the questions of every function of `src`, faced and plain, in both orders (one with
/// `PNC_ORDER` set to `fwd` or `rev`), `reps` times, and prints each answer.
pub fn run(src: &str, reps: usize) {
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

/// Prints the record of the check of the modular solver's empty answers; asserts none wrong.
pub fn report(c: &zedc::store::presburger::EmptyCheck) {
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

/// The literal `n` as source text; a negative one as `(0 - m)`.
pub fn lit(n: i64) -> String {
    match n < 0 {
        true => format!("(0 - {})", -n),
        false => n.to_string(),
    }
}

/// The moduli of the random chains.
pub const MODS: [i64; 16] = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 25, 27];

/// A modulus of [`MODS`] drawn from `rng`.
pub fn modulus(rng: &mut crate::instances::Rng) -> i64 {
    MODS[rng.below(MODS.len())]
}

/// A random modular or bound case on `x`.
pub fn case(rng: &mut crate::instances::Rng) -> String {
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
pub fn chain(rng: &mut crate::instances::Rng) -> String {
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

/// Of the relation `w` on one integer `x` bounded on both sides: whether its body holds at
/// some `x` of the defined range, and whether it fails at some, by trying each; `None` if `x`
/// is not bounded.
pub fn enumerated(w: &zedc::store::presburger::Relation) -> Option<(bool, bool)> {
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

/// The first `n` primes.
pub fn primes(n: usize) -> Vec<i64> {
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
pub fn pow2(n: usize, d: i8) -> String {
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
pub fn axis_src(axis: &str, n: usize) -> String {
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

/// The formula of the named `axis` at size `n`. From Codex's round-2 probe
/// (library/r2-codex-pncx_probe.rs).
pub fn pncx_formula(axis: &str, n: usize) -> zedc::store::presburger::Formula {
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

/// The residue modulo the product of the clause's three primes at which all three of its
/// literals are false: `(m, c)`, the clause excluding `x mod m == c`.
pub fn pncx_sat_residue(primes: &[i64], cl: &[(usize, bool); 3]) -> (i64, i64) {
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

/// Consecutive Fibonacci moduli force Euclid's long quotient sequence. Both
/// residue requirements are needed; x = 0 or 1 cannot witness the formula.
pub fn pncx_crt_bits(n: usize) -> zedc::store::presburger::Formula {
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

/// The front's linear questions of the source of `axis`: none found, in time linear in the
/// size, at the sizes `n` and `8n`.
pub fn pncx_front_scale(axis: &str, n: usize) {
    let inputs = crate::scaling::inputs(n, |n| {
        let src = axis_src(axis, n);
        let stmts = crate::deep::statements(&src);
        let tokens = zedc::lex::lex_fence(&src).unwrap();
        let unit = elab(&src).unwrap();
        (src, stmts, tokens, unit)
    });
    crate::scaling::check_order(axis, n, 1, |n| {
        let (src, stmts, tokens, unit) = &inputs[&n];
        assert!(zedc::front::linear_questions(src, tokens, stmts, unit).is_empty());
    });
}

/// The 3,600 formulas of the T8 suite against enumeration, three families of 1,200 drawn from
/// one generator: of family `only`, the formulas numbered in `part` are decided and checked,
/// and the rest are only drawn, so each piece has the formulas it had when the three families
/// ran as one test (47 s alone at load 32) and stays well under 60 s. At most `most_refused`
/// are refused: 33 in families 1 and 2 and 34 in family 3, 100 in all, as the one test
/// allowed, with family 3's 34 shared among its four parts by their refusals on
/// 2026-11-12 (5, 3, 12 and 4).
pub fn t8_enum_suite(only: usize, part: std::ops::Range<usize>, most_refused: usize) {
    use std::sync::Arc;
    use zedc::store::int::Int;
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, decide, satisfiable};
    let negctl = std::env::var_os("PNCX_ENUM_NEGCTL").is_some();
    let mut rng = crate::instances::Rng::new(0x3141_5926);
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
        if only != 1 || !part.contains(&idx) {
            continue;
        }
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
        if only != 2 || !part.contains(&idx) {
            continue;
        }
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
        if only != 3 || !part.contains(&idx) {
            continue;
        }
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
        "T8_ENUM_SUITE family {only} formulas {part:?}: checked={total_checked} sat={total_sat} unsat={total_unsat} refused={total_refused}"
    );
    assert_eq!(total_checked + total_refused, part.len());
    assert!(total_refused <= most_refused, "{total_refused} refused");
}

/// One formula of `one_variable_modular_formulas_match_enumeration`: the formula, the copies
/// `x_k = s_k * x + off_k` of `x`, the divisions `(q, r, m, s, off)` of `s * x + off` by `m`,
/// and the interval of `x` (bounded above when the flag is set).
pub type ModularCase = (
    zedc::store::presburger::Formula,
    zedc::store::presburger::Atom,
    Vec<(zedc::store::presburger::Atom, i64, i64)>,
    Vec<(
        zedc::store::presburger::Atom,
        zedc::store::presburger::Atom,
        i64,
        i64,
        i64,
    )>,
    i64,
    i64,
    bool,
);

/// The formula of case `case_idx` of `one_variable_modular_formulas_match_enumeration`, drawn
/// from `rng`.
pub fn modular_case(rng: &mut crate::instances::Rng, case_idx: usize) -> ModularCase {
    modular_case_with(rng, case_idx, None)
}

/// As `modular_case_with`, with the bounds named by a mode: 0 none, 1 lower only, 2 upper
/// only, 3 both.
pub fn modular_case_mode(
    rng: &mut crate::instances::Rng,
    case_idx: usize,
    mode: Option<u8>,
) -> ModularCase {
    let sides = mode.map(|m| match m {
        0 => (false, false),
        1 => (true, false),
        2 => (false, true),
        _ => (true, true),
    });
    modular_case_with(rng, case_idx, sides)
}

/// As `modular_case`, but where `sides` is `Some((has_lo, has_hi))` the bound `x >= lo` is
/// written only if `has_lo` and `x <= hi` only if `has_hi`; with neither, the clauses that
/// compare `x` with a number are replaced by residue clauses, so that `x` has no bound at all
/// (I5.3).
pub fn modular_case_with(
    rng: &mut crate::instances::Rng,
    case_idx: usize,
    sides: Option<(bool, bool)>,
) -> ModularCase {
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    let moduli: [i64; 20] = [
        2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 25, 27, 30,
    ];
    let x0 = Atom::Sym(Arc::from("x"));
    let mut parts: Vec<Formula> = Vec::new();
    // Build 0..=3 shifted/reflected unit-equality copies of `x`: `x_k = s_k * x_0 + off_k`.
    let num_copies = rng.below(4);
    let mut copies: Vec<(Atom, i64, i64)> = vec![(x0.clone(), 1, 0)];
    for k in 1..=num_copies {
        let prev_idx = rng.below(copies.len());
        let (prev_atom, prev_s, prev_off) = copies[prev_idx].clone();
        let step_s = if rng.below(5) == 0 { -1i64 } else { 1i64 };
        let step_d = rng.int(-8, 8);
        let cur_atom = Atom::Sym(Arc::from(format!("x@{k}")));
        // cur_atom - step_s * prev_atom - step_d == 0
        let lin = Lin::atom(cur_atom.clone())
            .plus(&Lin::atom(prev_atom).times(-step_s))
            .plus(&Lin::constant(-step_d));
        parts.push(Formula::Con(Con::eq(&lin, &Lin::constant(0))));
        copies.push((cur_atom, step_s * prev_s, step_s * prev_off + step_d));
    }

    // Choose interval regime: negative, around 0, large positive, short, or semi-bounded.
    let (lo, hi, is_bounded) = match case_idx % 5 {
        0 => {
            let l = rng.int(-220, -160);
            let h = l + rng.int(0, 75);
            (l, h, true)
        }
        1 => {
            let l = rng.int(-40, 10);
            let h = l + rng.int(-2, 65);
            (l, h, true)
        }
        2 => {
            let l = rng.int(10_000, 10_030);
            let h = l + rng.int(0, 80);
            (l, h, true)
        }
        3 => {
            let l = rng.int(-15, 25);
            let h = l + rng.int(-1, 5);
            (l, h, true)
        }
        _ => {
            let l = rng.int(-20, 20);
            (l, l + 120, false)
        }
    };

    let (has_lo, has_hi) = sides.unwrap_or((true, is_bounded));
    if has_lo {
        parts.push(Formula::Con(Con::ge(
            &Lin::atom(x0.clone()).plus(&Lin::constant(-lo)),
            &Lin::constant(0),
        )));
    }
    if has_hi {
        parts.push(Formula::Con(Con::ge(
            &Lin::constant(hi).minus(&Lin::atom(x0.clone())),
            &Lin::constant(0),
        )));
    }

    // Define 2..=5 Euclidean divisions on random copies of `x`.
    let num_divs = 2 + rng.below(4);
    let mut divs: Vec<(Atom, Atom, i64, i64, i64)> = Vec::new();
    for d_idx in 0..num_divs {
        let (ref copy_atom, copy_s, copy_off) = copies[rng.below(copies.len())];
        let m = moduli[rng.below(moduli.len())];
        let shift = rng.int(-5, 5);
        let q_atom = Atom::Aux((d_idx * 2) as u32);
        let r_atom = Atom::Aux((d_idx * 2 + 1) as u32);
        // copy_atom + shift - m * q_atom - r_atom == 0 && 0 <= r_atom <= m - 1
        let eq_lin = Lin::atom(copy_atom.clone())
            .plus(&Lin::constant(shift))
            .plus(&Lin::atom(q_atom.clone()).times(-m))
            .plus(&Lin::atom(r_atom.clone()).times(-1));
        parts.push(Formula::Con(Con::eq(&eq_lin, &Lin::constant(0))));
        parts.push(Formula::Con(Con::ge(
            &Lin::atom(r_atom.clone()),
            &Lin::constant(0),
        )));
        parts.push(Formula::Con(Con::ge(
            &Lin::constant(m - 1).minus(&Lin::atom(r_atom.clone())),
            &Lin::constant(0),
        )));
        divs.push((q_atom, r_atom, m, copy_s, copy_off + shift));
    }

    // Build 2..=5 modular/bound clauses (unit congruences, negated guard+congruence, holes,
    // and single-modulus or multi-bound disjunctions).
    let num_clauses = 2 + rng.below(4);
    for _ in 0..num_clauses {
        let (_, ref r_atom, m, _, _) = divs[rng.below(divs.len())];
        let r_val = rng.int(0, m - 1);
        let b_val = rng.int(lo - 5, hi + 5);
        let kind = match rng.below(6) {
            k @ 1..=3 if sides == Some((false, false)) => [0, 4, 5][k - 1],
            k => k,
        };
        let cl = match kind {
            0 => {
                // x mod m != r_val
                Formula::negate(Formula::Con(Con::eq(
                    &Lin::atom(r_atom.clone()),
                    &Lin::constant(r_val),
                )))
            }
            1 => {
                // !(r == r_val && x >= b_val)
                let is_r = Formula::Con(Con::eq(&Lin::atom(r_atom.clone()), &Lin::constant(r_val)));
                let ge_b = Formula::Con(Con::ge(
                    &Lin::atom(x0.clone()).plus(&Lin::constant(-b_val)),
                    &Lin::constant(0),
                ));
                Formula::negate(Formula::and(vec![is_r, ge_b]))
            }
            2 => {
                // r == r1 || r == r2 || x <= b_val
                let r2 = rng.int(0, m - 1);
                Formula::or(vec![
                    Formula::Con(Con::eq(&Lin::atom(r_atom.clone()), &Lin::constant(r_val))),
                    Formula::Con(Con::eq(&Lin::atom(r_atom.clone()), &Lin::constant(r2))),
                    Formula::Con(Con::ge(
                        &Lin::constant(b_val).minus(&Lin::atom(x0.clone())),
                        &Lin::constant(0),
                    )),
                ])
            }
            3 => {
                // Hole: x < b_val || x > b_val + gap
                let gap = rng.int(0, 12);
                Formula::or(vec![
                    Formula::Con(Con::ge(
                        &Lin::constant(b_val - 1).minus(&Lin::atom(x0.clone())),
                        &Lin::constant(0),
                    )),
                    Formula::Con(Con::ge(
                        &Lin::atom(x0.clone()).plus(&Lin::constant(-(b_val + gap + 1))),
                        &Lin::constant(0),
                    )),
                ])
            }
            4 => {
                // Remainder interval: r < r_val + 1
                Formula::Con(Con::ge(
                    &Lin::constant(r_val).minus(&Lin::atom(r_atom.clone())),
                    &Lin::constant(0),
                ))
            }
            _ => {
                // Disjunction of two negated residues across two divisions (share = 1/(m1*m2) < 1)
                let (_, ref r2_atom, m2, _, _) = divs[rng.below(divs.len())];
                let r2_val = rng.int(0, m2 - 1);
                Formula::or(vec![
                    Formula::negate(Formula::Con(Con::eq(
                        &Lin::atom(r_atom.clone()),
                        &Lin::constant(r_val),
                    ))),
                    Formula::negate(Formula::Con(Con::eq(
                        &Lin::atom(r2_atom.clone()),
                        &Lin::constant(r2_val),
                    ))),
                ])
            }
        };
        parts.push(cl);
    }

    let f = Formula::and(parts);
    (f, x0, copies, divs, lo, hi, is_bounded)
}
