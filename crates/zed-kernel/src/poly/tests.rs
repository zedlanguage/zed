//! Unit tests of the polynomial normal form: each rule with its expected output.

use std::sync::Arc;

use num_bigint::BigInt;

use super::*;
use crate::term::build::{let_, lit, prim, var};

/// `s` read as a term: `+ - * / ^`, unary `-`, parentheses, integer literals, names, and
/// `f(...)` as an application of an unknown function (an atom).
fn t(s: &str) -> Term {
    let toks: Vec<String> = {
        let mut v = Vec::new();
        let cs: Vec<char> = s.chars().collect();
        let mut i = 0;
        while i < cs.len() {
            let c = cs[i];
            if c.is_whitespace() {
                i += 1;
            } else if c.is_alphanumeric() || c == '_' {
                let from = i;
                while i < cs.len() && (cs[i].is_alphanumeric() || cs[i] == '_') {
                    i += 1;
                }
                v.push(cs[from..i].iter().collect());
            } else {
                v.push(c.to_string());
                i += 1;
            }
        }
        v
    };
    let mut at = 0;
    let e = expr(&toks, &mut at, 0);
    assert_eq!(at, toks.len(), "all of `{s}` read");
    e
}

fn expr(toks: &[String], at: &mut usize, min: u8) -> Term {
    let mut l = atom(toks, at);
    while let Some(op) = toks.get(*at) {
        let (p, prec, right) = match op.as_str() {
            "+" => (Prim::Add, 1, false),
            "-" => (Prim::Sub, 1, false),
            "*" => (Prim::Mul, 2, false),
            "/" => (Prim::Div, 2, false),
            "^" => (Prim::Pow, 4, true),
            _ => break,
        };
        if prec < min {
            break;
        }
        *at += 1;
        let r = expr(toks, at, if right { prec } else { prec + 1 });
        l = prim(p, vec![l, r]);
    }
    l
}

fn atom(toks: &[String], at: &mut usize) -> Term {
    let tok = &toks[*at];
    *at += 1;
    match tok.as_str() {
        "(" => {
            let e = expr(toks, at, 0);
            assert_eq!(toks[*at], ")");
            *at += 1;
            e
        }
        "-" => prim(Prim::Neg, vec![expr(toks, at, 3)]),
        _ if tok.chars().all(|c| c.is_ascii_digit()) => match tok.parse::<i64>() {
            Ok(n) => lit(n),
            Err(_) => Term::Lit(Value::Big(Arc::new(crate::Rat::int(
                tok.parse::<BigInt>().expect("digits"),
            )))),
        },
        _ if toks.get(*at).map(String::as_str) == Some("(") => {
            *at += 1;
            let mut args = Vec::new();
            while toks[*at] != ")" {
                args.push(expr(toks, at, 0));
                if toks[*at] == "," {
                    *at += 1;
                }
            }
            *at += 1;
            crate::term::build::app(var(tok), args)
        }
        _ => var(tok),
    }
}

fn nf(s: &str, binders: &[&str]) -> String {
    normal_form(&t(s), binders, Carrier::Int).expect("not refused")
}

fn verdict(l: &str, r: &str, binders: &[&str], c: Carrier) -> Verdict {
    decide(&t(l), &t(r), binders, c).verdict
}

#[test]
fn products_of_sums_are_expanded() {
    assert_eq!(nf("(x + y) * (x - y)", &["x", "y"]), "x ^ 2 - y ^ 2");
    assert_eq!(
        nf("(x + y) * (x + y)", &["x", "y"]),
        "x ^ 2 + 2 * x * y + y ^ 2"
    );
    assert_eq!(
        nf("(a + b) * (c + d)", &["a", "b", "c", "d"]),
        "a * c + a * d + b * c + b * d"
    );
}

#[test]
fn a_literal_power_is_a_monomial() {
    assert_eq!(nf("x ^ 3", &["x"]), "x ^ 3");
    assert_eq!(nf("(2 * x) ^ 3", &["x"]), "8 * x ^ 3");
    assert_eq!(nf("(x + 1) ^ 3", &["x"]), "x ^ 3 + 3 * x ^ 2 + 3 * x + 1");
    assert_eq!(nf("x ^ 0", &["x"]), "1");
    assert_eq!(nf("(x ^ 9) ^ 0", &["x"]), "1");
    assert_eq!(nf("(x * y) ^ 2 * x", &["x", "y"]), "x ^ 3 * y ^ 2");
}

#[test]
fn like_monomials_are_merged() {
    assert_eq!(nf("x * y + y * x - 2 * x * y", &["x", "y"]), "0");
    assert_eq!(nf("x + x + x", &["x"]), "3 * x");
    assert_eq!(nf("-(x - y) + x", &["x", "y"]), "y");
}

#[test]
fn other_terms_are_atoms() {
    // An unknown name, a call and a power with a non-literal exponent are each a variable.
    assert_eq!(nf("f(x) * f(x) + z", &["x"]), "f(x) ^ 2 + z");
    assert_eq!(nf("x ^ n * x ^ n", &["x"]), "(x^n) ^ 2");
}

#[test]
fn a_let_is_read_through() {
    let e = let_("s", t("x + y"), t("s * s"));
    assert_eq!(
        normal_form(&e, &["x", "y"], Carrier::Int).expect("not refused"),
        "x ^ 2 + 2 * x * y + y ^ 2"
    );
    // A let whose value is not used is not reached.
    let e = let_("u", t("(a+b)*(c+d)*(e+f)*(g+h)"), t("x"));
    assert_eq!(
        normal_form(&e, &["x"], Carrier::Int).expect("not refused"),
        "x"
    );
}

#[test]
fn rational_coefficients_at_rat() {
    let half = t("x / 2 + x / 2");
    assert_eq!(normal_form(&half, &["x"], Carrier::Rat).expect("ok"), "x");
    assert_eq!(
        normal_form(&t("(x + 1) / 3"), &["x"], Carrier::Rat).expect("ok"),
        "1/3 * x + 1/3"
    );
    // At `int`, `/` is no ring operation: the quotient is an atom.
    assert_eq!(
        normal_form(&t("x / 2 + x / 2"), &["x"], Carrier::Int).expect("ok"),
        "2 * (x / 2)"
    );
    // A divisor that is not a literal, or zero, gives an atom.
    assert_eq!(
        normal_form(&t("x / y"), &["x", "y"], Carrier::Rat).expect("ok"),
        "(x / y)"
    );
    assert_eq!(
        normal_form(&t("x / 0"), &["x"], Carrier::Rat).expect("ok"),
        "(x / 0)"
    );
}

#[test]
fn the_row_identities_are_proved() {
    let xy = &["x", "y"];
    assert_eq!(
        verdict("(x + y) * (x - y)", "x * x - y * y", xy, Carrier::Int),
        Verdict::Proved
    );
    assert_eq!(
        verdict(
            "(a + b) * (c + d) * (e + f)",
            "a*c*e + a*c*f + a*d*e + a*d*f + b*c*e + b*c*f + b*d*e + b*d*f",
            &["a", "b", "c", "d", "e", "f"],
            Carrier::Int
        ),
        Verdict::Proved
    );
    let d = decide(
        &t("(1 + x + x ^ 2 + x ^ 3) ^ 2"),
        &t("(1 + x) ^ 2 * (1 + x ^ 2) ^ 2"),
        &["x"],
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
    assert_eq!(d.terms, Some([7, 7]));
    assert_eq!(d.degree, Some(6));
}

#[test]
fn a_false_identity_is_refuted_with_small_values() {
    let d = decide(
        &t("(x + y) * (x + y)"),
        &t("x * x + y * y"),
        &["x", "y"],
        Carrier::Int,
    );
    let Verdict::Refuted(p) = d.verdict else {
        panic!("not refuted: {:?}", d.verdict)
    };
    assert_eq!(p.to_string(), "x = 1, y = 1");
    // A difference of a constant: the first value of each binder.
    let Verdict::Refuted(p) = verdict("x + 1", "x", &["x"], Carrier::Int) else {
        panic!()
    };
    assert_eq!(p.to_string(), "x = 0");
    // `x * (x - 1) * (x + 1) * (x - 2)` is zero at 0, 1, -1 and 2.
    let Verdict::Refuted(p) = verdict("x * (x - 1) * (x + 1) * (x - 2)", "0", &["x"], Carrier::Int)
    else {
        panic!()
    };
    assert_eq!(p.to_string(), "x = -2");
}

#[test]
fn a_ring_or_an_atom_is_never_refuted() {
    // Holds mod 2, so it is no theorem's counterexample at a ring.
    assert_eq!(
        verdict(
            "(x + y) * (x + y)",
            "x * x + y * y",
            &["x", "y"],
            Carrier::Ring
        ),
        Verdict::Differs
    );
    // `f(x)` may be anything.
    assert_eq!(
        verdict("f(x) + 1", "f(x)", &["x"], Carrier::Int),
        Verdict::Differs
    );
    // But equal atoms cancel.
    assert_eq!(
        verdict(
            "(f(x) + 1) ^ 2",
            "f(x) ^ 2 + 2 * f(x) + 1",
            &["x"],
            Carrier::Ring
        ),
        Verdict::Proved
    );
}

#[test]
fn refused_shapes() {
    // Four sums over more than one name: a true identity is refused, a false one refuted.
    let lhs = "(a + b) * (c + d) * (e + f) * (g + h)";
    let names = &["a", "b", "c", "d", "e", "f", "g", "h"];
    let mut rhs = Vec::new();
    for x in ["a", "b"] {
        for y in ["c", "d"] {
            for z in ["e", "f"] {
                for w in ["g", "h"] {
                    rhs.push(format!("{x}*{y}*{z}*{w}"));
                }
            }
        }
    }
    let rhs = rhs.join(" + ");
    let Verdict::Refused(r) = verdict(lhs, &rhs, names, Carrier::Int) else {
        panic!("not refused")
    };
    assert_eq!(r.why, Refused::Sums(4));
    assert_eq!(r.product, "((((a + b) * (c + d)) * (e + f)) * (g + h))");
    assert_eq!(r.agreed.len(), 2);
    let m = r.message("law four(a: int, …) = …");
    assert!(m.starts_with(
        "Cannot expand `((((a + b) * (c + d)) * (e + f)) * (g + h))`: it multiplies 4 sums of more than one name."
    ));
    assert!(m.contains("note: the two sides agree at every point tried"));
    assert!(m.ends_with("Try `law four(a: int, …) = … proof { … }` instead."));
    // A false identity of that shape is refuted at a point.
    let wrong = format!("{rhs} + 1");
    assert!(matches!(
        verdict(lhs, &wrong, names, Carrier::Int),
        Verdict::Refuted(_)
    ));
    // `(x + y) ^ 4` counts one sum: its base has two monomials, so it expands to five.
    assert_eq!(
        verdict(
            "(x + y) ^ 4",
            "x^4 + 4*x^3*y + 6*x^2*y^2 + 4*x*y^3 + y^4",
            &["x", "y"],
            Carrier::Int,
        ),
        Verdict::Proved
    );
    // A base of five monomials to the 4th counts the fewer of 4 and 5 - 1: four sums.
    let names5 = &["a", "b", "c", "d", "f"];
    let Verdict::Refused(r) = verdict(
        "(a + b + c + d + f) ^ 4",
        "(f + d + c + b + a) ^ 4",
        names5,
        Carrier::Int,
    ) else {
        panic!()
    };
    assert_eq!(r.why, Refused::Sums(4));
    assert_eq!(r.product, "(((((a + b) + c) + d) + f)^4)");
    // To the 3rd it counts three, and to the 4th a base of four monomials counts three too.
    for (l, r, n) in [
        (
            "(a + b + c + d + f) ^ 3",
            "(f + d + c + b + a) ^ 3",
            &names5[..],
        ),
        ("(a + b + c + d) ^ 4", "(d + c + b + a) ^ 4", &names5[..4]),
        (
            "((a + b) * (c + d)) ^ 9",
            "(a * c + a * d + b * c + b * d) ^ 9",
            &names5[..4],
        ),
    ] {
        assert_eq!(verdict(l, r, n, Carrier::Int), Verdict::Proved, "{l}");
    }
    // A product of a base of three sums squared: the fewer of 6 and 8 - 1, refused.
    let Verdict::Refused(r) = verdict(
        "((a + b) * (c + d) * (f + a)) ^ 2",
        "((a + b) * (c + d) * (a + f)) ^ 2",
        names5,
        Carrier::Int,
    ) else {
        panic!()
    };
    assert_eq!(r.why, Refused::Sums(6));
    // Sums all in one name are never refused, at any count.
    assert_eq!(
        verdict(
            "(1 + x) ^ 40",
            "(1 + x) ^ 20 * (1 + x) ^ 20",
            &["x"],
            Carrier::Int
        ),
        Verdict::Proved
    );
    // An exponent past u64::MAX on a name.
    let Verdict::Refused(r) = verdict(
        "x ^ 18446744073709551616",
        "x ^ 18446744073709551616",
        &["x"],
        Carrier::Int,
    ) else {
        panic!()
    };
    assert_eq!(r.why, Refused::Exponent);
    // But not on 1 or -1.
    assert_eq!(
        verdict("(-1) ^ 18446744073709551617", "-1", &[], Carrier::Int),
        Verdict::Proved
    );
}

#[test]
fn the_points_are_deterministic() {
    let a = || {
        decide(
            &t("(a + b) * (c + d) * (e + f) * (g + h)"),
            &t("(a + b) * (c + d) * (e + f) * (h + g)"),
            &["a", "b", "c", "d", "e", "f", "g", "h"],
            Carrier::Int,
        )
    };
    let (x, y) = (a(), a());
    assert_eq!(x.verdict, y.verdict);
    let Verdict::Refused(r) = x.verdict else {
        panic!()
    };
    assert_eq!(r.agreed.len(), 2);
    assert_ne!(r.agreed[0], r.agreed[1]);
}

#[test]
fn the_dense_and_sparse_products_agree() {
    // Sums of many terms at every `step`-th index from `base` take the dense product; check it
    // against the sparse one.
    let p = |n: i64, s: i64, base: u128, step: u128| -> Poly<u128> {
        let mut terms: Vec<(u128, BigInt)> = (0..n)
            .map(|i| {
                let c = (i * 7919 + s) % 1009 - 504;
                (base + i as u128 * step, BigInt::from(c) << (i % 70))
            })
            .filter(|(_, c)| !c.is_zero())
            .collect();
        terms.sort_by_key(|(k, _)| *k);
        Poly {
            den: BigInt::one(),
            terms,
        }
    };
    for n in [1, 2, 3, 17, 300] {
        for (base_a, step_a, base_b, step_b) in [(0, 1, 0, 1), (3, 5, 7, 5), (2, 6, 1, 10)] {
            let a = p(n, 3, base_a, step_a);
            let b = p(n + 5, 11, base_b, step_b);
            let sparse = a.sparse_mul(&b);
            let plan = a.plan(&b).expect("packed keys");
            if plan.dense <= plan.sparse {
                assert_eq!(a.dense_mul(&b, plan.slot, plan.step), sparse, "n = {n}");
            }
            // Force the dense product at a slot wide enough, at the common step and at 1.
            let common = if n == 1 { step_b } else { step_a.gcd(&step_b) };
            assert_eq!(a.dense_mul(&b, 8, common), sparse, "n = {n}");
            assert_eq!(a.dense_mul(&b, 8, 1), sparse, "n = {n}");
        }
    }
    let plan = p(300, 3, 0, 1).plan(&p(300, 4, 0, 1)).expect("packed keys");
    assert!(plan.dense <= plan.sparse);
    // The step is the greatest common divisor of the distances from each side's lowest index.
    let step = |a: Poly<u128>, b: Poly<u128>| a.plan(&b).map(|p| p.step);
    assert_eq!(step(p(300, 3, 3, 5), p(300, 4, 7, 5)), Some(5));
    assert_eq!(step(p(300, 3, 2, 6), p(300, 4, 1, 10)), Some(2));
    assert_eq!(step(p(300, 3, 2, 7), p(300, 4, 1, 1)), Some(1));
}

#[test]
fn sparse_keys_past_u128() {
    // 40 names of degree 9: (10)^40 is past 2^128, so the keys are lists.
    let names: Vec<String> = (0..40).map(|i| format!("v{i}")).collect();
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let sum = refs.join(" + ");
    let id_l = format!("({sum}) ^ 3 * v0 ^ 6");
    let (l, z) = (t(&id_l), t("0"));
    let id = Identity::new(&l, &z, &refs, Carrier::Int);
    assert!(matches!(id.keys(&id.reachable()), Keys::Sparse));
    assert_eq!(
        verdict(
            &id_l,
            &format!("v0 ^ 6 * ({sum}) * ({sum}) ^ 2"),
            &refs,
            Carrier::Int
        ),
        Verdict::Proved
    );
}

#[test]
fn modular_arithmetic() {
    assert_eq!(mulmod(P - 1, P - 1), 1);
    assert_eq!(powmod(0, &BigUint::zero()), 1);
    assert_eq!(powmod(3, &BigUint::from(P - 1)), 1);
    assert_eq!(small_mod(-1), P - 1);
    assert_eq!((0..5).map(small).collect::<Vec<_>>(), [0, 1, -1, 2, -2]);
}

/// `x ^ P - x` and `x ^ (2 * P - 1) - x` are zero at every point modulo `P` (Fermat): the two
/// points agree, the normal forms differ, and the search for a witness reads each exponent
/// below `P` and stops at once, where it tried `P - 1` values before.
#[test]
fn a_difference_zero_modulo_p_has_no_witness() {
    assert_eq!(
        verdict("x ^ 2305843009213693951", "x", &["x"], Carrier::Int),
        Verdict::Differs
    );
    assert_eq!(
        verdict(
            "x ^ 4611686018427387901 + y",
            "x + y",
            &["x", "y"],
            Carrier::Int
        ),
        Verdict::Differs
    );
}

/// A sum of the `(index, coefficient)` pairs, like indices merged and zeros dropped.
fn sum_at(pairs: impl IntoIterator<Item = (u128, i64)>) -> Poly<u128> {
    let mut m = std::collections::BTreeMap::new();
    for (k, c) in pairs {
        *m.entry(k).or_insert_with(BigInt::zero) += c;
    }
    Poly {
        den: BigInt::one(),
        terms: m.into_iter().filter(|(_, c)| !c.is_zero()).collect(),
    }
}

/// The support product with no budget, so it never gives way to another method.
fn support(a: &Poly<u128>, b: &Poly<u128>) -> Vec<(u128, BigInt)> {
    let mut plan = a.plan(b).expect("packed keys");
    plan.dense = f64::INFINITY;
    plan.sparse = f64::INFINITY;
    a.support_mul(b, &plan).expect("no budget")
}

#[test]
fn the_support_product_agrees_with_the_sparse_one() {
    // `((x + y)^k + x)` at radix `2k + 1`, `x` the low digit: indices that no common step
    // reduces, the family the support product is for.
    for k in [1u128, 2, 5, 40] {
        let r = 2 * k + 1;
        let mut binomial = 1i64;
        let a = sum_at(
            (0..=k)
                .map(|i| {
                    let t = (i + (k - i) * r, binomial);
                    binomial = binomial * (k - i) as i64 / (i + 1) as i64;
                    t
                })
                .chain([(1, 1)]),
        );
        assert_eq!(support(&a, &a), a.sparse_mul(&a), "k = {k}");
    }
    // (x + y)(x - y) = x^2 - y^2: the middle index cancels, and must not be kept as a zero.
    let (a, b) = (sum_at([(1, 1), (100, 1)]), sum_at([(1, 1), (100, -1)]));
    assert_eq!(
        support(&a, &b),
        vec![(2, BigInt::from(1)), (200, BigInt::from(-1))]
    );
    // One term on a side, and indices past 2^64, whose squares fill all eight digits.
    let wide = sum_at([(3, 2), (1 << 100, -3), ((1 << 120) + 7, 5)]);
    for b in [sum_at([(9, 4)]), wide.clone()] {
        assert_eq!(support(&wide, &b), wide.sparse_mul(&b));
    }
    // Pseudo-random sums: few distinct sums (on a few progressions) and all distinct ones (the
    // primes must grow), with small coefficients that cancel. A slot test that took a slot of
    // two sums for one, or a coefficient read from a shared slot, would differ here.
    let mut x = 0x2545_f491_4f6c_dd1du64;
    let mut next = |m: u64| {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x % m
    };
    for round in 0..60 {
        let gaps = [3, 1000, 1 << 40][round % 3];
        let (n, m) = (1 + next(80), 1 + next(80));
        let mut side = |n: u64| {
            sum_at((0..n).map(|_| {
                let lane = u128::from(next(4)) * gaps * 97;
                (
                    lane + u128::from(next(50)) * gaps + u128::from(next(2)),
                    next(5) as i64 - 2,
                )
            }))
        };
        let (a, b) = (side(n), side(m));
        if a.terms.is_empty() || b.terms.is_empty() {
            continue;
        }
        assert_eq!(support(&a, &b), a.sparse_mul(&b), "round {round}");
    }
}

#[test]
fn the_square_of_a_wide_index_is_exact() {
    for a in [
        0u128,
        1,
        3,
        u128::from(u64::MAX),
        1 << 64,
        (1 << 64) + 1,
        u128::MAX - 5,
        u128::MAX,
    ] {
        let want = BigUint::from(a) * BigUint::from(a);
        let mut got = square(a).to_vec();
        while got.last() == Some(&0) {
            got.pop();
        }
        assert_eq!(got, want.to_u32_digits(), "a = {a}");
    }
}

#[test]
fn the_product_takes_the_support_product_where_it_is_cheaper() {
    // The shape of `(x + y) ^ k + x` at k = 256 with coefficients of about 256 bits, like its
    // binomial ones: the sparse product pays (k + 2)^2 pairs of 4-word coefficients, the dense
    // one a span of about 2k^2 slots, and the support product about 3k sums.
    let k = 256u128;
    let r = 2 * k + 1;
    let wide = |i: u128| (BigInt::one() << 250u32) + BigInt::from(i);
    let mut terms: std::collections::BTreeMap<u128, BigInt> =
        (0..=k).map(|i| (i + (k - i) * r, wide(i))).collect();
    terms.insert(1, wide(k + 1));
    let a = Poly {
        den: BigInt::one(),
        terms: terms.into_iter().collect(),
    };
    let plan = a.plan(&a).expect("packed keys");
    assert_eq!(a.support_mul(&a, &plan), Some(a.sparse_mul(&a)));
    // Sides whose pairs are all distinct go to the sparse product: the sampled estimate says so.
    let b = sum_at((0..64u128).map(|i| (i * i * i * 1009 + i, 1)));
    let plan = b.plan(&b).expect("packed keys");
    assert_eq!(b.support_mul(&b, &plan), None);
}
