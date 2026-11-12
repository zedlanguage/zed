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
    // `(x + y) ^ 4` counts four sums.
    let Verdict::Refused(r) = verdict(
        "(x + y) ^ 4",
        "x^4 + 4*x^3*y + 6*x^2*y^2 + 4*x*y^3 + y^4",
        &["x", "y"],
        Carrier::Int,
    ) else {
        panic!()
    };
    assert_eq!(r.why, Refused::Sums(4));
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
    // Univariate sums of many terms take the dense product; check it against the sparse one.
    let p = |n: i64, s: i64| -> Poly<u128> {
        let mut terms: Vec<(u128, BigInt)> = (0..n)
            .map(|i| {
                let c = (i * 7919 + s) % 1009 - 504;
                (i as u128, BigInt::from(c) << (i % 70))
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
        let (a, b) = (p(n, 3), p(n + 5, 11));
        let sparse = a.sparse_mul(&b);
        if let Some(slot) = a.dense_cost(&b) {
            assert_eq!(a.dense_mul(&b, slot), sparse, "n = {n}");
        }
        // Force the dense product at a slot wide enough.
        let wide = a.dense_mul(&b, 8);
        assert_eq!(wide, sparse, "n = {n}");
    }
    assert!(p(300, 3).dense_cost(&p(300, 4)).is_some());
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
