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
    // Four sums over more than one name: cheap to expand, so proved, and a false one refuted.
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
    assert_eq!(verdict(lhs, &rhs, names, Carrier::Int), Verdict::Proved);
    let wrong = format!("{rhs} + 1");
    assert!(matches!(
        verdict(lhs, &wrong, names, Carrier::Int),
        Verdict::Refuted(_)
    ));
    // Each side here and below is a sum, not a product of powers, so the expansion decides,
    // not `Identity::factored`. Powers of sums of many names, and of a product of three sums.
    let names5 = &["a", "b", "c", "d", "f"];
    for (l, r, n) in [
        (
            "(x + y) ^ 4",
            "x^4 + 4*x^3*y + 6*x^2*y^2 + 4*x*y^3 + y^4",
            &["x", "y"][..],
        ),
        (
            "(a + b + c + d + f) ^ 4 - f ^ 4",
            "(f + d + c + b + a) ^ 4 - f ^ 4",
            &names5[..],
        ),
        (
            "(a + b + c + d + f) ^ 3 - a",
            "(f + d + c + b + a) ^ 3 - a",
            &names5[..],
        ),
        (
            "((a + b) * (c + d)) ^ 9 - a",
            "(a * c + a * d + b * c + b * d) ^ 9 - a",
            &names5[..4],
        ),
        (
            "((a + b) * (c + d) * (f + a)) ^ 2 - a",
            "((a + b) * (c + d) * (a + f)) ^ 2 - a",
            &names5[..],
        ),
        (
            "(1 + x) ^ 40 - x",
            "(1 + x) ^ 20 * (1 + x) ^ 20 - x",
            &["x"][..],
        ),
    ] {
        let d = decide(&t(l), &t(r), n, Carrier::Int);
        assert_eq!(d.verdict, Verdict::Proved, "{l}");
        assert!(d.work <= LIMIT, "{l}");
    }
    // A product past the limit, refused before it runs: `(1 + x) ^ 256 * (1 + y) ^ 256` is
    // 65536 terms of up to 512 bits, each of which the third power's 257 terms multiply.
    let xyz = &["x", "y", "z"];
    let past = "(1 + x) ^ 256 * (1 + y) ^ 256 * (1 + z) ^ 256 - x";
    let d = decide(
        &t(past),
        &t("(1 + z) ^ 256 * (1 + y) ^ 256 * (1 + x) ^ 256 - x"),
        xyz,
        Carrier::Int,
    );
    let Verdict::Refused(r) = d.verdict else {
        panic!("not refused")
    };
    let Refused::Work(work) = r.why else {
        panic!("{:?}", r.why)
    };
    assert_eq!(
        r.product,
        "((((1 + x)^256) * ((1 + y)^256)) * ((1 + z)^256))"
    );
    assert_eq!(r.agreed.len(), 2);
    // The prediction is the work spent and the refused product's charge, which alone passes
    // the limit; the work spent stays below it.
    assert!(d.work <= LIMIT && work - d.work > LIMIT);
    let m = r.message("law three(x: int, y: int, z: int) = …");
    let ms = (work / LIMIT * LIMIT_MS).ceil();
    assert!(
        m.starts_with(&format!(
            "Cannot expand `{}`: expanding the law takes at least {ms:.0} ms, more than 250 ms.\n  note: the time is predicted from the sizes of the sums and products: at least {work:.0} units of work, against a limit of 17500000 units measured as 250 ms on one machine, so that every machine refuses the same laws.",
            r.product
        )),
        "{m}"
    );
    assert!(m.contains("note: the two sides agree at every point tried"));
    assert!(m.ends_with("Try `law three(x: int, y: int, z: int) = … proof { … }` instead."));
    // A false identity of that shape is refuted at a point.
    assert!(matches!(
        verdict(
            past,
            "(1 + z) ^ 256 * (1 + y) ^ 256 * (1 + x) ^ 256 - y",
            xyz,
            Carrier::Int
        ),
        Verdict::Refuted(_)
    ));
    // A power whose cost grows with its exponent's value is proved while its predicted time is
    // below the limit: past the A98 rule's limit of exponent 70 on two names.
    let xy = &["x", "y"];
    let d = decide(
        &t("(x + y) ^ 1000 - x"),
        &t("(y + x) ^ 500 * (x + y) ^ 500 - x"),
        xy,
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
    assert!(!d.factored);
    // The smallest laws cost little: two sums of two one-word terms on each side.
    let d = decide(&t("a + c"), &t("c + a"), &["a", "c"], Carrier::Int);
    assert_eq!((d.verdict, d.size, d.work), (Verdict::Proved, 6, 8.8));
    let d = decide(&t("x"), &t("x"), &["x"], Carrier::Int);
    assert_eq!((d.verdict, d.size, d.work), (Verdict::Proved, 2, 0.0));
    // An exponent past u64::MAX on a name, in a sum (alone it is a factor: `products_of_powers`).
    let Verdict::Refused(r) = verdict(
        "x ^ 18446744073709551616 - x",
        "x ^ 18446744073709551616 - x",
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
fn products_of_powers() {
    let xy = &["x", "y"];
    // Products of powers of the same factors, each factor expanded once, the sides never.
    for (l, r, c) in [
        (
            "(1 + x) ^ 1048576",
            "(1 + x) ^ 524288 * (x + 1) ^ 524288",
            Carrier::Int,
        ),
        // Exponents past u64::MAX, which the expansion refuses.
        (
            "(x + y) ^ 18446744073709551616",
            "(y + x) ^ 18446744073709551616",
            Carrier::Int,
        ),
        (
            "x ^ 18446744073709551616",
            "x ^ 18446744073709551616",
            Carrier::Int,
        ),
        // Powers of products and of powers.
        ("((x + y) ^ 3 * x) ^ 2", "x ^ 2 * (y + x) ^ 6", Carrier::Int),
        // Signs: `y - x` is -1 times `x - y`.
        (
            "(x - y) ^ 1000001 * (y - x)",
            "-((y - x) ^ 1000002)",
            Carrier::Int,
        ),
        (
            "(-1) ^ 18446744073709551617 * (1 + x) ^ 99",
            "-((x + 1) ^ 99)",
            Carrier::Int,
        ),
        // Constants: the content of a factor, and constants that do not cancel.
        ("(2 * x + 2 * y) ^ 3", "8 * (x + y) ^ 3", Carrier::Int),
        ("(x / 2 + y / 2) ^ 4", "(x + y) ^ 4 / 16", Carrier::Rat),
        ("2 ^ 10 * (x + y) ^ 9", "4 ^ 5 * (y + x) ^ 9", Carrier::Ring),
        // A factor of zero.
        ("(x - x) ^ 5 * (x + y) ^ 1000000", "0", Carrier::Int),
    ] {
        let d = decide(&t(l), &t(r), xy, c);
        assert_eq!(d.verdict, Verdict::Proved, "{l} == {r}");
        assert!(d.factored, "{l} == {r}");
        assert_eq!(d.terms, None, "{l} == {r}");
    }
    // A shared value is read once: 60 squarings by `let` are `(x + y) ^ (2 ^ 60)`.
    let mut shared = var("a60");
    for i in (1..=60).rev() {
        let value = if i == 1 {
            t("(x + y) * (y + x)")
        } else {
            let a = format!("a{}", i - 1);
            prim(Prim::Mul, vec![var(&a), var(&a)])
        };
        shared = let_(&format!("a{i}"), value, shared);
    }
    let d = decide(
        &shared,
        &t("(x + y) ^ 1152921504606846976"),
        xy,
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, true));
    // Different factors are left to the expansion.
    let d = decide(
        &t("(1 + x) ^ 3 * (1 - x) ^ 3"),
        &t("(1 - x ^ 2) ^ 3"),
        xy,
        Carrier::Int,
    );
    assert_eq!(
        (d.verdict, d.factored, d.terms),
        (Verdict::Proved, false, Some([4, 4]))
    );
    // A side that is a sum is one factor at exponent 1: the expansion decides at once.
    let d = decide(
        &t("x * x - y * y"),
        &t("(x - y) * (x + y)"),
        xy,
        Carrier::Int,
    );
    assert_eq!(
        (d.verdict, d.factored, d.terms),
        (Verdict::Proved, false, Some([2, 2]))
    );
    // A factor that holds a product of four sums is expanded once.
    let eight = &["a", "b", "c", "d", "e", "f", "g", "h"];
    let d = decide(
        &t("((a + b) * (c + d) * (e + f) * (g + h) + 1) ^ 2"),
        &t("((h + g) * (f + e) * (d + c) * (b + a) + 1) ^ 2"),
        eight,
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, true));
    // A factor whose expansion passes the limit leaves the identity to the expansion, which
    // refuses it at the same limit.
    let d = decide(
        &t("((1 + x) ^ 256 * (1 + y) ^ 256 * (1 + z) ^ 256 + 1) ^ 2"),
        &t("((1 + z) ^ 256 * (1 + y) ^ 256 * (1 + x) ^ 256 + 1) ^ 2"),
        &["x", "y", "z"],
        Carrier::Int,
    );
    assert!(!d.factored);
    let Verdict::Refused(r) = d.verdict else {
        panic!("not refused")
    };
    assert!(matches!(r.why, Refused::Work(w) if w > LIMIT));
    // A product of powers of different factors is left to the expansion, which proves it while
    // its predicted time is below the limit.
    let d = decide(
        &t("(1 + x) ^ 200 * (1 - x) ^ 200"),
        &t("(1 - x ^ 2) ^ 200"),
        xy,
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, false));
    // Exponents that multiply past `2^128` are left to the expansion, which refuses them.
    let Verdict::Refused(r) = verdict(
        "((x + y) ^ 18446744073709551616) ^ 18446744073709551616",
        "((y + x) ^ 18446744073709551616) ^ 18446744073709551616",
        xy,
        Carrier::Int,
    ) else {
        panic!()
    };
    assert_eq!(r.why, Refused::Exponent);
    // A false identity of any size is refuted at a point first.
    for (l, r) in [
        ("(1 + x) ^ 1048576", "(1 + x) ^ 524288 * (1 + x) ^ 524289"),
        ("(2 * x + 2) ^ 2", "2 * (x + 1) ^ 2"),
        ("(x - y) ^ 3", "(y - x) ^ 3"),
        (
            "(x + y) ^ 18446744073709551616",
            "(x + y) ^ 18446744073709551617",
        ),
    ] {
        assert!(
            matches!(verdict(l, r, xy, Carrier::Int), Verdict::Refuted(_)),
            "{l} == {r}"
        );
    }
}

#[test]
fn the_points_are_deterministic() {
    let a = || {
        decide(
            &t("(1 + x) ^ 256 * (1 + y) ^ 256 * (1 + z) ^ 256 - x"),
            &t("(1 + z) ^ 256 * (1 + y) ^ 256 * (1 + x) ^ 256 - x"),
            &["x", "y", "z"],
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
    assert!(matches!(
        id.keys(&id.shapes(), &id.reachable(&id.sides)),
        Keys::Sparse
    ));
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
    let plan = a.plan(b).expect("packed keys");
    a.support_mul(b, &plan, f64::INFINITY, &mut 0.0)
        .expect("no budget")
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
    let budget = plan.dense.min(plan.sparse);
    let mut spent = 0.0;
    assert_eq!(
        a.support_mul(&a, &plan, budget, &mut spent),
        Some(a.sparse_mul(&a))
    );
    assert!(spent < budget, "{spent} of {budget}");
    // Sides whose pairs are all distinct go to the sparse product: the sampled estimate says so.
    let b = sum_at((0..64u128).map(|i| (i * i * i * 1009 + i, 1)));
    let plan = b.plan(&b).expect("packed keys");
    let budget = plan.dense.min(plan.sparse);
    assert_eq!(b.support_mul(&b, &plan, budget, &mut 0.0), None);
}

/// The work the expansion of `term == 0` counts with no limit, and that identity's size.
fn work_of(term: &Term, binders: &[&str]) -> (f64, u64) {
    let zero = lit(0);
    let id = Identity::new(term, &zero, binders, Carrier::Int);
    let shapes = id.shapes();
    let reach = id.reachable(&id.sides);
    let mut budget = Budget::new(f64::INFINITY);
    let done = match id.keys(&shapes, &reach) {
        Keys::Packed(ctx) => id
            .expand::<u128>(&ctx, &reach, &id.sides, &mut budget)
            .is_ok(),
        Keys::Sparse => id
            .expand::<Sparse>(&Packing::none(), &reach, &id.sides, &mut budget)
            .is_ok(),
    };
    assert!(done, "an unbounded budget");
    (budget.spent, id.size)
}

/// The terms read by merging `s` sums of one term each, smallest first ([`Poly::sum`]):
/// `s q + 2 (s - 2^q)` for `q = floor(log2 s)`, each term read once per level of a merge tree
/// whose leaves sit at depths `q` and `q + 1`.
fn merged_terms(s: usize) -> f64 {
    let q = s.ilog2();
    (s * q as usize + 2 * (s - (1 << q))) as f64
}

/// The charges of [`LIMIT`]'s units: a sum of `s` names written `x1 + … + xs` merges its `s`
/// one-word summands two at a time, smallest first, each term read [`SUM_TERM`] and its word
/// [`SUM_WORD`]; a product of two sums in different names, sparse below the dense cost,
/// [`PAIR`] plus one word for each pair.
#[test]
fn the_charges_are_the_measured_ones() {
    let names: Vec<String> = (0..40).map(|i| format!("x{i}")).collect();
    let binders: Vec<&str> = names.iter().map(String::as_str).collect();
    let sum = |from: usize, n: usize| format!("({})", names[from..from + n].join(" + "));
    for s in 1..=40 {
        let (work, _) = work_of(&t(&sum(0, s)), &binders);
        assert!(
            (work - merged_terms(s) * (SUM_TERM + SUM_WORD)).abs() < 1e-9,
            "{s}: {work}"
        );
    }
    let (work, _) = work_of(&t(&format!("{} * {}", sum(0, 20), sum(20, 20))), &binders);
    let sums = 2.0 * merged_terms(20) * (SUM_TERM + SUM_WORD);
    assert!((work - sums - 400.0 * (PAIR + 1.0)).abs() < 1e-9, "{work}");
}

/// A chain of sums and differences is read as one sum of its summands with their signs, in
/// every shape it is written in, and a partial sum that is read elsewhere is formed once.
#[test]
fn a_chain_of_sums_is_one_sum() {
    let b = ["x", "y", "z", "w"];
    assert_eq!(nf("x - y - z - w", &b), "x - y - z - w");
    assert_eq!(nf("0 - x - y + 2", &b), "-x - y + 2");
    // Left-deep, right-deep and mixed, with subtractions that flip a whole chain.
    assert_eq!(nf("x + y - z + w", &b), nf("w + (x + (y - z))", &b));
    assert_eq!(nf("x - (y - (z - w))", &b), nf("x - y + z - w", &b));
    assert_eq!(nf("x - (y + z + w)", &b), nf("x - y - z - w", &b));
    // Every summand subtracted: the sum is negated once at the end.
    assert_eq!(nf("0 - x - y - z", &b), nf("-(x + y + z)", &b));
    // Summands that cancel, and repeated ones.
    assert_eq!(nf("x + y - x - y + z", &b), nf("z", &b));
    assert_eq!(nf("x + x + x - y", &b), nf("3 * x - y", &b));
    assert_eq!(nf("x - x", &b), nf("0", &b));
    // A summand that is a product or a power is formed first and merged whole.
    assert_eq!(nf("(x + y) * (x - y) + y * y - x * x + z", &b), nf("z", &b));
    // A partial sum shared through a `let` is formed once and read by both chains.
    let shared = let_("s", t("x + y + z"), t("s + w - s + s * s"));
    assert_eq!(
        normal_form(&shared, &b, Carrier::Int).expect("not refused"),
        nf(
            "w + x * x + y * y + z * z + 2 * x * y + 2 * x * z + 2 * y * z",
            &b
        )
    );
    // Rational coefficients with different denominators merge over their common one.
    let r = |s: &str| normal_form(&t(s), &b, Carrier::Rat).expect("expanded");
    assert_eq!(r("x / 2 + x / 3 + y / 6 - x"), r("y / 6 - x / 6"));
}
