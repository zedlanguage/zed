//! The rule of low complexity (DESIGN.md Part G): each family at n and 8n, the work held to
//! the order of its output. The terms are built as balanced trees of kernel terms, so their
//! depth is `log n`, and before any run is timed.

use zed_kernel::poly::{Carrier, Verdict, decide};
use zed_kernel::term::build::{lit, prim, var};
use zed_kernel::term::{Prim, Term};
use zed_tests::instances::Rng;
use zed_tests::scaling;

/// The sum of `terms` as a balanced tree.
fn sum(terms: &[Term]) -> Term {
    match terms {
        [] => lit(0),
        [t] => t.clone(),
        _ => {
            let (a, b) = terms.split_at(terms.len() / 2);
            prim(Prim::Add, vec![sum(a), sum(b)])
        }
    }
}

fn mul(a: Term, b: Term) -> Term {
    prim(Prim::Mul, vec![a, b])
}

fn pow(a: Term, n: i64) -> Term {
    prim(Prim::Pow, vec![a, lit(n)])
}

/// An identity and its binders.
struct Id {
    lhs: Term,
    rhs: Term,
    names: Vec<String>,
}

fn proved(id: &Id) {
    let names: Vec<&str> = id.names.iter().map(String::as_str).collect();
    let d = decide(&id.lhs, &id.rhs, &names, Carrier::Int);
    assert_eq!(d.verdict, Verdict::Proved);
}

/// `(1 + x + ... + x ^ k) ^ 2` against its `2k + 1` written monomials: one dense product.
fn square(k: usize) -> Id {
    let x = || var("x");
    let ones: Vec<Term> = (0..=k).map(|i| pow(x(), i as i64)).collect();
    let written: Vec<Term> = (0..=2 * k)
        .map(|j| {
            let c = j.min(2 * k - j) + 1;
            mul(lit(c as i64), pow(x(), j as i64))
        })
        .collect();
    Id {
        lhs: pow(sum(&ones), 2),
        rhs: sum(&written),
        names: vec!["x".into()],
    }
}

/// `A * B == B * A` for `A` and `B` of `n` random coefficients of 62 bits each in `x`.
fn commute(n: usize) -> Id {
    let mut rng = Rng::new(7);
    let mut poly = || {
        let terms: Vec<Term> = (0..n)
            .map(|i| {
                let c = (rng.next_u64() >> 1) as i64 - (1 << 62);
                mul(lit(c), pow(var("x"), i as i64))
            })
            .collect();
        sum(&terms)
    };
    let (a, b) = (poly(), poly());
    Id {
        lhs: mul(a.clone(), b.clone()),
        rhs: mul(b, a),
        names: vec!["x".into()],
    }
}

/// `(x0 + ... + x(n-1)) * (y + z)` against its `2n` written monomials: `n + 2` names, so the
/// monomials are lists past `u128`'s Kronecker keys.
fn linear(n: usize) -> Id {
    let mut names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    names.push("y".into());
    names.push("z".into());
    let xs: Vec<Term> = (0..n).map(|i| var(&format!("x{i}"))).collect();
    let written: Vec<Term> = (0..n)
        .flat_map(|i| ["y", "z"].map(|w| mul(var(&format!("x{i}")), var(w))))
        .collect();
    Id {
        lhs: mul(sum(&xs), sum(&[var("y"), var("z")])),
        rhs: sum(&written),
        names,
    }
}

/// `(1 + x + ... + x ^ (n-1)) * (1 + y + ... + y ^ (n-1))` and the same product commuted:
/// `n^2` distinct monomials, so order 2 in `n`, `n log n` in the output.
fn grid(n: usize) -> Id {
    let side = |w: &str| sum(&(0..n).map(|i| pow(var(w), i as i64)).collect::<Vec<_>>());
    Id {
        lhs: mul(side("x"), side("y")),
        rhs: mul(side("y"), side("x")),
        names: vec!["x".into(), "y".into()],
    }
}

#[test]
fn the_square_of_a_sum_of_k_powers() {
    let ins = scaling::inputs(1000, square);
    scaling::check("(1 + x + ... + x ^ k) ^ 2 of k terms", 1000, |n| {
        proved(&ins[&n])
    });
}

#[test]
fn a_dense_product_of_n_terms_commuted() {
    let ins = scaling::inputs(1000, commute);
    scaling::check("A * B == B * A, n terms each", 1000, |n| proved(&ins[&n]));
}

#[test]
fn a_sum_of_n_names_times_a_sum() {
    let ins = scaling::inputs(500, linear);
    scaling::check("(x0 + ... + xn) * (y + z)", 500, |n| proved(&ins[&n]));
}

#[test]
fn a_grid_of_n_squared_monomials() {
    let ins = scaling::inputs(30, grid);
    scaling::check_order("(sum x ^ i) * (sum y ^ j), n terms each", 30, 2, |n| {
        proved(&ins[&n])
    });
}

/// `(x + y) ^ k == (x + y) ^ (k / 2) * (y + x) ^ (k - k / 2)`: a power of a sum of two names
/// counts one sum (POLY-nf-power), and expands to `k + 1` monomials of up to `k` bits, so order
/// 2 in `k`, linear in the output's bits. Each side's squarings multiply homogeneous sums, whose
/// packed indices are a common step apart (`Poly::dense_cost`).
fn binomial(k: usize) -> Id {
    let s = |a: &str, b: &str| sum(&[var(a), var(b)]);
    let h = k / 2;
    Id {
        lhs: pow(s("x", "y"), k as i64),
        rhs: mul(pow(s("x", "y"), h as i64), pow(s("y", "x"), (k - h) as i64)),
        names: vec!["x".into(), "y".into()],
    }
}

#[test]
fn a_power_of_a_sum_of_two_names() {
    let ins = scaling::inputs(500, binomial);
    scaling::check_order("(x + y) ^ k, k + 1 monomials of k bits", 500, 2, |n| {
        proved(&ins[&n])
    });
}
