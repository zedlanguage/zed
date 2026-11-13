//! The rule of low complexity (DESIGN.md Part G): each family at n and 8n, the work held to
//! the order of its output. The terms are built as balanced trees of kernel terms, so their
//! depth is `log n`, and before any run is timed.

use std::sync::Arc;

use num_bigint::BigInt;
use zed_kernel::poly::{Carrier, LIMIT, Verdict, decide};
use zed_kernel::term::build::{lit, prim, var};
use zed_kernel::term::{Prim, Term};
use zed_kernel::{Rat, Value};
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

/// The written monomials `c * x ^ i * y ^ j`, as a balanced sum.
fn written(monomials: impl IntoIterator<Item = (BigInt, usize, usize)>) -> Term {
    let terms: Vec<Term> = monomials
        .into_iter()
        .map(|(c, i, j)| {
            let c = Term::Lit(Value::Big(Arc::new(Rat::int(c))));
            mul(c, mul(pow(var("x"), i as i64), pow(var("y"), j as i64)))
        })
        .collect();
    sum(&terms)
}

/// The binomial coefficients `C(k, 0) … C(k, k)`.
fn binomials(k: usize) -> Vec<BigInt> {
    let mut row = vec![BigInt::from(1)];
    for i in 0..k {
        let next = &row[i] * BigInt::from(k - i) / BigInt::from(i + 1);
        row.push(next);
    }
    row
}

/// `a - x`: a sum, so that the expansion decides it, not the reading of a product of powers of
/// the same factors (`Decision::factored`).
fn less_x(a: Term) -> Term {
    prim(Prim::Sub, vec![a, var("x")])
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
    // The counted work beside the meter's instructions: their ratio is the spread of the
    // counter (COMPLEXITY.md POLY-nf-work).
    eprintln!("size {} work {} limit {LIMIT}", d.size, d.work);
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

/// `A * B - x == B * A - x` for `A` and `B` of `n` random coefficients of 62 bits each in `x`.
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
        lhs: less_x(mul(a.clone(), b.clone())),
        rhs: less_x(mul(b, a)),
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

/// `(1 + x + ... + x ^ (n-1)) * (1 + y + ... + y ^ (n-1)) - x` and the same product commuted:
/// `n^2` distinct monomials, so order 2 in `n`, `n log n` in the output.
fn grid(n: usize) -> Id {
    let side = |w: &str| sum(&(0..n).map(|i| pow(var(w), i as i64)).collect::<Vec<_>>());
    Id {
        lhs: less_x(mul(side("x"), side("y"))),
        rhs: less_x(mul(side("y"), side("x"))),
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

/// The sum of `terms` as written, `((t0 + t1) + t2) + …`: a left-deep chain of depth `n`.
fn chain(terms: impl IntoIterator<Item = Term>) -> Term {
    terms
        .into_iter()
        .reduce(|a, b| prim(Prim::Add, vec![a, b]))
        .unwrap_or_else(|| lit(0))
}

/// [`linear`] with both sums written as chains, as a law's source gives them: the chain is
/// read as one sum of its summands, not as `n` sums of growing partial sums
/// (POLY-sum-chain-fold).
fn linear_chain(n: usize) -> Id {
    let mut names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    names.push("y".into());
    names.push("z".into());
    let written = (0..n).flat_map(|i| ["y", "z"].map(|w| mul(var(&format!("x{i}")), var(w))));
    Id {
        lhs: mul(
            chain((0..n).map(|i| var(&format!("x{i}")))),
            chain([var("y"), var("z")]),
        ),
        rhs: chain(written),
        names,
    }
}

#[test]
fn a_written_chain_of_n_names_times_a_sum() {
    let ins = scaling::inputs(500, linear_chain);
    scaling::check(
        "x0 + ... + xn written as a chain, times (y + z)",
        500,
        |n| proved(&ins[&n]),
    );
}

/// The plan row's law, from Zed source: before the chain was read as one sum, its written side
/// of 8192 monomials cost about 3.6 s and was refused by the limit.
#[test]
fn the_law_of_4096_names_times_a_sum_is_proved_from_source() {
    let n = 4096;
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let params: Vec<String> = xs
        .iter()
        .chain(["y".to_string(), "z".to_string()].iter())
        .map(|x| format!("{x}: int"))
        .collect();
    let lhs = format!("({}) * (y + z)", xs.join(" + "));
    let rhs: Vec<String> = xs
        .iter()
        .flat_map(|x| [format!("{x} * y"), format!("{x} * z")])
        .collect();
    let src = format!(
        "sides({}) = ({lhs}, {});\n",
        params.join(", "),
        rhs.join(" + ")
    );
    let sides = &super::sides_of(&src, &["sides"])[0];
    // The elaboration of the source is not timed: only the decision is the row's.
    let start = std::time::Instant::now();
    let d = super::decide_sides(sides, Carrier::Int);
    eprintln!("work {} limit {LIMIT}, {:?}", d.work, start.elapsed());
    assert_eq!(d.verdict, Verdict::Proved);
    assert!(d.work <= LIMIT / 10.0, "{} of {LIMIT}", d.work);
}

/// `x0 * x1 * c0 + ... + x(n-1) * x0 * c(n-1) - x0` against the same monomials in reverse,
/// `c` of two words each: `n` names, so the monomials are lists past `u128`'s Kronecker keys,
/// and only sums are formed, each charged by its terms and words (`poly::LIMIT`, QUESTIONS
/// A99), so order `n log n` with the balanced tree.
fn ring_of_names(n: usize) -> Id {
    let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let c = |i: usize| Term::Lit(Value::Big(Arc::new(Rat::int(BigInt::from(i + 1) << 100))));
    let monomial = |i: usize| mul(c(i), mul(var(&names[i]), var(&names[(i + 1) % n])));
    let forward: Vec<Term> = (0..n).map(monomial).collect();
    let backward: Vec<Term> = (0..n).rev().map(monomial).collect();
    Id {
        lhs: less_x(sum(&forward)),
        rhs: less_x(sum(&backward)),
        names,
    }
}

#[test]
fn a_sum_of_n_monomials_in_n_names() {
    let ins = scaling::inputs(1000, ring_of_names);
    scaling::check("x0 * x1 * c0 + ... + x(n-1) * x0 * c(n-1)", 1000, |n| {
        proved(&ins[&n])
    });
}

#[test]
fn a_grid_of_n_squared_monomials() {
    let ins = scaling::inputs(30, grid);
    scaling::check_order("(sum x ^ i) * (sum y ^ j), n terms each", 30, 2, |n| {
        proved(&ins[&n])
    });
}

/// `(x + y) ^ k - x` against its `k + 1` monomials written out, less `x`: the power expands to
/// `k + 1` monomials of up to `k` bits, so order 2 in `k`, linear in the output's bits. The
/// squarings multiply homogeneous sums, whose packed indices are a common step apart
/// (`Poly::plan`). The written side makes the law long enough to be expanded: written as two
/// powers, `(x + y) ^ k` costs about `k^2 / 64` words, which the size rule of QUESTIONS A98
/// refused from k = 72 on; the limit of 250 ms (`poly::LIMIT`, QUESTIONS A99) is passed
/// between k = 4096 and 8192 (`l03_09_egraph::calibration`).
fn binomial(k: usize) -> Id {
    let s = |a: &str, b: &str| sum(&[var(a), var(b)]);
    let c = binomials(k);
    Id {
        lhs: less_x(pow(s("x", "y"), k as i64)),
        rhs: less_x(written(
            c.into_iter().enumerate().map(|(i, c)| (c, i, k - i)),
        )),
        names: vec!["x".into(), "y".into()],
    }
}

/// `(x0 + y) ^ 1 * (x1 + y) ^ 2 * ... * (x(n-1) + y) ^ n * (1 + y) ^ (2^62)` against the same
/// factors written backward, each sum reversed, as balanced products: read as a product of
/// powers of the same factors (POLY-nf-power-value), each factor expanded once and hashed, so
/// order `n` (a hash map), though either side expanded has more than `2^n` monomials.
fn factors(n: usize) -> Id {
    let mut names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    names.push("y".into());
    let product = |backward: bool| {
        let mut parts: Vec<Term> = (0..n)
            .map(|i| {
                let (a, b) = (var(&format!("x{i}")), var("y"));
                let base = if backward { sum(&[b, a]) } else { sum(&[a, b]) };
                pow(base, i as i64 + 1)
            })
            .collect();
        parts.push(pow(sum(&[lit(1), var("y")]), 1 << 62));
        if backward {
            parts.reverse();
        }
        fn balanced(ts: &[Term]) -> Term {
            match ts {
                [t] => t.clone(),
                _ => {
                    let (a, b) = ts.split_at(ts.len() / 2);
                    mul(balanced(a), balanced(b))
                }
            }
        }
        balanced(&parts)
    };
    Id {
        lhs: product(false),
        rhs: product(true),
        names,
    }
}

#[test]
fn a_product_of_powers_of_n_factors() {
    let ins = scaling::inputs(500, factors);
    scaling::check(
        "(x0 + y) * ... * (xn + y) ^ n, n factors read as powers",
        500,
        |n| proved(&ins[&n]),
    );
}

#[test]
fn a_power_of_a_sum_of_two_names() {
    let ins = scaling::inputs(500, binomial);
    scaling::check_order("(x + y) ^ k, k + 1 monomials of k bits", 500, 2, |n| {
        proved(&ins[&n])
    });
}

/// `((x + y) ^ k + x) ^ 2` against its `3k + 3` monomials written out, `k >= 2`: the square
/// multiplies a sum whose monomials are homogeneous of degree `k` apart from `x`, so its packed
/// indices leave gaps that no common step removes, and its product is formed from its `3k + 3`
/// output monomials, not from the `(k + 2)^2` pairs or the `(k + 1)^2` indices the pairs span
/// (POLY-nf-sparse-product). The output has `3k + 3` monomials of up to `2k` bits: order 2 in
/// `k`. Written out, the law is long enough to be expanded (`binomial`).
fn gapped_square(k: usize) -> Id {
    let xy = || sum(&[var("x"), var("y")]);
    let twice = binomials(2 * k)
        .into_iter()
        .enumerate()
        .map(|(i, c)| (c, i, 2 * k - i));
    let middle = binomials(k)
        .into_iter()
        .enumerate()
        .map(|(i, c)| (2 * c, i + 1, k - i));
    let square = std::iter::once((BigInt::from(1), 2, 0));
    Id {
        lhs: pow(sum(&[pow(xy(), k as i64), var("x")]), 2),
        rhs: written(twice.chain(middle).chain(square)),
        names: vec!["x".into(), "y".into()],
    }
}

#[test]
fn the_square_of_a_power_of_a_sum_beside_one_name() {
    // At k = 2048 the square is about 2 s of work, refused (QUESTIONS A99); 8 * 32 = 256 is
    // about 50 ms.
    let ins = scaling::inputs(32, gapped_square);
    scaling::check_order(
        "((x + y) ^ k + x) ^ 2, 3k + 3 monomials of 2k bits",
        32,
        2,
        |n| proved(&ins[&n]),
    );
}
