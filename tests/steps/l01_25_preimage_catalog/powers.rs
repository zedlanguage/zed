//! A product whose factors are all one value, `k` of them, is read as its power `e ** k`
//! before revision (DESIGN.md sec:constraints, "How a constraint reaches the domains"), for
//! any `k`: its preimage is that of the power written out. Products of factors that differ
//! are not powers, and the reading costs time linear in the product.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::{Demand, Domains, Preimage, preimage};

use super::{check, doms, shown};

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn bind(x: &str, e: Term, body: Term) -> Term {
    Term::Let(x.into(), Arc::new(e), Arc::new(body))
}

/// `f * f * … * f`, `k` factors, multiplied from the left as the parser groups them.
fn product(f: &Term, k: usize) -> Term {
    (1..k).fold(f.clone(), |p, _| prim(Prim::Mul, p, f.clone()))
}

/// `f * (f * (… * f))`, `k` factors, multiplied from the right.
fn product_right(f: &Term, k: usize) -> Term {
    (1..k).fold(f.clone(), |p, _| prim(Prim::Mul, f.clone(), p))
}

/// `k` factors `f`, split in halves at each level, as `(x * x) * (x * x)` is.
fn product_halved(f: &Term, k: usize) -> Term {
    if k == 1 {
        return f.clone();
    }
    prim(
        Prim::Mul,
        product_halved(f, k / 2),
        product_halved(f, k - k / 2),
    )
}

fn power(f: &Term, k: usize) -> Term {
    prim(Prim::Pow, f.clone(), int(k as i64))
}

fn at_most(t: Term, n: i64) -> Term {
    prim(Prim::Le, t, int(n))
}

fn pre(t: &Term, ds: &Domains) -> Preimage {
    preimage(t, ds, &Demand::Bool(true))
}

/// `i + 1`, a factor that is a term and not a name.
fn shifted() -> Term {
    prim(Prim::Add, var("i"), int(1))
}

/// Asserts that `test(product)` and `test(f ** k)` have the same preimage over `ds`, and
/// returns it printed.
fn same_as_power(
    f: &Term,
    k: usize,
    make: fn(&Term, usize) -> Term,
    test: impl Fn(Term) -> Term,
    ds: &Domains,
) -> String {
    let written = pre(&test(make(f, k)), ds);
    let pow = pre(&test(power(f, k)), ds);
    assert_eq!(written, pow, "{k} factors {f}");
    shown(&written)
}

#[test]
fn a_product_of_one_factor_any_number_of_times_is_read_as_its_power() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    // `i * i * … * i <= 1`: for an even count, `-1 <= i <= 1`; for an odd count, `i <= 1`.
    let le1 = |t| at_most(t, 1);
    for (k, want) in [
        (1, "i [-50..=1]; exact"),
        (2, "i [-1..=1]; exact"),
        (64, "i [-1..=1]; exact"),
        (65, "i [-50..=1]; exact"),
        (1000, "i [-1..=1]; exact"),
        (1001, "i [-50..=1]; exact"),
    ] {
        assert_eq!(
            same_as_power(&var("i"), k, product, le1, &ds),
            want,
            "k = {k}"
        );
    }
}

#[test]
fn a_repeated_term_past_64_factors_is_read_as_its_power() {
    // `(i + 1) * … * (i + 1) <= 0`, 65 factors: an odd power, so `i + 1 <= 0`.
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let le0 = |t| at_most(t, 0);
    assert_eq!(
        same_as_power(&shifted(), 65, product, le0, &ds),
        "i [-50..=-1]; exact"
    );
    // 1000 factors: an even power, 0 only at `i = -1`.
    assert_eq!(
        same_as_power(&shifted(), 1000, product, le0, &ds),
        "i [-1..=-1]; exact"
    );
}

#[test]
fn the_grouping_of_the_factors_does_not_change_the_power() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let le1 = |t| at_most(t, 1);
    for k in [2, 3, 64, 65, 1000] {
        let left = same_as_power(&var("i"), k, product, le1, &ds);
        assert_eq!(
            same_as_power(&var("i"), k, product_right, le1, &ds),
            left,
            "k = {k}"
        );
        assert_eq!(
            same_as_power(&var("i"), k, product_halved, le1, &ds),
            left,
            "k = {k}"
        );
    }
}

#[test]
fn a_power_reads_as_one_whatever_its_demand_on_the_value() {
    // `i * … * i` in `[0..=1]`, 100 factors, as the demand on the product's value.
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let z = Demand::Ints(IntervalSet::range(
        zedc::store::interval::End::Fin(0),
        zedc::store::interval::End::Fin(1),
    ));
    let written = preimage(&product(&var("i"), 100), &ds, &z);
    assert_eq!(written, preimage(&power(&var("i"), 100), &ds, &z));
    assert_eq!(shown(&written), "i [-1..=1]; exact");
}

#[test]
fn factors_bound_to_names_are_followed() {
    // `y = i * i; z = y * y * … * y` with 40 factors `y`: `i ** 80`.
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let t = bind(
        "y",
        prim(Prim::Mul, var("i"), var("i")),
        at_most(product(&var("y"), 40), 1),
    );
    let p = pre(&t, &ds);
    assert_eq!(p, pre(&at_most(power(&var("i"), 80), 1), &ds));
    assert_eq!(shown(&p), "i [-1..=1]; exact");
}

#[test]
fn a_product_shared_by_names_counts_each_factor_it_stands_for() {
    // `x1 = i * i; x2 = x1 * x1; …; x20 <= 1`: `i ** 2^20`, read once per name.
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let depth = 20;
    let mut body = at_most(var(&format!("x{depth}")), 1);
    for n in (1..=depth).rev() {
        let prev = if n == 1 {
            "i".to_string()
        } else {
            format!("x{}", n - 1)
        };
        body = bind(
            &format!("x{n}"),
            prim(Prim::Mul, var(&prev), var(&prev)),
            body,
        );
    }
    let p = pre(&body, &ds);
    assert_eq!(p, pre(&at_most(power(&var("i"), 1 << depth), 1), &ds));
    assert_eq!(shown(&p), "i [-1..=1]; exact");
}

#[test]
fn a_shared_count_past_the_exponent_width_is_read_from_its_two_halves() {
    // `x1 = i * i; …; x32 <= 0`: 2^32 factors, one more than the `u32` exponent of `**`
    // holds. `x32` is read by the entry for `*` from its two operands, each `x31`, which is
    // `i ** 2^31`. The box must hold `i = 0`, the one point that meets the demand.
    let ds = doms(&[("i", Some(-3), Some(3))]);
    let depth = 32;
    let mut body = at_most(var(&format!("x{depth}")), 0);
    for n in (1..=depth).rev() {
        let prev = if n == 1 {
            "i".to_string()
        } else {
            format!("x{}", n - 1)
        };
        body = bind(
            &format!("x{n}"),
            prim(Prim::Mul, var(&prev), var(&prev)),
            body,
        );
    }
    let p = pre(&body, &ds);
    assert!(p.domains["i"].contains(0), "{}", shown(&p));
}

#[test]
fn factors_that_differ_are_not_a_power() {
    let ds = doms(&[("i", Some(-50), Some(50)), ("j", Some(-50), Some(50))]);
    // `i * i * j <= 1`: a product of two values, read by the entry for `*`.
    let mixed = at_most(prim(Prim::Mul, product(&var("i"), 2), var("j")), 1);
    // `i * (j * i) <= 1`: the same factor twice, not next to each other.
    let apart = at_most(
        prim(Prim::Mul, var("i"), prim(Prim::Mul, var("j"), var("i"))),
        1,
    );
    // `(i * i) * (j * j) <= 1`: two powers of different values.
    let two = at_most(
        prim(Prim::Mul, product(&var("i"), 2), product(&var("j"), 2)),
        1,
    );
    for t in [mixed, apart, two] {
        let p = pre(&t, &ds);
        // None is the square or the cube of one value, so no product is read as one.
        assert!(!p.exact, "{t}: {}", shown(&p));
        check(&t, &ds, &Demand::Bool(true), &p, (-6, 6));
    }
    // `(i * i) * (i + 0)`: the same value, but not the same term, is not read as a power.
    let other = at_most(
        prim(
            Prim::Mul,
            product(&var("i"), 2),
            prim(Prim::Add, var("i"), int(0)),
        ),
        1,
    );
    let p = pre(&other, &ds);
    check(&other, &ds, &Demand::Bool(true), &p, (-6, 6));
}

#[test]
fn a_product_with_a_different_factor_holds_powers_inside_it() {
    // `(i * i * … * i) * j <= 1`, 100 factors `i`: the inner product is still read as
    // `i ** 100`, so its interval is `[0..=50 ** 100]` and not that of 100 independent
    // factors, which would hold negative values.
    let ds = doms(&[("i", Some(-50), Some(50)), ("j", Some(1), Some(50))]);
    let t = at_most(prim(Prim::Mul, product(&var("i"), 100), var("j")), 1);
    let u = at_most(prim(Prim::Mul, power(&var("i"), 100), var("j")), 1);
    let p = pre(&t, &ds);
    assert_eq!(p, pre(&u, &ds));
    check(&t, &ds, &Demand::Bool(true), &p, (-3, 3));
}

/// The sizes are a product of 512 factors and one of 4096. The transfer recurses on the depth
/// of the term, so the measurement runs on a 256 MiB stack, as the `long` tests of
/// [`super::scaling`] do; the terms are built before the timing.
#[test]
fn reading_a_product_as_a_power_is_linear_in_its_factors() {
    let measure = || {
        let ds = doms(&[("i", Some(-50), Some(50)), ("j", Some(-50), Some(50))]);
        let sizes = [512, scaling::FACTOR * 512];
        let at = |k: usize| sizes.iter().position(|&s| s == k).expect("a built size");
        // `i * i * … * i <= 1`.
        let powers: Vec<Term> = sizes
            .iter()
            .map(|&k| at_most(product(&var("i"), k), 1))
            .collect();
        scaling::check("`i * i * … * i <= 1` with n factors", sizes[0], |k| {
            pre(&powers[at(k)], &ds);
        });
        // `i * i * j * i * j * … <= 1`: no product but the innermost is a power, and the first
        // factor of each product lies as deep as the product, so a reading that looks into the
        // factors of each product again costs the square of their number.
        let alternating = |k: usize| {
            (2..k).fold(product(&var("i"), 2), |p, n| {
                let f = if n % 2 == 0 { "j" } else { "i" };
                prim(Prim::Mul, p, var(f))
            })
        };
        let mixed: Vec<Term> = sizes.iter().map(|&k| at_most(alternating(k), 1)).collect();
        scaling::check(
            "`i * i * j * i * j * … <= 1` with n factors",
            sizes[0],
            |k| {
                pre(&mixed[at(k)], &ds);
            },
        );
    };
    let thread = std::thread::Builder::new().stack_size(1 << 28);
    thread.spawn(measure).unwrap().join().unwrap();
}
