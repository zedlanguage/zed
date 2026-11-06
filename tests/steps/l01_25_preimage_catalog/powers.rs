//! A product whose factors are all one value, `k` of them, is read as its power `e ** k`
//! before revision (DESIGN.md sec:constraints, "How a constraint reaches the domains"), for
//! any `k`: its preimage is that of the power written out. Products of factors that differ
//! are not powers, and the reading costs time linear in the product.

use zed_kernel::Shared;

use num_bigint::BigInt;
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
    Term::Let(x.into(), Shared::new(e), Shared::new(body))
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
        zedc::store::interval::End::of(0),
        zedc::store::interval::End::of(1),
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

/// `x1 = i * i; x2 = x1 * x1; …; x<depth> = …; test(x<depth>)`: `i ** 2^depth` written as
/// `depth` names, each the square of the one before it.
fn squares(depth: usize, test: Term) -> Term {
    let mut body = test;
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
    body
}

/// The integer literal `n`, of any size, as the kernel holds it.
fn big(n: BigInt) -> Term {
    Term::Lit(Value::int(n))
}

/// `f ** k` for an exponent `k` written as a term.
fn power_of(f: &Term, k: Term) -> Term {
    prim(Prim::Pow, f.clone(), k)
}

#[test]
fn a_shared_count_past_the_exponent_width_is_read_as_its_power() {
    // `x1 = i * i; …; x32 <= 0`: 2^32 factors, one more than `u32` holds, read as
    // `i ** 2^32`: an even power, 0 only at `i = 0`.
    let ds = doms(&[("i", Some(-3), Some(3))]);
    for depth in [31, 32, 33, 64, 65, 200] {
        let k = big(BigInt::from(1) << depth);
        let p = pre(&squares(depth, at_most(var(&format!("x{depth}")), 0)), &ds);
        assert_eq!(p, pre(&at_most(power_of(&var("i"), k), 0), &ds), "{depth}");
        assert_eq!(shown(&p), "i [0..=0]; exact", "{depth}");
    }
    // `y = x32 * i`: 2^32 + 1 factors, an odd count, so `y <= 0` is `i <= 0`.
    for depth in [32, 64, 200] {
        let x = format!("x{depth}");
        let t = squares(
            depth,
            bind(
                "y",
                prim(Prim::Mul, var(&x), var("i")),
                at_most(var("y"), 0),
            ),
        );
        let k = big((BigInt::from(1) << depth) + 1);
        let p = pre(&t, &ds);
        assert_eq!(p, pre(&at_most(power_of(&var("i"), k), 0), &ds), "{depth}");
        assert_eq!(shown(&p), "i [-3..=0]; exact", "{depth}");
        check(&t, &ds, &Demand::Bool(true), &p, (-1, 1));
    }
}

#[test]
fn a_count_of_any_size_gives_an_exact_end() {
    // `x<d> == 3 ** 2^d`: the count is held exactly, so the end `3 ** 2^d` is exact and the
    // answer is `i = ±3` at every depth, as for the small form at depth 3. Corner: the counts
    // 2^32 - 1, the largest in `u32`, and 2^32, one past it.
    let ds = doms(&[("i", Some(-3), Some(3))]);
    let three_to = |k: BigInt| power_of(&int(3), big(k));
    for depth in [3, 32, 33, 64] {
        let k = BigInt::from(1) << depth;
        let t = squares(
            depth,
            prim(Prim::Eq, var(&format!("x{depth}")), three_to(k.clone())),
        );
        let p = pre(&t, &ds);
        assert_eq!(shown(&p), "i [-3..=-3, 3..=3]; exact", "{depth}");
        let direct = prim(Prim::Eq, power_of(&var("i"), big(k.clone())), three_to(k));
        assert_eq!(p, pre(&direct, &ds), "{depth}");
        // `x<d> - 1 == 3 ** 2^d`: one more than the end, no integer. The sum is formed by the
        // preimage, kept; the kernel writes out a constant `3 ** 2^d + 1`.
        let k = BigInt::from(1) << depth;
        let t = squares(
            depth,
            prim(
                Prim::Eq,
                prim(Prim::Sub, var(&format!("x{depth}")), int(1)),
                three_to(k),
            ),
        );
        assert_eq!(shown(&pre(&t, &ds)), "i []; exact", "{depth} + 1");
    }
    // `p1 = i * x1; p2 = p1 * x2; …; p31 = p30 * x31`: 1 + 2 + … + 2^31 = 2^32 - 1 factors,
    // an odd count, so `p31 == 3 ** (2^32 - 1)` is `i = 3`.
    let k = (BigInt::from(1) << 32) - 1;
    let mut body = prim(Prim::Eq, var("p31"), three_to(k));
    for n in (1..=31).rev() {
        let prev = if n == 1 {
            "i".to_string()
        } else {
            format!("p{}", n - 1)
        };
        body = bind(
            &format!("p{n}"),
            prim(Prim::Mul, var(&prev), var(&format!("x{n}"))),
            body,
        );
    }
    let p = pre(&squares(31, body), &ds);
    assert_eq!(shown(&p), "i [3..=3]; exact");
}

#[test]
fn a_power_with_a_small_exponent_keeps_every_solution() {
    // `i ** k` against the interpreter at every point, for `k` from 0 to 70, and the same
    // count of factors written out as a product.
    let ds = doms(&[("i", Some(-6), Some(6))]);
    for k in 0..=70usize {
        for test in [
            at_most(power(&var("i"), k), 1),
            at_most(power(&shifted(), k), 0),
            prim(Prim::Eq, power(&var("i"), k), int(1)),
            prim(Prim::Ge, power(&var("i"), k), int(64)),
        ] {
            let p = pre(&test, &ds);
            check(&test, &ds, &Demand::Bool(true), &p, (-6, 6));
        }
        if k >= 1 {
            let le1 = |t| at_most(t, 1);
            same_as_power(&var("i"), k, product, le1, &ds);
        }
    }
}

#[test]
fn an_exponent_of_any_size_is_read_by_its_parity() {
    // `i ** k <= 0` over `-3..=3`: `i <= 0` for an odd `k`, `i = 0` for an even one, and every
    // `i` for `k = 0`. `i ** k == 1`: 1 for an odd `k`, -1 and 1 for an even one.
    let ds = doms(&[("i", Some(-3), Some(3))]);
    let two = BigInt::from(2);
    let ten = || big(BigInt::from(10));
    let billion = || int(1_000_000_000);
    let cases: Vec<(&str, Term, bool)> = vec![
        ("0", int(0), false),
        ("1", int(1), true),
        ("u32::MAX", int(u32::MAX as i64), true),
        ("u32::MAX + 1", int(u32::MAX as i64 + 1), false),
        ("i64::MAX", int(i64::MAX), true),
        ("2^64", big(two.pow(64)), false),
        ("2^64 + 1", big(two.pow(64) + 1), true),
        // `10 ** 10 ** 9` and `3 ** 10 ** 9`, which the kernel holds as unbuilt prime powers:
        // built, each would be over a billion bits.
        ("10 ** 10 ** 9", power_of(&ten(), billion()), false),
        ("3 ** 10 ** 9", power_of(&int(3), billion()), true),
    ];
    for (name, k, odd) in cases {
        let le0 = at_most(power_of(&var("i"), k.clone()), 0);
        let eq1 = prim(Prim::Eq, power_of(&var("i"), k.clone()), int(1));
        // The points of -1..=1 the interpreter finds meet each test: it runs every one of these
        // powers, since its base is -1, 0 or 1.
        let (le0_want, eq1_want, le0_met, eq1_met) = match (name, odd) {
            ("0", _) => ("i []; exact", "i [-3..=3]; exact", 0, 3),
            (_, true) => ("i [-3..=0]; exact", "i [1..=1]; exact", 2, 1),
            (_, false) => ("i [0..=0]; exact", "i [-1..=-1, 1..=1]; exact", 1, 2),
        };
        let p = pre(&le0, &ds);
        assert_eq!(shown(&p), le0_want, "i ** {name} <= 0");
        let met = check(&le0, &ds, &Demand::Bool(true), &p, (-1, 1));
        assert_eq!(met, le0_met, "i ** {name} <= 0");
        let p = pre(&eq1, &ds);
        assert_eq!(shown(&p), eq1_want, "i ** {name} == 1");
        let met = check(&eq1, &ds, &Demand::Bool(true), &p, (-1, 1));
        assert_eq!(met, eq1_met, "i ** {name} == 1");
    }
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

/// The sizes are a product of 512 factors and one of 4096. The measurement runs on a 2 MiB
/// stack, as the `long` tests of [`super::scaling`] do; the terms are built before the timing.
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
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

/// `x1 = i * i; x2 = x1 * i; x3 = x2 * x1; …`: the count at depth `d` is the Fibonacci
/// number `F(d + 2)`, a sum of two earlier counts at each name, as nested squares are.
fn fibonacci(depth: usize, test: Term) -> Term {
    let name = |k: usize| {
        if k == 0 {
            "i".to_string()
        } else {
            format!("x{k}")
        }
    };
    let mut body = test;
    for n in (1..=depth).rev() {
        let other = name(n.saturating_sub(2));
        body = bind(
            &name(n),
            prim(Prim::Mul, var(&name(n - 1)), var(&other)),
            body,
        );
    }
    body
}

/// `x1 = i * i; …; x<d> <= 0`, and the same over [`fibonacci`] counts, at depths 2048 and
/// 16384: the count at depth `d` has about `d` bits and is held exactly (COMPLEXITY.md S30b),
/// so the counts take `O(d^2)` bits in all, the `O(n log N)` of sec:constraints with `N` the
/// largest count; its time stays within the linear limit at these depths. On a 2 MiB stack;
/// the terms are built before the timing.
#[test]
fn reading_nested_squares_as_a_power_is_linear_in_their_depth() {
    let measure = || {
        let ds = doms(&[("i", Some(-3), Some(3))]);
        let sizes = [2048, scaling::FACTOR * 2048];
        let at = |d: usize| sizes.iter().position(|&s| s == d).expect("a built size");
        let squared: Vec<Term> = sizes
            .iter()
            .map(|&d| squares(d, at_most(var(&format!("x{d}")), 0)))
            .collect();
        for t in &squared {
            assert_eq!(shown(&pre(t, &ds)), "i [0..=0]; exact");
        }
        scaling::check_order("`x1 = i * i; …; x<n> <= 0`", sizes[0], 1, |d| {
            pre(&squared[at(d)], &ds);
        });
        let chained: Vec<Term> = sizes
            .iter()
            .map(|&d| fibonacci(d, at_most(var(&format!("x{d}")), 0)))
            .collect();
        for t in &chained {
            assert!(pre(t, &ds).exact);
        }
        scaling::check_order(
            "`x1 = i * i; x2 = x1 * i; …; x<n> <= 0`",
            sizes[0],
            1,
            |d| {
                pre(&chained[at(d)], &ds);
            },
        );
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}
