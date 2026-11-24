//! The tests of DESIGN step L1.17d (sec:domains, "One form for bounds, sizes and costs"; plan
//! row KEPT-ast-normal-form), on `zedc_lattice::bound_form`: one normal form and one content
//! address for equal polynomials, the rewrites of exponentials and logarithms, held powers of
//! sums, the sum rule of constants, Hardy's order and dominance, the cost reading `O`, the work
//! of a loop, exact sizes of kept constants, and the printer read back. The fib bound under
//! RECUR-monotone waits on that row (not Done), as row KEPT-ast-normal-form records. The
//! scaling tests are in `bench/bound_form.rs`.

use std::cmp::Ordering;
use std::collections::BTreeSet;

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use zed_kernel::Rat;
use zed_tests::seed::Rng;
use zedc_lattice::bound_form::{
    Form, Mono, Reading, bits, digits, dominated, maxima, order, read, work,
};

fn ex(t: &str) -> Form {
    read(t, Reading::Exact).unwrap_or_else(|e| panic!("`{t}`: {e}"))
}

fn cost(t: &str) -> Form {
    read(t, Reading::Cost).unwrap_or_else(|e| panic!("`{t}`: {e}"))
}

/// The content address of step M0.7 of a form's expanded normal form.
fn addr(f: &Form) -> impl std::fmt::Debug + PartialEq {
    let term = f.expanded().expect("memory for the expansion").to_term();
    let g = zedc::zir::lower::lower(&term).unwrap_or_else(|e| panic!("{f}: {e}"));
    zedc::zir::canon::address(&g).expect("memory for the address")
}

/// The one monomial of a one-term form.
fn mono(f: &Form) -> Mono {
    let t = f.terms();
    assert_eq!(t.len(), 1, "{f}");
    t[0].0.clone()
}

#[test]
fn equal_polynomials_have_one_form_and_one_address() {
    let forms = ["n*n", "n^2", "(n + 1)^2 - 2*n - 1"].map(ex);
    for f in &forms[1..] {
        assert_eq!(f, &forms[0]);
        assert_eq!(addr(f), addr(&forms[0]), "{f}");
    }
    assert_eq!(forms[0].to_string(), "n^2");
    // Negative control: a different polynomial has another form and another address.
    let other = ex("n^2 + 1");
    assert_ne!(other, forms[0]);
    assert_ne!(addr(&other), addr(&forms[0]));
    // A power of a sum alone is held, and equal to its expansion.
    let held = ex("(n + 1)^2");
    assert_eq!(held.to_string(), "(n + 1)^2");
    let open = ex("n^2 + 2*n + 1");
    assert!(held.equals(&open).expect("memory"));
    assert_eq!(addr(&held), addr(&open));
    assert!(!held.equals(&other).expect("memory"));
    // A constant kept as a power (`(-2)^2` is `2^2`) and the same constant built (`4`) get one
    // address (seed 9013687090289476703 of the random test below found them apart).
    let kept = ex("(-2)^2*n + 3^5/2^3");
    let built = ex("(-2)*(-2)*n + 243/8");
    assert_eq!(kept, built);
    assert_eq!(addr(&kept), addr(&built));
    let apart = ex("4*n + 243/7");
    assert_ne!(addr(&kept), addr(&apart));
}

#[test]
fn exponentials_split_over_sums_products_and_coprime_bases() {
    let f = ex("2^(2*k + 3)");
    assert_eq!(f, ex("8*(2^k)^2"));
    assert_eq!(f.to_string(), "8*(2^k)^2");
    assert_eq!(ex("6^k"), ex("2^k*3^k"));
    assert_eq!(ex("6^k").to_string(), "2^k*3^k");
    assert_eq!(ex("4^k"), ex("2^(2*k)"));
    assert_eq!(ex("(2^k)^n"), ex("2^(k*n)"));
    // Negative controls.
    assert_ne!(f, ex("8*(2^k)^3"));
    assert_ne!(ex("6^k"), ex("2^k*3^(k + 1)"));
}

#[test]
fn logarithms_in_a_cost_are_base_two_and_split() {
    assert_eq!(cost("log(n^2 * 2^k)"), cost("2*log(n) + k"));
    assert_eq!(cost("log(8)"), cost("3"));
    assert_eq!(cost("log(6*n)"), cost("1 + log(3) + log(n)"));
    assert_ne!(cost("log(3)"), cost("1"));
    // Exact readings have no `log`.
    assert!(read("log(n)", Reading::Exact).is_err());
    // A log of a sum is an atom of its own.
    assert_eq!(cost("log(n + 1)").len(), 1);
}

#[test]
fn a_huge_power_of_a_sum_stays_held_in_little_memory() {
    let (f, live) = zed_alloc_count::live(|| ex("(n + 1)^(2^40)"));
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
    assert_eq!(f.to_string(), "(n + 1)^1099511627776");
    // Its 2^40 + 1 monomials are refused before any is built.
    assert!(f.expanded().is_err());
    assert_eq!(f.big_o().expect("memory").to_string(), "n^1099511627776");
}

#[test]
fn constants_are_added_only_when_the_sum_builds_no_more_than_its_operands() {
    let (f, live) = zed_alloc_count::live(|| ex("3^(2^40) + 1"));
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
    assert_eq!(f.len(), 1);
    assert_eq!(f.terms()[0].1.len(), 2, "{f}");
    let g = ex("2^64 + 2^63");
    assert_eq!(g, ex("3*2^63"));
    assert_eq!(g.terms()[0].1.len(), 1, "{g}");
    // Small constants are added.
    assert_eq!(ex("2 + 3"), ex("5"));
    assert_eq!(ex("n + 2*n"), ex("3*n"));
    assert_eq!(ex("n - n"), Form::zero());
}

#[test]
fn hardy_order_and_dominance() {
    let pairs = [
        ("n^2", "n*log(n)^5"),
        ("2^n", "n^100"),
        ("3^n", "2^n*n^9"),
        ("2^(2^n)", "3^(n^5)"),
        ("n*log(n)", "n"),
        ("n^2*m", "n*m"),
    ];
    for (big, small) in pairs {
        let (a, b) = (mono(&cost(big)), mono(&cost(small)));
        assert!(dominated(&b, &a), "{small} <= {big}");
        assert!(!dominated(&a, &b), "{big} not <= {small}");
        assert_eq!(order(&a, &b), Ordering::Greater, "{big} > {small}");
        assert_eq!(order(&b, &a), Ordering::Less, "{small} < {big}");
    }
    // Incomparable by dominance, ordered all the same.
    let (a, b) = (mono(&cost("n*m")), mono(&cost("n^2")));
    assert!(!dominated(&a, &b) && !dominated(&b, &a));
    assert_eq!(order(&a, &b), order(&b, &a).reverse());
    assert_ne!(order(&a, &b), Ordering::Equal);
}

#[test]
fn the_cost_reading_drops_coefficients_and_dominated_monomials() {
    assert_eq!(
        cost("3*n^2 + n*log(n)")
            .big_o()
            .expect("memory")
            .to_string(),
        "n^2"
    );
    assert_eq!(cost("n*m + n").big_o().expect("memory").to_string(), "m*n");
    let both = cost("n^2 + n*m").big_o().expect("memory");
    assert_eq!(both.len(), 2, "{both}");
    // A monomial of negative coefficient is no cost.
    assert_eq!(
        cost("n^2 - n^3").big_o().expect("memory").to_string(),
        "n^2"
    );
}

#[test]
fn the_work_of_a_loop_is_its_trip_count_times_its_body() {
    // `0 ..< 2n - 2` with a body of work `n`.
    let w = work(&ex("2*n - 2"), &ex("n")).expect("memory");
    assert_eq!(w.to_string(), "2*n^2");
    assert_eq!(w.big_o().expect("memory").to_string(), "n^2");
    // `0 ..< 2^k` with a body of work `k`.
    let w = work(&ex("2^k"), &ex("k")).expect("memory");
    assert_eq!(w.big_o().expect("memory").to_string(), "k*2^k");
}

#[test]
fn sizes_of_a_kept_constant_are_exact_and_build_nothing() {
    let x = Rat::int(BigInt::from(3))
        .pow(&(BigUint::one() << 40u32))
        .expect("kept");
    let ((b, d), live) = zed_alloc_count::live(|| {
        (
            bits(&x).expect("memory").expect("an integer"),
            digits(&x).expect("memory").expect("an integer"),
        )
    });
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
    assert_eq!(b, BigUint::from(1_742_684_699_132u64));
    assert_eq!(d, BigUint::from(524_600_367_424u64));
    assert_eq!(
        bits(&Rat::new(BigInt::from(1), BigInt::from(2)).expect("a rat")).expect("memory"),
        None
    );
}

/// Corner cases against the built numbers: exact powers of 10 and 2 and their neighbors, kept
/// and built, negative values, 0 and 1.
#[test]
fn sizes_agree_with_the_built_numbers() {
    let check = |x: &Rat, v: &BigInt| {
        let want_bits = BigUint::from(v.bits());
        let want_digits = BigUint::from(match v.magnitude().bits() {
            0 => 1,
            _ => v.magnitude().to_string().len(),
        });
        assert_eq!(bits(x).expect("memory"), Some(want_bits), "bits of {v}");
        assert_eq!(
            digits(x).expect("memory"),
            Some(want_digits),
            "digits of {v}"
        );
    };
    for e in 0u32..300 {
        for (b, d) in [
            (10, 0),
            (10, -1),
            (10, 1),
            (2, 0),
            (2, -1),
            (3, 0),
            (7, 0),
            (6, 0),
        ] {
            let v = BigInt::from(b as i64).pow(e) + BigInt::from(d as i64);
            check(&Rat::int(v.clone()), &v);
            check(&Rat::int(-v.clone()), &(-v.clone()));
        }
        // Kept: `10^e` as `2^e * 5^e`, `3^e * 7^e`.
        for (b, c) in [(2, 5), (3, 7), (5, 2)] {
            let k = Rat::int(BigInt::from(b))
                .pow(&BigUint::from(e))
                .and_then(|x| x.mul(&Rat::int(BigInt::from(c)).pow(&BigUint::from(e))?))
                .expect("kept");
            let v = BigInt::from(b).pow(e) * BigInt::from(c).pow(e);
            check(&k, &v);
            check(&k.neg(), &(-v));
        }
    }
}

#[test]
fn every_printed_form_reads_back_to_the_same_form() {
    let texts = [
        ("n^2", Reading::Exact),
        ("(n + 1)^2", Reading::Exact),
        ("8*(2^k)^2", Reading::Exact),
        ("2^k*3^k", Reading::Exact),
        ("n/2", Reading::Exact),
        ("n^(-1)", Reading::Exact),
        ("1/(n + 1)", Reading::Exact),
        ("3 - n^2", Reading::Exact),
        ("2^(n*m) + 2^n", Reading::Exact),
        ("realRoot([-2, 0, 1], 1)^n", Reading::Exact),
        ("f(n, m + 1)*n", Reading::Exact),
        ("2*xs::len", Reading::Exact),
        ("3^(2^40) + 1", Reading::Exact),
        ("n^m", Reading::Exact),
        ("(2^k)^(-1)", Reading::Exact),
        ("2^64 + 5*n/3", Reading::Exact),
        ("n*log(n) + log(3)*n + k", Reading::Cost),
        ("log(n + 1)^2", Reading::Cost),
    ];
    for (t, r) in texts {
        let f = read(t, r).unwrap_or_else(|e| panic!("`{t}`: {e}"));
        let p = f.to_string();
        let g = read(&p, r).unwrap_or_else(|e| panic!("`{t}` printed `{p}`: {e}"));
        assert_eq!(f, g, "`{t}` printed `{p}`");
    }
    assert_eq!(
        ex("realRoot([-2, 0, 1], 1)").to_string(),
        "realRoot([-2, 0, 1], 1)"
    );
}

/// A random polynomial in `x`, `y`, `z`, as a tree.
enum P {
    V(usize),
    C(i64),
    Add(Box<P>, Box<P>),
    Mul(Box<P>, Box<P>),
    Pow(Box<P>, u32),
}

fn gen_p(r: &mut Rng, depth: u32) -> P {
    match (depth, r.below(5)) {
        (0, k) | (_, k @ 0) => match k % 2 {
            0 => P::V(r.below(3)),
            _ => P::C(r.int(-3, 3)),
        },
        (_, 1 | 2) => P::Add(Box::new(gen_p(r, depth - 1)), Box::new(gen_p(r, depth - 1))),
        (_, 3) => P::Mul(Box::new(gen_p(r, depth - 1)), Box::new(gen_p(r, depth - 1))),
        _ => P::Pow(Box::new(gen_p(r, depth - 1)), 2 + r.below(2) as u32),
    }
}

/// An equal polynomial written another way: operands swapped, products distributed, powers
/// multiplied out, `q - q` added.
fn same_p(p: &P, r: &mut Rng) -> P {
    let b = |p: P| Box::new(p);
    match p {
        P::V(i) => P::V(*i),
        P::C(c) => P::C(*c),
        P::Add(a, c) => P::Add(b(same_p(c, r)), b(same_p(a, r))),
        P::Mul(a, c) => match &**c {
            P::Add(c1, c2) if r.coin() => P::Add(
                b(P::Mul(b(same_p(a, r)), b(same_p(c1, r)))),
                b(P::Mul(b(same_p(a, r)), b(same_p(c2, r)))),
            ),
            _ => P::Mul(b(same_p(c, r)), b(same_p(a, r))),
        },
        P::Pow(a, 2) if r.coin() => P::Mul(b(same_p(a, r)), b(same_p(a, r))),
        P::Pow(a, e) => {
            let q = gen_p(r, 1);
            let minus = P::Mul(b(P::C(-1)), b(same_p(&q, r)));
            P::Add(b(P::Pow(b(same_p(a, r)), *e)), b(P::Add(b(q), b(minus))))
        }
    }
}

fn text_p(p: &P) -> String {
    match p {
        P::V(i) => ["x", "y", "z"][*i].to_string(),
        P::C(c) if *c < 0 => format!("({c})"),
        P::C(c) => c.to_string(),
        P::Add(a, b) => format!("({} + {})", text_p(a), text_p(b)),
        P::Mul(a, b) => format!("({} * {})", text_p(a), text_p(b)),
        P::Pow(a, e) => format!("({})^{e}", text_p(a)),
    }
}

fn eval_p(p: &P, at: &[BigInt; 3]) -> BigInt {
    match p {
        P::V(i) => at[*i].clone(),
        P::C(c) => BigInt::from(*c),
        P::Add(a, b) => eval_p(a, at) + eval_p(b, at),
        P::Mul(a, b) => eval_p(a, at) * eval_p(b, at),
        P::Pow(a, e) => eval_p(a, at).pow(*e),
    }
}

/// 10,000 random pairs: equal normal forms exactly when the polynomials agree at 20 random
/// 64-bit points (two different polynomials of degree `d` agree at a random point with
/// probability at most `d / 2^64`, Schwartz 1980, doi:10.1145/322217.322225). Half the pairs
/// are equal by construction, so both answers are tried; the first 300 equal pairs also share
/// a content address.
#[test]
fn random_polynomials_have_equal_forms_exactly_when_they_agree_at_random_points() {
    let (mut r, seed) = Rng::fresh("random_polynomials_have_equal_forms");
    let (mut equal, mut unequal, mut addressed) = (0, 0, 0);
    for i in 0..10_000 {
        let a = gen_p(&mut r, 3);
        let b = match r.coin() {
            true => same_p(&a, &mut r),
            false => match r.coin() {
                true => gen_p(&mut r, 3),
                false => P::Add(Box::new(same_p(&a, &mut r)), Box::new(P::V(r.below(3)))),
            },
        };
        let (ta, tb) = (text_p(&a), text_p(&b));
        let agree = (0..20).all(|_| {
            let at = [0; 3].map(|_| BigInt::from(r.next_u64()));
            eval_p(&a, &at) == eval_p(&b, &at)
        });
        let (fa, fb) = (ex(&ta), ex(&tb));
        let (ea, eb) = (
            fa.expanded().expect("memory"),
            fb.expanded().expect("memory"),
        );
        assert_eq!(
            ea == eb,
            agree,
            "seed {seed} pair {i}: `{ta}` and `{tb}`: {ea} and {eb}"
        );
        assert_eq!(
            fa.equals(&fb).expect("memory"),
            agree,
            "seed {seed} pair {i}"
        );
        match agree {
            true => {
                equal += 1;
                if addressed < 300 {
                    assert_eq!(addr(&fa), addr(&fb), "seed {seed} pair {i}: `{ta}`, `{tb}`");
                    addressed += 1;
                }
            }
            false => unequal += 1,
        }
    }
    assert!(
        equal > 3_000 && unequal > 3_000,
        "seed {seed}: {equal} equal, {unequal} unequal"
    );
}

/// The cost reading's maxima against the definition, every pair compared, on random monomials
/// in one to three symbols (the sweep of `maxima`) and in four and five (the check against the
/// maxima kept), with distinct exponents so that no two dominate each other. Exponents below 6
/// make ties in single coordinates common, which the ranks of the sweep must keep equal.
#[test]
fn the_maxima_of_random_monomials_are_those_no_other_dominates() {
    let (mut r, seed) = Rng::fresh("the_maxima_of_random_monomials");
    for round in 0..1000 {
        let syms = ["n", "m", "k", "h", "w"];
        let count = 1 + round % 5;
        let mut f = Form::zero();
        let mut seen = std::collections::BTreeSet::new();
        for _ in 0..1 + r.below(30) {
            let es: Vec<u32> = (0..count).map(|_| r.below(6) as u32).collect();
            if !seen.insert(es.clone()) {
                continue;
            }
            let text = (es.iter().zip(syms))
                .map(|(e, s)| format!("{s}^{e}"))
                .collect::<Vec<_>>()
                .join("*");
            f = f.plus(&cost(&text)).expect("memory");
        }
        let ms: Vec<Mono> = f.terms().into_iter().map(|(m, _)| m.clone()).collect();
        let want: std::collections::BTreeSet<Mono> = (ms.iter())
            .filter(|m| !ms.iter().any(|o| o != *m && dominated(m, o)))
            .cloned()
            .collect();
        let got: std::collections::BTreeSet<Mono> = f
            .big_o()
            .expect("memory")
            .terms()
            .into_iter()
            .map(|(m, _)| m.clone())
            .collect();
        assert_eq!(got, want, "seed {seed} round {round}: {f}");
    }
}

/// The monomials of `text`, a sum, by `maxima` directly (no coefficients).
fn maxima_of(texts: &[String]) -> BTreeSet<Mono> {
    let ms = texts.iter().map(|t| mono(&cost(t))).collect();
    maxima(ms).into_iter().collect()
}

/// Corners of the sweep in `d <= 3` coordinates: no monomial; only the constant (no
/// coordinate); one; a chain, where one dominates all; an antichain on the plane
/// `i + j + k = 6`, where all are maxima; the same monomial twice, kept once; ties in two of
/// three coordinates, where the third decides; an opaque atom as a coordinate beside symbols.
#[test]
fn the_maxima_sweep_corners() {
    let s = |v: &[&str]| v.iter().map(|t| t.to_string()).collect::<Vec<_>>();
    assert!(maxima(Vec::new()).is_empty());
    assert_eq!(maxima_of(&s(&["1"])).len(), 1);
    assert_eq!(maxima_of(&s(&["n*m*k"])).len(), 1);
    let chain = maxima_of(&s(&["n", "n*m", "n*m*k", "n^2*m*k", "m", "1"]));
    assert_eq!(chain, maxima_of(&s(&["n^2*m*k"])));
    let plane: Vec<String> = (0..=6)
        .flat_map(|i| (0..=6 - i).map(move |j| format!("n^{i}*m^{j}*k^{}", 6 - i - j)))
        .collect();
    assert_eq!(maxima_of(&plane).len(), plane.len());
    assert_eq!(maxima_of(&s(&["n*m", "n*m"])).len(), 1);
    let ties = maxima_of(&s(&["n*m*k^2", "n*m*k", "n*m^2*k", "n^2*m*k"]));
    assert_eq!(ties, maxima_of(&s(&["n*m*k^2", "n*m^2*k", "n^2*m*k"])));
    let opaque = maxima_of(&s(&["n*f(n, m)", "n^2", "f(n, m)", "m*f(n, m)"]));
    assert_eq!(opaque, maxima_of(&s(&["n*f(n, m)", "n^2", "m*f(n, m)"])));
}

/// QUESTIONS.md A226's reduction from orthogonal vectors, checked against all pairs: for
/// vectors `a_1..a_n`, `b_1..b_n` in {0,1}^D, the monomials `a_i' = prod x_k^(a_ik) * p^i *
/// q^(n-i)` and `b_j' = prod x_k^(1-b_jk) * p^n * q^n * z`, one symbol per coordinate; some
/// `a_i'` is not a maximum exactly when some `a_i . b_j = 0`. Random instances at D from 1
/// to 6 and n from 1 to 8, each asserted, and two fixed instances that reach both answers:
/// `a = (1,0), (0,1)` against `b = (1,1)` (no pair orthogonal) and against `b = (0,1)`
/// (`(1,0) . (0,1) = 0`).
#[test]
fn orthogonal_vectors_reduce_to_the_maxima_of_monomials() {
    let (mut r, seed) = Rng::fresh("orthogonal_vectors_reduce_to_the_maxima");
    let fixed = [
        (vec![vec![1, 0], vec![0, 1]], vec![vec![1, 1], vec![1, 1]]),
        (vec![vec![1, 0], vec![0, 1]], vec![vec![1, 1], vec![0, 1]]),
    ];
    for round in 0..602 {
        let (a, b) = match fixed.get(round) {
            Some(ab) => ab.clone(),
            None => {
                let d = 1 + round % 6;
                let n = 1 + r.below(8);
                let mut draw = || (0..d).map(|_| r.below(2)).collect::<Vec<usize>>();
                let a: Vec<Vec<usize>> = (0..n).map(|_| draw()).collect();
                (a, (0..n).map(|_| draw()).collect())
            }
        };
        let n = a.len();
        let text = |v: &[usize], rest: String| {
            (v.iter().enumerate())
                .map(|(k, e)| format!("x{k}^{e}*"))
                .collect::<String>()
                + &rest
        };
        let a_m: Vec<String> = (a.iter().enumerate())
            .map(|(i, v)| text(v, format!("p^{}*q^{}", i + 1, n - i - 1)))
            .collect();
        let b_m: Vec<String> = (b.iter())
            .map(|v| {
                let flip: Vec<usize> = v.iter().map(|e| 1 - e).collect();
                text(&flip, format!("p^{n}*q^{n}*z"))
            })
            .collect();
        let all: Vec<String> = a_m.iter().chain(&b_m).cloned().collect();
        let kept = maxima_of(&all);
        let some_a_dropped = a_m.iter().any(|t| !kept.contains(&mono(&cost(t))));
        let orthogonal =
            (a.iter()).any(|x| (b.iter()).any(|y| x.iter().zip(y).all(|(p, q)| p * q == 0)));
        assert_eq!(
            some_a_dropped, orthogonal,
            "seed {seed} round {round}: {a:?} {b:?}"
        );
        if round < fixed.len() {
            assert_eq!(orthogonal, round == 1, "the fixed instance {round}");
        }
    }
}

#[test]
fn negative_and_zero_corners() {
    assert_eq!(ex("0").to_string(), "0");
    assert_eq!(ex("-n").to_string(), "-n");
    assert!(read("1/0", Reading::Exact).is_err());
    assert!(read("0^(-1)", Reading::Exact).is_err());
    assert!(read("n < 3", Reading::Exact).is_err());
    assert!(read("log(-1)", Reading::Cost).is_err());
    assert!(ex("n - n").big_o().expect("memory").is_zero());
    let w = work(&ex("-n"), &ex("n")).expect("memory");
    assert!(w.is_zero(), "{w}");
    // A negative base has no coprime base: the power is opaque, not a constant.
    assert!(ex("(-2)^n").terms().iter().all(|(m, _)| !m.is_one()));
}
