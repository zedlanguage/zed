//! The benchmarks of DESIGN step L1.17d (plan row KEPT-ast-normal-form): the bound normal form
//! at `t` and `8t` monomials. The bodies timed are checked at small sizes in `bound_form.rs`.

use num_bigint::BigInt;
use zed_tests::scaling::{check_order, inputs};
use zedc_lattice::bound_form::{Atom, Form, Mono, maxima};

/// `n^i * m^j * k^l` as a monomial.
fn mono3(i: usize, j: usize, l: usize) -> Mono {
    let p = |x: &str, e: usize| Mono::atom(Atom::Sym(x.into()), BigInt::from(e));
    p("n", i).mul(&p("m", j)).mul(&p("k", l))
}

/// The sweep of [`maxima`] in three coordinates (plan row BOUND-maxima-many-symbols): `t`
/// monomials on the plane `i + j + l = 2t` (`j = 37 i mod t`), none dominating another, so all
/// `t` are maxima, each with one below it (`l - 1`): the rank sorts, O(t log t) comparisons of
/// exponents of O(log t) bits, and `2t` staircase lookups, O(log t) each, power 1 under the
/// limit: 5.33 times by instructions from 1024 to 8192 (Colab l44, 2026-11-24). The check of
/// each against the maxima kept (the method for four or more coordinates, and before this row
/// for three) is O(t^2) here; run on this input at 128 and 1024 as a negative control (not
/// kept), it failed at 64.2 times.
#[test]
fn the_maxima_of_a_staircase_in_three_symbols_scale_as_t_log_t() {
    let t = 1usize << 10;
    let monos = inputs(t, |t| {
        (0..t)
            .flat_map(|i| {
                let j = i * 37 % t;
                let l = 2 * t - i - j;
                [mono3(i, j, l), mono3(i, j, l - 1)]
            })
            .collect::<Vec<Mono>>()
    });
    check_order("the maxima of 2t monomials in n, m and k", t, 1, |t| {
        assert_eq!(maxima(monos[&t].clone()).len(), t);
    });
}

/// `n^i * m^j`.
fn mono(i: usize, j: usize) -> Form {
    let p = |x: &str, e: usize| Form::atom(Atom::Sym(x.into()), BigInt::from(e));
    p("n", i).mul(&p("m", j)).expect("memory")
}

/// A staircase of `t` maxima `n^i * m^(t-i)`, each with a monomial below it, summed one
/// monomial at a time, read as a cost and printed: `t` sums of O(log t) map operations, then
/// the two-coordinate sweep of [`zedc_lattice::bound_form::maxima`], O(t log t) comparisons,
/// and the printer's sort, O(t log t). Each comparison reads exponents of O(log t) bits, so the
/// work is O(t log^2 t) at most, power 1 under the limit of 10.5 from `t` to `8t`.
#[test]
fn the_cost_of_a_sum_of_monomials_scales_as_t_log_t() {
    let t = 1usize << 8;
    let monos = inputs(t, |t| {
        (0..t)
            .flat_map(|i| [mono(i, t - i), mono(i.saturating_sub(1), t - i - 1)])
            .collect::<Vec<Form>>()
    });
    check_order(
        "the cost reading of a sum of 2t monomials in n and m",
        t,
        1,
        |t| {
            let f = monos[&t]
                .iter()
                .fold(Form::zero(), |a, m| a.plus(m).expect("memory"));
            assert_eq!(f.len(), 2 * t);
            let o = f.big_o().expect("memory");
            assert_eq!(o.len(), t);
            assert!(!o.to_string().is_empty());
        },
    );
}
