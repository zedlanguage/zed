//! The benchmarks of DESIGN step L1.17d (plan row KEPT-ast-normal-form): the bound normal form
//! at `t` and `8t` monomials. The bodies timed are checked at small sizes in `bound_form.rs`.

use num_bigint::BigInt;
use zed_tests::scaling::{check_order, inputs};
use zedc_lattice::bound_form::{Atom, Form};

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
