//! Deep terms (PRE-stack, PRE-stack-explicit): each analysis of the transfer recurses on the
//! depth of the term through frames kept on the heap. The tests here check the preimages of the
//! terms a few levels deep on the default stack; `bench::deep` checks the same preimages 10,000
//! deep on a 2 MiB thread stack (before PRE-stack the transfer overflowed that stack at depth
//! 3,000) and times depths up to 100,000.

use zed_kernel::{Prim, Shared, Term, Value};

use zedc::store::preimage::{Demand, preimage};

use super::{doms, shown};

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

/// `i + 1 + ... + 1 >= k`, with `k` ones nested to the left.
pub(super) fn sum(k: usize) -> Term {
    let t = (0..k).fold(var("i"), |a, _| prim(Prim::Add, a, int(1)));
    prim(Prim::Ge, t, int(k as i64))
}

/// `let x1 = i + 1; ...; let xk = x(k-1) + 1; xk >= k`.
pub(super) fn lets(k: usize) -> Term {
    let name = |j: usize| if j == 0 { "i".into() } else { format!("x{j}") };
    (1..=k)
        .rev()
        .fold(prim(Prim::Ge, var(&name(k)), int(k as i64)), |body, j| {
            Term::Let(
                name(j).into(),
                Shared::new(prim(Prim::Add, var(&name(j - 1)), int(1))),
                Shared::new(body),
            )
        })
}

/// `if i >= k { ... if i >= 1 { i + 1 } else { 1 - i } ... + 1 } else { k - i } >= 0`, the
/// ifs nested in their first arm.
pub(super) fn ifs(k: usize) -> Term {
    let t = (1..=k as i64).fold(var("i"), |t, j| {
        Term::If(
            Shared::new(prim(Prim::Ge, var("i"), int(j))),
            Shared::new(prim(Prim::Add, t, int(1))),
            Shared::new(prim(Prim::Sub, int(j), var("i"))),
        )
    });
    prim(Prim::Ge, t, int(0))
}

/// The preimage of `true` under `make(k)` for `i` in `[-50, 50]`, on the default stack, at each
/// of the small depths `ks`. The same terms 10,000 deep on a 2 MiB stack, deeper than the
/// transfer reached before PRE-stack, are benchmarks since TEST-bench-move-l0125 (author P178):
/// `bench::deep` checks those preimages too.
fn shallow(make: fn(usize) -> Term, ks: &[usize], expected: &str) {
    for &k in ks {
        let p = preimage(
            &make(k),
            &doms(&[("i", Some(-50), Some(50))]),
            &Demand::Bool(true),
        );
        assert_eq!(shown(&p), expected, "{k} deep");
    }
}

#[test]
fn a_short_sum_has_its_preimage() {
    shallow(sum, &[0, 1, 2, 5], "i [0..=50]; exact");
}

#[test]
fn a_short_chain_of_lets_has_its_preimage() {
    shallow(lets, &[0, 1, 2, 5], "i [0..=50]; exact");
}

#[test]
fn a_few_nested_ifs_have_their_preimage() {
    shallow(ifs, &[1, 2, 5], "i [-50..=50]; exact");
}
