//! Deep terms (PRE-stack, PRE-stack-explicit): each analysis of the transfer recurses on the
//! depth of the term through frames kept on the heap, so a term nested 100,000 deep has its
//! preimage on a 2 MiB thread stack. Before PRE-stack the transfer overflowed that stack at
//! depth 3,000.

use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::scaling;
use zedc::store::preimage::{Demand, preimage};

use super::{doms, shown};

/// The default stack of a test thread.
const STACK: usize = 2 << 20;

/// How deep the terms are.
const DEEP: usize = 100_000;

/// Runs `f` on a thread with a 2 MiB stack, whatever `RUST_MIN_STACK` says.
fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .expect("a test thread")
        .join()
        .expect("the test passes on a 2 MiB stack");
}

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
fn sum(k: usize) -> Term {
    let t = (0..k).fold(var("i"), |a, _| prim(Prim::Add, a, int(1)));
    prim(Prim::Ge, t, int(k as i64))
}

/// `let x1 = i + 1; ...; let xk = x(k-1) + 1; xk >= k`.
fn lets(k: usize) -> Term {
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
fn ifs(k: usize) -> Term {
    let t = (1..=k as i64).fold(var("i"), |t, j| {
        Term::If(
            Shared::new(prim(Prim::Ge, var("i"), int(j))),
            Shared::new(prim(Prim::Add, t, int(1))),
            Shared::new(prim(Prim::Sub, int(j), var("i"))),
        )
    });
    prim(Prim::Ge, t, int(0))
}

/// The preimage of `true` under `make(DEEP)` for `i` in `[-50, 50]`, on a 2 MiB stack.
fn deep(make: fn(usize) -> Term, expected: &'static str) {
    on_small_stack(move || {
        let t = make(DEEP);
        let p = preimage(
            &t,
            &doms(&[("i", Some(-50), Some(50))]),
            &Demand::Bool(true),
        );
        assert_eq!(shown(&p), expected);
    });
}

#[test]
fn a_sum_100000_deep_has_its_preimage_on_a_2_mib_stack() {
    deep(sum, "i [0..=50]; exact");
}

#[test]
fn a_chain_of_100000_lets_has_its_preimage_on_a_2_mib_stack() {
    deep(lets, "i [0..=50]; exact");
}

#[test]
fn ifs_nested_100000_deep_have_their_preimage_on_a_2_mib_stack() {
    deep(ifs, "i [-50..=50]; exact");
}

/// The transfer of a deep term, its frames on the heap, costs O(depth), at depths 12,500 and
/// 100,000; the terms are built before the timing.
fn scales(what: &'static str, make: fn(usize) -> Term) {
    on_small_stack(move || {
        let n = DEEP / scaling::FACTOR;
        let (a, b) = (make(n), make(DEEP));
        let d = doms(&[("i", Some(-50), Some(50))]);
        scaling::check(what, n, |k| {
            preimage(if k == n { &a } else { &b }, &d, &Demand::Bool(true));
        });
    });
}

#[test]
fn a_deep_sum_costs_linear_work_in_its_depth() {
    scales("the preimage of a deep sum", sum);
}

#[test]
fn a_deep_chain_of_lets_costs_linear_work_in_its_depth() {
    scales("the preimage of a deep chain of lets", lets);
}

#[test]
fn deep_ifs_cost_linear_work_in_their_depth() {
    scales("the preimage of deep ifs", ifs);
}
