//! Step POLY-nf: the sparse polynomial normal form over a commutative ring (DESIGN.md
//! sec:verification, rung 2 at `int`; sec:optimizer, rung 3), as the kernel library
//! `zed_kernel::poly`. Laws reach the checker at step L12.0 (struct law members) and the rungs
//! that ask it come with HULL-elim, HULL-pos, L3.9, HULL-monoid and MOD-residue, so these tests
//! elaborate each identity's two sides from Zed source, as the tuple of a function over the
//! law's binders, and decide them with the kernel library.
//!
//! `rows` holds the plan row's tests, `refusal` the refusal of a law whose expansion is
//! predicted to take more than 250 ms, `calibration` that prediction against the time taken,
//! `witness` the points and witnesses, `measure` the corpus's obligations, each far within the
//! limit, `factored` the products of powers of the same factors, and `scaling` the rule of low
//! complexity.
//!
//! The tests sit in the folder of step L3.9, whose group and ring normal forms this library
//! gives; the row exists so that L3.9 does not wait.

mod calibration;
mod factored;
mod measure;
mod refusal;
mod rows;
mod scaling;
mod witness;

use std::sync::Arc;

use zed_kernel::poly::{Carrier, Decision, decide};
use zed_kernel::term::{Prim, Term};
use zed_tests::step_helpers::l01_16_elaboration::elab;

/// The two sides of each `name(params) = (lhs, rhs);` of `src`, with the binders' kernel
/// names, in the order of `names`.
pub(crate) fn sides_of(src: &str, names: &[&str]) -> Vec<(Term, Term, Vec<Arc<str>>)> {
    let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    names
        .iter()
        .map(|name| {
            let def = unit.defs.iter().find(|d| d.name == *name).expect("defined");
            let Term::Lam(ps, body) = &*def.term else {
                panic!("{src}: not a function: {}", def.term)
            };
            let Term::Prim(Prim::Tuple, parts) = &**body else {
                panic!("{src}: not a tuple: {body}")
            };
            (parts[0].clone(), parts[1].clone(), ps.clone())
        })
        .collect()
}

/// The decision on the two sides at `carrier`.
pub(crate) fn decide_sides(s: &(Term, Term, Vec<Arc<str>>), carrier: Carrier) -> Decision {
    let names: Vec<&str> = s.2.iter().map(|p| &**p).collect();
    decide(&s.0, &s.1, &names, carrier)
}

/// The decision on `lhs == rhs` over `params` at `carrier`.
pub(crate) fn law(params: &str, lhs: &str, rhs: &str, carrier: Carrier) -> Decision {
    let src = format!("sides({params}) = ({lhs}, {rhs});\n");
    decide_sides(&sides_of(&src, &["sides"])[0], carrier)
}
