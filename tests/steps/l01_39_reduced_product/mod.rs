//! Step L1.39: the reduced product (DESIGN.md sec:domains and sec:constraints).
//!
//! Each name in scope holds a product of its cell, its type and its binding time, and the
//! scope holds the linear relation and the written constraints. `spec` checks the design's
//! examples: an arm whose test fixes `n mod 4 == 1` within `0..=10` holds `n` in `1..=9`, an
//! arm whose test no value meets is unreachable and the program is accepted, and a binding
//! read from a static `if` is static. `random` checks against the interpreter that each
//! arm's scope holds every value that reaches it and that no value reaches an unreachable
//! arm, and `controls` checks each reduction and that each check of `random` rejects a wrong
//! answer.

mod controls;
mod exact;
mod random;
mod scaling;
mod spec;

use std::sync::Arc;

use zed_kernel::Term;
use zed_kernel::types::Type;
use zedc::store::product::{Arm, Product, Scope, arms};

use crate::l01_16_elaboration::elab;
use crate::l01_25_preimage_catalog::function;

/// The scope of integer parameters `ps`, known only when the program runs.
fn ints(ps: &[Arc<str>]) -> Scope {
    Scope::new(
        ps.iter()
            .map(|p| (p.clone(), Product::of_type(Type::int()))),
    )
}

/// The arms of the function `ok` that `src` defines, its parameters integers.
fn arms_of(src: &str) -> (Vec<Arc<str>>, Term, Vec<Arm>) {
    let (ps, body) = function(src);
    let a = arms(&body, &ints(&ps));
    (ps, body, a)
}

/// The arm of `arms` whose test prints as containing `guard`, taken by `outcome`.
fn arm<'a>(arms: &'a [Arm], guard: &str, outcome: bool) -> &'a Arm {
    arms.iter()
        .find(|a| a.guard.contains(guard) && a.outcome == outcome)
        .unwrap_or_else(|| {
            let all: Vec<String> = arms.iter().map(|a| a.guard.clone()).collect();
            panic!("no arm with test `{guard}` and outcome {outcome} among {all:?}")
        })
}

/// The top-level binding `name` of the unit `src`, as a chain of `let` bindings.
fn binding(src: &str, name: &str) -> Term {
    elab(src)
        .unwrap_or_else(|e| panic!("{src}: {e:?}"))
        .get(name)
        .unwrap_or_else(|| panic!("{src}: no binding `{name}`"))
}
