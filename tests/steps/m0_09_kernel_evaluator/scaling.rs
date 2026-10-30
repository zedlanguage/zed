//! The evaluator's values at the rule of low complexity (DESIGN.md Part G). A family is
//! shared, not copied, when a variable, a literal or a lookup yields it, so reading a family
//! of `n` entries once per entry costs `O(n log n)`, not `O(n²)`.

use zed_kernel::term::build::{app, lam, lit, prim, var};
use zed_kernel::{Evaluator, Family, Prim, Term, Value, World};
use zed_tests::kernel::*;
use zed_tests::scaling;

/// The keys `0..n`, each mapped to itself.
fn keys(n: usize) -> Value {
    Value::Family(Family::set(0..n as i64))
}

fn run(t: &Term) -> Value {
    Evaluator::new(World::new()).run(t).unwrap()
}

/// `fam(F, k -> F[k])`, reading the family `F` once per key: through a literal, or through a
/// variable bound to it, or through a family nested in a tuple.
fn reads(n: usize, how: usize) -> Term {
    let f = lit(keys(n));
    match how {
        0 => fam_with(f.clone(), |k| get(f, k)),
        1 => app(
            lam(&["f"], fam_with(var("f"), |k| get(var("f"), k))),
            vec![f],
        ),
        _ => {
            let t = prim(Prim::Tuple, vec![f, lit(1)]);
            app(
                lam(
                    &["t"],
                    fam_with(nth(var("t"), 0), |k| get(nth(var("t"), 0), k)),
                ),
                vec![t],
            )
        }
    }
}

#[test]
fn reading_a_family_once_per_entry_scales() {
    for (how, what) in ["a literal", "a variable", "a tuple"]
        .into_iter()
        .enumerate()
    {
        scaling::check(
            &format!("reading {what} once per entry, by entries"),
            2000,
            |n| {
                run(&reads(n, how));
            },
        );
    }
}

#[test]
fn each_read_yields_the_family() {
    for how in 0..3 {
        assert_eq!(run(&reads(100, how)), keys(100), "read {how}");
    }
}
