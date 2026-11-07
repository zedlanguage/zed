//! The lazy scope ([`Scope::lazy`]) against the eager one: under random sequences of tests,
//! joins and bindings on names related to two hubs, the lazy scope settles every name to
//! the product the eager scope holds, and is empty exactly when the eager one is.

use std::sync::Arc;

use zed_kernel::{Prim, Shared, Term};
use zed_tests::instances::Rng;
use zedc::store::cell::Premises;
use zedc::store::product::Scope;

use super::nests::{and, boxed, diff_ge, int, names, or, prim, var};

const LEAVES: [&str; 5] = ["a0", "a1", "a2", "a3", "a4"];
const HUBS: [&str; 2] = ["n", "m"];

/// A random test of nesting `depth` at most: a spoke `ai - n >= c` or `n - ai >= c`, a bound
/// on a hub or on a leaf, or a disjunction or a conjunction of two tests.
fn test(rng: &mut Rng, depth: usize) -> Term {
    let (leaf, hub) = (rng.pick(&LEAVES), rng.pick(&HUBS));
    match rng.below(if depth == 0 { 4 } else { 6 }) {
        0 => diff_ge(leaf, hub, rng.int(-3, 3)),
        1 => diff_ge(hub, leaf, rng.int(-3, 3)),
        2 => prim(
            rng.pick(&[Prim::Ge, Prim::Le]),
            var(hub),
            int(rng.int(-15, 15)),
        ),
        3 => prim(
            rng.pick(&[Prim::Ge, Prim::Le]),
            var(leaf),
            int(rng.int(-15, 15)),
        ),
        4 => or(test(rng, depth - 1), test(rng, depth - 1)),
        _ => and(test(rng, depth - 1), test(rng, depth - 1)),
    }
}

/// Checks that `lazy` settles every name to what `eager` holds, and that the two are empty
/// together. Returns the number of names the lazy scope held unsettled.
fn same(eager: &Scope, lazy: &Scope, all: &[Arc<str>], trace: &[String]) -> usize {
    assert_eq!(eager.bottom, lazy.bottom, "{}", trace.join("\n"));
    if eager.bottom {
        return 0;
    }
    let mut stale = 0;
    for x in all {
        let settled = lazy.settled(x);
        assert_eq!(eager.get(x), settled, "{x} after\n{}", trace.join("\n"));
        stale += usize::from(lazy.get(x) != settled);
    }
    stale
}

#[test]
fn a_lazy_scope_settles_each_name_to_the_eager_product() {
    let p = Premises::new();
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let start = boxed(&["n", "m", "a0", "a1", "a2", "a3", "a4"], 20);
    let mut stale = 0;
    for seed in 0..300 {
        let mut rng = Rng::new(seed);
        let (mut eager, mut lazy) = (start.clone(), start.clone().lazy());
        let mut trace = vec![format!("seed {seed}")];
        for _ in 0..12 {
            match rng.below(8) {
                0..6 => {
                    let (t, outcome) = (test(&mut rng, 2), rng.below(4) != 0);
                    trace.push(format!("assume {t:?} is {outcome}"));
                    eager = eager.assume(&t, outcome, &p);
                    lazy = lazy.assume(&t, outcome, &p);
                }
                6 => {
                    // The two outcomes of a test, each narrowed further, then joined.
                    let (t, u, v) = (test(&mut rng, 1), test(&mut rng, 1), test(&mut rng, 1));
                    trace.push(format!("join {t:?} and {u:?} with not it and {v:?}"));
                    let arms = |s: &Scope| {
                        let yes = s.assume(&t, true, &p).assume(&u, true, &p);
                        let no = s.assume(&t, false, &p).assume(&v, true, &p);
                        yes.join(&no)
                    };
                    (eager, lazy) = (arms(&eager), arms(&lazy));
                }
                _ => {
                    // A name bound again, to what another name holds: a hub rebound drops
                    // its spokes.
                    let (x, y) = (rng.pick(&all), rng.pick(&all));
                    trace.push(format!("bind {x} to the product of {y}"));
                    let e = Shared::new(Term::Var(y.clone()));
                    let (pe, pl) = (eager.get(&y), lazy.settled(&y));
                    eager.bind(&x, pe, &e);
                    lazy.bind(&x, pl, &e);
                }
            }
            stale += same(&eager, &lazy, &all, &trace);
            if eager.bottom {
                break;
            }
        }
    }
    // The lazy scope did leave names unsettled, so the comparison is not of two eager scopes.
    assert!(stale > 0, "the lazy scope settled every name at once");
}
