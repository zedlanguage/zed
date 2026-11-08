//! Deep relations, such as a generator's chain of guards gives: a formula's drop, copy,
//! comparison, hash, printing and maps keep their work on the heap, so a formula nested
//! 100,000 deep is built, mapped, printed, decided and dropped on a 2 MiB thread stack. The
//! recursive forms these replace overflowed that stack at 4,000.

use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;
use std::thread;

use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, Shared, satisfiable};

/// The default stack of a test thread.
const STACK: usize = 2 << 20;

/// How many guards the deep chain has: 100,000 levels of `&&`, `||` and `!`, about 133,000
/// deep.
const DEEP: usize = 100_000;

/// Runs `f` on a thread with a 2 MiB stack, whatever `RUST_MIN_STACK` says.
fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .expect("a test thread")
        .join()
        .expect("the test passes on a 2 MiB stack");
}

fn x(i: usize) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(format!("x{}", i % 8))))
}

/// The guard `x(i) >= i`.
fn guard(i: usize) -> Formula {
    Formula::Con(Con::ge(&x(i), &Lin::constant(i as i128)))
}

/// `x0 >= 0 && (x1 >= 1 || !(x2 >= 2 || (x3 >= 3 && ...)))` over `n` guards, as a generator
/// writes a guard for each step of a chain. The three forms take turns, so that neither
/// [`Formula::and`] nor [`Formula::or`] flattens a level into the one above.
fn chain(n: usize) -> Formula {
    (0..n).rev().fold(guard(n), |inner, i| match i % 3 {
        0 => Formula::and(vec![guard(i), inner]),
        1 => Formula::or(vec![guard(i), Formula::negate(inner)]),
        _ => Formula::or(vec![guard(i), inner]),
    })
}

/// Each constraint `t >= 0` made `t + 1 >= 0`, and back.
fn loosen(c: &Con) -> Formula {
    Formula::Con(Con::ge(&c.lin, &Lin::constant(-1)))
}
fn tighten(c: &Con) -> Formula {
    Formula::Con(Con::ge(&c.lin, &Lin::constant(1)))
}

#[test]
fn a_chain_of_guards_100000_deep_is_mapped_copied_compared_printed_decided_and_dropped() {
    on_small_stack(|| {
        let f = chain(DEEP);
        assert_eq!(f.cons().len(), DEEP + 1);

        let loose = f.map_cons(&loosen);
        assert_ne!(loose, f);
        assert_eq!(loose.cmp(&f), f.cmp(&loose).reverse());
        assert_ne!(loose.cmp(&f), std::cmp::Ordering::Equal);
        assert_eq!(loose.map_cons(&tighten), f);

        let copy = f.clone();
        assert_eq!(copy, f);
        assert_eq!(copy.cmp(&f), std::cmp::Ordering::Equal);
        let set: HashSet<&Formula> = [&f, &copy, &loose].into_iter().collect();
        assert_eq!(set.len(), 2, "a copy hashes as its original");

        let shown = f.to_string();
        assert!(
            shown.starts_with("x0 >= 0 && (x1 >= 1 || !(x2 >= 2 || (x3 >= 3 && "),
            "{}",
            &shown[..80]
        );
        assert_eq!(shown.matches('(').count(), shown.matches(')').count());
        assert!(format!("{f:?}").starts_with("And([Con(Con { lin: "));

        // At x_k = 1000 every guard of the first thousand holds, so the chain holds; with
        // x0 forgotten the first guard is dropped and the rest still holds there.
        let at: Model = (0..8)
            .map(|k| (Atom::Sym(Arc::from(format!("x{k}"))), Int::from(1000i64)))
            .collect();
        assert!(f.holds(&at));
        assert!(f.forget(&Arc::from("x0")).holds(&at));

        // Deciding it puts the chain in negation normal form, which follows its depth too.
        assert!(satisfiable(&f).expect("decided").is_some());

        drop((f, copy, loose));
    });
}

#[test]
fn small_formulas_print_compare_and_hash_as_before() {
    let (a, b) = (guard(1), guard(2));
    let both = Formula::and(vec![a.clone(), b.clone()]);
    let either = Formula::or(vec![a.clone(), b.clone()]);
    let not_a = Formula::negate(a.clone());
    assert_eq!(
        Formula::and(vec![either.clone(), not_a.clone()]).to_string(),
        "(x1 >= 1 || x2 >= 2) && !(x1 >= 1)"
    );
    assert_eq!(
        Formula::negate(both.clone()).to_string(),
        "!(x1 >= 1 && x2 >= 2)"
    );
    assert_eq!(Formula::top().to_string(), "true");
    assert_eq!(Formula::bottom().to_string(), "false");
    assert_eq!(
        format!(
            "{:?}",
            Formula::Not(Shared::new(Formula::Or(Shared::new(vec![]))))
        ),
        "Not(Or([]))"
    );
    assert_eq!(
        format!("{not_a:?}"),
        format!(
            "Not(Con({:?}))",
            match &a {
                Formula::Con(c) => c,
                _ => unreachable!("a constraint"),
            }
        )
    );
    // The variants in the order they are declared, then their parts in order, a prefix first.
    let order = [
        a.clone(),
        b.clone(),
        not_a.clone(),
        Formula::top(),
        Formula::And(Shared::new(vec![a.clone()])),
        Formula::And(Shared::new(vec![a.clone(), b.clone()])),
        Formula::And(Shared::new(vec![b.clone()])),
        Formula::And(Shared::new(vec![not_a.clone()])),
        Formula::bottom(),
        either.clone(),
    ];
    for (i, p) in order.iter().enumerate() {
        for (j, q) in order.iter().enumerate() {
            assert_eq!(p.cmp(q), i.cmp(&j), "{p:?} against {q:?}");
            assert_eq!(p == q, i == j);
        }
    }
    let set: HashSet<Formula> = order.iter().cloned().chain(order.iter().cloned()).collect();
    assert_eq!(set.len(), order.len());
}

#[test]
fn mapping_copying_comparing_printing_and_dropping_a_chain_cost_its_size() {
    // Each operation keeps one stack entry per level of the part it is in, so it costs O(n).
    let built: BTreeMap<usize, Formula> = [DEEP / 8, DEEP]
        .into_iter()
        .map(|n| (n, chain(n)))
        .collect();
    on_small_stack(move || {
        scaling::check_order(
            "a chain of guards mapped, copied, compared, hashed, printed and dropped",
            DEEP / 8,
            1,
            |n| {
                let f = &built[&n];
                let loose = f.map_cons(&loosen);
                let copy = f.clone();
                assert!(copy == *f && loose != *f);
                let set: HashSet<&Formula> = [f, &copy].into_iter().collect();
                std::hint::black_box((set.len(), f.to_string().len()));
            },
        );
    });
}

#[test]
fn deciding_a_chain_costs_its_size() {
    let built: BTreeMap<usize, Formula> = [DEEP / 8, DEEP]
        .into_iter()
        .map(|n| (n, chain(n)))
        .collect();
    on_small_stack(move || {
        scaling::check_order("a chain of guards decided", DEEP / 8, 1, |n| {
            std::hint::black_box(satisfiable(&built[&n]).is_ok());
        });
    });
}
