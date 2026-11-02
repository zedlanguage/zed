//! The scalar tier at the rule of low complexity (DESIGN.md Part G).

use zed_kernel::{Evaluator, Prim, Term, Value, World};

#[test]
fn a_chain_of_n_failures_merging_scales() {
    // Each `+` merged the failures so far with one more by copying them into a new set. The
    // chain is a kernel term, so that only the evaluator is timed; it nests n deep, past the
    // default thread stack.
    let chain = |n: usize| {
        (1..n).fold(Term::Lit(Value::atom("e0")), |t, i| {
            Term::Prim(Prim::Add, vec![t, Term::Lit(Value::atom(&format!("e{i}")))])
        })
    };
    let run = move |n: usize| {
        Evaluator::new(World::new())
            .run(&chain(n))
            .unwrap()
            .to_string()
    };
    zed_tests::scaling::check("n failures merged by a chain of `+`", 1000, |n| {
        run(n);
    });
    assert_eq!(run(3), "#errs({#e0, #e1, #e2})");
}
