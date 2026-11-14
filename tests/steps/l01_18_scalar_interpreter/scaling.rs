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

/// A chain of `n` bindings of `f32` arithmetic, each the one before through `*`, `+`, `/`, a
/// power with an `int` exponent, `abs`, `min` and casts to `f64` and back (FLOAT-f32).
fn f32_chain(n: usize) -> String {
    let mut src = String::from("whole(positional v: int) = v;\na0 = 0.5f32;\n");
    for i in 1..n {
        let p = i - 1;
        let step = match i % 4 {
            0 => format!("a{p} * 1.0001f32 + 0.25f32"),
            1 => format!("min(abs(a{p}) / 1.5f32, 1.0e30f32)"),
            2 => format!("a{p} ^ whole(2) - 0.125f32"),
            _ => format!("f32(f64(a{p}))"),
        };
        src.push_str(&format!("a{i} = {step};\n"));
    }
    src.push_str(&format!("x = String(a{});\n", n - 1));
    src
}

#[test]
fn checking_and_running_a_chain_of_f32_arithmetic_scales() {
    use zed_tests::step_helpers::l01_16_elaboration::value;
    let srcs: std::collections::HashMap<usize, String> =
        [100, 800].into_iter().map(|n| (n, f32_chain(n))).collect();
    assert!(value(&srcs[&100], "x").starts_with('"'));
    zed_tests::scaling::check_order("a chain of n f32 bindings", 100, 1, |n| {
        value(&srcs[&n], "x");
    });
}
