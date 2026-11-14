//! The inputs of the benchmarks in `bench/scaling.rs`, the scalar tier at the rule of low
//! complexity (DESIGN.md Part G), and their results at a small size.

use zed_kernel::{Evaluator, Prim, Term, Value, World};

/// `#e0 + #e1 + … + #e{n - 1}`, a kernel term nested `n` deep.
pub(crate) fn chain_of_failures(n: usize) -> Term {
    (1..n).fold(Term::Lit(Value::atom("e0")), |t, i| {
        Term::Prim(Prim::Add, vec![t, Term::Lit(Value::atom(&format!("e{i}")))])
    })
}

/// The value of `t` printed, by the kernel's evaluator.
pub(crate) fn evaluated(t: &Term) -> String {
    Evaluator::new(World::new()).run(t).unwrap().to_string()
}

/// A chain of `n` bindings of `f32` arithmetic, each the one before through `*`, `+`, `/`, a
/// power with an `int` exponent, `abs`, `min` and casts to `f64` and back (FLOAT-f32).
pub(crate) fn f32_chain(n: usize) -> String {
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
fn a_chain_of_failures_merges_them_all() {
    assert_eq!(evaluated(&chain_of_failures(3)), "#errs({#e0, #e1, #e2})");
}

#[test]
fn a_chain_of_f32_arithmetic_runs_to_a_string() {
    // Nine links reach each of the four steps twice.
    use zed_tests::step_helpers::l01_16_elaboration::value;
    assert!(value(&f32_chain(9), "x").starts_with('"'));
}
