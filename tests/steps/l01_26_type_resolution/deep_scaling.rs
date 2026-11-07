//! The checker at the rule of low complexity (DESIGN.md Part G), on programs nested thousands
//! deep: checked on a 2 MiB stack with no recursion on the nesting, in linear time. Moved from
//! `scaling` so that each module runs in well under 60 s one test at a time.

use zed_tests::scaling;

use super::scaling::resolved;
use super::sig;

/// Checks each program of `shapes` on a 2 MiB stack, `n` deep and `8n` deep, and checks the
/// time is linear. The checker recursed once per level of nesting, and overflowed this stack
/// at 1,000 deep (sums, blocks, negations, calls) or below 4,000 (`else if` chains).
fn checks_deep(shapes: &[&str], n: usize) {
    use zed_tests::deep::{on_small_stack, program, statements};
    on_small_stack(|| {
        for &shape in shapes {
            let small = statements(&program(shape, n).text);
            let large = statements(&program(shape, 8 * n).text);
            let small_res = zedc::resolve::resolve(&small).unwrap();
            let large_res = zedc::resolve::resolve(&large).unwrap();
            scaling::check_order(&format!("checking {shape}"), n, 1, |k| {
                let (stmts, res) = if k == n {
                    (&small, &small_res)
                } else {
                    (&large, &large_res)
                };
                let info = zedc::check::check(stmts, res);
                assert!(info.errors.is_empty(), "{shape}: {:?}", info.errors);
            });
        }
    });
}

#[test]
fn blocks_nested_100000_deep_check_on_a_2_mib_stack() {
    checks_deep(&["nested blocks"], 12_500);
}

// The shapes below cost about a million instructions for each `+` and a third of that for each
// negation, branch or call, in the kernel's type algebra (`Type::new`, `Type::zip`, `Lits`),
// before and after the walk moved to a heap stack. The checker built the scalar types and
// their meets anew at each node; they are now made once and read off one split
// (CHK-node-cost), and a `+` costs about 140,000 instructions, a negation or call about 70,000
// to 80,000. They are checked 8,000 deep, eight times past the depth that overflowed.

#[test]
fn sums_8000_deep_check_on_a_2_mib_stack() {
    checks_deep(&["a left-nested sum", "a sum nested in parentheses"], 1_000);
}

#[test]
fn long_bodies_and_else_if_chains_8000_deep_check_on_a_2_mib_stack() {
    checks_deep(
        &["a long sum in a function's body", "an `else if` chain"],
        1_000,
    );
}

#[test]
fn negations_and_calls_8000_deep_check_on_a_2_mib_stack() {
    checks_deep(&["nested negations", "nested calls"], 1_000);
}

/// Checks the program of `shape` 1,000 deep on a 2 MiB stack, then `n` and `8n` deep and
/// checks the time is linear, on a 512 MiB stack: printing a type recurses on its nesting
/// (`Ty::write`, for the text of each binding's origin), and overflows 2 MiB below 8,000 deep;
/// at 8,000 nested lambdas the drop of their type, recursive through `Arc<Sig>`, overflows it
/// too (gdb, TY-sub-stack, 2026-11-07). Nested tuples fit 2 MiB.
fn checks_linear(shape: &str, n: usize) {
    use zed_tests::deep::{on_small_stack, program, statements};
    let stmts = statements(&program(shape, 1_000).text);
    let res = zedc::resolve::resolve(&stmts).unwrap();
    on_small_stack(|| assert!(zedc::check::check(&stmts, &res).errors.is_empty()));
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(1 << 29);
        thread
            .spawn_scoped(scope, || {
                let small = statements(&program(shape, n).text);
                let large = statements(&program(shape, 8 * n).text);
                let small_res = zedc::resolve::resolve(&small).unwrap();
                let large_res = zedc::resolve::resolve(&large).unwrap();
                scaling::check_order(&format!("checking {shape}"), n, 1, |k| {
                    let (stmts, res) = if k == n {
                        (&small, &small_res)
                    } else {
                        (&large, &large_res)
                    };
                    let info = zedc::check::check(stmts, res);
                    assert!(info.errors.is_empty(), "{shape}: {:?}", info.errors);
                });
            })
            .unwrap()
            .join()
            .unwrap()
    });
}

#[test]
fn lambdas_nested_8000_deep_check_in_linear_time() {
    // Each lambda's signature was walked again, copied and dropped by each lambda around it,
    // to name its variables and to replace the classes it was solved to, so the time was
    // quadratic, and `Ty::replace` overflowed a 2 MiB stack near 4,000 deep. A signature held
    // in a type now keeps the variables it holds (`Sig::facts`, CHK-lambda), and one that
    // holds none of those replaced is shared whole.
    checks_linear("nested lambdas", 1_000);
}

#[test]
fn tuples_nested_8000_deep_check_in_linear_time() {
    // Whether a tuple's components may hold a variable, the unknown or a function was found by
    // a walk of the components at each level, so the time grew as n^2 and more (CHK-tuple). A
    // tuple shape now keeps those facts (`ty::Row`).
    checks_linear("nested tuples", 1_000);
}

/// `f(positional x) = ((… (x, 1) …, 1), 1);`, a variable `n` tuples deep.
fn nested_around(n: usize) -> String {
    format!(
        "f(positional x) = {}x{};\n",
        "(".repeat(n),
        ", 1)".repeat(n)
    )
}

#[test]
fn a_variable_nested_in_tuples_checks_in_linear_time() {
    assert_eq!(sig(&nested_around(2), "f"), "(_) -> ((_, 1), 1)");
    zed_tests::deep::on_small_stack(|| {
        let units = resolved(500, nested_around);
        scaling::check_order("a variable nested in n tuples", 500, 1, |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
}

/// `(int) -> ((int) -> (… (int) -> result))`, `n` arrows deep.
fn curried_type(n: usize, result: zedc::check::ty::Ty) -> zedc::check::ty::Ty {
    use std::sync::Arc;
    use zed_kernel::types::Type;
    use zedc::check::ty::{SParam, Sig, Ty};
    (0..n).fold(result, |t, _| {
        let x = SParam {
            name: "x".into(),
            positional: true,
            default: None,
        };
        Ty::func(Arc::new(Sig::one(vec![x], vec![Ty::set(Type::int())], t)))
    })
}

/// Takes `t` apart level by level: dropping it whole recurses through each `Arc<Sig>` and
/// overflows a 2 MiB stack near 8,000 deep, which is not what the test below is about.
fn take_apart(t: zedc::check::ty::Ty) {
    let mut stack = vec![t];
    while let Some(mut t) = stack.pop() {
        for s in std::mem::take(&mut t.fns) {
            if let Ok(s) = std::sync::Arc::try_unwrap(s) {
                for a in s.arrows {
                    stack.push(a.result);
                    stack.extend(a.params);
                }
            }
        }
    }
}

#[test]
fn function_types_nested_16000_deep_compare_on_a_2_mib_stack() {
    // The comparison of function types (`Ty::sub`, `fits_sig` and the cover of rule 6 of
    // sec:type_resolution) recursed once per level of nesting, about 8 frames a level, and
    // overflowed a 2 MiB stack at 800 levels. Its frames now live on a stack on the heap
    // (`Comparing`, TY-sub-stack); each level is compared once, so the time is linear.
    use zed_kernel::types::Type;
    use zedc::check::ty::Ty;
    // Only the fit is timed. At each level a failed fit is followed by the search for a cover,
    // which compares the level below again, so the time of a refusal about doubles with each
    // level (TY-refuse-exp in STATUS.md): 0.44 ms 5 deep and 0.67 s 16 deep with the
    // recursion, about the same with the explicit stack (13.5 s 20 deep).
    let n = 2_000;
    let int = || Ty::set(Type::int());
    let number = || Ty::set(&Type::int() | &Type::f64());
    assert!(!curried_type(3, number()).subtype(&curried_type(3, int())));
    zed_tests::deep::on_small_stack(|| {
        let built: std::collections::BTreeMap<usize, _> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, (curried_type(m, int()), curried_type(m, number()))))
            .collect();
        scaling::check_order("comparing function types n deep", n, 1, |m| {
            let (narrow, wide) = &built[&m];
            assert!(narrow.subtype(wide), "{m} deep");
        });
        for (narrow, wide) in built.into_values() {
            take_apart(narrow);
            take_apart(wide);
        }
    });
}

/// `x = bitAnd(bitAnd(… bitAnd(1, 1) …, 1), 1);`, `n` calls of the bit word nested.
fn bit_words(n: usize) -> String {
    format!("x = {}1{};\n", "bitAnd(".repeat(n), ", 1)".repeat(n))
}

#[test]
fn bit_words_8000_deep_check_on_a_2_mib_stack() {
    // A bit word's arguments are checked from the walk's frame `Bits`, so the nesting keeps
    // no frame of the thread's stack per call. Checked by a recursive call per argument, this
    // overflowed the stack below 1,000 deep. 1,000,000 deep does not fit the 60 s limit of a
    // test: measured at 100,000 deep (linear from 12,500), parsing takes 10 s and checking
    // 16 s, about 100 us and 160 us a call, the checker's in the kernel's type algebra as for
    // the calls above; 1,000,000 deep would take about 100 s to parse and 160 s to check.
    use zed_tests::deep::{on_small_stack, statements};
    let n = 1_000;
    let small = statements(&bit_words(n));
    let large = statements(&bit_words(8 * n));
    let small_res = zedc::resolve::resolve(&small).unwrap();
    let large_res = zedc::resolve::resolve(&large).unwrap();
    on_small_stack(|| {
        scaling::check_order("checking nested bit words", n, 1, |k| {
            let (stmts, res) = if k == n {
                (&small, &small_res)
            } else {
                (&large, &large_res)
            };
            let info = zedc::check::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
}
