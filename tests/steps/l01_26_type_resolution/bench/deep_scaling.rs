//! The time of checking programs nested thousands deep, on a 2 MiB stack with no recursion on
//! the nesting (DESIGN.md Part G), and written function types 4,000 deep on 512 KiB. The
//! checks of each shape a few levels deep are in `deep_scaling`.

use zed_tests::scaling;

use super::super::deep_scaling::{bit_words, checks_written, curried_type, nested_around};
use super::super::scaling::resolved;

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
                let info = zedc::check::walk::check(stmts, res);
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

/// Checks the program of `shape` `n` and `8n` deep on a 2 MiB stack and checks the time is
/// linear. Until TY-write-stack this ran on a 512 MiB stack: at 8,000 nested lambdas the drop
/// of their type recursed through each `Arc<Sig>` and overflowed 2 MiB (gdb, TY-sub-stack);
/// a signature is now dropped on a stack of its own (`Drop for Sig`).
fn checks_linear(shape: &str, n: usize) {
    use zed_tests::deep::{on_small_stack, program, statements};
    on_small_stack(|| {
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
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{shape}: {:?}", info.errors);
        });
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

#[test]
fn a_variable_nested_in_tuples_checks_in_linear_time() {
    zed_tests::deep::on_small_stack(|| {
        let units = resolved(500, nested_around);
        scaling::check_order("a variable nested in n tuples", 500, 1, |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
}

#[test]
fn function_types_nested_16000_deep_compare_on_a_2_mib_stack() {
    // The comparison of function types (`Ty::sub`, `fits_sig` and the cover of rule 6 of
    // sec:type_resolution) recursed once per level of nesting, about 8 frames a level, and
    // overflowed a 2 MiB stack at 800 levels. Its frames now live on a stack on the heap
    // (`Comparing`, TY-sub-stack); each level is compared once, so the time is linear.
    use zed_kernel::types::Type;
    use zedc::check::ty::Ty;
    // The fit is timed here, the refusal in the test below (TY-refuse-exp).
    let n = 2_000;
    let int = || Ty::set(Type::int());
    let number = || Ty::set(&Type::int() | &Type::f64());
    zed_tests::deep::on_small_stack(|| {
        let built: std::collections::BTreeMap<usize, _> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, (curried_type(m, int()), curried_type(m, number()))))
            .collect();
        scaling::check_order("comparing function types n deep", n, 1, |m| {
            let (narrow, wide) = &built[&m];
            assert!(narrow.subtype(wide), "{m} deep");
        });
    });
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
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
}

#[test]
fn a_refusal_of_function_types_nested_8000_deep_is_linear() {
    // `(int) -> … -> int | f64` is not `(int) -> … -> int`. At each level the arrow's fit
    // fails, and the search for a cover (rule 6 of sec:type_resolution) compares the same two
    // results again, so each level was compared twice for each level around it: 1.0 ms 6 deep,
    // 15.5 ms 10 deep, 0.92 s 16 deep, doubling per level (TY-refuse-exp). The verdict of each
    // pair of functions compared is now kept for the comparison (`Cx::fitted`), so each level
    // is compared once.
    use zed_kernel::types::Type;
    use zedc::check::ty::Ty;
    let n = 1_000;
    let int = || Ty::set(Type::int());
    let number = || Ty::set(&Type::int() | &Type::f64());
    zed_tests::deep::on_small_stack(|| {
        let built: std::collections::BTreeMap<usize, _> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, (curried_type(m, int()), curried_type(m, number()))))
            .collect();
        scaling::check_order("refusing function types n deep", n, 1, |m| {
            let (narrow, wide) = &built[&m];
            assert!(!wide.subtype(narrow), "{m} deep");
        });
    });
}


#[test]
fn function_types_written_4000_deep_check_on_a_512_kib_stack() {
    // The denotation of a written type (`Denote::ty`, zedc-check) recursed once per level of
    // its nesting, and so did the variables of a signature, gathered from those of the
    // functions it holds (`Sig::facts`): each overflowed a 2 MiB stack at 3,200 deep and needed
    // 1 GiB (TY-sub-stack). Each now keeps a stack of its own (TY-write-stack). These ran
    // 16,000 deep on 2 MiB and 64,000 deep on the 8 MiB stack of a main thread, on which zedc
    // checks a program; 4,000 deep on 512 KiB is the same stack a level, so a recursion of one
    // frame of 128 bytes a level overflows it too.
    scaling::on_a_thread(512 << 10, || checks_written(4_000));
}
