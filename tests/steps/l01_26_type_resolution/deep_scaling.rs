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
    });
}

/// Programs with a function type written `n` deep: `p(g: t) = 0; q(f: t) = p(g: f);` for `t`
/// the type `(h: … (x: int) -> int …) -> int`, the same with a bounded result variable at each
/// level, and `h(g: t)` for `t` a nest of `n` bounds clauses `(… T0 -> T0 for T0 in int …) ->
/// Tk for Tk in f64`.
fn written_deep(n: usize) -> [String; 3] {
    let (mut plain, mut bounded) = (String::from("(x: int) -> int"), String::new());
    bounded.push_str(&plain);
    for i in 0..n {
        plain = format!("(h{i}: {plain}) -> int");
        bounded = format!("((h{i}: {bounded}) -> T{i} for T{i} in int)");
    }
    let mut clauses = "(".repeat(n - 1);
    clauses.push_str("T0 -> T0 for T0 in int");
    for i in 1..n {
        clauses.push_str(&format!(") -> T{i} for T{i} in f64"));
    }
    let passed = |t: &str| format!("p(g: {t}) = 0;\nq(f: {t}) = p(g: f);\n");
    [
        passed(&plain),
        passed(&bounded),
        format!("h(g: {clauses}) = 0;\n"),
    ]
}

/// Resolves and checks each of [`written_deep`]`(n)`, its types denoted, their variables
/// gathered, printed and dropped, on the thread it is called on.
fn checks_written(n: usize) {
    for text in written_deep(n) {
        let stmts = zed_tests::deep::statements(&text);
        let res = zedc::resolve::resolve(&stmts).unwrap();
        let info = zedc::check::walk::check(&stmts, &res);
        assert!(info.errors.is_empty(), "{n} deep: {:?}", info.errors);
        assert!(info.sigs.values().all(|s| !s.to_string().is_empty()));
    }
}

#[test]
fn function_types_written_16000_deep_check_on_a_2_mib_stack() {
    // The denotation of a written type (`Denote::ty`, zedc-check) recursed once per level of
    // its nesting, and so did the variables of a signature, gathered from those of the
    // functions it holds (`Sig::facts`): each overflowed this stack at 3,200 deep and needed
    // 1 GiB (TY-sub-stack). Each now keeps a stack of its own (TY-write-stack).
    zed_tests::deep::on_small_stack(|| checks_written(16_000));
}

#[test]
fn function_types_written_64000_deep_check_on_an_8_mib_stack() {
    // The 8 MiB stack of a main thread, on which zedc checks a program (the post-batch TODO):
    // four times as deep as on 2 MiB, so a recursion of one frame of 128 bytes a level would
    // overflow it too.
    zed_tests::deep::on_main_sized_stack(|| checks_written(64_000));
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
    assert!(curried_type(3, int()).subtype(&curried_type(3, number())));
    assert!(!curried_type(3, number()).subtype(&curried_type(3, int())));
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

/// `p` expects a function of `d` curried arrows that take int, String at `at`, and return a pair
/// of ints at the end; `g` has `d` curried parameters and returns the one at `uses` plus 1, and `last`.
fn curried_refusal(d: usize, uses: usize, at: usize, last: &str) -> String {
    let arrows: String = (0..d)
        .map(|i| if i == at { "(String) -> " } else { "(int) -> " })
        .collect();
    let lambdas: String = (1..d).map(|i| format!("(a{i}) -> ")).collect();
    format!(
        "p(f: {arrows}(int, int)) = 0;\ng(positional a0) = {lambdas}(a{uses} + 1, {last});\ny = p(f: g);\n"
    )
}

/// The message for `curried_refusal(d, …)`: `g`'s signature, its parameter at `uses` int and
/// its result `result`, and `p`'s slot, its parameter at `at` String.
fn curried_refusal_message(d: usize, uses: usize, at: usize, result: &str) -> String {
    let given = (0..d).fold(result.to_string(), |r, i| {
        let p = if d - 1 - i == uses { "int" } else { "_" };
        format!("({p}) -> {}", if i == 0 { r } else { format!("({r})") })
    });
    let expected = (0..d).fold("(int, int)".to_string(), |r, i| {
        let p = if d - 1 - i == at { "String" } else { "int" };
        format!("({p}) -> {}", if i == 0 { r } else { format!("({r})") })
    });
    format!(
        "`g` is `{given}`, not `{expected}`: it is passed where a function of that type is \
         expected, and its own type does not fit that one [g]"
    )
}

#[test]
fn a_refusal_deep_in_a_curried_type_names_the_argument() {
    // A function passed where curried function types are expected is refused at the argument,
    // with both types whole, whether the mismatch is in the result 40 levels down or at a
    // parameter in the middle of the chain; the same function with every level fitting is
    // taken. Compared level by level twice, 40 levels took about 2^40 comparisons.
    use super::type_errors;
    let d = 40;
    let none = d;
    assert_eq!(
        type_errors(&curried_refusal(d, 0, none, "1")),
        Vec::<String>::new()
    );
    assert_eq!(
        type_errors(&curried_refusal(d, 0, none, "0.5")),
        [curried_refusal_message(d, 0, none, "(int, 0.5)")]
    );
    assert_eq!(
        type_errors(&curried_refusal(d, 20, 20, "1")),
        [curried_refusal_message(d, 20, 20, "(int, 1)")]
    );
    assert_eq!(
        type_errors(&curried_refusal(d, 20, 21, "1")),
        Vec::<String>::new()
    );
}
