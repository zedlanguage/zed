//! The checker on programs nested as deep as overflowed a stack when it recursed once a level:
//! each is checked on a 2 MiB stack, or on as small a stack a level as an 8 MiB one at the depth
//! it ran at, with no recursion on the nesting. The time of each, linear in the depth, is
//! measured in `bench::deep_scaling`.

use zed_tests::deep::{on_small_stack, program, statements};
use zed_tests::scaling;

use super::sig;

/// Checks each program of `shapes` `n` deep on a 2 MiB stack, and finds no type error.
fn checks_on_a_small_stack(shapes: &[&str], n: usize) {
    on_small_stack(|| {
        for &shape in shapes {
            let stmts = statements(&program(shape, n).text);
            let res = zedc::resolve::resolve(&stmts).unwrap();
            let info = zedc::check::walk::check(&stmts, &res);
            assert!(info.errors.is_empty(), "{shape}: {:?}", info.errors);
        }
    });
}

#[test]
fn sums_blocks_negations_calls_and_bit_words_1000_deep_check_on_a_2_mib_stack() {
    // A small instance of the benchmarks in `bench::deep_scaling` on nested blocks, sums,
    // negations, calls and bit words. The checker recursed once per level of nesting, and
    // overflowed this stack at 1,000 deep, and the bit words below 1,000.
    checks_on_a_small_stack(
        &[
            "nested blocks",
            "a left-nested sum",
            "a sum nested in parentheses",
            "nested negations",
            "nested calls",
        ],
        1_000,
    );
    on_small_stack(|| {
        let info = super::info(&bit_words(1_000)).0;
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn long_bodies_else_if_chains_lambdas_and_tuples_4000_deep_check_on_a_2_mib_stack() {
    // A small instance of the benchmarks in `bench::deep_scaling` on long bodies, `else if`
    // chains, nested lambdas and nested tuples. `else if` chains overflowed this stack below
    // 4,000 deep, and `Ty::replace` near 4,000 nested lambdas.
    checks_on_a_small_stack(
        &[
            "a long sum in a function's body",
            "an `else if` chain",
            "nested lambdas",
            "nested tuples",
        ],
        4_000,
    );
}

/// `f(positional x) = ((… (x, 1) …, 1), 1);`, a variable `n` tuples deep.
pub(super) fn nested_around(n: usize) -> String {
    format!(
        "f(positional x) = {}x{};\n",
        "(".repeat(n),
        ", 1)".repeat(n)
    )
}

#[test]
fn a_variable_nested_in_tuples_is_kept_in_its_result() {
    // A small instance of the benchmark
    // `bench::deep_scaling::a_variable_nested_in_tuples_checks_in_linear_time`.
    assert_eq!(sig(&nested_around(2), "f"), "(T) -> ((T, 1), 1)");
    on_small_stack(|| {
        let info = super::info(&nested_around(4_000)).0;
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// `(int) -> ((int) -> (… (int) -> result))`, `n` arrows deep.
pub(super) fn curried_type(n: usize, result: zedc::check::ty::Ty) -> zedc::check::ty::Ty {
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
fn function_types_nested_1000_deep_compare_on_a_2_mib_stack() {
    // A small instance of the benchmarks in `bench::deep_scaling` on function types nested
    // deep, compared and refused. The comparison of function types (`Ty::sub`, `fits_sig` and
    // the cover of rule 6 of sec:type_resolution) recursed once per level of nesting, about 8
    // frames a level, and overflowed a 2 MiB stack at 800 levels (TY-sub-stack).
    use zed_kernel::types::Type;
    use zedc::check::ty::Ty;
    let int = || Ty::set(Type::int());
    let number = || Ty::set(&Type::int() | &Type::f64());
    assert!(curried_type(3, int()).subtype(&curried_type(3, number())));
    assert!(!curried_type(3, number()).subtype(&curried_type(3, int())));
    on_small_stack(|| {
        let (narrow, wide) = (curried_type(1_000, int()), curried_type(1_000, number()));
        assert!(narrow.subtype(&wide));
        assert!(!wide.subtype(&narrow));
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

/// `x = bitAnd(bitAnd(… bitAnd(1, 1) …, 1), 1);`, `n` calls of the bit word nested.
pub(super) fn bit_words(n: usize) -> String {
    format!("x = {}1{};\n", "bitAnd(".repeat(n), ", 1)".repeat(n))
}

/// `p` expects a function of `d` curried arrows that take int, String at `at`, and return a pair
/// of ints at the end; `g` has `d` curried parameters and returns the one at `uses` plus `int(1)`,
/// and `last`. The `int(1)` fixes the carrier: a curried function generic in its first
/// parameter does not yet fit the curried type (follow-up CURRIED-generic-fit).
fn curried_refusal(d: usize, uses: usize, at: usize, last: &str) -> String {
    let arrows: String = (0..d)
        .map(|i| if i == at { "(String) -> " } else { "(int) -> " })
        .collect();
    let lambdas: String = (1..d).map(|i| format!("(a{i}) -> ")).collect();
    format!(
        "p(f: {arrows}(int, int)) = 0;\ng(positional a0) = {lambdas}(a{uses} + int(1), {last});\ny = p(f: g);\n"
    )
}

/// The message for `curried_refusal(d, …)`: `g`'s signature, its parameter at `uses` int and
/// its result `result`, and `p`'s slot, its parameter at `at` String.
fn curried_refusal_message(d: usize, uses: usize, at: usize, result: &str) -> String {
    let given = (0..d).fold(result.to_string(), |r, i| {
        let p = if d - 1 - i == uses { "int" } else { "_" };
        format!("({p}) -> {r}")
    });
    let expected = (0..d).fold("(int, int)".to_string(), |r, i| {
        let p = if d - 1 - i == at { "String" } else { "int" };
        format!("({p}) -> {r}")
    });
    format!(
        "`g` is `{given}`, not `{expected}`: it is passed where a function of that type is \
         expected, and its own type does not fit that one. [g]"
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
