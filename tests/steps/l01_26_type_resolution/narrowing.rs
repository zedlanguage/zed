//! An `is` test narrows the name it tests: to the tested type where it holds, and to the
//! rest where it does not, through `not`, `&&` and `||`.

use super::{sig, type_errors};
use zed_tests::instances::permutations;
use zed_tests::step_helpers::l01_16_elaboration::value;

const N: &str = "n(x: int | String) = if x is String { len(x) } else { x * 2 };\n";

#[test]
fn each_branch_sees_its_part_of_the_union() {
    assert_eq!(sig(N, "n"), "(x: int | String) -> int");
    assert_eq!(value(&format!("{N}y = n(x: \"ab\");\n"), "y"), "2");
    assert_eq!(value(&format!("{N}y = n(x: 5);\n"), "y"), "10");
}

#[test]
fn not_swaps_the_branches() {
    assert!(
        type_errors("n(x: int | String) = if x is not String { x * 2 } else { len(x) };\n")
            .is_empty()
    );
}

#[test]
fn and_narrows_where_both_hold_and_or_where_both_fail() {
    assert!(
        type_errors(
            "n(x: int | String, y: int | String) = if x is int && y is int { x + y } else { 0 };\n"
        )
        .is_empty()
    );
    assert!(
        type_errors(
            "n(x: int | String, y: int | String) = \
             if x is String || y is String { 0 } else { x + y };\n"
        )
        .is_empty()
    );
}

#[test]
fn the_right_operand_sees_the_left_ones_narrowing() {
    assert!(type_errors("long(x: int | String) = x is String && len(x) > 2;\n").is_empty());
    assert!(type_errors("short(x: int | String) = x is int || len(x) < 2;\n").is_empty());
    assert_eq!(
        type_errors("long(x: int | String) = x is int && len(x) > 2;\n"),
        [
            "`len` does not take (int): no arrow of `len` takes these types. Try `len(String(x))` instead. [len(x)]"
        ]
    );
}

#[test]
fn without_a_test_the_whole_union_must_fit() {
    assert_eq!(
        type_errors("n(x: int | String) = x * 2;\n"),
        ["`*` does not take (String, 2): no arrow of `*` takes these types. [x * 2]"]
    );
    // The narrowed branch is checked as the narrowed type.
    assert_eq!(
        type_errors("n(x) = if x is String { x + 1 } else { 0 };\n"),
        ["`+` does not take (String, 1): no arrow of `+` takes these types. [x + 1]"]
    );
}

#[test]
fn the_tested_classes_end_alike_whatever_the_order_of_their_tests_and_uses() {
    // Plan row PROOF-join-narrowed-rescan-rounds (b): each test `if a is int { a } else { b }`
    // links the class of `a` to the class it gives, which holds `b`'s, and the uses (`* 2`,
    // `len`, `+`) narrow the classes they are made on. The search of `Ck::join_narrowed`
    // runs no use check (its step (b5): a link it joins has an end of carriers, into which
    // no tuple or function flowed), so the uses act on it only through the masks they left
    // before it runs. The statements are independent, and each of their 24
    // orders makes the classes, and so their roots and links, in another order; the
    // signature and the errors are the same in every order.
    let parts = [
        "  x1 = if a is int { a } else { b };\n",
        "  x2 = if b is int { b } else { c };\n",
        "  x3 = if c is int { c + 1 } else { d };\n",
        "  y = d * 2;\n",
    ];
    for last in ["", "  z = len(d);\n"] {
        let mut seen: Option<(String, Vec<String>)> = None;
        for order in permutations(4) {
            let body: String = order.iter().map(|&i| parts[i]).collect();
            let text = format!(
                "f(positional a, positional b, positional c, positional d) {{\n{body}{last}  \
                 return (x1, x2, x3, y);\n}}\n"
            );
            let mut errors = type_errors(&text);
            errors.sort();
            let got = (
                if errors.is_empty() {
                    sig(&text, "f")
                } else {
                    String::new()
                },
                errors,
            );
            match &seen {
                None => seen = Some(got),
                Some(first) => assert_eq!(&got, first, "{text}"),
            }
        }
        // The program with `len(d)` beside `d * 2` is rejected, and the one without accepted.
        let (sig, errors) = seen.expect("24 orders");
        assert_eq!(last.is_empty(), errors.is_empty(), "{sig} {errors:?}");
    }
}

#[test]
fn a_passed_function_comparing_a_narrowed_value_with_a_literal_ends_alike_in_every_order() {
    // Plan row PROOF-join-narrowed-literal-carrier: a class the search of `Ck::join_narrowed`
    // narrows (`b` or `c`, tested or joined to a tested class) is passed to a function whose
    // body compares it with the literal `1` (`isOne`, or a lambda), and a later use narrows
    // it to a float (`+ 0.5`, `* 0.5`). A literal's carrier is chosen from its class's mask
    // (`Ck::class_takes`), so a check of that body run inside the search could choose it at
    // a mask the search has not yet narrowed in one order and at the narrowed one in
    // another. The proof at `Ck::join_narrowed` (step (b5)) shows no check runs inside the
    // search; these programs give one signature, and no errors, in every order of their
    // statements.
    let top = "isOne(positional x) = x == 1;\napply(positional g, positional v) = g(v);\n";
    let one = "(_, U, _) -> (int | U, bool) for U in f32 | f64 | rat";
    let chain = "(_, T, V) -> (int | T, bool) for V in f32 | f64 | rat";
    let cases: [(&[&str], &str); 6] = [
        (
            &[
                "  x1 = if a is int { a } else { b };\n",
                "  y = apply(isOne, b);\n",
                "  z = b + 0.5;\n",
            ],
            one,
        ),
        (
            &[
                "  x1 = if a is int { a } else { b };\n",
                "  x2 = if b is int { b } else { c };\n",
                "  y = apply(isOne, c);\n",
                "  z = c + 0.5;\n",
            ],
            chain,
        ),
        (
            &[
                "  x1 = if a is int { a } else { b };\n",
                "  y = apply(isOne, if a is f64 { a } else { b });\n",
                "  z = b + 0.5;\n",
            ],
            one,
        ),
        (
            &[
                "  x1 = if a is int { a } else { b };\n",
                "  y = apply((positional v) -> v == 1, b);\n",
                "  z = b + 0.5;\n",
            ],
            one,
        ),
        (
            &[
                "  x1 = if a is int { a } else { b };\n",
                "  y = apply(isOne, if b is f64 { 1 } else { b });\n",
                "  z = a * 0.5;\n",
            ],
            "(T, U, _) -> (int | U, bool) for T in f32 | f64 | rat, U in int | f32 | f64 | rat",
        ),
        (
            &[
                "  x1 = if a is int { a } else { b };\n",
                "  x2 = if b is int { b } else { c };\n",
                "  y = apply((positional v) -> v + 1 == 2, c);\n",
                "  z = c * 0.5;\n",
            ],
            chain,
        ),
    ];
    for (parts, want) in cases {
        for order in permutations(parts.len()) {
            let body: String = order.iter().map(|&i| parts[i]).collect();
            let text = format!(
                "{top}f(positional a, positional b, positional c) {{\n{body}  return (x1, y);\n}}\n"
            );
            assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
            assert_eq!(sig(&text, "f"), want, "{text}");
        }
    }
}

#[test]
fn a_condition_must_be_bool() {
    assert_eq!(
        type_errors("c = if 1 { 2 } else { 3 };\n"),
        [
            "the condition of `if` is 1, not bool: `if` chooses its branch by a `bool`, and this condition may be another value. [1]"
        ]
    );
}
