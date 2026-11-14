//! `min` and `max` of two tuples (DESIGN.md sec:reduction, item 5; plan row MINMAX-tuples): the
//! first component in which they differ decides, by `min` or `max` of that pair.

use super::x;
use zed_kernel::{Prim, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::{Checked, checked, errors, value};
use zed_tests::step_helpers::l01_26_type_resolution::sig;

#[test]
fn the_first_component_that_differs_decides() {
    assert_eq!(x("min((1, 2), (1, 3))"), "(1, 2)");
    assert_eq!(x("max((1, 2), (1, 3))"), "(1, 3)");
    assert_eq!(x("min((2, 0), (1, 9))"), "(1, 9)");
    assert_eq!(x("max((1r/2r, 2), (1r/3r, 9))"), "(1r/2r, 2)");
    assert_eq!(x("min((1, (2, 3)), (1, (2, 1)))"), "(1, (2, 1))");
    assert_eq!(x("(1, 2).min((0, 9))"), "(0, 9)");
    assert_eq!(x("max(min((5, 1), (4, 9)), (4, 8))"), "(4, 9)");
}

#[test]
fn the_nearest_pair_of_clusters_as_corpus_14_finds_it() {
    // Corpus 14 folds `(d2, label, label)` with `>< min`; the fold is step L3.2, the pairwise
    // `min` it folds with is here.
    assert_eq!(
        x("min(min((2.0f64, 1, 3), (0.5f64, 2, 4)), (0.5f64, 1, 9))"),
        "(0.5, 1, 9)"
    );
    assert_eq!(
        sig(
            "f(positional p: (f64, int, int), positional q: (f64, int, int)) = min(p, q);\n",
            "f"
        ),
        "((f64, int, int), (f64, int, int)) -> (f64, int, int)"
    );
}

#[test]
fn a_float_part_is_ordered_as_ieee_minimum_and_maximum() {
    // A NaN in the first component that differs is taken by both, as at the top level.
    assert_eq!(x("min((2.0f64, 1), (0.0f64 / 0.0f64, 0))"), "(nan, 0)");
    assert_eq!(x("max((2.0f64, 1), (0.0f64 / 0.0f64, 0))"), "(nan, 0)");
    assert_eq!(x("min((1, 0.0f64 / 0.0f64), (1, 2.0f64))"), "(1, nan)");
    // `-0.0` is below `0.0` in either order, so `min` commutes.
    assert_eq!(x("min((0.0f64, 1), (-0.0f64, 1))"), "(-0.0, 1)");
    assert_eq!(x("min((-0.0f64, 1), (0.0f64, 1))"), "(-0.0, 1)");
    assert_eq!(x("max((-0.0f64, 1), (0.0f64, 1))"), "(0.0, 1)");
}

#[test]
fn min_of_a_number_and_infinity_is_the_number() {
    // An infinity made by arithmetic is a float; `f64(#inf)` is the cast of an atom, which
    // plan row NAN-cast-atoms implements, and until then evaluates to the atom `#inf`.
    assert_eq!(x("min(2.0f64, 1.0f64 / 0.0f64)"), "2.0");
    assert_eq!(x("max(2.0f64, 1.0f64 / 0.0f64)"), "inf");
    assert_eq!(x("min(2.0f64, -1.0f64 / 0.0f64)"), "-inf");
    // Through a parameter whose class meets the float.
    assert_eq!(
        value(
            "m(positional a) = min(a, 1.0f64 / 0.0f64);\nx = m(2.0f64);\n",
            "x"
        ),
        "2.0"
    );
}

#[test]
fn tuples_min_and_max_cannot_order_are_refused() {
    assert_eq!(
        errors("x = min((1, 2), (1, 2, 3));\n"),
        [
            "`min` does not take (1, 2) and (1, 2, 3): no tuple of 2 on the other side. [min((1, 2), (1, 2, 3))]",
            "`min` does not take (1, 2) and (1, 2, 3): no tuple of 3 on the other side. [min((1, 2), (1, 2, 3))]",
        ]
    );
    assert_eq!(
        errors("x = min((1, \"a\"), (1, \"b\"));\n"),
        [
            "`min` does not take (\"a\", \"b\"): no arrow of `min` takes these types. [min((1, \"a\"), (1, \"b\"))]"
        ]
    );
    assert_eq!(
        errors("x = min((1, 2.0), (1, 3));\n"),
        // As `min(2.0, 3)` is: nothing gives the decimal a carrier (DESIGN.md L1.26a).
        [
            "Nothing gives the literal `2.0` a carrier. Try `x = min((1, 2.0f64), (1, 3))` \
             instead.\n  fixes, each checked here:\n    x = min((1, 2.0f64), (1, 3));    the \
             literal is then the f64 2.0\n    x = min((1, 2.0r), (1, 3));      the literal is then \
             exactly 2.0, a rat [2.0]"
        ]
    );
    assert_eq!(
        errors("x = min((1, 2), 3);\n"),
        ["`min` does not take (1, 2) and 3, only two tuples or two numbers. [min((1, 2), 3)]"]
    );
    assert_eq!(
        errors("text(positional v: String) = v;\nx = min((int(text(\"x\")), 2), (1, 3));\n"),
        [
            "`min` does not order #invalid in a tuple: it compares tuples component by component, and an atom has no order among the numbers; handle it before `min`. [min((int(text(\"x\")), 2), (1, 3))]"
        ]
    );
}

#[test]
fn an_operator_of_the_same_signature_does_not_take_tuples() {
    // `+`, `-` and `*` have the arrows of `min` and `max`; only a call of the word itself
    // takes two tuples. Two tuples under `+` are refused as before, not added componentwise.
    assert_eq!(
        errors("y = (-3, 1) + \"a\";\n"),
        [
            "`+` does not take ((-3, 1), \"a\"): no arrow of `+` takes these types. [(-3, 1) + \"a\"]"
        ]
    );
    assert_eq!(
        errors("y = (1, 2) + (3, 4);\n"),
        [
            "`+` does not take ((1, 2), (3, 4)): no arrow of `+` takes these types. [(1, 2) + (3, 4)]"
        ]
    );
    assert_eq!(
        errors("y = (1, 2) - (3, 4);\n"),
        [
            "`-` does not take ((1, 2), (3, 4)): no arrow of `-` takes these types. [(1, 2) - (3, 4)]"
        ]
    );
    assert_eq!(
        errors("y = (1, 2) * (3, 4);\n"),
        [
            "`*` does not take ((1, 2), (3, 4)): no arrow of `*` takes these types. [(1, 2) * (3, 4)]"
        ]
    );
    // The word itself, by name or as a method, still takes them.
    assert_eq!(x("min((1, 2), (3, 4))"), "(1, 2)");
    assert_eq!(x("(1, 2).max((3, 4))"), "(3, 4)");
}

/// `min` (`min` true) or `max` of `a` and `b` by the kernel.
pub(crate) fn pick(min: bool, a: &Value, b: &Value) -> Value {
    let p = if min { Prim::Min } else { Prim::Max };
    zed_kernel::eval(&Term::Prim(
        p,
        vec![Term::Lit(a.clone()), Term::Lit(b.clone())],
    ))
    .unwrap()
}

#[test]
fn the_laws_hold_over_every_triple_of_small_tuples() {
    // Every tuple of a float and an int from small sets, and every triple of them: `min` and
    // `max` are commutative, associative, idempotent and selective, bit for bit (printed text
    // tells NaN and `-0.0` apart); without NaN and `-0.0` they agree with the natural order; a
    // 1-tuple agrees with the scalar word.
    let floats = [f64::NAN, f64::NEG_INFINITY, -0.0, 0.0, 1.0, f64::INFINITY];
    let ts: Vec<Value> = floats
        .iter()
        .flat_map(|&f| {
            (0..2).map(move |i| Value::tuple(vec![Value::float(f), Value::int(i.into())]))
        })
        .collect();
    let s = |v: &Value| v.to_string();
    for min in [true, false] {
        for a in &ts {
            assert_eq!(s(&pick(min, a, a)), s(a));
            for b in &ts {
                let ab = pick(min, a, b);
                assert_eq!(s(&ab), s(&pick(min, b, a)), "{a} {b}");
                assert!(s(&ab) == s(a) || s(&ab) == s(b), "{a} {b}");
                let plain = |v: &Value| !s(v).contains("nan") && !s(v).contains("-0.0");
                if plain(a) && plain(b) {
                    let natural = if min { a.min(b) } else { a.max(b) };
                    assert_eq!(s(&ab), s(natural), "{a} {b}");
                }
                for c in &ts {
                    assert_eq!(
                        s(&pick(min, &ab, c)),
                        s(&pick(min, a, &pick(min, b, c))),
                        "{a} {b} {c}"
                    );
                }
            }
        }
        for &f in &floats {
            for &g in &floats {
                let one = |x: f64| Value::tuple(vec![Value::float(x)]);
                let scalar = pick(min, &Value::float(f), &Value::float(g));
                assert_eq!(s(&pick(min, &one(f), &one(g))), format!("({scalar},)"));
            }
        }
    }
}

#[test]
fn min_and_max_through_a_function_value_take_two_tuples() {
    // The word itself is passed, so a call through the name or parameter that holds it takes
    // two tuples as a call of `min` by name does.
    let v = |text: &str| value(text, "x");
    assert_eq!(v("f = min;\nx = f((1, 2), (1, 3));\n"), "(1, 2)");
    assert_eq!(v("g = max;\nx = g((1, 2), (1, 3));\n"), "(1, 3)");
    assert_eq!(
        v(
            "ap(positional h, positional a, positional b) = h(a, b);\nx = ap(min, (1, 2), (0, 9));\n"
        ),
        "(0, 9)"
    );
    assert_eq!(v("f = max;\nx = f(f((5, 1), (4, 9)), (5, 0));\n"), "(5, 1)");
    // It refuses through the name what it refuses by its own, and the message names the
    // word as well as the name.
    assert_eq!(
        errors("f = min;\ny = f((1, 2), 3);\n"),
        [
            "`f`, which is `min`, does not take (1, 2) and 3, only two tuples or two numbers. [f((1, 2), 3)]"
        ]
    );
}

#[test]
fn a_function_of_the_arrows_of_min_that_is_not_min_does_not_take_tuples() {
    // A parameter declared with the arrows of `min` is any function of those arrows, `+` among
    // them: the tuple rule follows the word, not the signature.
    assert_eq!(
        errors(
            "ap(positional h: (positional a: int, positional b: int) -> int, positional p: (int, int), positional q: (int, int)) = h(p, q);\n"
        ),
        [
            "`h` does not take ((int, int), (int, int)): no arrow of `h` takes these types. [h(p, q)]"
        ]
    );
}

#[test]
fn a_parameter_met_with_a_tuple_takes_the_tuples_each_call_gives() {
    // `a` is met with a tuple, so it may hold a tuple; each call checks `min` again on what it
    // gives, by the rule a call of `min` by name follows.
    let v = |text: &str| value(text, "x");
    let g = "g(positional a) = min(a, (1, 2));\n";
    assert_eq!(v(&format!("{g}x = g((0, 9));\n")), "(0, 9)");
    assert_eq!(v(&format!("{g}x = g((1, 3));\n")), "(1, 2)");
    assert_eq!(
        v("g(positional a) = max((1, 2), a);\nx = g((0, 9));\n"),
        "(1, 2)"
    );
    assert_eq!(
        v("g(positional a) = a.min((1, 2));\nx = g((0, 9));\n"),
        "(0, 9)"
    );
    assert_eq!(
        v("g(positional a) = min(a, (1, (2, 3)));\nx = g((1, (0, 9)));\n"),
        "(1, (0, 9))"
    );
    assert_eq!(
        v("g(positional a, positional b) = min(a, (b, 2));\nx = g((0, 9), 1);\n"),
        "(0, 9)"
    );
    // Through a function that passes it on.
    assert_eq!(
        v(&format!("{g}h(positional b) = g(b);\nx = h((0, 9));\n")),
        "(0, 9)"
    );
    // The result is a variable a call binds to the join of the two operands, which the
    // unknown `_` shows; `(1, 2) | _` is the same set.
    assert_eq!(sig(g, "g"), "_ -> _");
}

#[test]
fn a_parameter_met_with_a_tuple_refuses_what_min_refuses() {
    let g = "g(positional a) = min(a, (1, 2));\n";
    let e = |call: &str| errors(&format!("{g}x = {call};\n"));
    assert_eq!(
        e("g((0, 9, 1))"),
        [
            "`min` does not take (0, 9, 1) and (1, 2): no tuple of 2 on the other side. [g((0, 9, 1))]",
            "`min` does not take (0, 9, 1) and (1, 2): no tuple of 3 on the other side. [g((0, 9, 1))]"
        ]
    );
    assert_eq!(
        e("g((#red, 9))"),
        [
            "`min` does not order #red in a tuple: it compares tuples component by component, and an atom has no order among the numbers; handle it before `min`. [g((#red, 9))]"
        ]
    );
    assert_eq!(
        e("g((0.5, 1.0))"),
        [
            "`min` does not take (0.5, 1): no arrow of `min` takes these types. [g((0.5, 1.0))]",
            "`min` does not take (1.0, 2): no arrow of `min` takes these types. [g((0.5, 1.0))]"
        ]
    );
    // A number is not a tuple: the parameter keeps no number carrier.
    assert_eq!(
        e("g(3)"),
        ["`g` does not take (3): no arrow of `g` takes these types. [g(3)]"]
    );
    assert_eq!(
        errors("g(positional a) = min(a, (1, (2, 3)));\nx = g((1, 9));\n"),
        ["`min` does not take 9 and (2, 3), only two tuples or two numbers. [g((1, 9))]"]
    );
    // A value that is a number by its own use is not met with a tuple.
    assert_eq!(
        errors("g(positional a) = min(a + 1, (1, 2));\n"),
        ["`min` does not take _ and (1, 2), only two tuples or two numbers. [min(a + 1, (1, 2))]"]
    );
}

#[test]
fn a_generic_function_that_calls_min_on_its_own_parameters_takes_numbers() {
    // Two parameters met only with each other by `min` take its numbers, as two met by `<` take
    // its carriers (DESIGN.md sec:type_resolution: a prelude word removes the carriers it does
    // not take); neither is met with a tuple, so neither may hold one.
    let g = "g(positional a, positional b) = min(a, b);\n";
    assert_eq!(sig(g, "g"), "(T, T) -> T for T in int | f32 | f64 | rat");
    assert_eq!(value(&format!("{g}x = g(3, 2);\n"), "x"), "2");
    assert_eq!(
        errors(&format!("{g}x = g((1, 2), (0, 9));\n")),
        [
            "`g` does not take ((1, 2), (0, 9)): no arrow of `g` takes these types. [g((1, 2), (0, 9))]"
        ]
    );
}

#[test]
fn messages_through_a_function_value_name_the_word() {
    assert_eq!(
        errors("f = min;\nx = f((1, 2), (1, 2, 3));\n"),
        [
            "`f`, which is `min`, does not take (1, 2) and (1, 2, 3): no tuple of 2 on the other side. [f((1, 2), (1, 2, 3))]",
            "`f`, which is `min`, does not take (1, 2) and (1, 2, 3): no tuple of 3 on the other side. [f((1, 2), (1, 2, 3))]"
        ]
    );
    assert_eq!(
        errors(
            "ap(positional h, positional p, positional q) = h(p, q);\nx = ap(max, (1, 2), 3);\n"
        ),
        [
            "`h`, which is `max`, does not take (1, 2) and 3, only two tuples or two numbers. [ap(max, (1, 2), 3)]"
        ]
    );
    // By its own name, the word is named once.
    assert_eq!(
        errors("x = min((1, 2), 3);\n"),
        ["`min` does not take (1, 2) and 3, only two tuples or two numbers. [min((1, 2), 3)]"]
    );
}

#[test]
fn a_call_joins_the_result_of_min_as_min_joins_it() {
    let g = "g(positional a) = min(a, (1, 2));\n";
    // The result of `g((0, 5))` is that of `min((0, 5), (1, 2))`, whose type joins the two
    // tuples of length 2 component by component (DESIGN.md sec:reduction, item 5); each
    // component is an operation on integer literals alone that nothing fixes, so `int`, as
    // `three() = 1 + 2` is `() -> int` (L1.26a).
    assert_eq!(
        sig(&format!("{g}h() = g((0, 5));\n"), "h"),
        "() -> (int, int)"
    );
    // Through a chain that passes the result on: one tuple, not one per link.
    let chain = "g0(positional a) = min(a, (0, 0));\n\
                 g1(positional a) = g0(min(a, (1, 0)));\n\
                 g2(positional a) = g1(min(a, (2, 0)));\n";
    assert_eq!(sig(chain, "g2"), "_ -> _");
    assert_eq!(
        sig(&format!("{chain}h() = g2((5, 9));\n"), "h"),
        "() -> (int, int)"
    );
    // The operands of a chain are still checked against the argument and each other.
    assert_eq!(
        errors(&format!("{chain}x = g2((5, 9, 1));\n")),
        [
            "`min` does not take (5, 9, 1) and (0 | 1 | 2, 0): no tuple of 2 on the other side. [g2((5, 9, 1))]",
            "`min` does not take (5, 9, 1) and (0 | 1 | 2, 0): no tuple of 3 on the other side. [g2((5, 9, 1))]"
        ]
    );
    assert_eq!(
        errors("g0(positional a) = min(a, (0, 0));\ng1(positional a) = g0(min(a, (1.0, 0)));\n"),
        [
            "`min` does not take (1.0, 0): no arrow of `min` takes these types. [g0(min(a, (1.0, 0)))]"
        ]
    );
    // `max` of a `min` is one of the three operands as well.
    assert_eq!(
        value(
            "h(positional a) = max(min(a, (0, 0)), (1, 0));\nx = h((5, 9));\n",
            "x"
        ),
        "(1, 0)"
    );
}

#[test]
fn branches_of_an_if_stay_a_union_through_a_call() {
    // Rule 3 of sec:type_resolution: branch types union, and a call keeps them apart; only
    // the result of `min` or `max` is joined.
    let p = "p(positional c) = if c { (0, 5) } else { (1, 2) };\n";
    assert_eq!(sig(p, "p"), "bool -> (0, 5) | (1, 2)");
    assert_eq!(
        sig(&format!("{p}h(positional c) = p(c);\n"), "h"),
        "bool -> (0, 5) | (1, 2)"
    );
    let g = "g(positional a) = min(a, (1, 2));\n";
    assert_eq!(
        sig(
            &format!("{g}h(positional c) = if c {{ g((0, 5)) }} else {{ (7, 7) }};\n"),
            "h"
        ),
        "bool -> (int, int) | (7, 7)"
    );
    // An argument that is a union of branches is joined only where `min` takes it.
    assert_eq!(
        sig(&format!("{g}{p}h(positional c) = (p(c), g(p(c)));\n"), "h"),
        "bool -> ((0, 5) | (1, 2), (0 | 1, 2 | 5))"
    );
}

// The inputs of the benchmarks in `bench/tuple_min_max.rs`, which the test below checks at a
// small size.

/// Two tuples of `n` floats `0.0, 1.0, …` and a last int, 2 in the first and 1 in the second,
/// so only the last component decides.
pub(crate) fn tuples_differing_last(n: usize) -> (Value, Value) {
    let t = |last: i64| {
        let mut v: Vec<Value> = (0..n).map(|i| Value::float(i as f64)).collect();
        v.push(Value::int(last.into()));
        Value::tuple(v)
    };
    (t(2), t(1))
}

/// Two equal tuples built apart, `t(k + 1) = (t(k), t(k))` to depth `n`: 2^n paths through n
/// distinct pairs of parts.
pub(crate) fn equal_tuples_of_shared_parts(n: usize) -> (Value, Value) {
    let t = || {
        (0..n).fold(Value::tuple(vec![Value::float(1.0)]), |t, _| {
            Value::tuple(vec![t.clone(), t])
        })
    };
    (t(), t())
}

/// `a0 = (0, 1.0f64, 0);` and `a{i} = min(a{i - 1}, (i, 0.5f64, i));` for `i` below `n`.
pub(crate) fn chain_of_tuple_mins(n: usize) -> Checked {
    let mut text = String::from("a0 = (0, 1.0f64, 0);\n");
    for i in 1..n {
        text.push_str(&format!("a{i} = min(a{}, ({i}, 0.5f64, {i}));\n", i - 1));
    }
    checked(&text)
}

/// `x = min((0.0f64, …, 2), (0.0f64, …, 1));`, two tuples of `n` floats and a last int.
pub(crate) fn min_of_tuples_of_n_components(n: usize) -> Checked {
    let parts = |last: usize| {
        let mut v: Vec<String> = (0..n).map(|i| format!("{i}.0f64")).collect();
        v.push(last.to_string());
        v.join(", ")
    };
    checked(&format!("x = min(({}), ({}));\n", parts(2), parts(1)))
}

/// The unit `a0 = (1.0f64, 0); b0 = (2.0f64, 0);`, then `a{k}` and `b{k}` for k up to `n` as
/// `link` makes them from the name of the one before, then `x = min(a{n}, b{n});`.
fn nested_unit(n: usize, link: fn(&str, usize) -> String) -> Checked {
    let mut text = String::from("a0 = (1.0f64, 0);\nb0 = (2.0f64, 0);\n");
    for k in 1..=n {
        for side in ["a", "b"] {
            let before = format!("{side}{}", k - 1);
            text.push_str(&format!("{side}{k} = {};\n", link(&before, k)));
        }
    }
    text.push_str(&format!("x = min(a{n}, b{n});\n"));
    checked(&text)
}

/// `a{k} = (a{k - 1}, k)`: the type of `x` joins the two shapes at each of `n` levels.
pub(crate) fn min_of_tuples_nested(n: usize) -> Checked {
    nested_unit(n, |before, k| format!("({before}, {k})"))
}

/// `a{k} = (a{k - 1}, a{k - 1})`: 2^n paths through `n` distinct types on each side.
pub(crate) fn min_of_tuples_nested_through_shared_parts(n: usize) -> Checked {
    nested_unit(n, |before, _| format!("({before}, {before})"))
}

/// `g{i}(a) = g{i - 1}(min(a, k((i, 0))))` for `i` below `n`, and `x = g{n - 1}((5, 9));`: the
/// use of `a` by `min` is met with the same type in each function.
pub(crate) fn chain_of_functions_meeting_a_tuple(n: usize) -> Checked {
    let mut text =
        String::from("k(positional p: (int, int)) = p;\ng0(positional a) = min(a, k((0, 0)));\n");
    for i in 1..n {
        text.push_str(&format!(
            "g{i}(positional a) = g{}(min(a, k(({i}, 0))));\n",
            i - 1
        ));
    }
    text.push_str(&format!("x = g{}((5, 9));\n", n - 1));
    checked(&text)
}

/// `g{i}(a) = g{i - 1}(min(a, (i, 0)))` for `i` below `n`, and `x = g{n - 1}((5, 9));`: each
/// operand is a literal tuple of its own type.
pub(crate) fn chain_of_functions_meeting_a_literal_tuple(n: usize) -> Checked {
    let mut text = String::from("g0(positional a) = min(a, (0, 0));\n");
    for i in 1..n {
        text.push_str(&format!(
            "g{i}(positional a) = g{}(min(a, ({i}, 0)));\n",
            i - 1
        ));
    }
    text.push_str(&format!("x = g{}((5, 9));\n", n - 1));
    checked(&text)
}

#[test]
fn the_benchmark_inputs_give_their_results_at_a_small_size() {
    // The benchmarks time these inputs at thousands of components, links or levels; here each
    // is checked at 3. `checked` asserts the unit has no error.
    let (a, b) = tuples_differing_last(3);
    assert_eq!(pick(true, &a, &b), b);
    assert_eq!(pick(false, &a, &b), a);
    let (a, b) = equal_tuples_of_shared_parts(3);
    assert_eq!(pick(true, &a, &b).to_string(), a.to_string());
    assert_eq!(
        a.to_string(),
        "((((1.0,), (1.0,)), ((1.0,), (1.0,))), (((1.0,), (1.0,)), ((1.0,), (1.0,))))"
    );
    for unit in [
        chain_of_tuple_mins,
        min_of_tuples_of_n_components,
        min_of_tuples_nested,
        min_of_tuples_nested_through_shared_parts,
        chain_of_functions_meeting_a_tuple,
        chain_of_functions_meeting_a_literal_tuple,
    ] {
        unit(3);
    }
    assert_eq!(
        value(
            "a0 = (0, 1.0f64, 0);\na1 = min(a0, (1, 0.5f64, 1));\na2 = min(a1, (2, 0.5f64, 2));\n",
            "a2"
        ),
        "(0, 1.0, 0)"
    );
}
