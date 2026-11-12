//! An ordering of two tuples compares them component by component as far as the shorter goes
//! (DESIGN.md sec:order), and each value of one operand must compare with each of the other.
//! Two tuples both reach position `i` exactly when each has more than `i` components, so the
//! checker reads, at each position, the union of the components of one side's tuples against
//! that of the other's, once, and a pair of component types met again through shared rows is
//! not read again. Before (CHK-components-pairs) it read every pair of tuples: `t < t` over
//! `n` levels that each hold the one below twice took 2.67 s at `n = 16` (`2^n`), `x < x` over
//! 800 tuple shapes 39.9 s (`n²`), and over tuples of each length from 1 to 100, 12.8 s (`n³`).
//!
//! A pair that does not compare is reported once, with the place that reaches it, the types
//! of the two components there, each step that leads to it and the repairs, each tried
//! before it is offered (MSG-compare-components).

use std::collections::BTreeMap;

use zed_tests::scaling;

use super::{Resolved, info, type_errors};

/// `t0 = (1, 1)`, then `n - 1` bindings each holding the last twice, the last compared with
/// itself by `op`.
fn doubled(n: usize, op: &str) -> String {
    let mut text = "t0 = (1, 1);\n".to_string();
    text.extend((1..n).map(|i| format!("t{i} = (t{0}, t{0});\n", i - 1)));
    text.push_str(&format!("less = t{0} {op} t{0};\n", n - 1));
    text
}

/// A parameter of `n` tuple shapes `(#ai, int)`, compared with itself.
fn tagged(n: usize) -> String {
    let arms: Vec<String> = (0..n).map(|i| format!("(#a{i}, int)")).collect();
    format!("f(positional x: {}) = x < x;\n", arms.join(" | "))
}

/// A parameter of the tuples of `int` of each length from 1 to `n`, compared with itself.
fn lengths(n: usize) -> String {
    let arms: Vec<String> = (1..=n)
        .map(|i| match i {
            1 => "(int,)".to_string(),
            _ => format!("({})", vec!["int"; i].join(", ")),
        })
        .collect();
    format!("f(positional x: {}) = x < x;\n", arms.join(" | "))
}

/// `x` of `n` nested tuples around `(int,)` and `y` of `n` around `(inner,)`, each tuple's
/// second component an `int`, compared: the pair that does not compare is at depth `n`.
fn nested(n: usize, inner: &str) -> String {
    let around = |inner: &str| (0..n).fold(format!("({inner},)"), |t, _| format!("({t}, int)"));
    format!(
        "f(positional x: {}, positional y: {}) = x < y;\n",
        around("int"),
        around(inner)
    )
}

/// Each error of `text` in full: the message and its menu, with the text it points at, then
/// each note on its own line, with the text it points at.
fn full(text: &str) -> Vec<String> {
    let (info, _) = info(text);
    (info.errors.iter())
        .map(|e| {
            let notes = e
                .notes
                .iter()
                .map(|n| format!("\n{} [{}]", n.text, &text[n.span.start..n.span.end]));
            format!(
                "{}{} [{}]",
                e.message,
                e.menu,
                &text[e.span.start..e.span.end]
            ) + &notes.collect::<String>()
        })
        .collect()
}

#[test]
fn tuples_of_numbers_and_atoms_compare() {
    assert_eq!(type_errors(&doubled(3, "<")), Vec::<String>::new());
    assert_eq!(type_errors(&doubled(3, ">=")), Vec::<String>::new());
    assert_eq!(type_errors(&tagged(3)), Vec::<String>::new());
    // A proper prefix comes first, so tuples of different lengths compare.
    assert_eq!(type_errors(&lengths(3)), Vec::<String>::new());
}

#[test]
fn a_mismatch_in_the_first_component_is_reported_in_full() {
    let text = "f(positional x: (int, bool), positional y: (bool, bool)) = x < y;\n";
    assert_eq!(
        full(text),
        [
            "Cannot compare unequal types: `x[0] : int < y[0] : bool` in `x < y`. [x < y]\n`x` is \
             (int, bool) here [x]\n`x` is declared `(int, bool)` [positional x: (int, bool)]\n`y` \
             is (bool, bool) here [y]\n`y` is declared `(bool, bool)` [positional y: (bool, \
             bool)]\n`<` compares two tuples component by component, as far as the shorter goes [x \
             < y]\n`<` compares components `[0]`: `x[0] : int` with `y[0] : bool` [x < y]\n`<` \
             compares only two numbers of one kind or two values of one other kind [x < \
             y]\nrepair: change the type of `x` or `y` so that `x[0]` and `y[0]` compare [x < y]"
        ]
    );
}

#[test]
fn a_mismatch_in_a_later_component_is_reported_in_full() {
    // A cast that cannot fail inside the component is offered.
    let text = "f(positional x: (int, int), positional y: (int, rat)) = x < y;\n";
    assert_eq!(
        full(text),
        [
            "Cannot compare unequal types: `x[1] : int < y[1] : rat` in `x < y`. Try `(x[0], \
             rat(x[1])) < y` instead. [x < y]\n`x` is (int, int) here [x]\n`x` is declared `(int, \
             int)` [positional x: (int, int)]\n`y` is (int, rat) here [y]\n`y` is declared `(int, \
             rat)` [positional y: (int, rat)]\n`<` compares two tuples component by component, as \
             far as the shorter goes [x < y]\n`<` compares components `[1]`: `x[1] : int` with \
             `y[1] : rat` [x < y]\n`<` compares only two numbers of one kind or two values of one \
             other kind [x < y]\nrepair: `(x[0], rat(x[1])) < y` [x < y]"
        ]
    );
    // `f64(x[1])` may give `#inexact`, which inside a tuple is data, so no cast is offered.
    let text = "f(positional x: (int, int), positional y: (int, f64)) = x < y;\n";
    assert_eq!(
        full(text),
        [
            "Cannot compare unequal types: `x[1] : int < y[1] : f64` in `x < y`. [x < y]\n`x` is \
             (int, int) here [x]\n`x` is declared `(int, int)` [positional x: (int, int)]\n`y` is \
             (int, f64) here [y]\n`y` is declared `(int, f64)` [positional y: (int, f64)]\n`<` \
             compares two tuples component by component, as far as the shorter goes [x < y]\n`<` \
             compares components `[1]`: `x[1] : int` with `y[1] : f64` [x < y]\n`<` compares only \
             two numbers of one kind or two values of one other kind [x < y]\nrepair: change the \
             type of `x` or `y` so that `x[1]` and `y[1]` compare [x < y]"
        ]
    );
}

#[test]
fn a_mismatch_in_a_nested_tuple_is_reported_in_full() {
    let text = "f(positional x: (int, (bool, int)), positional y: (int, (bool, rat))) = x < y;\n";
    assert_eq!(
        full(text),
        [
            "Cannot compare unequal types: `x[1][1] : int < y[1][1] : rat` in `x < y`. Try `(x[0], \
             (x[1][0], rat(x[1][1]))) < y` instead. [x < y]\n`x` is (int, (bool, int)) here \
             [x]\n`x` is declared `(int, (bool, int))` [positional x: (int, (bool, int))]\n`y` is \
             (int, (bool, rat)) here [y]\n`y` is declared `(int, (bool, rat))` [positional y: \
             (int, (bool, rat))]\n`<` compares two tuples component by component, as far as the \
             shorter goes [x < y]\ncomponents `[1]` are tuples, compared the same way [x < y]\n`<` \
             compares components `[1]`: `x[1][1] : int` with `y[1][1] : rat` [x < y]\n`<` compares \
             only two numbers of one kind or two values of one other kind [x < y]\nrepair: `(x[0], \
             (x[1][0], rat(x[1][1]))) < y` [x < y]"
        ]
    );
    // A tuple met by values that are not tuples, one side holding an atom.
    let text = "f(positional x: (int, #a), positional y: (int, (int, int))) = x < y;\n";
    assert_eq!(
        full(text),
        [
            "Cannot compare unequal types: `x[1] : #a < y[1] : (int, int)` in `x < y`. [x < \
             y]\n`x` is (int, #a) here [x]\n`x` is declared `(int, #a)` [positional x: (int, \
             #a)]\n`y` is (int, (int, int)) here [y]\n`y` is declared `(int, (int, int))` \
             [positional y: (int, (int, int))]\n`<` compares two tuples component by component, as \
             far as the shorter goes [x < y]\n`<` compares components `[1]`: `x[1] : #a` with \
             `y[1] : (int, int)` [x < y]\n`<` compares a tuple only with a tuple, not `#a` [x < \
             y]\nrepair: change the type of `x` or `y` so that `x[1]` and `y[1]` compare [x < y]"
        ]
    );
}

#[test]
fn tuples_of_different_lengths_compare_as_far_as_the_shorter_goes() {
    // The third component of `x` is never compared.
    let text = "f(positional x: (int, int, bool), positional y: (int, int)) = x < y;\n";
    assert_eq!(full(text), Vec::<String>::new());
    // A mismatch inside the shared prefix is reported; the extra component is not named.
    let text = "f(positional x: (int, int), positional y: (int, rat, bool)) = x < y;\n";
    assert_eq!(
        full(text),
        [
            "Cannot compare unequal types: `x[1] : int < y[1] : rat` in `x < y`. Try `(x[0], \
             rat(x[1])) < y` instead. [x < y]\n`x` is (int, int) here [x]\n`x` is declared `(int, \
             int)` [positional x: (int, int)]\n`y` is (int, rat, bool) here [y]\n`y` is declared \
             `(int, rat, bool)` [positional y: (int, rat, bool)]\n`<` compares two tuples \
             component by component, as far as the shorter goes [x < y]\n`<` compares components \
             `[1]`: `x[1] : int` with `y[1] : rat` [x < y]\n`<` compares only two numbers of one \
             kind or two values of one other kind [x < y]\nrepair: `(x[0], rat(x[1])) < y` [x < y]"
        ]
    );
}

#[test]
fn a_value_that_is_not_a_tuple_is_offered_each_component_that_compares() {
    let text = "f(positional x: int, positional y: (int, bool)) = x < y;\n";
    assert_eq!(
        full(text),
        [
            "Cannot compare unequal types: `x : int < y : (int, bool)`. Try `x < y[0]` instead. [x \
             < y]\n`x` is int here [x]\n`x` is declared `int` [positional x: int]\n`y` is (int, \
             bool) here [y]\n`y` is declared `(int, bool)` [positional y: (int, bool)]\n`<` \
             compares a tuple only with a tuple, not `int` [x < y]\nrepair: `x < y[0]` [x < y]"
        ]
    );
    // An operand that is not a name is named by its side.
    let text = "f(positional x: (int, int)) = x < (1, true);\n";
    assert_eq!(
        full(text),
        [
            "Cannot compare unequal types: `x[1] : int` with component `[1]` of the right operand \
             (`true`) in `x < (1, true)`. [x < (1, true)]\n`x` is (int, int) here [x]\n`x` is \
             declared `(int, int)` [positional x: (int, int)]\nthis expression gives (1, true) \
             [(1, true)]\nthis literal, 1, is 1 [1]\nthis expression is true [true]\n`<` compares \
             two tuples component by component, as far as the shorter goes [x < (1, true)]\n`<` \
             compares components `[1]`: `x[1] : int` with component `[1]` of the right operand \
             (`true`) [x < (1, true)]\n`<` compares only two numbers of one kind or two values of \
             one other kind [x < (1, true)]\nrepair: change the type of `x` or the right operand \
             so that `x[1]` and component `[1]` of the right operand compare [x < (1, true)]"
        ]
    );
}

#[test]
fn a_component_that_does_not_compare_is_reported() {
    for (text, want) in [
        // Two carriers of numbers met at the first position, from two shapes of one side.
        (
            "f(positional x: (int, bool) | (f64, bool)) = x < x;\n",
            vec![
                "Cannot compare the values of one type with each other: `x[0] : int | f64 < x[0] : \
                 int | f64` in `x < x`. [x < x]",
            ],
        ),
        // The components of each position of every shape of a side are met together, as two
        // operands that are unions are.
        (
            "f(positional x: (int, bool) | (f64, bool), positional y: (bool, bool) | (rat, bool)) \
             = x < y;\n",
            vec![
                "Cannot compare unequal types: `x[0] : int | f64 < y[0] : rat | bool` in `x < y`. \
                 [x < y]",
            ],
        ),
        // Every piece that does not compare is named, though it comes from another shape.
        (
            "f(positional x: (int, (int, int)), positional y: (int, #a) | (int, int, bool)) \
             = x < y;\n",
            vec![
                "Cannot compare unequal types: `x[1] : (int, int) < y[1] : int | #a` in `x < y`. \
                 [x < y]",
            ],
        ),
        // A tuple with a number, at the second position of one shape only.
        (
            "f(positional x: (int, (int, int)) | (int, int)) = x < x;\n",
            vec![
                "Cannot compare the values of one type with each other: `x[1] : int | (int, int) < \
                 x[1] : int | (int, int)` in `x < x`. [x < x]",
            ],
        ),
        // A shape shorter than the other stops the comparison where it ends: the third
        // components are never compared.
        (
            "f(positional x: (int, int), positional y: (int, int, bool)) = x < y;\n",
            vec![],
        ),
    ] {
        assert_eq!(type_errors(text), want, "{text}");
    }
}

#[test]
fn each_offered_repair_is_accepted() {
    for text in [
        "f(positional x: (int, int), positional y: (int, rat)) = (x[0], rat(x[1])) < y;\n",
        "f(positional x: (int, (bool, int)), positional y: (int, (bool, rat))) \
         = (x[0], (x[1][0], rat(x[1][1]))) < y;\n",
        "f(positional x: (int, int), positional y: (int, rat, bool)) = (x[0], rat(x[1])) < y;\n",
        "f(positional x: int, positional y: (int, bool)) = x < y[0];\n",
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
    }
}

#[test]
fn rows_held_twice_at_each_level_compare_in_linear_time() {
    let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
        .into_iter()
        .map(|n| (n, Resolved::new(&doubled(n, "<"))))
        .collect();
    scaling::check_order(
        "t < t over n levels each holding the last twice",
        500,
        1,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "at {n}: {:?}", info.errors);
        },
    );
}

#[test]
fn many_tuple_shapes_compare_in_linear_time() {
    let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
        .into_iter()
        .map(|n| (n, Resolved::new(&tagged(n))))
        .collect();
    scaling::check_order("x < x over n tuple shapes (#ai, int)", 500, 1, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "at {n}: {:?}", info.errors);
    });
}

#[test]
fn tuples_of_every_length_compare_in_time_linear_in_their_components() {
    // The type holds n(n + 1)/2 components, so work linear in it is of order n².
    let units: BTreeMap<usize, Resolved> = [20, scaling::FACTOR * 20]
        .into_iter()
        .map(|n| (n, Resolved::new(&lengths(n))))
        .collect();
    scaling::check_order("x < x over tuples of each length from 1 to n", 20, 2, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "at {n}: {:?}", info.errors);
    });
}

#[test]
fn a_mismatch_at_depth_n_is_reported_in_linear_time() {
    // The message names the place, `n` indices, once, and one step for each level, each of
    // its own size; the two declared types, of size `n`, are printed once each.
    let units: BTreeMap<usize, Resolved> = [200, scaling::FACTOR * 200]
        .into_iter()
        .map(|n| (n, Resolved::new(&nested(n, "bool"))))
        .collect();
    scaling::check_order("x < y failing at depth n", 200, 1, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), 1, "at {n}");
        assert_eq!(info.errors[0].notes.len(), n + 8, "at {n}");
    });
}

#[test]
fn a_repair_at_depth_n_is_the_whole_comparison_rewritten() {
    // The headline's repair writes `x` again with its innermost `int` cast to `rat` and every
    // other component read from `x`, and the checker accepts it.
    let text = nested(2, "rat");
    let errors = type_errors(&text);
    let fixed = "(((rat(x[0][0][0]),), x[0][1]), x[1]) < y";
    assert_eq!(
        errors,
        [format!(
            "Cannot compare unequal types: `x[0][0][0] : int < y[0][0][0] : rat` in `x < y`. \
             Try `{fixed}` instead. [x < y]"
        )]
    );
    let accepted = text.replace("= x < y;", &format!("= {fixed};"));
    assert_eq!(type_errors(&accepted), Vec::<String>::new(), "{accepted}");
}

#[test]
fn a_repair_at_depth_n_is_written_in_time_linear_in_its_length() {
    // Complexity tradeoff: the repair is the whole comparison rewritten, and the component it
    // writes at level `j` is read from `x` by `j` indices, so the repair holds n(n + 1)/2
    // indices: work linear in it is of order n². Naming the place alone, `rat(x[0]…[0])` in
    // place of `x[0]…[0]`, was O(n), but it is not an expression the program can hold
    // (DESIGN.md sec:diagnostics). COMPLEXITY.md row F140.
    let units: BTreeMap<usize, Resolved> = [100, scaling::FACTOR * 100]
        .into_iter()
        .map(|n| (n, Resolved::new(&nested(n, "rat"))))
        .collect();
    scaling::check_order("x < y with a repair at depth n", 100, 2, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), 1, "at {n}");
        assert!(info.errors[0].message.contains("Try `("), "at {n}");
    });
}
