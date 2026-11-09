//! An ordering of two tuples compares them component by component as far as the shorter goes
//! (DESIGN.md sec:order), and each value of one operand must compare with each of the other.
//! Two tuples both reach position `i` exactly when each has more than `i` components, so the
//! checker reads, at each position, the union of the components of one side's tuples against
//! that of the other's, once, and a pair of component types met again through shared rows is
//! not read again. Before (CHK-components-pairs) it read every pair of tuples: `t < t` over
//! `n` levels that each hold the one below twice took 2.67 s at `n = 16` (`2^n`), `x < x` over
//! 800 tuple shapes 39.9 s (`n²`), and over tuples of each length from 1 to 100, 12.8 s (`n³`).

use std::collections::BTreeMap;

use zed_tests::scaling;

use super::{Resolved, type_errors};

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

#[test]
fn tuples_of_numbers_and_atoms_compare() {
    assert_eq!(type_errors(&doubled(3, "<")), Vec::<String>::new());
    assert_eq!(type_errors(&doubled(3, ">=")), Vec::<String>::new());
    assert_eq!(type_errors(&tagged(3)), Vec::<String>::new());
    // A proper prefix comes first, so tuples of different lengths compare.
    assert_eq!(type_errors(&lengths(3)), Vec::<String>::new());
}

#[test]
fn a_component_that_does_not_compare_is_reported() {
    let at = |what: &str, site: &str| format!("{what} [{site}]");
    let take = |args: &str, site: &str| {
        at(
            &format!(
                "`<` does not take {args}: these are the types of its arguments here, and `<` \
                 has no arrow that takes them all"
            ),
            site,
        )
    };
    for (text, want) in [
        // Two carriers of numbers met at the first position, from two shapes of one side.
        (
            "f(positional x: (int, bool) | (f64, bool)) = x < x;\n",
            vec![take("(int, f64)", "x < x")],
        ),
        // The components of each position of every shape of a side are met together, as two
        // operands that are unions are.
        (
            "f(positional x: (int, bool) | (f64, bool), positional y: (bool, bool) | (rat, bool)) \
             = x < y;\n",
            vec![take("(int | f64, bool | rat)", "x < y")],
        ),
        // Every piece that does not compare is named, though it comes from another shape.
        (
            "f(positional x: (int, (int, int)), positional y: (int, #a) | (int, int, bool)) \
             = x < y;\n",
            vec![
                at("`<` does not compare #a with a tuple", "x < y"),
                at("`<` does not compare int with a tuple", "x < y"),
            ],
        ),
        // A tuple with a number, at the second position of one shape only.
        (
            "f(positional x: (int, (int, int)) | (int, int)) = x < x;\n",
            vec![at("`<` does not compare int with a tuple", "x < x")],
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
