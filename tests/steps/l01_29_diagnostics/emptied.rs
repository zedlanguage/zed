//! A type written with no value is printed `Never`, and the rejection says why: for each part
//! of the written type that has no value, a step at that part names the part with none that
//! empties it, from the innermost part out. A rejection whose types all have values gets no
//! such step.

use zed_tests::scaling;

use super::{rejected, steps};

/// The steps of `out` that explain why a written type has no value.
fn why_none(out: &str) -> Vec<&str> {
    steps(out)
        .into_iter()
        .filter(|s| s.contains("has no value"))
        .collect()
}

#[test]
fn a_parameter_of_an_empty_tuple_type_says_why_it_is_never() {
    let out = rejected("f(positional x: (Never, int)) = x;\nr = f((1, 2));\n");
    assert_eq!(
        why_none(&out),
        [
            "this tuple type has no value, since its component 0, `Never`, has none, so it is \
`Never`"
        ],
        "{out}"
    );
    // The step is placed at the tuple as written, after the declaration it explains: the
    // declaration's line is quoted once, with the step's underline under the tuple.
    assert!(
        out.contains(
            "      1 | f(positional x: (Never, int)) = x;
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [5]
        |                 ^^^^^^^^^^^^ [6]
  [6] 1:17: this tuple type has no value, since its component 0, `Never`, has \
none, so it is `Never`"
        ),
        "{out}"
    );
}

#[test]
fn a_nested_empty_tuple_is_explained_from_the_inside_out() {
    let out = rejected("f(positional x: ((Never, int), bool)) = x;\nr = f(((1, 2), true));\n");
    assert_eq!(
        why_none(&out),
        [
            "this tuple type has no value, since its component 0, `Never`, has none, so it is \
`Never`",
            "this tuple type has no value, since its component 0, the tuple type of the step \
before, has none, so it is `Never`",
        ],
        "{out}"
    );
    // The inner tuple first, at column 18; then the outer one, at column 17.
    let at: Vec<&str> = out
        .lines()
        .filter(|l| l.contains("has no value"))
        .map(|l| {
            l.trim_start()
                .split_once("] ")
                .unwrap()
                .1
                .split_once(':')
                .unwrap()
                .1
        })
        .map(|l| l.split_once(':').unwrap().0)
        .collect();
    assert_eq!(at, ["18", "17"], "{out}");
}

#[test]
fn an_empty_component_in_second_place_is_named_by_its_position() {
    let out = rejected("f(positional x: (int, (bool, Never))) = x;\nr = f(1);\n");
    assert_eq!(
        why_none(&out),
        [
            "this tuple type has no value, since its component 1, `Never`, has none, so it is \
`Never`",
            "this tuple type has no value, since its component 1, the tuple type of the step \
before, has none, so it is `Never`",
        ],
        "{out}"
    );
}

#[test]
fn a_union_of_empty_tuples_explains_each_member_then_the_union() {
    let out = rejected("f(positional x: (int, (bool, Never)) | (Never, int)) = x;\nr = f(1);\n");
    assert_eq!(
        why_none(&out),
        [
            "this tuple type has no value, since its component 1, `Never`, has none, so it is \
`Never`",
            "this tuple type has no value, since its component 1, the tuple type of the step \
before, has none, so it is `Never`",
            "this tuple type has no value, since its component 0, `Never`, has none, so it is \
`Never`",
            "this union has no value, since none of its members has one, so it is `Never`",
        ],
        "{out}"
    );
}

#[test]
fn an_intersection_of_disjoint_types_says_no_value_is_in_all_of_them() {
    let out = rejected("f(positional x: int & bool) = x;\nr = f(1);\n");
    assert_eq!(
        why_none(&out),
        [
            "this intersection has no value, since no value is in all of `int` and `bool`, so it \
is `Never`"
        ],
        "{out}"
    );
}

#[test]
fn an_intersection_with_an_empty_operand_names_that_operand() {
    let out = rejected("f(positional x: ((Never, int) & int)) = x;\nr = f(1);\n");
    assert_eq!(
        why_none(&out),
        [
            "this tuple type has no value, since its component 0, `Never`, has none, so it is \
`Never`",
            "this intersection has no value, since its operand, the tuple type of the step \
before, has none, so it is `Never`",
        ],
        "{out}"
    );
}

#[test]
fn a_difference_that_removes_everything_says_so() {
    let out = rejected("f(positional x: (int \\ int, bool)) = x;\nr = f(1);\n");
    assert_eq!(
        why_none(&out),
        [
            "this difference has no value, since each value of `int` is also in `int`, so it is \
`Never`",
            "this tuple type has no value, since its component 0, the difference of the step \
before, has none, so it is `Never`",
        ],
        "{out}"
    );
}

#[test]
fn an_empty_tuple_inside_a_function_type_is_explained() {
    let out = rejected(
        "f(positional g: (int) -> (Never, int), positional y: int) = g(y);\nr = f(1, 2);\n",
    );
    assert_eq!(
        why_none(&out),
        [
            "this tuple type has no value, since its component 0, `Never`, has none, so it is \
`Never`"
        ],
        "{out}"
    );
}

#[test]
fn a_value_typed_by_an_empty_declaration_is_explained_where_it_was_declared() {
    // The rejection is at `+`; the derivation reaches `x` through `y`, then its declaration.
    let out = rejected("f(positional x: (int, (Never, bool))) = { y = x; y + true };\n");
    let all = steps(&out);
    let declared = all
        .iter()
        .position(|s| *s == "`x` is declared `Never`")
        .unwrap_or_else(|| panic!("{out}"));
    assert_eq!(
        all[declared + 1..declared + 3],
        [
            "this tuple type has no value, since its component 0, `Never`, has none, so it is \
`Never`",
            "this tuple type has no value, since its component 1, the tuple type of the step \
before, has none, so it is `Never`",
        ],
        "{out}"
    );
}

#[test]
fn a_rejection_whose_types_all_have_values_gets_no_such_step() {
    let out = rejected("f(positional x: (int, bool)) = x;\nr = f(true);\n");
    assert_eq!(
        steps(&out),
        [
            "this expression is true",
            "`f` takes ((int, bool)) -> (int, bool)",
            "`f` is declared here, `((int, bool)) -> (int, bool)`",
        ],
        "{out}"
    );
}

/// A parameter whose type is a union of `n` tuples with no value, each on its own line.
fn wide(n: usize) -> String {
    let mut src = String::from("f(positional x:\n");
    for i in 0..n {
        let bar = if i == 0 { " " } else { "|" };
        src += &format!("  {bar} (int, Never)\n");
    }
    src + ") = x;\nr = f(1);\n"
}

#[test]
fn explaining_a_union_of_n_empty_tuples_scales() {
    let inputs = scaling::inputs(500, wide);
    scaling::check("explaining a union of n empty tuples", 500, |n| {
        let out = rejected(&inputs[&n]);
        // One step for each tuple, then one for the union.
        assert_eq!(why_none(&out).len(), n + 1);
    });
}

/// A parameter whose type nests `n` tuples, each level on its own line, the innermost with
/// the component `Never`.
fn deep(n: usize) -> String {
    let mut src = String::from("f(positional x:\n");
    for _ in 0..n {
        src += "  (\n";
    }
    src += "  Never, int\n";
    for _ in 0..n - 1 {
        src += "  ), bool\n";
    }
    src + "  )) = x;\nr = f(1);\n"
}

#[test]
fn explaining_n_nested_empty_tuples_scales() {
    let inputs = scaling::inputs(200, deep);
    scaling::check("explaining n nested empty tuples", 200, |n| {
        let out = rejected(&inputs[&n]);
        // One step for each level, each naming the step before but the innermost.
        let why = why_none(&out);
        assert_eq!(why.len(), n);
        assert!(why[0].contains("`Never`, has none"), "{}", why[0]);
        assert!(why[n - 1].contains("of the step before"), "{}", why[n - 1]);
    });
}
