//! Calls of declared functions: positional and named arguments, defaults, `...`, uniform
//! calls and bracket sections.

use super::{errors, term, value};

const TAX: &str = "tax(positional amount, rate = 8) = amount * rate div 100;\n";

#[test]
fn a_default_is_filled_where_the_call_omits_it() {
    let src = format!("{TAX}a = tax(250);\nb = tax(250, rate: 10);\n");
    assert_eq!(value(&src, "a"), "20");
    assert_eq!(value(&src, "b"), "25");
    assert_eq!(
        term(&src, "a"),
        "{ amount = 250; rate = 8; tax(amount, rate) }"
    );
    assert_eq!(term(&src, "b"), "tax(250, 10)");
}

#[test]
fn defaults_read_earlier_parameters_in_dependency_order() {
    let src =
        "box(positional w, h = w, d = h) = w * h * d;\ncube = box(2);\nslab = box(2, d: 1);\n";
    assert_eq!(value(src, "cube"), "8");
    assert_eq!(value(src, "slab"), "4");
    assert_eq!(term(src, "cube"), "{ w = 2; h = w; d = h; box(w, h, d) }");
}

#[test]
fn named_arguments_go_in_parameter_order_whatever_the_written_order() {
    let src = "span(lo, hi) = hi - lo;\nn = span(hi: 10, lo: 4);\n";
    assert_eq!(value(src, "n"), "6");
    assert_eq!(term(src, "n"), "span(4, 10)");
}

#[test]
fn curry_is_a_lambda_over_the_named_parameters_left_out() {
    let src = "greet(positional name, punct = \"!\", lead = \"hi\") = \"${lead}, ${name}${punct}\";\n\
               h = greet(\"Al\", lead: \"yo\", ...);\nq = h(punct: \"?\");\n";
    assert_eq!(
        term(src, "h"),
        "punct -> { name = \"Al\"; lead = \"yo\"; greet(name, punct, lead) }"
    );
    assert_eq!(value(src, "q"), "\"yo, Al?\"");
}

#[test]
fn a_receiver_fills_the_first_parameter_of_either_kind() {
    let src = "clamp(positional v, positional lo, positional hi) = \
               if v < lo { lo } else if v > hi { hi } else { v };\n\
               double(x) = x * 2;\n\
               a = 12.clamp(0, 10);\nb = 5.double;\nc = 3.double.clamp(0, 5);\n";
    assert_eq!(value(src, "a"), "10");
    assert_eq!(value(src, "b"), "10");
    assert_eq!(value(src, "c"), "5");
    assert_eq!(term(src, "b"), "double(5)");
    assert_eq!(term(src, "c"), "clamp(double(3), 0, 5)");
}

#[test]
fn a_member_naming_a_prelude_word_is_its_call() {
    let src = "name = \" Ada \";\nclean = name.trim;\nn = name.trim.len;\n";
    assert_eq!(term(src, "clean"), "trim(name)");
    assert_eq!(term(src, "n"), "len(trim(name))");
}

#[test]
fn brackets_index_one_level_and_fill_no_default() {
    let src = "add(positional a, positional b) = a + b;\ninc = add[1];\nr = inc(41);\n\
               neg(positional x) = 0 - x;\nm = neg[5];\npair = (7, 8);\nsecond = pair[1];\n";
    assert_eq!(term(src, "inc"), "$1 -> add(1, $1)");
    assert_eq!(value(src, "r"), "42");
    assert_eq!(value(src, "m"), "-5");
    assert_eq!(term(src, "second"), "pair[1]");
    assert_eq!(value(src, "second"), "8");
}

/// Row FAIL-curried-index: `f(x, y)` is `f[x][y]`, one parameter per bracket, so a bracket on
/// the section of a declared function applies the section, or makes a section of it while it
/// takes more than one parameter. A function value's brackets are the same.
#[test]
fn curried_indexing_applies_one_parameter_per_level() {
    let src = "add(positional x: int, positional y: int) = x + y;\n\
               t = add[1][2];\nb = add[1];\nu = b[2];\nv = add(1, 2);\n\
               add3(positional x: int, positional y: int, positional z: int) = x + 10 * y + 100 * z;\n\
               w = add3[1][2][3];\nc = add3[1][2];\nd = c[3];\ne = add3[1];\nf = e[2][3];\n\
               g = (p: int, q: int) -> p - q;\nh = g[5][2];\n";
    for (name, want) in [
        ("v", "3"),
        ("t", "3"),
        ("u", "3"),
        ("w", "321"),
        ("d", "321"),
        ("f", "321"),
        ("h", "3"),
    ] {
        assert_eq!(value(src, name), want, "{name} in\n{src}");
    }
}

/// A computed key is a bracket too, a function value's named parameters take brackets in
/// their declared order, a parameter whose function type is written gets a section from its
/// bracket, and a value that may be a function of one parameter or a tuple is applied, which
/// reads the tuple.
#[test]
fn curried_indexing_with_keys_named_parameters_and_written_types() {
    let cases = [
        (
            "add(positional x: int, positional y: int) = x + y;\nb = add[1];\nk = 2;\n\
             r = b[k];\nq = add[1][k];\n",
            &[("r", "3"), ("q", "3")][..],
        ),
        (
            "span(lo: int, hi: int) = hi - lo;\ns = span;\nr = s[4][10];\n",
            &[("r", "6")],
        ),
        (
            "ap(positional f: (int, int) -> int, positional k: int) = f[k];\n\
             r = ap((p: int, q: int) -> p - q, 5)[2];\n",
            &[("r", "3")],
        ),
        (
            "g(positional c: bool) = if c { ((p: int) -> p) } else { (1, 2) };\n\
             h = g(true)[1];\nj = g(false)[1];\n",
            &[("h", "1"), ("j", "2")],
        ),
    ];
    for (src, wants) in cases {
        for &(name, want) in wants {
            assert_eq!(value(src, name), want, "{name} in\n{src}");
        }
    }
}

/// A bracket with no one term is rejected: a value that may be a function of several
/// parameters (a section) or a tuple or a function of another number of parameters (an
/// application); a function of no parameters; and, at a call, a function of other than one
/// parameter reaching a bracket in a body checked with a type variable, which applies its
/// value to one argument (the kernel stopped there before this rejection).
#[test]
fn a_bracket_with_no_one_term_is_rejected() {
    let cases = [
        (
            "g(positional c: bool) = if c { ((p: int, q: int) -> p + q) } else { (1, 2) };\n\
             h = g(true)[1];\n",
            "it may be a function of 2 parameters or a tuple or a family",
        ),
        (
            "g(positional c: bool) = if c { ((p: int, q: int) -> p + q) } else { ((p: int) -> p) };\n\
             h = g(true)[1];\n",
            "it may be a function of 2 parameters or a function of 1 parameter",
        ),
        (
            "z() = 1;\ny = z;\nr = y[1];\n",
            "a function that takes no arguments, and this bracket gives it one",
        ),
        (
            "z() = 1;\ny = z;\nk = 1;\nr = y[k];\n",
            "a function that takes no arguments, and this bracket gives it one",
        ),
        (
            "ap(positional f, positional k) = f[k];\nr = ap((p: int, q: int) -> p + q, 1);\n",
            "a function of 2 parameters, and the bracket it reaches gives one argument",
        ),
        (
            "ap(positional f, positional k) = f[k];\nz() = 1;\nr = ap(z, 1);\n",
            "a function of 0 parameters, and the bracket it reaches gives one argument",
        ),
    ];
    for (src, want) in cases {
        let es = errors(src).join("\n");
        assert!(es.contains(want), "{want:?} missing from\n{src}\n{es}");
    }
}

/// Row FAIL-curried-index-untyped-param: a bracket on a parameter with no written type
/// applies a function as it picks a component of a tuple (DESIGN.md sec:values_morphisms,
/// application is indexing), so `ap(add)[2]` is `add(1, 2)`, as `add[1][2]` is.
#[test]
fn a_bracket_on_an_untyped_parameter_takes_a_function() {
    let src = "add(x: int, y: int) = x + y;\nap(positional f) = f[1];\nr = ap(add)[2];\n";
    assert_eq!(value(src, "r"), "3", "{src}");
}
