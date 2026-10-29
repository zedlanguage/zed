//! Calls of declared functions: positional and named arguments, defaults, `...`, uniform
//! calls and bracket sections.

use super::{term, value};

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
        "box(positional w, d = h, h = w) = w * h * d;\ncube = box(2);\nslab = box(2, d: 1);\n";
    assert_eq!(value(src, "cube"), "8");
    assert_eq!(value(src, "slab"), "4");
    assert_eq!(term(src, "cube"), "{ w = 2; h = w; d = h; box(w, d, h) }");
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
               h = greet(\"Al\", lead: \"yo\", ...);\nq = h(\"?\");\n";
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
    assert_eq!(term(src, "second"), "tupleGet(pair, 1)");
    assert_eq!(value(src, "second"), "8");
}
