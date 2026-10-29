//! Blocks, operators, strings, `if`, `else`, `?.`, lambdas, ports and `test` tables.

use zed_kernel::{Evaluator, World};

use super::{elab, term, value, with_prelude};

#[test]
fn statements_run_in_dependency_order_not_written_order() {
    let src = "net = gross - fee;\nfee = gross div 20;\ngross = 1200;\n";
    assert_eq!(value(src, "net"), "1140");
    let u = elab(src).unwrap();
    let order: Vec<&str> = u.defs.iter().map(|d| d.name.as_str()).collect();
    assert_eq!(order, ["gross", "fee", "net"]);
}

#[test]
fn a_block_is_its_lets_over_its_export() {
    let src = "area = { w = 3; h = w + 1; w * h };\n";
    assert_eq!(value(src, "area"), "12");
    assert_eq!(term(src, "area"), "{ w = 3; h = (w + 1); (w * h) }");
}

#[test]
fn return_of_several_values_is_a_tuple_and_destructuring_reads_it() {
    let src = "bounds(positional xs) {\n  return xs[0], xs[2];\n}\n\
               lo, hi = bounds((3, 5, 9));\nwidth = hi - lo;\n";
    assert_eq!(value(src, "width"), "6");
    // `_` binds nothing; the tuple is still read by position.
    let src = "_, mid, _ = (1, 2, 3);\ntwice = mid * 2;\n";
    assert_eq!(value(src, "twice"), "4");
}

#[test]
fn a_block_without_an_export_is_the_empty_tuple() {
    let src = "main() -> (stdout: Lines) {\n  stdout <- \"ready\";\n}\nrun = main();\n";
    let u = elab(src).unwrap();
    let mut ev = Evaluator::new(World::new().output("stdout"));
    let out = ev.run(&with_prelude(u.get("run").unwrap())).unwrap();
    assert_eq!(out.to_string(), "()");
    assert_eq!(ev.world.log("stdout")[0].to_string(), "\"ready\"");
    assert_eq!(
        term(src, "main"),
        "() -> { $1 = port.push(stdout, \"ready\"); () }"
    );
}

#[test]
fn arithmetic_comparison_and_power() {
    let src = "a = 2 ** 3 ** 2;\nb = -7 div 2;\nc = -7 mod 2;\nd = 1.5 * 4.0;\n\
               e = 3 <= 3;\nf = !(2 > 3);\ng = 10.0 / 4.0;\n";
    assert_eq!(value(src, "a"), "512", "`**` is right-associative");
    assert_eq!(value(src, "b"), "-4", "Euclidean division");
    assert_eq!(value(src, "c"), "1", "Euclidean modulus");
    assert_eq!(value(src, "d"), "6.0");
    assert_eq!(value(src, "e"), "true");
    assert_eq!(value(src, "f"), "true");
    assert_eq!(value(src, "g"), "2.5");
    assert_eq!(term(src, "a"), "(2 ** (3 ** 2))");
}

#[test]
fn and_or_are_if_forms_so_they_short_circuit() {
    // The right operand would be the atom `#divByZero` if it were evaluated.
    let src = "ok = true || 1 div 0 == 0;\nno = false && 1 div 0 == 0;\n";
    assert_eq!(value(src, "ok"), "true");
    assert_eq!(value(src, "no"), "false");
    assert_eq!(
        term(src, "ok"),
        "if true { true } else { ((1 div 0) == 0) }"
    );
}

#[test]
fn concatenation_and_interpolation() {
    let src = "who = \"Ada\";\nhello = \"hello, \" ++ who;\nline = \"${hello}! (${who})\";\n";
    assert_eq!(value(src, "hello"), "\"hello, Ada\"");
    assert_eq!(value(src, "line"), "\"hello, Ada! (Ada)\"");
    assert_eq!(
        term(src, "line"),
        "(((String(hello) ++ \"! (\") ++ String(who)) ++ \")\")"
    );
    // A hole of any type goes through `String`, which the interpreter binds.
    let src = "n = 3;\nmsg = \"n = ${n + 1}\";\n";
    assert_eq!(term(src, "msg"), "(\"n = \" ++ String((n + 1)))");
}

#[test]
fn if_chains() {
    let src = "grade(positional score) = if score >= 90 { #a } else if score >= 80 { #b } \
               else { #c };\nx = grade(85);\ny = grade(95);\nz = grade(10);\n";
    assert_eq!(value(src, "x"), "#b");
    assert_eq!(value(src, "y"), "#a");
    assert_eq!(value(src, "z"), "#c");
}

#[test]
fn else_replaces_an_atom_and_passes_any_other_value() {
    let src = "per(positional total, positional n) = total div n;\n\
               a = per(90, 3) else 0;\nb = per(90, 0) else 0;\n\
               c = per(90, 0) else #divByZero -> -1;\nd = per(90, 0) else #overflow -> -1;\n";
    assert_eq!(value(src, "a"), "30");
    assert_eq!(value(src, "b"), "0");
    assert_eq!(value(src, "c"), "-1");
    assert_eq!(
        value(src, "d"),
        "#divByZero",
        "a pattern that does not match passes it"
    );
    assert_eq!(term(src, "b"), "match per(90, 0) { #_ -> 0, $2 -> $2 }");
}

#[test]
fn safe_member_passes_an_atom_through() {
    let src = "half(positional x) = x div 2;\nm = #missing;\nn = 8;\n\
               a = m?.half;\nb = n?.half;\n";
    assert_eq!(value(src, "a"), "#missing");
    assert_eq!(value(src, "b"), "4");
    assert_eq!(
        term(src, "b"),
        "{ $2 = n; match $2 { #_ -> $2, _ -> half($2) } }"
    );
}

#[test]
fn lambdas_are_called_by_position_and_capture_their_scope() {
    let src = "rate = 3;\nscale = x -> x * rate;\nr = scale(14);\n\
               both = (a, b) -> { s = a + b; s * s };\nq = both(1, 2);\n";
    assert_eq!(value(src, "r"), "42");
    assert_eq!(value(src, "q"), "9");
}

#[test]
fn a_name_bound_twice_gets_one_kernel_name_per_binder() {
    let src = "x = 1;\nnext(positional x) = x + 1;\ny = next(x);\n";
    assert_eq!(term(src, "next"), "x@2 -> (x@2 + 1)");
    assert_eq!(term(src, "y"), "next(x@1)");
    assert_eq!(value(src, "y"), "2");
    // A binder named like a prelude word is renamed too, so the word stays free.
    let src = "len = 4;\nw = len * 2;\n";
    assert_eq!(term(src, "w"), "(len@1 * 2)");
    assert_eq!(value(src, "w"), "8");
}

#[test]
fn test_tables_check_each_case() {
    let src = "square(positional x) = x * x test { 3 -> 9, 4 -> 15 }\n\
               area(w, h) = w * h test { (2, 3) -> 6 }\n";
    let u = elab(src).unwrap();
    let got: Vec<(String, String)> = u
        .tests
        .iter()
        .map(|t| {
            let v = zed_kernel::eval(&with_prelude(u.close(t.check.clone()))).unwrap();
            (t.function.clone(), v.to_string())
        })
        .collect();
    let want = [("square", "true"), ("square", "false"), ("area", "true")];
    let want: Vec<(String, String)> = want
        .iter()
        .map(|(a, b)| (a.to_string(), b.to_string()))
        .collect();
    assert_eq!(got, want);
    // The tuple key gives the arguments in declaration order, whatever their kinds.
    assert_eq!(u.tests[2].check.to_string(), "(area(2, 3) == 6)");
}
