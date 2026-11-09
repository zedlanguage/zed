//! The layout the formatter writes, on small programs written carelessly.

use super::fmt;

#[track_caller]
fn check(text: &str, want: &str) {
    assert_eq!(fmt(text), want);
}

#[test]
fn spacing_and_parentheses_are_normalized() {
    check(
        "area(w,h)=w*h;\nmean(a,b)=((a+b))/2;\nf(x)=-(-x)^2;\n",
        "area(w, h) = w * h;\nmean(a, b) = (a + b) / 2;\nf(x) = -(-x)^2;\n",
    );
    check(
        "g(x)=(x-1)-(x-2);\nh(x)=x-(1-2);\nok(x)=(x<1)==(x<2);\n",
        "g(x) = x - 1 - (x - 2);\nh(x) = x - (1 - 2);\nok(x) = x < 1 == x < 2;\n",
    );
}

#[test]
fn a_block_puts_its_export_last() {
    check(
        "total(xs){return n+m;n=xs.length;m=1;}\n",
        "total(xs) {\n  n = xs.length;\n  m = 1;\n  n + m\n}\n",
    );
    check(
        "pair(x){a=x;return a,a;}\n",
        "pair(x) {\n  a = x;\n  return a, a;\n}\n",
    );
}

#[test]
fn a_block_of_one_export_stays_on_one_line() {
    check(
        "sign(x)=if x<0 {-1} else if x==0 {0} else {1};\n",
        "sign(x) = if x < 0 { -1 } else if x == 0 { 0 } else { 1 };\n",
    );
    // As an operand a block opens with a statement at L1, so its export is written `return`.
    check("f(x)={return x;}+1;\n", "f(x) = { return x; } + 1;\n");
}

#[test]
fn main_pushes_to_its_ports() {
    check(
        "main()->(stdout:Lines){name=\"Zed\";stdout<-\"hello, {name}\";}\n",
        "main() -> (stdout: Lines) {\n  name = \"Zed\";\n  stdout <- \"hello, {name}\";\n}\n",
    );
}

#[test]
fn test_tables_join_into_one_line_under_the_function() {
    check(
        "inc(x)=x+1 test{1->2} test{2->3}\n",
        "inc(x) = x + 1\n  test { 1 -> 2, 2 -> 3 }\n",
    );
    check(
        "twice(x){y=x+x;y} test{1->2}\n",
        "twice(x) {\n  y = x + x;\n  y\n}\n  test { 1 -> 2 }\n",
    );
}

#[test]
fn lambdas_calls_and_else_are_written_short() {
    check(
        "f(xs)=map(xs,(x)->x+1);\ng(a)=h(a:a,b:2,...);\nd(p)=p else #none->0;\n",
        "f(xs) = map(xs, x -> x + 1);\ng(a) = h(a:, b: 2, ...);\nd(p) = p else #none -> 0;\n",
    );
    check(
        "k(t)=t is not (int|#none);\nm()=(1).abs;\n",
        "k(t) = t is not int | #none;\nm() = (1).abs;\n",
    );
}

#[test]
fn comments_stay_with_their_statements() {
    check(
        "// Totals.\ntotal(xs) {\n  return n; // the count\n\n  // xs is a list\n  n = xs.length;\n  // done\n}\n",
        "// Totals.\ntotal(xs) {\n  // xs is a list\n  n = xs.length;\n  n // the count\n  // done\n}\n",
    );
    check(
        "f(x) = g(x, /* why */ 1); // after\n",
        "f(x) = g(x, 1); /* why */ // after\n",
    );
}

#[test]
fn blank_lines_collapse_to_one() {
    check(
        "a() = 1;\n\n\n\nb() = 2;\nc() = 3;\n",
        "a() = 1;\n\nb() = 2;\nc() = 3;\n",
    );
}

#[test]
fn parentheses_keep_a_block_from_opening_a_branch() {
    // An `if` condition's `{` would open the branch, and a default or a lambda body that
    // starts with `{` would be read as a block.
    check(
        "f(a,p)=if (p else {return a;}) {1} else {2};\n",
        "f(a, p) = if (p else { a }) { 1 } else { 2 };\n",
    );
    check(
        "g(p)=p else ({return 1;}+1);\nh(q)=x->({return q;}).k;\n",
        "g(p) = p else ({ return 1; } + 1);\nh(q) = x -> ({ return q; }.k);\n",
    );
}

#[test]
fn a_source_that_does_not_parse_is_reported_at_its_line_and_column() {
    let e = zedc::format::format_source(b"f(x) = 1;\ng(x) = ;\n").unwrap_err();
    assert!(e.starts_with("2:8: expected "), "{e}");
}

#[test]
fn a_source_that_does_not_load_is_reported_at_its_line_and_column() {
    // Saved as ISO-8859-1: `é` is the one byte E9.
    let latin1 = b"price = 1;\nname = \"caf\xe9\";\n";
    let e = zedc::format::format_source(latin1).unwrap_err();
    assert_eq!(
        e,
        "2:12: a Zed file is UTF-8 text, and the bytes here, E9 in hexadecimal, are not a UTF-8 \
         character, so the file cannot be read. Save the file as UTF-8 in your editor, or replace \
         these bytes with the character they were meant to be."
    );
    // Running the file reports the same position.
    assert_eq!(zedc::run::load(latin1).err().as_deref(), Some(e.as_str()));
    let bom = "\u{feff}total = 1;\n".as_bytes();
    let e = zedc::format::format_source(bom).unwrap_err();
    assert_eq!(
        e,
        "1:1: the file starts with a byte order mark (the bytes EF BB BF), and a Zed file may \
         not, since the same program would then be stored in two ways. Save the file as UTF-8 \
         without a byte order mark (in many editors this is \"UTF-8\" rather than \"UTF-8 with \
         BOM\")."
    );
}

#[test]
fn a_comparison_of_a_comparison_keeps_its_parentheses() {
    // `a == b == c` is a chain, which tests both pairs, so the parentheses change the meaning:
    // `(a == b) == c` compares a truth value with `c`.
    check("f(a,b,c)=(a==b)==c;\n", "f(a, b, c) = (a == b) == c;\n");
    check("f(a,b,c)=a==(b==c);\n", "f(a, b, c) = a == (b == c);\n");
    check("f(a,b,c)=(a<b)<c;\n", "f(a, b, c) = (a < b) < c;\n");
}

#[test]
fn a_match_puts_each_arm_on_its_own_line() {
    // Step L2.2: a comment stays with its arm, and a guard is written after the pattern.
    check(
        "depth(t)=match t{#leaf->0,// no children\n// a node\n#node(l:,r:) where l==r->1+depth(l),_->-1\n// none else\n};\n",
        "depth(t) = match t {\n  #leaf -> 0, // no children\n  // a node\n  #node(l:, r:) where l == r -> 1 + depth(l),\n  _ -> -1,\n  // none else\n};\n",
    );
}

#[test]
fn imports_and_annotations_stay_on_one_line() {
    // Step L2.2.
    check(
        "import geometry.shapes as gs;\nimport io.{read,write,};\n@memoized\nfib(n)=n;\n",
        "import geometry.shapes as gs;\nimport io.{read, write};\n@memoized fib(n) = n;\n",
    );
}

#[test]
fn a_one_tuple_keeps_its_comma_and_two_bounds_their_dots() {
    check("f(x)=x is (int ,);\n", "f(x) = x is (int,);\n");
    check(
        "f(m)=m is (#a..#a|#b->(#c|#d)..#c|#d->int);\n",
        "f(m) = m is (#a .. #a | #b -> #c | #d .. #c | #d -> int);\n",
    );
}

#[test]
fn a_sort_key_is_written_with_one_space_after_its_word() {
    // The key of `asc` and `desc` is any expression, a lambda too, and needs no parentheses.
    check(
        "byScore(rows)=rows.sort(desc  (score));\nbyKey(m)=m.keys.sort(asc v->m[v]);\n",
        "byScore(rows) = rows.sort(desc score);\nbyKey(m) = m.keys.sort(asc v -> m[v]);\n",
    );
    check(
        "two(xs)=sort(xs,asc(a.b),desc -c);\n",
        "two(xs) = sort(xs, asc a.b, desc -c);\n",
    );
}

#[test]
fn a_blank_line_among_moved_comments_is_kept() {
    // The comments inside a statement move to its end, one per line after the first, so when the
    // result is read again they are the next statement's leading comments, or the comments that
    // end the unit; the blank line after them stays, so formatting the result changes nothing.
    check(
        "a = f(1, // one\n  2, // two\n  3);\n\n// end\n",
        "a = f(1, 2, 3); // one\n// two\n\n// end\n",
    );
    check(
        "total = add(1, // the first\n  2, // the second\n  3);\n\n// The next one.\nnext = 4;\n",
        "total = add(1, 2, 3); // the first\n// the second\n\n// The next one.\nnext = 4;\n",
    );
    check(
        "// Section header.\n\n// What b is.\nb = 1;\n",
        "// Section header.\n\n// What b is.\nb = 1;\n",
    );
}

/// The type `text` parsed and printed back by `format_type`, as a message prints a type.
fn type_printed(text: &str) -> String {
    let tokens = zedc::lex::lex(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Type", zedc::parse::TOP).unwrap();
    let t = zedc::ast::ty(text, &tokens, &tree).unwrap();
    zedc::format::format_type(&t)
}

/// A message prints a type as the program writes it, not as the tree the parser builds.
#[test]
fn a_type_prints_as_it_is_written() {
    for text in [
        "int",
        "Lines",
        "String ->? String",
        "#a .. #b -> int",
        "#yes | #no",
        "(int, String)",
    ] {
        assert_eq!(type_printed(text), text);
    }
}

/// A function type is printed with the parentheses the grammar needs and no others (DESIGN.md
/// sec:grammar), whatever the program wrote: bare as a tuple component, a parameter, a payload
/// and a result; parenthesized as an operand of `|` and as a key. `(int)` is a grouped key, not
/// a parameter list, so `(int) -> int` parses to the same tree as `int -> int` and prints so. The
/// second check is the round trip: the printed text parses back to a tree that prints the same.
#[test]
fn a_function_type_prints_with_only_the_parentheses_it_needs() {
    for (text, shown) in [
        ("(((int) -> int), String)", "(int -> int, String)"),
        ("((int) -> int) | String", "(int -> int) | String"),
        ("(int) -> ((String) -> bool)", "int -> String -> bool"),
        (
            "(((int) -> Never), int) -> Never",
            "(int -> Never, int) -> Never",
        ),
        (
            "(((((int) -> int)) -> int)) -> int",
            "((int -> int) -> int) -> int",
        ),
        ("(int) -> (int | String)", "int -> int | String"),
        (
            "(int) -> (((int) -> int) | String)",
            "int -> (int -> int) | String",
        ),
        ("#a(((int) -> int))", "#a(int -> int)"),
        ("((int) -> int) ->? int", "(int -> int) ->? int"),
        ("((int, int)) ->? int", "((int, int)) ->? int"),
        ("((int,)) ->? int", "(int,) ->? int"),
        (
            "(int) -> ((T) -> T for T in int | f64)",
            "int -> (T -> T for T in int | f64)",
        ),
    ] {
        assert_eq!(type_printed(text), shown, "{text}");
        assert_eq!(type_printed(shown), shown, "{shown}");
    }
}

/// `#a0 | #a1 | …`, `n` atoms.
fn union_of(n: usize) -> String {
    (0..n)
        .map(|i| format!("#a{i}"))
        .collect::<Vec<_>>()
        .join(" | ")
}

#[test]
fn printing_a_type_scales_with_its_size() {
    let types: std::collections::HashMap<usize, zedc::ast::Type> = [200, 1600]
        .into_iter()
        .map(|n| {
            let text = union_of(n);
            let tokens = zedc::lex::lex(&text).unwrap();
            let tree = zedc::parse::parse(&text, &tokens, "Type", zedc::parse::TOP).unwrap();
            (n, zedc::ast::ty(&text, &tokens, &tree).unwrap())
        })
        .collect();
    zed_tests::scaling::check("printing a union type, by atoms", 200, |n| {
        zedc::format::format_type(&types[&n]);
    });
}

/// `^` is written with no spaces, as in mathematics; spaces in the source change nothing.
/// `fmt` checks that each result builds to the same statements and formats to itself.
#[test]
fn a_power_is_written_without_spaces() {
    let cases = [
        ("big = 2 ^ 48;", "big = 2^48;"),
        ("sq(x) = x ^ 2;", "sq(x) = x^2;"),
        ("f(x) = (-2) ^ 2 + -x ^ 2;", "f(x) = (-2)^2 + -x^2;"),
        ("half = 2 ^ -1;", "half = 2^-1;"),
        ("f(a, b, c) = a ^ b ^ c;", "f(a, b, c) = a^b^c;"),
        ("f(a, b, c) = (a ^ b) ^ c;", "f(a, b, c) = (a^b)^c;"),
        ("f(x) = (x + 1r) ^ 2;", "f(x) = (x + 1r)^2;"),
        ("f(x, k) = x * 2 ^ k;", "f(x, k) = x * 2^k;"),
        ("ok(n) = n in 0..=2 ^ 48;", "ok(n) = n in 0..=2^48;"),
        ("f(x) = x.len ^ 2;", "f(x) = x.len^2;"),
    ];
    for (spaced, want) in cases {
        let (spaced, want) = (format!("{spaced}\n"), format!("{want}\n"));
        check(&spaced, &want);
        check(&want, &want);
    }
}
