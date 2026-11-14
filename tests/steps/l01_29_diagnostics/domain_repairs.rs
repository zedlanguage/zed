//! The repairs of a value that may lie outside the ints its use takes, and of a value a
//! `Lines` port does not take, are the program's own code (MSG-domain-repairs-v): each names
//! the program's expression and never a value `v` the program does not have, and never a
//! refinement such as `is int[0..]`, which this zedc does not compile. Each repair the headline
//! offers is written into the program, and the program it gives is accepted.

use zedc::run::load;

/// `src` with a `main` added where it declares none, so that `load` checks its functions.
fn program(src: &str) -> String {
    match src.contains("main(m: MainArgs)") {
        true => src.to_string(),
        false => format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"a\";\n}}\n"),
    }
}

/// The rendered diagnostics of `src`, which must be rejected.
fn rejected(src: &str) -> String {
    super::rejected(&program(src))
}

/// Asserts that `src` checks.
fn checks(src: &str) {
    let src = program(src);
    load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}\n{e}"));
}

/// The repair the headline of `out` ends with, as in "Try `r` instead".
fn tried(out: &str) -> Option<&str> {
    let first = out.lines().next()?;
    let (_, rest) = first.split_once(" Try `")?;
    Some(&rest[..rest.find("` instead")?])
}

/// That no part of `out` names a value the program does not have, and that no repair, in a note
/// or the headline's Try, writes a refinement. The headline's annotation of an operand with its
/// type, as `k : int[0..=9]`, is no repair.
fn in_the_programs_words(out: &str) {
    assert!(!out.contains("`v`"), "{out}");
    assert!(!out.contains("${v}"), "{out}");
    let repairs = (out.lines().filter(|l| l.contains("repair:"))).chain(tried(out));
    for r in repairs {
        assert!(!r.contains(" is int["), "{r}\n{out}");
        assert!(!r.contains(": int[0.."), "{r}\n{out}");
    }
}

/// `src` with its one `call` replaced by the repair `r`, the branch left open filled with 0,
/// as a block where it binds a name (a block of one `if` alone would read as a set display).
fn repaired(src: &str, call: &str, r: &str) -> String {
    assert_eq!(src.matches(call).count(), 1, "{src}");
    let r = r.replace('…', "0");
    match r.contains(';') {
        true => src.replace(call, &format!("{{ {r} }}")),
        false => src.replace(call, &format!("({r})")),
    }
}

#[test]
fn a_tested_repair_holds_the_programs_code_and_is_accepted() {
    let cases = [
        // A name a test narrows is tested itself.
        (
            "f(positional n: int) = popCount(n);\n",
            "popCount(n)",
            "if n >= 0 { popCount(n) } else { … }",
        ),
        // An expression is bound to the parameter's name.
        (
            "f(positional n: int) = popCount(n - 1);\n",
            "popCount(n - 1)",
            "x = n - 1; if x >= 0 { popCount(x) } else { … }",
        ),
        // `x = x - 1` would define `x` in terms of itself, and `x = n - x` would read the new
        // `x`: the name takes the least number from 2 that the call does not write.
        (
            "f(positional x: int) = popCount(x - 1);\n",
            "popCount(x - 1)",
            "x2 = x - 1; if x2 >= 0 { popCount(x2) } else { … }",
        ),
        (
            "f(positional n: int) = { x = 3; x2 = 4; popCount(n - x - x2) };\n",
            "popCount(n - x - x2)",
            "x3 = n - x - x2; if x3 >= 0 { popCount(x3) } else { … }",
        ),
        // A width takes the operand below `2^width` as well.
        (
            "f(positional n: int) = bitNot(n, width: 8);\n",
            "bitNot(n, width: 8)",
            "if n >= 0 && n < 2^8 { bitNot(n, width: 8) } else { … }",
        ),
        (
            "f(positional n: int) = bitNot(n - 1, width: 8);\n",
            "bitNot(n - 1, width: 8)",
            "x = n - 1; if x >= 0 && x < 2^8 { bitNot(x, width: 8) } else { … }",
        ),
        // The call of a function whose parameter reaches a bit word.
        (
            "g(positional k) = popCount(k);\nf(positional n: int) = g(n + 2);\n",
            "g(n + 2)",
            "k = n + 2; if k >= 0 { g(k) } else { … }",
        ),
        // An int read from the input.
        (
            "main(m: MainArgs) {\n  m.stdout <- String(popCount(int(m.stdin[0]) else 0));\n}\n",
            "popCount(int(m.stdin[0]) else 0)",
            "x = int(m.stdin[0]) else 0; if x >= 0 { popCount(x) } else { … }",
        ),
        // The power's own repair names its value apart from the names the power writes.
        (
            "f(positional exponent: int) = 2^(exponent - 1);\n",
            "2^(exponent - 1)",
            "exponent2 = exponent - 1; if exponent2 >= 0 { 2^exponent2 } else { … }",
        ),
    ];
    for (src, call, want) in cases {
        let out = rejected(src);
        in_the_programs_words(&out);
        assert_eq!(tried(&out), Some(want), "{src}\n{out}");
        let fixed = repaired(src, call, want);
        checks(&fixed);
    }
}

#[test]
fn a_width_test_of_the_lower_bound_alone_is_not_enough() {
    // The control for the two-sided test above: with `n < 2^8` dropped, the repair would be
    // rejected again, since 256 is not below `2^8`.
    let fixed = "f(positional n: int) = if n >= 0 { bitNot(n, width: 8) } else { 0 };\n";
    let out = rejected(fixed);
    assert!(out.contains("`bitNot` takes `x` in int[0..<2^8]"), "{out}");
}

#[test]
fn no_test_is_offered_where_no_value_fits() {
    // No value of `-1` lies in int[0..], so a test of it would leave nothing to pass.
    let out = rejected("x = popCount(-1);\n");
    in_the_programs_words(&out);
    assert!(out.lines().next().unwrap().contains(" takes `"), "{out}");
    assert_eq!(tried(&out), None, "{out}");
}

/// The domain the headline of `out` names, as `` `x` in int[0..<2^8]`` in "`bitNot` takes `x` in
/// int[0..<2^8]: …", and the pass note naming the same domain.
fn same_domain(out: &str) {
    let first = out.lines().next().expect("a message");
    let (_, rest) = first.split_once(" takes `").expect("a domain headline");
    let (name, rest) = rest.split_once("` ").expect("the operand's name");
    let what = &rest[..rest.find(": `").expect("the code")];
    let pass = match what.strip_prefix("in ") {
        Some(_) => format!("repair: pass as `{name}` a value {what}"),
        None => format!("repair: pass as `{name}` {what}"),
    };
    assert!(out.contains(&pass), "{pass}\n{out}");
}

#[test]
fn a_width_repair_is_a_comparison_or_a_wider_literal_and_is_accepted() {
    // (program, call, the headline's repair, a further repair the notes offer)
    let cases = [
        // A funnel shift's `k` lies below the width: a test against the width's one value.
        (
            "f(positional n: int) = funnelShl(1, 2, n, width: 8);\n",
            "funnelShl(1, 2, n, width: 8)",
            "if n >= 0 && n < 8 { funnelShl(1, 2, n, width: 8) } else { … }",
            None,
        ),
        (
            "f(positional k: int) = if k >= 0 && k <= 9 { funnelShl(3, 5, k, width: 8) } else { 0 };\n",
            "funnelShl(3, 5, k, width: 8)",
            "if k >= 0 && k < 8 { funnelShl(3, 5, k, width: 8) } else { … }",
            Some("funnelShl(3, 5, k, width: 10)"),
        ),
        // A literal `k` at or above a literal width: the width rewritten.
        (
            "f(positional n: int) = funnelShl(3, 5, 8, width: 8);\n",
            "funnelShl(3, 5, 8, width: 8)",
            "funnelShl(3, 5, 8, width: 9)",
            None,
        ),
        // A width that is a name: tested against the least width the operands take.
        (
            "f(positional n: int) = bitNot(5, width: n);\n",
            "bitNot(5, width: n)",
            "if n >= 3 { bitNot(5, width: n) } else { … }",
            None,
        ),
        (
            "f(positional n: int) = funnelShl(1, 2, 3, width: n);\n",
            "funnelShl(1, 2, 3, width: n)",
            "if n >= 4 { funnelShl(1, 2, 3, width: n) } else { … }",
            None,
        ),
        // An operand at or above `2^width`.
        (
            "f(positional n: int) = bitNot(300, width: 8);\n",
            "bitNot(300, width: 8)",
            "bitNot(300, width: 9)",
            None,
        ),
        (
            "f(positional x: int) = if x >= 0 && x <= 300 { mulHi(x, 3, width: 8) } else { 0 };\n",
            "mulHi(x, 3, width: 8)",
            "if x >= 0 && x < 2^8 { mulHi(x, 3, width: 8) } else { … }",
            Some("mulHi(x, 3, width: 9)"),
        ),
        // `byteSwap` takes whole bytes: the next multiple of 8, or a test of the widths listed.
        (
            "f(positional n: int) = byteSwap(0x0102, width: 12);\n",
            "byteSwap(0x0102, width: 12)",
            "byteSwap(0x0102, width: 16)",
            None,
        ),
        (
            "f(positional n: int) = byteSwap(0x0102, width: n);\n",
            "byteSwap(0x0102, width: n)",
            "if n == 16 || n == 32 || n == 64 { byteSwap(0x0102, width: n) } else { … }",
            None,
        ),
    ];
    for (src, call, want, further) in cases {
        let out = rejected(src);
        in_the_programs_words(&out);
        assert!(!out.contains("with `is`"), "{src}\n{out}");
        same_domain(&out);
        assert_eq!(tried(&out), Some(want), "{src}\n{out}");
        checks(&repaired(src, call, want));
        if let Some(r) = further {
            assert!(out.contains(&format!("repair: `{r}`")), "{src}\n{out}");
            checks(&repaired(src, call, r));
        }
    }
    // The controls: a test one step short of each repair is rejected.
    for src in [
        "f(positional n: int) = if n >= 0 && n < 9 { funnelShl(1, 2, n, width: 8) } else { 0 };\n",
        "f(positional n: int) = if n >= 0 && n < 2^8 { funnelShl(1, 2, n, width: 8) } else { 0 };\n",
        "f(positional n: int) = if n >= 2 { bitNot(5, width: n) } else { 0 };\n",
        "f(positional n: int) = if n >= 3 { funnelShl(1, 2, 3, width: n) } else { 0 };\n",
        "f(positional n: int) = byteSwap(0x0102, width: 8);\n",
        "f(positional n: int) = if n == 8 || n == 16 { byteSwap(0x0102, width: n) } else { 0 };\n",
    ] {
        same_domain(&rejected(src));
    }
}

#[test]
fn a_width_of_no_one_value_is_written_in_the_domain_and_tested_alone() {
    // `k` lies below a width that varies: the domain names the width, and no test of `k`
    // alone is offered.
    let out = rejected(
        "f(positional n: int, positional w: int) = \
         if w >= 1 && w <= 8 { funnelShl(1, 2, n, width: w) } else { 0 };\n",
    );
    in_the_programs_words(&out);
    assert!(
        out.lines()
            .next()
            .unwrap()
            .starts_with("1:65: `funnelShl` takes `k` in int[0..<width]: "),
        "{out}"
    );
    same_domain(&out);
    assert_eq!(tried(&out), None, "{out}");
    // A width with no declared type: the test, and the parameters to declare.
    let src = "f(positional n) = bitNot(5, width: n);\n";
    let out = rejected(src);
    in_the_programs_words(&out);
    same_domain(&out);
    assert!(
        out.lines().next().unwrap().ends_with(
            "Try `if n >= 3 { bitNot(5, width: n) } else { … }` instead, with each parameter in \
             `n` declared `int`."
        ),
        "{out}"
    );
    checks("f(positional n: int) = if n >= 3 { bitNot(5, width: n) } else { 0 };\n");
}

#[test]
fn a_generic_operand_names_its_expression_and_the_parameters_to_declare() {
    let out = rejected("f(positional x) = popCount(x);\ng(positional y) = f(y + 1);\n");
    in_the_programs_words(&out);
    assert_eq!(
        tried(&out),
        Some("x = y + 1; if x >= 0 { … } else { … }"),
        "{out}"
    );
    assert!(
        out.lines().next().unwrap().ends_with(
            "instead, with each parameter in `y + 1` declared `int` and `x` passed inside the \
             branch."
        ),
        "{out}"
    );
    // The repair as the headline says it: `y` declared `int` and `x` passed inside the branch.
    let fixed = "f(positional x) = popCount(x);\n\
                 g(positional y: int) = { x = y + 1; if x >= 0 { f(x) } else { 0 } };\n";
    checks(fixed);
}

/// A program that reads a line into `t` with `bind` and pushes `t` to the output.
fn pushing(bind: &str) -> String {
    format!("main(m: MainArgs) {{\n  {bind}\n  m.stdout <- t;\n}}\n")
}

#[test]
fn a_lines_port_repair_writes_the_programs_value() {
    for (bind, line) in [
        // An int: written into a string.
        ("t = int(m.stdin[0]) else 0;", "m.stdout <- \"${t}\";"),
        // A string that may be an atom: an empty line in place of each atom.
        ("t = m.stdin[0];", "m.stdout <- t else \"\";"),
        // An int that may be an atom: both.
        ("t = int(m.stdin[0]);", "m.stdout <- \"${t}\" else \"\";"),
        // A number computed from literals alone, whatever carrier it takes: written into a
        // string (PORT-lines-int-name), through an operator, a name and an `else`.
        ("t = 2^62;", "m.stdout <- \"${t}\";"),
        ("t = 1 + 1;", "m.stdout <- \"${t}\";"),
        ("b = 2^62; t = b - 1;", "m.stdout <- \"${t}\";"),
        ("b = 2^62; t = b else 0;", "m.stdout <- \"${t}\";"),
    ] {
        let src = pushing(bind);
        let out = rejected(&src);
        in_the_programs_words(&out);
        assert!(out.contains(&format!(", as `{line}`")), "{src}\n{out}");
        // The headline is the push annotated with the value's type, ending with the repair.
        assert!(
            out.lines().next().unwrap().contains(
                "A `Lines` port takes a `String` or a family of strings: `m.stdout <- t : "
            ),
            "{src}\n{out}"
        );
        assert_eq!(tried(&out), Some(line), "{src}\n{out}");
        let fixed = src.replace("m.stdout <- t;", line);
        checks(&fixed);
    }
    // The control for the catch-all: an `else` for one atom of several leaves the others, and
    // the port still refuses the value.
    let out = rejected(
        &pushing("t = m.stdin[0];")
            .replace("m.stdout <- t;", "m.stdout <- t else #outOfBounds -> \"\";"),
    );
    assert!(out.contains("A `Lines` port takes"), "{out}");
}

/// `t1 = 2^62; t2 = t1 + 1; …; m.stdout <- tn;` pushed to the output.
pub(super) fn a_pushed_chain(n: usize) -> String {
    let binds: String = (2..=n)
        .map(|i| format!("t{i} = t{} + 1; ", i - 1))
        .collect();
    pushing(&format!("t1 = 2^62; {binds}t = t{n};"))
}

/// The push of [`a_pushed_chain`] is repaired by writing `t` into a string. The push reads the
/// carriers of one class of n merged operations (one find in the union of the classes), and
/// the message derives `tn` through every name (COMPLEXITY.md, PORT-lines-int-name).
pub(super) fn a_pushed_chain_rejected(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(tried(&out), Some("m.stdout <- \"${t}\";"), "{n}");
}

#[test]
fn a_pushed_chain_of_names_of_literals_is_rejected() {
    for n in [1, 2, 20] {
        a_pushed_chain_rejected(&a_pushed_chain(n), n);
    }
}

/// A function that binds `x2` to `x{n+1}` and passes `x` less all of them to `popCount`, so
/// that the repair's name is the first of `n + 2` numbers the call does not write.
pub(super) fn crowded(n: usize) -> String {
    let names: Vec<String> = (2..n + 2).map(|i| format!("x{i}")).collect();
    let binds: String = names.iter().map(|x| format!("  {x} = 1;\n")).collect();
    format!(
        "f(positional x: int) = {{\n{binds}  popCount(x - {})\n}};\n",
        names.join(" - ")
    )
}

/// The repair of [`crowded`]`(n)` names its value by the first number the call does not
/// write. Each number tried is looked up among the call's words, collected once
/// (COMPLEXITY.md, `fresh`): trying each against the call's text afresh is quadratic in the
/// names.
pub(super) fn the_repairs_value_named(src: &str, n: usize) {
    let out = rejected(src);
    let first = out.lines().next().expect("a message");
    assert!(
        first.contains(&format!("Try `x{} = x - ", n + 2)),
        "{first}"
    );
}

#[test]
fn naming_the_repairs_value_among_the_names_of_the_call() {
    for n in [1, 2, 20] {
        the_repairs_value_named(&crowded(n), n);
    }
}

/// `bitNot(1 + 1 + … + 1, width: 2)` with `n` ones.
pub(super) fn a_wide_bit_not(n: usize) -> String {
    let sum = vec!["1"; n].join(" + ");
    format!("x = bitNot({sum}, width: 2);\n")
}

/// The least width that holds `n` is the number of its binary digits, and the rewritten call
/// is cut once around the width (COMPLEXITY.md, MSG-width-headline): linear in the call's
/// text.
pub(super) fn a_width_repair(src: &str, n: usize) {
    let out = rejected(src);
    let first = out.lines().next().expect("a message");
    let digits = usize::BITS - n.leading_zeros();
    assert!(
        first.ends_with(&format!(", width: {digits})` instead.")),
        "{}",
        &first[first.len().saturating_sub(200)..]
    );
}

#[test]
fn a_width_repair_of_a_long_call() {
    // 4 needs 3 binary digits, 8 needs 4 and 31 needs 5, each past the width 2 written.
    for n in [4, 8, 31] {
        a_width_repair(&a_wide_bit_not(n), n);
    }
}
