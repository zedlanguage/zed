//! A program with a recursion beside other definitions, as `zedc run` and `zedc check` load
//! it: the recursion is rejected, and every other definition is still checked, so an error in
//! one is reported with it, each once (SIG-lost-spin). Before, the checker stopped at the
//! cycle and only the recursion was reported.

use super::rejected;

#[test]
fn an_error_beside_a_recursion_is_reported_with_it() {
    let out = rejected(
        "spin(positional n: int) = spin(n + 1);\nf(positional c: int) = 1 + c;\nmain = f(true);\n",
    );
    let heads: Vec<&str> = out.lines().filter(|l| !l.starts_with(' ')).collect();
    assert_eq!(
        heads,
        [
            "1:1: `spin` is defined in terms of itself, which is recursion: this version of zedc does not compile it yet.",
            "3:8: `f` does not take (true): no arrow of `f` takes these types.",
        ],
        "{out}"
    );
    assert!(
        out.contains(
            "`f` is declared here with no type written for its result; the type the checker \
             found for `f` is `int -> int`"
        ),
        "{out}"
    );
}

/// A call of the recursive function gives no value and adds no error of its own: `f(spin(1))`
/// is not reported, `f(true)` is.
#[test]
fn a_call_of_a_recursion_adds_no_error() {
    let out = rejected(
        "spin(positional n: int) = spin(n + 1);\nf(positional c: int) = 1 + c;\n\
         main = f(spin(1)) + f(true);\n",
    );
    let heads: Vec<&str> = out.lines().filter(|l| !l.starts_with(' ')).collect();
    assert_eq!(heads.len(), 2, "{out}");
    assert!(
        heads[0].starts_with("1:1: `spin` is defined in terms of itself"),
        "{out}"
    );
    assert!(
        heads[1].starts_with("3:21: `f` does not take (true)"),
        "{out}"
    );
}

/// MSG-recursion-chain: the message of a cycle shows each use that closes it, at its site, in
/// the order of the cycle from its first definition by name, then the repairs
/// (DESIGN.md sec:diagnostics). Before, it named the definitions only.
const NOT_YET: &str = ": this version of zedc does not compile it yet.";

const NO_STEP: &str = "a value cannot be defined in terms of itself, since no step of the \
                       program makes the earlier value";

/// The repair that steps the value `x` from its earlier one, `next` the new value and
/// `indexed` the value with each read of `x` made `x[i-1]`.
fn step_repair(x: &str, next: &str, indexed: &str) -> String {
    format!(
        "repair: to step `{x}` from its earlier value, write a `loop` with a start value, as \
         `loop t {{ while t < 10; initial {x} = 0; {x}' = {next}; }}`, or an indexed definition, \
         as `{x}[i in 0..<10] = {indexed} with {x}[-1] = 0`, with the start value in place of 0 \
         and the number of steps in place of 10. Loops and indexed definitions are part of the \
         Zed language, and this version of zedc does not compile them yet."
    )
}

/// The repair that writes the value `x` as a function.
fn function_repair(x: &str) -> String {
    format!(
        "repair: to define a recursive function, write `{x}` as a function with a parameter. \
         Recursion is part of the Zed language, and this version of zedc does not compile it \
         yet."
    )
}

#[test]
fn a_self_recursive_function_shows_its_use() {
    let out = rejected("spin(positional n: int) = spin(n);\nmain = 0;\n");
    assert_eq!(
        out,
        format!(
            "1:1: `spin` is defined in terms of itself, which is recursion{NOT_YET}\n  \
             [1] 1:27: `spin` uses itself here\n      \
             1 | spin(positional n: int) = spin(n);\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]\n        \
             |                           ^^^^ [1]\n  \
             [2] 1:1: repair: remove the use shown, which ends the cycle"
        )
    );
}

#[test]
fn a_two_cycle_shows_each_use_in_the_order_of_the_cycle() {
    // `odd` is written first; the cycle starts at `even`, the first by name.
    let out = rejected(
        "odd(positional n: int) = if n == 0 { false } else { even(n - 1) };\n\
         even(positional n: int) = if n == 0 { true } else { odd(n - 1) };\nmain = 0;\n",
    );
    assert_eq!(
        out,
        format!(
            "2:1: `even`, `odd` are defined in terms of each other, which is recursion\
             {NOT_YET}\n  \
             [1] 2:53: `even` uses `odd` here\n      \
             2 | even(positional n: int) = if n == 0 {{ true }} else {{ odd(n - 1) }};\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [3]\n        \
             |                                                     ^^^ [1]\n  \
             [2] 1:53: `odd` uses `even` here\n      \
             1 | odd(positional n: int) = if n == 0 {{ false }} else {{ even(n - 1) }};\n        \
             |                                                     ^^^^\n  \
             [3] 2:1: repair: remove one of the uses shown, which ends the cycle"
        )
    );
}

/// Three values, each read as the next is computed: the row "A definition that reads its own
/// value", the reads in the order of the cycle `a`, `c`, `b`, not the order of the text.
#[test]
fn a_three_cycle_of_values_shows_each_read_in_the_order_of_the_cycle() {
    let out = rejected("a = c + 1;\nb = a * 2;\nc = b - 3;\nmain = 0;\n");
    assert_eq!(
        out,
        format!(
            "1:1: `a`, `c`, `b` are defined in terms of each other's values.\n  \
             [1] 1:5: `a` reads `c` here\n      \
             1 | a = c + 1;\n        \
             | ^^^^^^^^^^ [4, 5, 6]\n        \
             |     ^ [1]\n  \
             [2] 3:5: `c` reads `b` here\n      \
             3 | c = b - 3;\n        \
             |     ^\n  \
             [3] 2:5: `b` reads `a` here\n      \
             2 | b = a * 2;\n        \
             |     ^\n  \
             [4] 1:1: {NO_STEP}\n  \
             [5] 1:1: {}\n  \
             [6] 1:1: {}",
            step_repair("a", "a + 1", "a[i-1] + 1"),
            function_repair("a"),
        )
    );
}

/// A cycle closed by a call inside a function declared in the body: the use shown is the call
/// in the inner function.
#[test]
fn a_cycle_through_a_nested_call_shows_the_inner_use() {
    let out =
        rejected("f(positional n: int) = { h(positional m: int) = f(m); h(n) };\nmain = 0;\n");
    assert_eq!(
        out,
        format!(
            "1:1: `f` is defined in terms of itself, which is recursion{NOT_YET}\n  \
             [1] 1:49: `f` uses itself here\n      \
             1 | f(positional n: int) = {{ h(positional m: int) = f(m); h(n) }};\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]\n        \
             |                                                 ^ [1]\n  \
             [2] 1:1: repair: remove the use shown, which ends the cycle"
        )
    );
}

/// Two cycles in one unit, one of functions and one of values: each is reported with its own
/// uses and repairs.
#[test]
fn two_separate_cycles_are_each_shown_with_their_uses() {
    let out = rejected(
        "f(positional n: int) = g(n);\ng(positional n: int) = f(n);\nx = y + 1;\ny = x;\nmain = 0;\n",
    );
    assert_eq!(
        out,
        format!(
            "1:1: `f`, `g` are defined in terms of each other, which is recursion{NOT_YET}\n  \
             [1] 1:24: `f` uses `g` here\n      \
             1 | f(positional n: int) = g(n);\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [3]\n        \
             |                        ^ [1]\n  \
             [2] 2:24: `g` uses `f` here\n      \
             2 | g(positional n: int) = f(n);\n        \
             |                        ^\n  \
             [3] 1:1: repair: remove one of the uses shown, which ends the cycle\n\
             3:1: `x`, `y` are defined in terms of each other's values.\n  \
             [1] 3:5: `x` reads `y` here\n      \
             3 | x = y + 1;\n        \
             | ^^^^^^^^^^ [3, 4, 5]\n        \
             |     ^ [1]\n  \
             [2] 4:5: `y` reads `x` here\n      \
             4 | y = x;\n        \
             |     ^\n  \
             [3] 3:1: {NO_STEP}\n  \
             [4] 3:1: {}\n  \
             [5] 3:1: {}",
            step_repair("x", "x + 1", "x[i-1] + 1"),
            function_repair("x"),
        )
    );
}

/// A value of a block that reads its own name, where the unit defines that name too: the
/// repairs step it with its own value, and offer the `x` of the unit, which the read may have
/// meant, by renaming.
#[test]
fn a_value_that_reads_itself_is_offered_the_other_definition_of_its_name() {
    let out = rejected("x = 3;\nmain = { x = x * 2 + 1; x };\n");
    assert_eq!(
        out,
        format!(
            "2:10: `x` is defined in terms of its own value.\n  \
             [1] 2:14: `x` reads itself here\n      \
             2 | main = {{ x = x * 2 + 1; x }};\n        \
             |          ^^^^^^^^^^^^^^ [2, 3, 5]\n        \
             |              ^ [1]\n  \
             [2] 2:10: {NO_STEP}\n  \
             [3] 2:10: {}\n  \
             [4] 1:1: repair: to read the `x` defined here, give the `x` that reads its own \
             value another name\n      \
             1 | x = 3;\n        \
             | ^^^^^^\n  \
             [5] 2:10: {}",
            step_repair("x", "x * 2 + 1", "x[i-1] * 2 + 1"),
            function_repair("x"),
        )
    );
}

/// A cycle of `n` functions, each calling the next, the last the first.
pub(super) fn long(n: usize) -> String {
    (0..n)
        .map(|i| format!("c{i}(positional k: int) = c{}(k);\n", (i + 1) % n))
        .collect()
}

/// A unit's text, statements and resolution.
pub(super) type Resolved = (String, Vec<zedc::ast::Stmt>, zedc::resolve::Resolution);

/// [`long`]`(n)` resolved.
pub(super) fn a_long_cycle(n: usize) -> Resolved {
    let text = long(n);
    let tokens = zedc::lex::lex_fence(&text).unwrap();
    let tree = zedc::parse::parse(&text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(&text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap_or_else(|e| panic!("{e:?}"));
    (text, stmts, res)
}

/// The report of the cycle of [`a_long_cycle`]`(n)`: one, with its `n` uses.
pub(super) fn the_report_of_a_long_cycle((text, stmts, res): &Resolved, n: usize) {
    use zedc::resolve::tables::Tables;
    let tables = Tables::with_text(stmts, res, Some(text));
    let items: Vec<_> = stmts.iter().collect();
    let (_, cycles) = tables.order_around_cycles(&items);
    let reports = tables.cycle_reports(&items, &cycles);
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].notes.len(), n + 1);
    let message = &reports[0].message;
    assert!(
        message.starts_with("`c0`") && message.contains("`c1`"),
        "{message}"
    );
}

/// The check of [`a_long_cycle`]`(n)` reports the cycle once, with its `n` uses.
pub(super) fn a_long_cycle_checked((_, stmts, res): &Resolved, n: usize) {
    let info = zedc::check::walk::check(stmts, res);
    assert_eq!(info.errors.len(), 1);
    assert_eq!(info.errors[0].notes.len(), n + 1);
}

#[test]
fn reporting_and_checking_a_long_cycle() {
    for n in [2, 3, 12] {
        let unit = a_long_cycle(n);
        the_report_of_a_long_cycle(&unit, n);
        a_long_cycle_checked(&unit, n);
    }
}
