//! The checker's scopes on difference paths against the solver's (item ST-walk-checker-admit).
//!
//! The checker's scopes are lazy, bind each name a test reads to itself and carry a premise on
//! each test, and a test of difference constraints there edits the paths of names
//! (`NameProducts`) instead of running the solver. With `path_check` on, each admitted test
//! is run again by the solver on the scope it started from, and the two scopes are compared:
//! bottom, the settled product of each name, the relation, the ends of single names and the
//! refusals. Each program here is checked whole by `zedc::run::load`, so every scope the walk
//! makes, joins, bindings and unbindings included, is compared where a test is admitted.

use zedc::store::product::path_check;

/// `f` over `params`, of body `open body close`, with a `main` that does nothing.
fn program(params: &[String], open: &str, body: &str, close: &str) -> String {
    format!(
        "f({}) =\n  {open}{body} {close};\nmain(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n",
        params.join(", ")
    )
}

/// Nested `if`s, each test in `tests` around the next, every `else` 0.
fn nested(tests: &[String]) -> (String, String) {
    let open: String = tests.iter().map(|t| format!("if {t} {{ ")).collect();
    let close = "} else { 0 } ".repeat(tests.len());
    (open, close)
}

/// `x_0 … x_(n-1)`, each in `0..=4n`, then the chain `x_i >= x_(i-1) + 1`.
fn chain(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("x{i}: int")).collect();
    let mut tests = Vec::new();
    for i in 0..n {
        tests.push(format!("x{i} >= 0"));
        tests.push(format!("x{i} <= {}", 4 * n));
    }
    tests.extend((1..n).map(|i| format!("x{i} >= x{} + 1", i - 1)));
    let (open, close) = nested(&tests);
    program(
        &params,
        &open,
        &format!("popCount(x{} - {})", n - 1, n - 1),
        &close,
    )
}

/// The s4 raise: `y_j` in `0..=1`, the chain `x_(i+1) >= x_i` from `x_0 >= 0`, then for each
/// `j` the test `x_0 >= j + 1 || y_j <= -1`, whose second arm is dead: each raises the head.
fn raise(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("x{i}: int, y{i}: int")).collect();
    let mut tests = Vec::new();
    for i in 0..n {
        tests.push(format!("y{i} >= 0"));
        tests.push(format!("y{i} <= 1"));
    }
    tests.push("x0 >= 0".to_string());
    tests.extend((0..n - 1).map(|i| format!("x{} >= x{i}", i + 1)));
    tests.extend((0..n).map(|j| format!("x0 >= {} || y{j} <= -1", j + 1)));
    let (open, close) = nested(&tests);
    program(
        &params,
        &open,
        &format!("popCount(x{} - {n})", n - 1),
        &close,
    )
}

/// The chain of [`chain`] with `w_i = y + x_i` bound under each link, `y = x_0 + 1` (or the
/// sum of every `x_i` when `all`), and the sum of the `w_i` read at the end: the walk binds
/// each `w_i` in the scope of the link above it and reads its summary over the inputs there.
fn reads(n: usize, all: bool) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("x{i}: int")).collect();
    let y = match all {
        true => (0..n)
            .map(|i| format!("x{i}"))
            .collect::<Vec<_>>()
            .join(" + "),
        false => "x0 + 1".to_string(),
    };
    let mut tests = Vec::new();
    for i in 0..n {
        tests.push(format!("x{i} >= 0"));
        tests.push(format!("x{i} <= {}", 4 * n));
    }
    let (mut open, mut close) = nested(&tests);
    open = format!("{{ y = {y}; {open}");
    close += "}";
    for i in 1..n {
        open += &format!("if x{i} >= x{} + 1 {{ w{i} = y + x{i}; ", i - 1);
        close = format!("}} else {{ 0 }} {close}");
    }
    let sum: Vec<String> = (1..n).map(|i| format!("w{i}")).collect();
    program(
        &params,
        &open,
        &format!("popCount({})", sum.join(" + ")),
        &close,
    )
}

/// The admitted tests and the differences found while `src` is checked.
fn compared(src: &str) -> (u64, Vec<String>) {
    let src = src.to_string();
    zed_tests::scaling::on_a_thread(1 << 29, move || {
        path_check::start();
        let loaded = zedc::run::load(src.as_bytes()).map(|_| ());
        let (admitted, differences) = path_check::stop();
        if let Err(e) = loaded {
            panic!("rejected:\n{src}\n{e}");
        }
        (admitted, differences)
    })
}

/// Checks `src` with the comparison on: at least one test admitted, and no difference.
fn same_as_the_solver(what: &str, src: &str) -> u64 {
    let (admitted, differences) = compared(src);
    assert!(
        differences.is_empty(),
        "{what}: the scopes on paths differ from the solver's:\n{}\n{src}",
        differences.join("\n")
    );
    assert!(admitted > 0, "{what}: no test admitted\n{src}");
    admitted
}

#[test]
fn a_chain_of_difference_tests_in_the_checker_matches_the_solver() {
    for n in [2, 3, 8] {
        same_as_the_solver(&format!("chain, n = {n}"), &chain(n));
    }
}

#[test]
fn a_raised_head_in_the_checker_matches_the_solver() {
    // Each `x_0 >= j + 1 || y_j <= -1` bounds the head alone: its own lower end moves and the
    // shared interval does not, which the per-path ends record (`PathRange::head_hi`,
    // `tail_lo`). Its `else` scope, `x_0 <= j && y_j >= 0`, is built by the checker as the
    // join of the arms, never as the whole `||`.
    for n in [2, 3, 6] {
        same_as_the_solver(&format!("raise, n = {n}"), &raise(n));
    }
}

#[test]
fn names_bound_under_a_chain_match_the_solver() {
    // Each `w_i` is a fresh binding in a scope on a path, and is unbound when its arm ends;
    // binding records its bounds in the relation without folding the pending conjuncts in
    // (`Relation::state_fresh`), and its summary reads its inputs by name
    // (`Ck::read_image`).
    for n in [2, 4, 8] {
        same_as_the_solver(&format!("one input, n = {n}"), &reads(n, false));
        same_as_the_solver(&format!("n inputs, n = {n}"), &reads(n, true));
    }
}

/// The tests `x_i >= 0` and `x_i <= hi` of each name `x_i` of `names`, which give each the
/// finite bounds a name needs to go on a path (`NameProducts::member`).
fn bounded(names: &[&str], hi: usize) -> Vec<String> {
    names
        .iter()
        .flat_map(|x| [format!("{x} >= 0"), format!("{x} <= {hi}")])
        .collect()
}

#[test]
fn a_chain_that_closes_on_itself_is_unreachable_as_the_solver_finds() {
    // `x_2 >= x_1 + 1 >= x_0 + 2` and then `x_0 >= x_2`: the back edge closes the path with a
    // positive weight, so the innermost arm is unreachable and its `x_0 - 1` is never a
    // negative bit count.
    let names = ["x0", "x1", "x2"];
    let params = names.map(|x| format!("{x}: int"));
    let mut tests = bounded(&names, 9);
    tests.extend(["x1 >= x0 + 1", "x2 >= x1 + 1", "x0 >= x2"].map(String::from));
    let (open, close) = nested(&tests);
    same_as_the_solver(
        "closed chain",
        &program(&params, &open, "popCount(x0 - 1)", &close),
    );
}

#[test]
fn a_test_no_path_holds_hands_the_scope_back_to_the_solver() {
    // `x_0 + x_2 >= 5` is no difference constraint: the solver takes it, the relation then
    // holds a conjunct no path holds, the paths' stars are projected as stale
    // (`Scope::stale`), and every test below, `x_2 >= 3` included, goes to the solver.
    let names = ["x0", "x1", "x2"];
    let params = names.map(|x| format!("{x}: int"));
    let mut tests = bounded(&names, 9);
    tests.extend(["x1 >= x0 + 1", "x2 >= x1 + 1", "x0 + x2 >= 5", "x2 >= 3"].map(String::from));
    let (open, close) = nested(&tests);
    same_as_the_solver(
        "chain, then a sum",
        &program(&params, &open, "popCount(x2 - 3)", &close),
    );
}

#[test]
fn a_test_both_ways_of_a_path_member_matches_the_solver() {
    // Each `if` has a reached `else` here: `x_1 <= x_0` links the names the other way, `x_1
    // >= 5` gives the tail its own lower end, and `x_1 <= 4` bounds the shared interval.
    let params = ["x0: int", "x1: int"].map(String::from);
    let src = program(
        &params,
        "if x0 >= 0 { if x0 <= 9 { if x1 >= 0 { if x1 <= 10 { if x1 >= x0 + 1 { \
         if x1 >= 5 { popCount(x1 - 5) } else { popCount(4 - x1) } } else { ",
        "popCount(x0)",
        "} } else { 0 } } else { 0 } } else { 0 } } else { 0 }",
    );
    same_as_the_solver("both ways", &src);
}

/// Checks each program of `make` at `n = 16` and 128 and holds the work to the limit of order
/// n. On main before ST-walk-checker-admit the checker took no test on paths and these grew
/// 23.5 (chain), 25.9 (raise) and 21.1 (one input read) times in instructions.
fn checked_in_linear_work(what: &str, make: fn(usize) -> String) {
    let programs = zed_tests::scaling::inputs(16, make);
    zed_tests::scaling::check(what, 16, |m| {
        if let Err(e) = zedc::run::load(programs[&m].as_bytes()) {
            panic!("{what}, n = {m}: rejected: {e}");
        }
    });
}

mod bench;
