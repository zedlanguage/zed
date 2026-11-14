//! Elaboration at the rule of low complexity (DESIGN.md Part G): the inputs of the benchmarks
//! in `bench.rs` and the check each makes at each size, run here at small sizes, and the tests
//! that the forms those benchmarks time give the right result.

use zed_tests::deep::{program, statements};
use zedc::ast::{Stmt, unit};
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::{Resolution, resolve};

use super::{Checked, checked, elab, term, value};

/// `h0(x = 1) = x;` and `h{i}(x = h{i-1}() + h{i-1}()) = x;` up to `k`, and `main = h{k}();`.
pub(super) fn chain(k: usize) -> String {
    let mut src = "h0(x = 1) = x;\n".to_string();
    for i in 1..=k {
        src += &format!("h{i}(x = h{j}() + h{j}()) = x;\n", j = i - 1);
    }
    src + &format!("main = h{k}();\n")
}

/// The term of `main` in the elaborated chain of defaults is short: a call holds no copy of
/// a default.
pub(super) fn defaults_stay_short(u: &Checked) {
    let u = u.elab();
    let main = u.defs.iter().find(|d| d.name == "main").unwrap();
    assert!(main.term.to_string().len() < 40, "{}", main.term);
}

#[test]
fn a_chain_of_defaults_calls_each_default_once() {
    assert_eq!(value(&chain(3), "main"), "8");
    assert_eq!(term(&chain(3), "main"), "{ x@4 = h3$x@4(); h3(x@4) }");
    assert_eq!(
        term(&chain(3), "h3$x@4"),
        "() -> ({ x@3 = h2$x@3(); h2(x@3) } + { x@3 = h2$x@3(); h2(x@3) })"
    );
}

#[test]
fn a_compound_default_reads_the_parameters_it_names() {
    let src = "area(positional w: int, h = w + 1) = w * h;\na = area(3);\nb = area(3, h: 2);\n";
    assert_eq!(value(src, "a"), "12");
    assert_eq!(value(src, "b"), "6");
    assert_eq!(term(src, "a"), "{ w = 3; h = area$h(w); area(w, h) }");
    assert_eq!(term(src, "area$h"), "w -> (w + 1)");
}

/// The order `topo` gave before it kept the ready items in a heap: the first ready item by
/// index, found by a scan of all of them, at each step.
fn topo_by_scan(deps: &[Vec<usize>]) -> Result<Vec<usize>, Vec<usize>> {
    let n = deps.len();
    let mut done = vec![false; n];
    let mut order = Vec::new();
    while order.len() < n {
        match (0..n).find(|&i| !done[i] && deps[i].iter().all(|&d| done[d])) {
            Some(i) => {
                done[i] = true;
                order.push(i);
            }
            None => {
                let mut seen = std::collections::BTreeMap::new();
                let mut path = Vec::new();
                let mut i = (0..n).find(|&i| !done[i]).unwrap();
                while !seen.contains_key(&i) {
                    seen.insert(i, path.len());
                    path.push(i);
                    i = *deps[i].iter().find(|&&d| !done[d]).unwrap();
                }
                return Err(path.split_off(seen[&i]));
            }
        }
    }
    Ok(order)
}

#[test]
fn the_dependency_order_is_the_first_ready_by_index() {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = |m: usize| {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        (x % m as u64) as usize
    };
    let (mut orders, mut cycles) = (0, 0);
    for _ in 0..2000 {
        let n = 1 + next(12);
        let deps: Vec<Vec<usize>> = (0..n)
            .map(|_| (0..next(3)).map(|_| next(n)).collect())
            .collect();
        let want = topo_by_scan(&deps);
        match &want {
            Ok(_) => orders += 1,
            Err(_) => cycles += 1,
        }
        assert_eq!(zedc::elab::topo(&deps), want, "{deps:?}");
    }
    assert!(
        orders > 200 && cycles > 200,
        "{orders} orders, {cycles} cycles"
    );
}

/// `n` items, each waiting on the next.
pub(super) fn reversed_chain(n: usize) -> Vec<Vec<usize>> {
    (0..n)
        .map(|i| if i + 1 < n { vec![i + 1] } else { Vec::new() })
        .collect()
}

/// The last item of a reversed chain is the first ready.
pub(super) fn orders_reversed(deps: &[Vec<usize>]) {
    assert_eq!(zedc::elab::topo(deps).unwrap()[0], deps.len() - 1);
}

/// `n` items, `n` a multiple of 4: the first half one cycle, each item waiting on the next
/// through a join of its own; the second half `n / 4` cycles of two, each with a join of both
/// that the first item waits on.
pub(super) fn cycle_graph(n: usize) -> Vec<Vec<usize>> {
    let half = n / 2;
    let mut deps: Vec<Vec<usize>> = vec![Vec::new(); n];
    for i in 0..half {
        let join = deps.len();
        deps[i].push(join);
        deps.push(vec![(i + 1) % half]);
    }
    for i in (half..n).step_by(2) {
        let join = deps.len();
        deps[i].push(join);
        deps.push(vec![i, i + 1]);
        deps[i + 1].push(i);
    }
    deps
}

/// `topo_joined` finds the one long cycle of [`cycle_graph`]`(k)` first and every short one.
pub(super) fn finds_every_cycle(deps: &[Vec<usize>], k: usize) {
    let cycles = zedc::elab::topo_joined(deps, k).unwrap_err();
    assert_eq!(cycles.len(), 1 + k / 4);
    assert_eq!(cycles[0].len(), k / 2);
}

/// Functions nested `n` deep, each declaring a local and the next function, which it calls.
pub(super) fn nested(n: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        src += &format!("h{i}(positional x) {{\ny{i} = x + 1;\n");
    }
    src += "x\n";
    for i in (0..n).rev() {
        if i + 1 < n {
            src += &format!("h{}(y{i})\n", i + 1);
        }
        src += "}\n";
    }
    src + "main = h0(1);\n"
}

/// The checker finds no error in `u`, checked again.
pub(super) fn checks_clean(u: &Checked) {
    assert!(u.check().errors.is_empty());
}

/// `u` elaborates and defines `main`.
pub(super) fn elaborates_main(u: &Checked) {
    let u = u.elab();
    assert!(u.defs.iter().any(|d| d.name == "main"));
}

/// Functions nested `n` deep, each declaring `w` functions beside the next, and calling one.
pub(super) fn wide(n: usize, w: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        src += &format!("h{i}(positional x) {{\n");
        for j in 0..w {
            src += &format!("g{i}_{j}(positional z) = z;\n");
        }
        src += &format!("y{i} = g{i}_0(x) + 1;\n");
    }
    src += "x\n";
    for i in (0..n).rev() {
        if i + 1 < n {
            src += &format!("h{}(y{i})\n", i + 1);
        }
        src += "}\n";
    }
    src + "main = h0(1);\n"
}

/// The type of `main` in `src` and the signature of `h{last}`, which a search stopped by
/// its budget does not find.
pub(super) fn found(src: &str, last: usize) -> (Option<String>, Option<String>) {
    let (i, names) = zed_tests::step_helpers::l01_26_type_resolution::info(src);
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let name = format!("h{last}");
    let sig = i.sigs.iter().find(|(id, _)| names[**id] == name);
    (
        i.tops.get("main").map(|t| t.to_string()),
        sig.map(|(_, s)| s.to_string()),
    )
}

/// `main` of [`wide`]`(n, _)`, the text `text`, has type `int`.
pub(super) fn wide_finds_main(text: &str, n: usize) {
    assert_eq!(found(text, n - 1).0.as_deref(), Some("int"));
}

/// A function with `n` named parameters, and a call naming each of them, last first.
pub(super) fn named(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("d{i} = 0")).collect();
    let args: Vec<String> = (0..n).rev().map(|i| format!("d{i}: {i}")).collect();
    format!(
        "f({}) = d0;\ny = f({});\n",
        params.join(", "),
        args.join(", ")
    )
}

/// A function whose parameter `g` has a type with `n` named parameters, and a call of `g`
/// naming each of them, last first.
pub(super) fn named_through_a_value(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("d{i}: int")).collect();
    let args: Vec<String> = (0..n).rev().map(|i| format!("d{i}: {i}")).collect();
    format!(
        "h(g: ({}) -> int) = g({});\n",
        params.join(", "),
        args.join(", ")
    )
}

/// `u` elaborates and its last definition is `last`.
pub(super) fn last_def_is(u: &Checked, last: &str) {
    let u = u.elab();
    assert_eq!(u.defs.last().unwrap().name, last);
}

#[test]
fn an_argument_named_for_no_parameter_of_the_value_called_is_rejected() {
    assert_eq!(value(&named(3), "y"), "0");
    let e = elab(&named_through_a_value(2).replace("g(d1", "g(d2")).unwrap_err();
    assert_eq!(
        e,
        [
            "this argument is passed by the name `d2`, and `(d0: int, d1: int) -> int` has no parameter of that name, so the argument has no parameter to go to. [1]"
        ]
    );
}

/// A function of `n` parameters declared `String`, and `g` calling it once on `n` arguments
/// that may each be a string, `#a` or `#b`, so that each passes its atoms by.
pub(super) fn passing_many_arguments(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("positional x{i}: String")).collect();
    format!(
        "h({}) = x0;\n\
         g(positional k) = {{ v = if k == 1 {{ #a }} else {{ if k == 2 {{ #b }} else {{ \"s\" }} }}; h({}) }};\n",
        params.join(", "),
        vec!["v"; n].join(", ")
    )
}

#[test]
fn an_atom_passes_by_at_the_call_and_a_string_reaches_the_body() {
    for (k, want) in [(1, "#a"), (2, "#b"), (3, "\"s\"")] {
        let text = format!("{}y = g({k});\n", passing_many_arguments(3));
        assert_eq!(value(&text, "y"), want);
    }
}

/// `c = 2;` and a function `f` with `n` rows `c -> c`.
pub(super) fn rows(n: usize) -> String {
    let rows: Vec<String> = (0..n).map(|_| "c -> c".to_string()).collect();
    format!("c = 2;\nf(x) = x test {{ {} }}\n", rows.join(", "))
}

/// `u` elaborates to `n` test cases.
pub(super) fn has_a_test_per_row(u: &Checked, n: usize) {
    assert_eq!(u.elab().tests.len(), n);
}

/// Functions nested `n` deep, each with a parameter of no declared type, the innermost
/// adding all of them.
pub(super) fn open(n: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        src += &format!("h{i}(positional x{i}) {{\n");
    }
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    src += &format!("{}\n", xs.join(" + "));
    for i in (0..n).rev() {
        if i + 1 < n {
            src += &format!("h{}(x{i})\n", i + 1);
        }
        src += "}\n";
    }
    src + "main = h0(1);\n"
}

/// The signature of the innermost function of [`open`]`(n)` is in terms of `h0`'s variable,
/// which it neither binds nor bounds, so it prints `_` there.
pub(super) fn open_signature_is_h0s(n: usize) {
    use zed_tests::step_helpers::l01_26_type_resolution::sig_of;
    let t = (Some("int".to_string()), Some("(_) -> _".to_string()));
    assert_eq!(found(&open(n), n - 1), t);
    let h0 = sig_of(&open(n), "h0");
    let last = sig_of(&open(n), &format!("h{}", n - 1));
    let a = &last.arrows[0];
    assert!(last.own.is_empty() && last.bounds.is_empty());
    assert_eq!(
        (a.params[0].vars.len(), &a.params[0].vars),
        (1, &a.result.vars)
    );
    assert!(h0.own.is_superset(&a.result.vars), "the variable is h0's");
}

/// A function `f` of `n` terms, and a function `g` that calls it on one branch, with `n` rows
/// that take the other.
pub(super) fn big_callee(n: usize) -> String {
    let body: String = (0..n).map(|i| format!(" + x * {i}")).collect();
    let rows: Vec<String> = (0..n).map(|i| format!("{i} -> {i}")).collect();
    format!(
        "f(positional x) = x{body};\n\
         g(positional x) = if x >= 0 {{ x }} else {{ f(x) }} test {{ {} }}\n",
        rows.join(", ")
    )
}

/// `text` and the front end's result on it.
pub(super) fn front(text: &str) -> (String, zedc::query::Db) {
    let mut db = zedc::query::Db::new();
    db.front(text);
    (text.to_string(), db)
}

/// The `n` rows of `text` run on a copy of `db` and each passes.
pub(super) fn rows_pass(text: &str, db: &zedc::query::Db, n: usize) {
    let got = zedc::testing::test_in(&mut db.clone(), text);
    assert_eq!(got.len(), n);
    assert!(got.iter().all(|o| o.failure.is_none()), "{:?}", got[0]);
}

/// `k` overloads of `f` and `g`, a tuple of `k` uses of `f`: the statements and their
/// resolution.
pub(super) fn uses_of_overloads(k: usize) -> (Vec<Stmt>, Resolution) {
    let text = zed_tests::step_helpers::l01_14_name_resolution::overloads(k)
        + "g = ("
        + &vec!["f"; k].join(", ")
        + ");\n";
    let tokens = lex_fence(&text).unwrap();
    let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(&text, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap();
    (stmts, res)
}

/// The top-level order of [`uses_of_overloads`]`(k)` puts `g` after every overload.
pub(super) fn orders_after_overloads(stmts: &[Stmt], res: &Resolution, k: usize) {
    let order = zedc::elab::top_order(stmts, res).unwrap();
    assert_eq!(order.len(), k + 1);
    assert_eq!(order[k], k);
}

/// The top-level order of `stmts` holds each of them.
pub(super) fn orders_all(stmts: &[Stmt], res: &Resolution) {
    let order = zedc::elab::top_order(stmts, res).unwrap();
    assert_eq!(order.len(), stmts.len());
}

/// `u`, a program of shape `shape`, elaborates to at least one definition.
pub(super) fn elaborates_some(u: &Checked, shape: &str) {
    assert!(!u.elab().defs.is_empty(), "{shape}");
}

/// `t = x is int \ int \ … \ int;`, `n` differences nested to the left.
pub(super) fn differences(n: usize) -> String {
    format!("x = 1;\nt = x is {};\n", vec!["int"; n + 1].join(" \\ "))
}

/// `t = x else #a(#a(…#a…)) -> 0;`, the pattern `n` atoms deep, its payloads by position, or
/// by name when `named`.
pub(super) fn else_patterns(n: usize, named: bool) -> String {
    let open = if named { "#a(f: " } else { "#a(" };
    let p = open.repeat(n) + "#a" + &")".repeat(n);
    format!("x = #b;\nt = x else {p} -> 0;\n")
}

/// `u`, of [`differences`] or [`else_patterns`], elaborates to its two definitions.
pub(super) fn elaborates_two(u: &Checked, what: &str) {
    assert_eq!(u.elab().defs.len(), 2, "{what}");
}

/// Each input of the benchmarks in `bench.rs` at a few sizes, through the check the benchmark
/// makes at each size it times, and the values of the programs whose value is known: the
/// timing of each family at large sizes is held in `bench.rs`.
#[test]
fn each_benchmark_input_elaborates_at_small_sizes() {
    let nested_signature = (
        Some("int".to_string()),
        Some("(T) -> T for T in int | f32 | f64 | rat".to_string()),
    );
    for n in [1, 2, 9] {
        defaults_stay_short(&checked(&chain(n)));
        orders_reversed(&reversed_chain(n));
        finds_every_cycle(&cycle_graph(4 * n), 4 * n);
        let u = checked(&nested(n));
        checks_clean(&u);
        elaborates_main(&u);
        assert_eq!(value(&nested(n), "main"), n.to_string());
        assert_eq!(found(&nested(n), n - 1), nested_signature, "{n}");
        wide_finds_main(&wide(n, 20), n);
        last_def_is(&checked(&named(n)), "y");
        assert_eq!(value(&named(n), "y"), "0");
        last_def_is(&checked(&named_through_a_value(n)), "h");
        last_def_is(&checked(&passing_many_arguments(n)), "g");
        has_a_test_per_row(&checked(&rows(n)), n);
        elab(&open(n)).unwrap();
        assert_eq!(value(&open(n), "main"), n.to_string());
        let (text, db) = front(&big_callee(n));
        rows_pass(&text, &db, n);
        let (stmts, res) = uses_of_overloads(n);
        orders_after_overloads(&stmts, &res, n);
        for (what, text) in [
            ("a difference of types", differences(n)),
            ("a pattern by position", else_patterns(n, false)),
            ("a pattern by name", else_patterns(n, true)),
        ] {
            let u = Checked::new(statements(&text));
            checks_clean(&u);
            elaborates_two(&u, what);
        }
    }
    assert_eq!(value(&nested(3), "main"), "3");
    assert_eq!(found(&nested(3), 2), nested_signature);
    assert_eq!(value(&open(4), "main"), "4");
    open_signature_is_h0s(6);
}

/// Each deep program the benchmarks in `bench.rs` order or elaborate, a few levels deep: its
/// top-level order holds every statement, and it elaborates to a definition.
#[test]
fn each_deep_benchmark_program_is_ordered_and_elaborated_at_small_depths() {
    for n in [4, 5, 9] {
        for shape in [
            "a left-nested sum",
            "nested calls",
            "a long sum in a function's body",
            "nested blocks",
            "nested tuples",
        ] {
            let stmts = statements(&program(shape, n).text);
            let res = resolve(&stmts).unwrap();
            orders_all(&stmts, &res);
        }
        for shape in [
            "nested blocks",
            "a left-nested sum",
            "a sum nested in parentheses",
            "an `else if` chain",
            "nested negations",
            "nested calls",
        ] {
            elaborates_some(&Checked::new(statements(&program(shape, n).text)), shape);
        }
    }
}

#[test]
fn errors_inside_types_and_patterns_keep_their_order() {
    // Every part of a type is elaborated, and its errors reported in written order; the first
    // refused part of a pattern ends it. The expected output is the recursive code's.
    let port = "`Lines` is the type of a port, which only a port parameter has; no value has it, so it cannot be written here. To repair it, write the type of the values the port carries, such as `String`. [Lines]";
    assert_eq!(
        super::errors("x = 1;\nt = x is (Lines, int \\ Lines) | Lines;\n"),
        [port, port, port]
    );
    let twice = "the pattern names `k` twice, and a pattern names each field of the payload once. Remove one of the two. [#c(k: #a, k: #b)]";
    for p in [
        "#a(#c(k: #a, k: #b), #d(j: #a, j: #b))",
        "#a(f: #c(k: #a, k: #b), h: #d(j: #a, j: #b))",
    ] {
        assert_eq!(
            super::errors(&format!("x = #b;\nt = x else {p} -> 0;\n")),
            [twice],
            "{p}"
        );
    }
}

#[test]
fn elaborating_from_the_checkers_findings_gives_what_elaborate_gives() {
    // The benchmarks in `bench.rs` time `elaborate_checked` on a unit checked before timing; it
    // must give the definitions and test cases `elaborate` gives, and only the checker's
    // warnings differ.
    let mut texts = vec![
        chain(3),
        nested(3),
        named(3),
        named_through_a_value(3),
        "c = 2;\nf(x) = x test { c -> c, 1 -> 1 }\n".to_string(),
        open(4),
        big_callee(3),
        differences(3),
        else_patterns(3, false),
        else_patterns(3, true),
        "f(positional x, positional k) = x * k + 1;\ng = f(2.5f64, 2);\n".to_string(),
    ];
    for shape in [
        "nested blocks",
        "a left-nested sum",
        "an `else if` chain",
        "nested negations",
        "nested calls",
    ] {
        texts.push(program(shape, 5).text);
    }
    for text in &texts {
        let (alone, whole) = (checked(text).elab(), elab(text).unwrap());
        assert_eq!(
            (&alone.defs, &alone.tests),
            (&whole.defs, &whole.tests),
            "{text}"
        );
        assert!(alone.warnings.is_empty());
    }
    // A product that may not fit in a machine word is warned by the checker's widening pass,
    // which `elaborate_checked` does not run.
    let text = "area = 3037000500 * 3037000500;\n";
    let (alone, whole) = (checked(text).elab(), elab(text).unwrap());
    assert_eq!(alone.defs, whole.defs);
    assert_eq!((alone.warnings.len(), whole.warnings.len()), (0, 1));
}
