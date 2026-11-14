//! MSG-overload-false-cycle: a call of an overload set waits, in the order of a scope's
//! definitions, on the overloads its arguments can select, not on every overload of the name.
//! Before, `f(positional n: int) = n; f(positional s: bool) = f(1);` was rejected as recursion
//! of `f`, though `f(1)` runs the `int` overload only.
//!
//! DESIGN.md sec:type_resolution, rule 1: "Each node's type is computed from its inputs' types
//! by the operator's arrow set (selecting arrows by input-region intersection). Because the
//! graph is acyclic (recursion and generations are region-fenced, see rule 5), inference is a
//! topological pass, not unification search." Rule 6: "If no arrow applies, that is the error
//! [...] Which *implementation* runs is equally fixed: of the applicable arrows, drop each one
//! that another applicable arrow is strictly more specific than, and run the earliest declared
//! of those left". The dependency theorem, proof of (1): "Overload dispatch over a union-typed
//! argument selects the arrow per region of the argument's type (rule 6 of
//! sec:type_resolution), a choice among arms that are all in `G(P)`." Proof of (2a):
//! "Elaboration builds, in each scope, the graph of definitions and their references, and
//! takes its strongly connected components. A component with more than one definition, or a
//! single definition that refers to itself, is recursion".
//!
//! So a call refers to the overloads it can run. When the arguments admit exactly one, the call
//! refers to it, and recursion through it is reported, naming each overload by its written head.
//! When two or more are applicable, which one runs is fixed by type checking (step L2.6), and
//! until then the call refers to none of them; this zedc rejects such a call, since it does not
//! yet choose among definitions that share a name.

use super::rejected;
use zedc::resolve::tables::Tables;

const NOT_YET: &str = ": this version of zedc does not compile it yet.";

/// The rejection of a call of an overload set, which this zedc does not compile yet.
fn no_dispatch(at: &str) -> String {
    format!(
        "{at}: `f` names 2 definitions, and this version of zedc does not yet choose among \
         definitions that share a name. Give each of them a name of its own."
    )
}

/// The first lines of the diagnostics `out`, one for each error.
fn heads(out: &str) -> Vec<&str> {
    out.lines().filter(|l| !l.starts_with(' ')).collect()
}

/// The reported case: the `bool` overload calls `f(1)`, which runs the `int` overload, so there
/// is no cycle; the only errors are the calls this zedc cannot dispatch yet.
#[test]
fn a_call_that_selects_another_overload_is_no_recursion() {
    let out =
        rejected("f(positional n: int) = n;\nf(positional s: bool) = f(1);\nmain = f(true);\n");
    assert_eq!(
        heads(&out),
        [no_dispatch("2:25"), no_dispatch("3:8")],
        "{out}"
    );
}

/// The same with the two declarations in the other order.
#[test]
fn a_call_that_selects_another_overload_is_no_recursion_in_either_order() {
    let out =
        rejected("f(positional s: bool) = f(1);\nf(positional n: int) = n;\nmain = f(true);\n");
    assert_eq!(
        heads(&out),
        [no_dispatch("1:25"), no_dispatch("3:8")],
        "{out}"
    );
}

/// A named argument selects the overload that has a parameter of that name: `f(x: k)` runs
/// `f(x: int)`, the one parameter of which takes its argument by name.
#[test]
fn a_named_argument_selects_its_overload() {
    let out = rejected("f(x: int) = x;\nf(b: bool, k: int) = f(x: k);\nmain = 0;\n");
    assert_eq!(heads(&out), [no_dispatch("2:22")], "{out}");
}

/// `k.f` is the call `f(k)`, the receiver its first argument, so it runs the `int` overload.
#[test]
fn a_member_call_selects_by_its_receiver() {
    let out = rejected(
        "f(positional n: int) = n;\nf(positional b: bool, positional k: int) = k.f;\nmain = 0;\n",
    );
    assert_eq!(heads(&out), [no_dispatch("2:44")], "{out}");
}

/// An overload that calls itself is still recursion, named by its written head.
#[test]
fn an_overload_that_calls_itself_is_recursion() {
    let out = rejected("f(positional n: int) = f(n);\nf(positional s: bool) = 0;\nmain = 1;\n");
    assert_eq!(
        out,
        format!(
            "1:1: `f(positional n: int)` is defined in terms of itself, which is recursion\
             {NOT_YET}\n  \
             [1] 1:24: `f(positional n: int)` uses itself here\n      \
             1 | f(positional n: int) = f(n);\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]\n        \
             |                        ^ [1]\n  \
             [2] 1:1: repair: remove the use shown, which ends the cycle"
        )
    );
}

/// The same through a member call, `n.f`, the call `f(n)`.
#[test]
fn an_overload_that_calls_itself_as_a_member_is_recursion() {
    let out = rejected("f(positional n: int) = n.f;\nf(positional b: bool) = 0;\nmain = 0;\n");
    assert_eq!(
        heads(&out),
        [format!(
            "1:1: `f(positional n: int)` is defined in terms of itself, which is recursion\
             {NOT_YET}"
        )],
        "{out}"
    );
    assert!(
        out.contains("[1] 1:24: `f(positional n: int)` uses itself here"),
        "{out}"
    );
}

/// Two overloads that call each other with arguments that select each other: `f(n > 0)` runs
/// the `bool` overload and `f(1)` the `int` one.
#[test]
fn two_overloads_that_call_each_other_are_recursion() {
    let out =
        rejected("f(positional n: int) = f(n > 0);\nf(positional b: bool) = f(1);\nmain = 1;\n");
    assert_eq!(
        out,
        format!(
            "1:1: `f(positional n: int)`, `f(positional b: bool)` are defined in terms of each \
             other, which is recursion{NOT_YET}\n  \
             [1] 1:24: `f(positional n: int)` uses `f(positional b: bool)` here\n      \
             1 | f(positional n: int) = f(n > 0);\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [3]\n        \
             |                        ^ [1]\n  \
             [2] 2:25: `f(positional b: bool)` uses `f(positional n: int)` here\n      \
             2 | f(positional b: bool) = f(1);\n        \
             |                         ^\n  \
             [3] 1:1: repair: remove one of the uses shown, which ends the cycle"
        )
    );
}

/// The same by named arguments.
#[test]
fn two_overloads_that_call_each_other_by_name_are_recursion() {
    let out = rejected("f(x: int) = f(b: true, k: x);\nf(b: bool, k: int) = f(x: k);\nmain = 0;\n");
    assert_eq!(
        heads(&out),
        [format!(
            "1:1: `f(x: int)`, `f(b: bool, k: int)` are defined in terms of each other, which \
             is recursion{NOT_YET}"
        )],
        "{out}"
    );
}

/// A parameter with a written type selects by that type: `g`'s `c` is a `bool`, so `f(c)`
/// runs the `bool` overload, which calls `g`.
#[test]
fn a_typed_parameter_selects_its_overload_through_another_function() {
    let out = rejected(
        "f(positional n: int) = n;\nf(positional b: bool) = g(b);\ng(positional c: bool) = f(c);\nmain = 0;\n",
    );
    assert_eq!(
        out,
        format!(
            "2:1: `f(positional b: bool)`, `g` are defined in terms of each other, which is \
             recursion{NOT_YET}\n  \
             [1] 2:25: `f(positional b: bool)` uses `g` here\n      \
             2 | f(positional b: bool) = g(b);\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [3]\n        \
             |                         ^ [1]\n  \
             [2] 3:25: `g` uses `f(positional b: bool)` here\n      \
             3 | g(positional c: bool) = f(c);\n        \
             |                         ^\n  \
             [3] 2:1: repair: remove one of the uses shown, which ends the cycle"
        )
    );
}

/// `f(1)` with an `int` and an `f64` overload: the literal may take either carrier (rule 2, "a
/// numeric literal takes the carrier expected"), so both are applicable and rule 6 chooses
/// between them in type checking, step L2.6. Until then the call refers to neither, in both
/// orders of the declarations, and this zedc rejects the call as one it cannot dispatch yet.
#[test]
fn a_call_that_only_type_checking_can_dispatch_refers_to_no_overload() {
    for src in [
        "f(positional n: int) = n;\nf(positional x: f64) = f(1);\nmain = 1;\n",
        "f(positional x: f64) = f(1);\nf(positional n: int) = n;\nmain = 1;\n",
    ] {
        let out = rejected(src);
        let at = if src.starts_with("f(positional n") {
            "2:24"
        } else {
            "1:24"
        };
        assert_eq!(heads(&out), [no_dispatch(at)], "{out}");
    }
}

/// An argument no overload takes, here a loose atom, selects none (rule 6: "a *loose* atom
/// operand selects no arrow and passes through"), so it is no use of the calling overload.
#[test]
fn an_argument_no_overload_takes_refers_to_no_overload() {
    let out = rejected("f(positional n: int) = n;\nf(positional b: bool) = f(#none);\nmain = 0;\n");
    assert_eq!(heads(&out), [no_dispatch("2:25")], "{out}");
}

/// The set passed as a value, `h = f`, refers to every overload, so an overload that reads `h`
/// is in a cycle with it.
#[test]
fn an_overload_set_passed_as_a_value_refers_to_every_overload() {
    let out =
        rejected("f(positional n: int) = n;\nf(positional b: bool) = h(1);\nh = f;\nmain = 0;\n");
    assert_eq!(
        heads(&out),
        [format!(
            "2:1: `f(positional b: bool)`, `h` are defined in terms of each other, which is \
             recursion{NOT_YET}"
        )],
        "{out}"
    );
    assert!(
        out.contains("[2] 3:5: `h` uses `f(positional b: bool)` here"),
        "{out}"
    );
}

/// The resolved unit of `text`.
fn resolved(text: &str) -> (Vec<zedc::ast::Stmt>, zedc::resolve::Resolution) {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap_or_else(|e| panic!("{e:?}"));
    (stmts, res)
}

/// A unit's text, statements and resolution.
pub(super) type Resolved = (
    String,
    Vec<zedc::ast::Stmt>,
    zedc::resolve::Resolution,
);

/// A chain of `n` overloads, each calling the next by its parameter's name, the last the
/// first, resolved.
pub(super) fn a_cycle_of_overloads(n: usize) -> Resolved {
    let text: String = (0..n)
        .map(|i| format!("f(p{i}: int | #t{i}) = f(p{}: 1);\n", (i + 1) % n))
        .collect();
    let (stmts, res) = resolved(&text);
    (text, stmts, res)
}

/// The cycle of [`a_cycle_of_overloads`]`(n)` is one cycle of `n` overloads, reported with a
/// note for each and one more.
pub(super) fn the_cycle_of_overloads_reported((text, stmts, res): &Resolved, n: usize) {
    let tables = Tables::with_text(stmts, res, Some(text));
    let items: Vec<_> = stmts.iter().collect();
    let (_, cycles) = tables.order_around_cycles(&items);
    assert_eq!(cycles.len(), 1);
    assert_eq!(cycles[0].len(), n);
    let reports = tables.cycle_reports(&items, &cycles);
    assert_eq!(reports[0].notes.len(), n + 1);
}

#[test]
fn a_cycle_through_many_overloads() {
    for n in [2, 3, 9] {
        the_cycle_of_overloads_reported(&a_cycle_of_overloads(n), n);
    }
}

/// `n` overloads and `n` definitions each calling one of them, and `n` calls that two or more
/// overloads admit, resolved.
pub(super) fn calls_of_overloads(n: usize) -> Resolved {
    let mut text: String = (0..n)
        .map(|i| format!("f(positional a: int, p{i}: int | #t{i} = 0) = a;\n"))
        .collect();
    for i in 0..n {
        text.push_str(&format!("g{i} = f(1, p{i}: 2);\nh{i} = f(1);\n"));
    }
    let (stmts, res) = resolved(&text);
    (text, stmts, res)
}

/// The `3n` items of [`calls_of_overloads`]`(n)` are ordered with no cycle.
pub(super) fn the_calls_of_overloads_ordered((text, stmts, res): &Resolved, n: usize) {
    let tables = Tables::with_text(stmts, res, Some(text));
    let items: Vec<_> = stmts.iter().collect();
    let order = tables.order(&items).expect("no cycle");
    assert_eq!(order.len(), 3 * n);
}

#[test]
fn calls_of_many_overloads() {
    for n in [1, 2, 9] {
        the_calls_of_overloads_ordered(&calls_of_overloads(n), n);
    }
}
