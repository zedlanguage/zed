//! The checker at the rule of low complexity (DESIGN.md Part G). A signature search tried
//! each carrier for each untyped parameter, up to a budget, and began each run from a copy of
//! everything found so far. An untyped parameter is now a class of a union-find forest, and
//! each body is checked once.

use std::collections::BTreeMap;

use zed_kernel::types::Type as KType;
use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::{Resolved, info, sig, sig_of};

/// The units `text(m)` at `n` and `FACTOR * n`, read and resolved before the timing, so that a
/// test times the checker alone (COMPLEXITY.md F85).
pub(super) fn resolved(n: usize, text: impl Fn(usize) -> String) -> BTreeMap<usize, Resolved> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, Resolved::new(&text(m))))
        .collect()
}

#[test]
fn searching_the_signatures_of_many_functions_scales() {
    // Twenty constants for each function, each adopting its literal with no search, so that
    // what the unit has found is large beside the searches.
    let units = resolved(25, |n| {
        let mut text: String = (0..20 * n)
            .map(|j| format!("k{j} = 0.5 + {j}n;\n"))
            .collect();
        text.extend((0..n).map(|i| format!("h{i}(x) = x / {}.0;\n", i + 1)));
        text
    });
    scaling::check(
        "the signatures of n functions beside 20n constants",
        25,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(info.sigs.len(), n);
            assert_eq!(info.adopt.len(), 20 * n);
        },
    );
}

/// A function of `n` untyped parameters, all added together.
fn sum(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    format!("f({}) = {};\n", ps.join(", "), xs.join(" + "))
}

#[test]
fn a_function_of_many_untyped_parameters_scales() {
    // The search tried the product of the carriers of the parameters, 3^n, until its budget
    // of 256 combinations gave `_`. The parameters now merge into one class, once each.
    // The body is a chain of `n` additions, nested `n` deep, on a 2 MiB stack.
    zed_tests::deep::on_small_stack(|| {
        assert_eq!(sig(&sum(3), "f"), "(T, T, T) -> T for T in int | f64 | rat");
        let wide = sig(&sum(40), "f");
        assert!(wide.ends_with(") -> T for T in int | f64 | rat"), "{wide}");
        scaling::check("a function of n untyped parameters", 400, |n| {
            let (info, _) = info(&sum(n));
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
}

/// `n` functions, each calling the one before with its untyped parameter.
fn chain(n: usize) -> String {
    let mut src = "g0(positional x) = -x;\n".to_string();
    for i in 1..n {
        src += &format!("g{i}(positional x) = g{}(x) * x;\n", i - 1);
    }
    src
}

#[test]
fn a_chain_of_functions_with_untyped_parameters_scales() {
    // Each takes the bound of the one it calls, by its signature, with no search.
    assert_eq!(sig(&chain(3), "g2"), "(T) -> T for T in int | f64 | rat");
    let units = resolved(400, chain);
    scaling::check("a chain of n functions", 400, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.sigs.len(), n);
    });
}

#[test]
fn many_else_patterns_scale() {
    // Each `else` with a pattern read every binder of the unit to find its own.
    let units = resolved(1000, |n| {
        (0..n)
            .map(|i| format!("v{i} = #e(code: {i}) else #e(code:) -> code;\n"))
            .collect()
    });
    scaling::check("n bindings each with an else pattern", 1000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// A function of `n` untyped parameters that returns them all, so that its signature has `n`
/// type variables.
fn tuple(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    format!("f({}) = ({});\n", ps.join(", "), xs.join(", "))
}

#[test]
fn a_signature_of_many_type_variables_scales() {
    // Naming the variables looked for each among those named before (COMPLEXITY.md F28).
    let s = sig_of(&tuple(2), "f");
    assert_eq!(s.to_string(), "(_, _) -> (_, _)");
    assert_eq!(s.own.len(), 2, "two variables, though both print `_`");
    let units = resolved(1000, tuple);
    scaling::check("a signature of n type variables", 1000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// `n` functions, each calling the one before twice with its untyped parameter, the first
/// taking a component of it.
fn fan(n: usize) -> String {
    let mut src = "g0(positional t) = t[0];\n".to_string();
    for i in 1..n {
        let call = format!("g{}(t)", i - 1);
        src += &format!("g{i}(positional t) = {call} + {call};\n");
    }
    src
}

#[test]
fn needs_replayed_through_a_fan_of_calls_scale() {
    // Each of the two calls met the needs of the one before anew, so they doubled at each
    // function; a use met twice now gives what it gave the first time.
    let s = sig_of(&fan(3), "g2");
    assert_eq!(s.to_string(), "(_) -> U for U in int | f64 | rat");
    assert_eq!(s.needs.len(), 1, "one need, met once for both calls");
    let units = resolved(250, fan);
    scaling::check(
        "needs replayed through n functions, each calling the one before twice",
        250,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

/// `n` atoms, each with a payload of one field: of `n` names, or of one name with `n` shapes.
fn payloads(n: usize, one_name: bool) -> Vec<zedc::check::ty::Ty> {
    use zed_kernel::types::Type;
    use zedc::check::ty::{Shape, Ty};
    (0..n)
        .map(|i| {
            let name = if one_name {
                "e".to_string()
            } else {
                format!("e{i}")
            };
            let mut t = Ty::set(Type::atom_with(&name, &Type::top()));
            let shape = Shape::new(
                Vec::new(),
                [(format!("f{i}").into(), Ty::empty())]
                    .into_iter()
                    .collect(),
            );
            t.payloads.insert(name.into(), Some(vec![shape]));
            t
        })
        .collect()
}

#[test]
fn the_union_of_many_atoms_with_payloads_scales() {
    let sides: std::collections::BTreeMap<usize, (Vec<_>, Vec<_>)> = [256, scaling::FACTOR * 256]
        .into_iter()
        .map(|n| (n, (payloads(n, false), payloads(n, true))))
        .collect();
    scaling::check("the union of n atoms with payloads", 256, |n| {
        let (names, shapes) = &sides[&n];
        let u = zedc::check::ty::Ty::union_all(names);
        assert_eq!(u.payloads.len(), n);
        assert!(u.payloads.values().all(Option::is_some));
        let u = zedc::check::ty::Ty::union_all(shapes);
        assert_eq!(u.payloads["e"].as_ref().map(Vec::len), Some(n));
    });
}

/// `g(positional a0) = (a1) -> (a2) -> … -> (an) -> (a0, a1, …, an);`, `n` curried lambdas,
/// the innermost using every parameter around it.
fn curried(n: usize) -> String {
    let lambdas: String = (1..=n).map(|i| format!("(a{i}) -> ")).collect();
    let all: Vec<String> = (0..=n).map(|i| format!("a{i}")).collect();
    format!("g(positional a0) = {lambdas}({});\n", all.join(", "))
}

#[test]
fn curried_lambdas_using_every_parameter_check_in_linear_time() {
    // Each lambda names its parameter's class when it is closed. The name is kept on the
    // class, and the class variable stays in the signatures inside, which are not rewritten:
    // only `finish` writes the names, once per signature it shows. Before CHK-curried the
    // name replaced the class in every lambda inside, n - k signatures at the k-th, so the
    // time was quadratic. The facts of a signature are persistent sets shared with the
    // signatures inside (`VarFacts::held`), so merging them costs O(log n) per variable.
    assert_eq!(
        sig(&curried(3), "g"),
        "(_) -> ((_) -> ((_) -> ((_) -> (_, _, _, _))))"
    );
    let n = 100;
    let built: std::collections::BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = zed_tests::deep::statements(&curried(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, (stmts, res))
        })
        .collect();
    scaling::check_order("n curried lambdas using every parameter", n, 1, |m| {
        let (stmts, res) = &built[&m];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// `g(positional a0) = (a1) -> … -> (an) -> (a0 + 1, a1 + 1, …, an + 1);`, `n` curried
/// lambdas whose parameters each take the carrier int when their lambda ends.
fn curried_sums(n: usize) -> String {
    let lambdas: String = (1..=n).map(|i| format!("(a{i}) -> ")).collect();
    let all: Vec<String> = (0..=n).map(|i| format!("a{i} + 1")).collect();
    format!("g(positional a0) = {lambdas}({});\n", all.join(", "))
}

#[test]
fn curried_lambdas_whose_parameters_take_a_carrier_check_in_linear_time() {
    // Each lambda's parameter takes int when the lambda ends. `generalize` replaced the class
    // by int in each of the n - k lambdas inside the k-th, which hold it: n^2, 38.2 times the
    // bytes for 8 times n at ab0d3a84. Now a class solved to a type with no variable is
    // replaced outside the lambdas only, and read through the union-find inside them by the
    // comparisons and messages that read them; `finish` settles each signature once
    // (CHK-carrier, COMPLEXITY.md F77). Per node at n = 100 and 800: 274103 and 274564
    // instructions, 49621 and 49236 bytes; replaced at every depth, 798369 and 4944027
    // instructions, 101619 and 481807 bytes.
    assert_eq!(
        sig(&curried_sums(2), "g"),
        "(int) -> ((int) -> ((int) -> (int, int, int)))"
    );
    let n = 100;
    let built: std::collections::BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = zed_tests::deep::statements(&curried_sums(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, (stmts, res))
        })
        .collect();
    scaling::check_order(
        "n curried lambdas whose parameters take a carrier",
        n,
        1,
        |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

/// [`curried_sums`] with `h = g(0)` put in a tuple and tested by `is` against its written
/// type, whose `n` arrows take int.
fn curried_tested(n: usize) -> String {
    let arrows: String = (0..n).map(|_| "(int) -> (").collect();
    let ints = vec!["int"; n + 1].join(", ");
    let shut = ")".repeat(n);
    format!(
        "{}h = g(0);\nt = (h, 1);\nr = if t is (({arrows}({ints}){shut}), int) {{ 1 }} else {{ t }};\n",
        curried_sums(n)
    )
}

#[test]
fn an_is_test_of_curried_lambdas_whose_parameters_take_a_carrier_scales() {
    // `is` compares the lambdas of `t` with the written ones, reading the classes solved
    // inside them through the union-find (`Ty::diff_with`), so the `else` branch, where `t`
    // is not of the type, narrows to nothing. A tuple takes no function, so `t = (h, 1)` is
    // rejected, once. The comparison of function types recursed once per lambda, about 8
    // frames a level, and overflowed a 2 MiB stack at 800; it now keeps its frames on the
    // heap (`Comparing`, TY-sub-stack).
    let (info, _) = super::info(&curried_tested(2));
    assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    assert_eq!(info.tops["r"].to_string(), "1");
    let n = 100;
    zed_tests::deep::on_small_stack(|| {
        let built: std::collections::BTreeMap<usize, _> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| {
                let stmts = zed_tests::deep::statements(&curried_tested(m));
                let res = zedc::resolve::resolve(&stmts).unwrap();
                (m, (stmts, res))
            })
            .collect();
        scaling::check_order("an is test of n curried lambdas", n, 1, |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
        });
    });
}

#[test]
fn nested_lambdas_name_their_variables_as_before() {
    // The names a lambda takes skip those of the lambdas inside it, found from their facts.
    // Only a variable bounded by carriers is printed by name; the others are `_` (DESIGN.md
    // sec:diagnostics, PRINT-tyvars).
    for (text, want) in [
        (
            "g(positional a) = (b) -> (c) -> (a, b, c);\n",
            "(_) -> ((_) -> ((_) -> (_, _, _)))",
        ),
        (
            "g(positional a) = (b) -> (c) -> (d) -> (e) -> (f) -> (h) -> (a, b, c, d, e, f, h);\n",
            "(_) -> ((_) -> ((_) -> ((_) -> ((_) -> ((_) -> ((_) -> (_, _, _, _, _, _, _)))))))",
        ),
        (
            "g(positional a) = (T) -> (b) -> (c) -> a;\n",
            "(_) -> ((_) -> ((_) -> ((_) -> _)))",
        ),
        (
            "g(positional f) = (x) -> (y) -> f(x, y) + x;\n",
            "(_) -> ((U) -> ((_) -> U)) for U in int | f64 | rat",
        ),
        (
            "g(positional a, positional b) = ((c) -> (d) -> (c, d), a + b);\n",
            "(V, V) -> (((_) -> ((_) -> (_, _))), V) for V in int | f64 | rat",
        ),
        // The results of `h(x)` and `f(x)` are classes of `g`'s level that first appear
        // inside the lambdas, and are named in the order they appear there.
        (
            "g(positional f, positional h) = (x) -> (y) -> (h(y, x), f(x), y);\n",
            "(_, _) -> ((_) -> ((_) -> (_, _, _)))",
        ),
        (
            "g(positional f) = ((x) -> f(x), (y) -> (f(y), y));\n",
            "(_) -> (((_) -> _), ((_) -> (_, _)))",
        ),
    ] {
        assert_eq!(sig(text, "g"), want, "{text}");
    }
}

/// `curried_sums(n)` and `y = g(0)(1)…(n);`: a chain of n calls on one value, each through
/// the function the call before gives.
fn call_chain(n: usize) -> String {
    let args: String = (1..=n).map(|i| format!("({i})")).collect();
    format!("{}y = g(0){args};\n", curried_sums(n))
}

#[test]
fn a_chain_of_calls_on_one_value_checks_in_linear_time() {
    // Each call's result is a function that holds the rest of the chain. A set of functions
    // hashed each whole (`Ty::union`), and `hold` walked each result whole, so each call cost
    // the depth left: n^2. A signature's hash is now made once from those of the functions it
    // holds ([`Sig::digest`]), and `hold` reads their facts (CHK-carrier, COMPLEXITY.md F77).
    // Per node at n = 100 and 800: 413888 and 413130 instructions, 70057 and 69516 bytes;
    // before, 1076078 and 5444818 instructions, 82672 and 166976 bytes.
    let (info, _) = super::info(&call_chain(3));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.tops["y"].to_string(), "(int, int, int, int)");
    let n = 100;
    let built: std::collections::BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = zed_tests::deep::statements(&call_chain(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, (stmts, res))
        })
        .collect();
    scaling::check_order("a chain of n calls on one value", n, 1, |m| {
        let (stmts, res) = &built[&m];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// A unit whose function `q` passes its parameter, an overload of `n` arrows, to `p`, whose
/// slot is the same overload: `q`'s function has an arrow for each of `p`'s.
fn overloads(n: usize) -> String {
    let ov = (0..n)
        .map(|i| format!("((x: #a{i}) -> #b{i})"))
        .collect::<Vec<_>>()
        .join(" & ");
    format!("p(f: {ov}) = 0;\nq(g: {ov}) = p(f: g);\n")
}

#[test]
fn passing_an_overload_of_many_arrows_scales() {
    scales(
        "an overload of n arrows passed to a slot of n arrows",
        200,
        overloads,
        |unit| {
            let info = unit.check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(info.sigs.len(), 2);
        },
    );
}

/// Like [`overloads`], but each arrow of `q`'s function takes its atom or `#z`, so no arrow
/// of it equals the arrow of the slot it fits.
fn wider_overloads(n: usize) -> String {
    let ov = |wide: &str| {
        (0..n)
            .map(|i| format!("((x: #a{i}{wide}) -> #b{i})"))
            .collect::<Vec<_>>()
            .join(" & ")
    };
    format!("p(f: {}) = 0;\nq(g: {}) = p(f: g);\n", ov(""), ov(" | #z"))
}

/// An overload of n arrows passed to a slot of n other arrows: each arrow of the slot is
/// looked up by its parameter's atom in an index of the function's arrows, which gives the one
/// arrow that takes it (COMPLEXITY.md F82). Before the index each was compared with every
/// arrow of the function: 57.1 times the bytes at n = 100 and 800.
#[test]
fn passing_an_overload_to_a_slot_of_other_arrows_scales() {
    scales(
        "an overload of n arrows passed to a slot of n other arrows",
        100,
        wider_overloads,
        |unit| {
            let info = unit.check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

/// Like [`wider_overloads`], but every arrow of `q`'s function takes `#c` as well as its own
/// atom, and each arrow of the slot takes `#c` alone: every arrow of the function offers what
/// each arrow of the slot needs, and only the results tell them apart.
fn shared_overloads(n: usize) -> String {
    let ov = |param: &dyn Fn(usize) -> String| {
        (0..n)
            .map(|i| format!("((x: {}) -> #b{i})", param(i)))
            .collect::<Vec<_>>()
            .join(" & ")
    };
    format!(
        "p(f: {}) = 0;\nq(g: {}) = p(f: g);\n",
        ov(&|_| "#c".into()),
        ov(&|i| format!("#c | #a{i}"))
    )
}

/// The arrows share the piece of the parameter the slot's arrows need, so the index of arrows
/// by parameter leaves every arrow; the index by result leaves one (COMPLEXITY.md F82; the
/// parameter index alone cost n^2/2 comparisons, 57.6x at n and 8n).
#[test]
fn passing_an_overload_whose_arrows_share_a_parameter_piece_scales() {
    scales(
        "an overload of n arrows sharing a parameter piece passed to a slot of n arrows",
        100,
        shared_overloads,
        |unit| {
            let info = unit.check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

/// A unit whose function `p` has a slot written as an overload of `n` arrows nested `n` deep
/// in parentheses: resolve and the checker read each intersection once, with the one around
/// it.
fn nested_overload(n: usize) -> String {
    let arrow = |i: usize| format!("((x: #a{i}) -> #b{i})");
    let ov = (1..n).fold(arrow(0), |inner, i| format!("({inner}) & {}", arrow(i)));
    format!("p(f: {ov}) = 0;\n")
}

#[test]
fn a_slot_written_as_an_overload_nested_in_parentheses_scales() {
    // Resolution and the checker are timed, on statements parsed before the timing.
    let n = 100;
    let units: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, zed_tests::deep::statements(&nested_overload(m))))
        .collect();
    scaling::check("a slot of n arrows nested n deep in parentheses", n, |m| {
        let stmts = &units[&m];
        let res = zedc::resolve::resolve(stmts).unwrap();
        let info = zedc::check::walk::check(stmts, &res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.sigs.len(), 1);
    });
}

/// A slot `(x: #a0 | ... | #a(n-1)) -> String` and an overload of `n` arrows `(x: #ai) ->
/// String` that cover it only together: each arrow is compared once with the slot's arrow, and
/// the union of their parameter types once with its parameter (`check::ty::covered`,
/// COMPLEXITY.md F82).
fn covering_overload(n: usize) -> String {
    let slot = (0..n)
        .map(|i| format!("#a{i}"))
        .collect::<Vec<_>>()
        .join(" | ");
    let ov = (0..n)
        .map(|i| format!("((x: #a{i}) -> String)"))
        .collect::<Vec<_>>()
        .join(" & ");
    format!("p(f: (x: {slot}) -> String) = 0;\nq(g: {ov}) = p(f: g);\n")
}

#[test]
fn an_overload_of_many_arrows_that_cover_a_slot_together_scales() {
    scales(
        "an overload of n arrows covering a slot together",
        100,
        covering_overload,
        |unit| assert_eq!(unit.type_errors(), Vec::<String>::new()),
    );
}

/// A slot of `w` parameters and a function of one arrow that takes all but the last, where it
/// takes `int` and the slot passes `int | bool`: the cover compares the arrow's parameters in
/// one pass, not once for each parameter left out (`check::ty::part_of`; that cost the
/// square of the width, 38.8 times the bytes at w = 100 and 800).
fn wide_arrows(w: usize) -> String {
    let params = |last: &str| {
        (0..w)
            .map(|j| format!("x{j}: {}", if j + 1 == w { last } else { "int" }))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "p(f: ({}) -> String) = 0;\nq(g: ({}) -> String) = p(f: g);\n",
        params("int | bool"),
        params("int")
    )
}

#[test]
fn a_function_of_many_parameters_that_misses_one_scales() {
    scales(
        "an arrow of w parameters that misses the slot's last",
        100,
        wide_arrows,
        |unit| {
            let errors = unit.type_errors();
            assert_eq!(errors.len(), 1, "{errors:?}");
        },
    );
}

/// The cases of rule 6 that `check::ty::covered` builds or refuses with a reason, each at `n`
/// and `8 * n` arrows: the source of `p(f: g)` for the slot `slot` and the overload of
/// `arrows`.
fn slot_and_overload(slot: &str, arrows: impl Iterator<Item = String>) -> String {
    let ov = arrows.collect::<Vec<_>>().join(" & ");
    format!("p(f: {slot}) = 0;\nq(g: {ov}) = p(f: g);\n")
}

/// Runs `want` on the unit `text(m)` at `n` and `8 * n`, both read and resolved before either
/// is run.
fn scales(what: &str, n: usize, text: impl Fn(usize) -> String, want: impl Fn(&Resolved) + Sync) {
    let units = resolved(n, text);
    scaling::check(what, n, |m| want(&units[&m]));
}

/// The atoms `#{name}0 | ... | #{name}(n-1)`.
fn atoms(name: &str, n: usize) -> String {
    (0..n)
        .map(|i| format!("#{name}{i}"))
        .collect::<Vec<_>>()
        .join(" | ")
}

/// Case (3), built: `n` arrows `(x: #ai) -> String` within the slot's result, and `n` arrows
/// `(x: #c | #ai) -> String | #bi` outside it, each taking `#c`, what the others leave; the
/// intersection of their `n` results is `String` (`check::ty::met`).
#[test]
fn many_arrows_whose_results_intersect_within_the_slots_scale() {
    let text = |n| {
        let within = (0..n).map(|i| format!("((x: #a{i}) -> String)"));
        let outside = (0..n).map(|i| format!("((x: #c | #a{i}) -> String | #b{i})"));
        let slot = format!("(x: #c | {}) -> String", atoms("a", n));
        slot_and_overload(&slot, within.chain(outside))
    };
    scales("n arrows met and n within", 100, text, |unit| {
        assert_eq!(unit.type_errors(), Vec::<String>::new());
    });
}

/// Case (3), refused with the reason: `(x: #ai | #a(i+1)) -> String | #bi` meet in `String` at
/// each atom, but no one set of them takes every atom; the message names the `n` arrows in
/// one pass (`check::ty::refused_cover`).
#[test]
fn many_arrows_whose_results_meet_only_on_different_sets_are_refused_in_linear_time() {
    let text = |n| {
        let arrows = (0..n).map(|i| format!("((x: #a{i} | #a{}) -> String | #b{i})", i + 1));
        slot_and_overload(&format!("(x: {}) -> String", atoms("a", n + 1)), arrows)
    };
    scales(
        "n arrows whose results meet on different sets",
        400,
        text,
        |unit| {
            let errors = unit.type_errors();
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert!(
                errors[0].contains("grows with the product of their number"),
                "{errors:?}"
            );
        },
    );
}

/// Case (2), built: `n` arrows `(x: #ai) -> String` and one whose parameter is a function type,
/// which binds nothing, cover `(x: #a0 | ... | ((y: int) -> int)) -> String`
/// (`check::ty::binds_nothing`).
#[test]
fn an_overload_with_a_function_arrow_covering_a_slot_scales() {
    let text = |n| {
        let arrows = (0..n).map(|i| format!("((x: #a{i}) -> String)"));
        let fun = std::iter::once("((x: (y: int) -> int) -> String)".to_string());
        let slot = format!("(x: {} | ((y: int) -> int)) -> String", atoms("a", n));
        slot_and_overload(&slot, arrows.chain(fun))
    };
    scales(
        "n arrows and a function arrow covering",
        100,
        text,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
}

/// A bounded variable at `w` parameters, bound to `int | f64`, is refused with the count of its
/// places, found by one walk of the arrow (`check::ty::one_place`).
#[test]
fn a_bounded_variable_at_many_parameters_is_refused_in_linear_time() {
    let text = |w| {
        let params = |t: &str| {
            (0..w)
                .map(|j| format!("x{j}: {t}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        format!(
            "p(f: ({}) -> int | f64) = 0;\nq(g: ({}) -> T for T in int | f64) = p(f: g);\n",
            params("int | f64"),
            params("T")
        )
    };
    scales("a bounded variable at w parameters", 100, text, |unit| {
        let errors = unit.type_errors();
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("places the arguments give"),
            "{errors:?}"
        );
    });
}

/// The intersection built where results hold a rigid variable or a function: `n` arrows
/// `(x: T) -> T | String | #bi for T in int | f64` and one `(x: int | f64) -> String | ((y:
/// int) -> int)`, at the slot `(x: U) -> U | String for U in int | f64`. The piece `U` of each
/// result is within the slot's, and the function is in no other result; the carriers of all
/// results but one are read off a pass from each end (`check::ty::meet_within`).
#[test]
fn many_results_that_hold_a_variable_or_a_function_meet_in_linear_time() {
    let text = |n| {
        let arrows = (0..n).map(|i| format!("((x: T) -> T | String | #b{i} for T in int | f64)"));
        let fun = std::iter::once("((x: int | f64) -> String | ((y: int) -> int))".to_string());
        slot_and_overload("(x: U) -> U | String for U in int | f64", arrows.chain(fun))
    };
    scales("n results holding a variable met", 100, text, |unit| {
        assert_eq!(unit.type_errors(), Vec::<String>::new());
    });
}

/// The intersection of [`many_results_that_hold_a_variable_or_a_function_meet_in_linear_time`]
/// timed alone, on results built before the timing: `n` results `U | String | #bi`, `U`
/// bounded by `int | f64`, met within `U | String`. There the check around the intersection
/// costs about 160,000 instructions a result, so a quadratic in the results that allocates
/// nothing, such as reading the carriers of every other result for each result, passes it
/// even at 3,200 results; here it fails at 1,000 (COMPLEXITY.md F82).
#[test]
fn many_results_that_hold_a_variable_meet_in_linear_time_alone() {
    use zedc::check::ty::{Carrier, Meet};
    let n = 1000;
    let u_or_string = || Ty::var("U".into()).union(&Ty::carrier(Carrier::Str));
    let meets: BTreeMap<usize, Meet> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let results = (0..m)
                .map(|i| u_or_string().union(&Ty::set(KType::atom(&format!("b{i}")))))
                .collect();
            let bound: &[Carrier] = &[Carrier::Int, Carrier::F64];
            (m, Meet::new(results, u_or_string(), &[("U", bound)]))
        })
        .collect();
    scaling::check("n results holding a variable met alone", n, |m| {
        assert!(meets[&m].within());
    });
}

/// `f`, which destructures its parameter into `n` names and gives the last and the first, and
/// a call of it on a tuple of `n`: `n` needs of one class, each checked at the call.
fn wide_destructuring(n: usize) -> String {
    let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
    let items: Vec<String> = (0..n).map(|i| i.to_string()).collect();
    format!(
        "f(positional p) {{\n  {} = p;\n  return (a{}, a0);\n}}\ny = f(({}));\n",
        names.join(", "),
        n - 1,
        items.join(", ")
    )
}

/// `n` functions, each destructuring its parameter into a pair, each called on a pair.
fn many_destructurings(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "swap{i}(positional p) {{\n  a, b = p;\n  return (b, a);\n}}\ny{i} = swap{i}(({i}, 0));\n"
            )
        })
        .collect()
}

/// `app`, which applies its parameter `g` to each of its `n` other parameters, called with the
/// generic `id` and `n` numbers: `n` needs of `g`'s class, each naming the type variable of
/// `id` that the call leaves unbound, checked at a call that binds `2n` variables.
fn generic_applied_to_many(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("positional a{i}")).collect();
    let calls: Vec<String> = (0..n).map(|i| format!("g(a{i})")).collect();
    let args: Vec<String> = (0..n).map(|i| i.to_string()).collect();
    format!(
        "id(positional x) = x;\napp(positional g, {}) = ({});\ny = app(id, {});\n",
        params.join(", "),
        calls.join(", "),
        args.join(", ")
    )
}

#[test]
fn needs_that_name_a_variable_the_call_leaves_unbound_check_in_linear_time() {
    let (info, _) = info(&generic_applied_to_many(3));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.tops["y"].to_string(), "(0, 1, 2)");
    // At n = 200 the scan of every bound variable at each signature (`Ty::replace_in`) gave
    // 19.2 times the instructions, inside the limit; at n = 400 it gave 26.5 times.
    scales(
        "a generic function applied to n parameters",
        400,
        generic_applied_to_many,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
}

#[test]
fn destructured_parameters_check_in_linear_time() {
    let (info, _) = info(&wide_destructuring(3));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.tops["y"].to_string(), "(2, 0)");
    scales(
        "a parameter destructured into n names",
        200,
        wide_destructuring,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
    scales(
        "n parameters each destructured into two names",
        100,
        many_destructurings,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
}

/// The variables named `{prefix}0` to `{prefix}(m-1)`, for `m` of `n` and `FACTOR * n`, made
/// before the timing.
fn variables(prefix: &str, n: usize) -> BTreeMap<usize, Vec<Ty>> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let vs = (0..m).map(|i| Ty::var(format!("{prefix}{i}").into()));
            (m, vs.collect())
        })
        .collect()
}

/// `n` rows `t(k) = (t(k-1), (t(k-1), Vk))`: each row merges the variables of its two
/// components, `k` and `k + 1` of them, the second set made from the first by adding `Vk`
/// (ROW-made-cost). Inserting each variable of the smaller set cost `O(k log k)` a row, and
/// took 70.6 times the instructions at 2,000 against 250; `Row::made` now also steps over the
/// nodes the two sets share (`check::ty::merge`), 10.0 times (COMPLEXITY.md F93).
#[test]
fn rows_made_from_overlapping_variable_sets_scale() {
    let n = 250;
    let vars = variables("V", n);
    scaling::check_order("n rows of overlapping variable sets", n, 1, |m| {
        let vs = &vars[&m];
        let t = vs[1..].iter().fold(vs[0].clone(), |s, v| {
            Ty::tuple(vec![s.clone(), Ty::tuple(vec![s, v.clone()])])
        });
        assert_eq!(t.var_facts().names.len(), m);
    });
}

/// `n` rows `z(k) = (x(k), y(k))`, with `x(k) = (x(k-1), Ak)` and `y(k) = (y(k-1), Bk)`: each
/// `z(k)` holds a set of `2k` variables no other row holds, made from two sets that share no
/// node, so `Row::made` costs `O(n^2 log n)` here (71.2 times the instructions and 39.4 times
/// the bytes at 2,000 against 250). Keeping a set for each row is the transitive closure of a
/// DAG; open for the author, question A8 (COMPLEXITY.md F93).
#[test]
#[ignore = "O(n^2 log n), open until the author answers question A8: COMPLEXITY.md F93, ROW-made-cost"]
fn rows_made_from_disjoint_variable_sets_scale() {
    let n = 250;
    let (xs, ys) = (variables("A", n), variables("B", n));
    scaling::check_order("n rows of disjoint variable sets", n, 1, |m| {
        let (a, b) = (&xs[&m], &ys[&m]);
        let (mut x, mut y) = (a[0].clone(), b[0].clone());
        let mut zs = Vec::with_capacity(m);
        for (a, b) in a[1..].iter().zip(&b[1..]) {
            x = Ty::tuple(vec![x, a.clone()]);
            y = Ty::tuple(vec![y, b.clone()]);
            zs.push(Ty::tuple(vec![x.clone(), y.clone()]));
        }
        assert_eq!(zs.last().map(|z| z.var_facts().names.len()), Some(2 * m));
    });
}

/// `p(s, v) = (s, (s, v))` applied `n` times, `f(a0, ..., an) = p(p(p(a0, a1), a2), ...)`, and,
/// if `call`, `f` called on `0, ..., n`: the type of each `p` holds the row of the one inside
/// twice, so the result's type has `2^n` paths through `n` rows (REPLACE-shared-rows).
fn shared_rows(n: usize, call: bool) -> String {
    let params: Vec<String> = (0..=n).map(|i| format!("positional a{i}")).collect();
    let body = (1..=n).fold("a0".to_string(), |s, i| format!("p({s}, a{i})"));
    let mut text = format!(
        "p(positional s, positional v) = (s, (s, v));\nf({}) = {body};\n",
        params.join(", ")
    );
    if call {
        let args: Vec<String> = (0..=n).map(|i| i.to_string()).collect();
        text.push_str(&format!("y = f({});\n", args.join(", ")));
    }
    text
}

#[test]
fn rows_shared_on_many_paths_are_replaced_once() {
    let (info, _) = info(&shared_rows(2, true));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(
        info.tops["y"].to_string(),
        "((0, (0, 1)), ((0, (0, 1)), 2))"
    );
    assert_eq!(
        sig(&shared_rows(2, false), "f"),
        "(_, _, _) -> ((_, (_, _)), ((_, (_, _)), _))"
    );
}

/// `n` rows `t(k) = (t(k-1), (t(k-1), Vk))`, `2^n` paths, with each `Vk` replaced by `Wk`:
/// `Ty::replace`, `Ty::subst` and `Ty::settle` each make a row once, however many paths reach
/// it (REPLACE-shared-rows, COMPLEXITY.md F97). Each walked every path before: 2^n.
#[test]
fn replacing_in_rows_shared_on_many_paths_scales() {
    let n = 100;
    let (vs, ws) = (variables("V", n), variables("W", n));
    let binds = |m: usize| -> zedc::check::ty::Binds {
        let pairs = vs[&m].iter().zip(&ws[&m]);
        (pairs.map(|(v, w)| (v.vars.first().cloned().unwrap(), w.clone()))).collect()
    };
    let binds: BTreeMap<_, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, binds(m)))
        .collect();
    // Built before timing, so the runs time the walks alone.
    let shared: BTreeMap<_, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let vs = &vs[&m];
            let t = vs[1..].iter().fold(vs[0].clone(), |s, v| {
                Ty::tuple(vec![s.clone(), Ty::tuple(vec![s, v.clone()])])
            });
            (m, t)
        })
        .collect();
    let replaced = |t: &Ty, m: usize| {
        let f = t.var_facts();
        assert_eq!(f.names.len() + f.classes.len(), m);
        assert!(f.names.iter().chain(&f.classes).all(|v| v.starts_with('W')));
    };
    scaling::check("Ty::replace in n shared rows", n, |m| {
        replaced(&shared[&m].replace(&binds[&m]), m)
    });
    scaling::check("Ty::subst in n shared rows", n, |m| {
        replaced(&shared[&m].subst(&binds[&m]), m)
    });
    scaling::check("Ty::settle in n shared rows", n, |m| {
        let b = &binds[&m];
        replaced(&shared[&m].settle(&|v: &str| b.get(v).cloned()), m)
    });
}

/// `n` functions `(Oi) -> (Oi, Hi)`, each holding the one variable `Hi` and owning `Oi`, with
/// all `2n` variables bound: each function keeps its own `Oi` and replaces `Hi`, looked up for
/// the variables it holds, not by a copy of the `2n` binds less its own (O(n^2) in all;
/// REPLACE-shared-rows, COMPLEXITY.md F97).
#[test]
fn replacing_in_many_functions_that_each_hold_one_bound_variable_scales() {
    use std::sync::Arc;
    use zedc::check::ty::{Arrow, Facts, Sig};
    let n = 250;
    let (os, hs, ws) = (variables("O", n), variables("H", n), variables("W", n));
    let name = |t: &Ty| t.vars.first().cloned().unwrap();
    let made = |m: usize| {
        let fns = (os[&m].iter().zip(&hs[&m])).map(|(o, h)| {
            Arc::new(Sig {
                arrows: vec![Arrow {
                    params: vec![o.clone()],
                    result: Ty::tuple(vec![o.clone(), h.clone()]),
                }],
                own: [name(o)].into(),
                held: [name(h)].into(),
                params: Vec::new(),
                bounds: BTreeMap::new(),
                data: false,
                word: None,
                needs: Vec::new(),
                named: 0,
                facts: Facts::default(),
            })
        });
        let binds: zedc::check::ty::Binds = (os[&m].iter().zip(&ws[&m]))
            .chain(hs[&m].iter().zip(&ws[&m]))
            .map(|(v, w)| (name(v), w.clone()))
            .collect();
        (
            Ty {
                fns: fns.collect(),
                ..Ty::empty()
            },
            binds,
        )
    };
    let made: BTreeMap<_, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, made(m)))
        .collect();
    scaling::check(
        "n functions each holding one of 2n bound variables",
        n,
        |m| {
            let (t, binds) = &made[&m];
            let out = t.replace(binds);
            for (s, (o, w)) in out.fns.iter().zip(os[&m].iter().zip(&ws[&m])) {
                assert_eq!(s.arrows[0].result, Ty::tuple(vec![o.clone(), w.clone()]));
            }
        },
    );
}

/// The program family checks with no walk that follows each of its `2^n` paths; it is of
/// order `n^2`, not `n`, because each call `p(s, v)` replays its data need on `s`, a type of
/// `k` rows at the `k`th call (`Ck::data`): open, COMPLEXITY.md F97. This O(n^2) awaits the
/// author's approval, question A20; it is not approved. The test measures the cost as it is
/// now, so that the `2^n` paths do not return unseen; power 2 here is not a claim that O(n^2)
/// is acceptable, and the fix of A20 lowers it to 1.
#[test]
fn rows_shared_on_many_paths_scale_as_n_squared() {
    for (what, call) in [("a function of n shared rows", false), ("its call", true)] {
        let units = resolved(25, |n| shared_rows(n, call));
        scaling::check_order(what, 25, 2, |m| {
            assert_eq!(units[&m].type_errors(), Vec::<String>::new());
        });
    }
}

/// `r(positional line, bump = 1) = { a1 = (line else 0) + bump; a2 = (line else a1) + bump;
/// … an }`: each sum meets the parameter's class beside an int on one path and an int alone
/// on another, so each keeps two states where it kept one (ISSUE1-tvar-else).
fn sums_of_a_line_or_a_count(n: usize) -> String {
    let steps: String = (1..=n)
        .map(|i| {
            format!(
                "a{i} = (line else {}) + bump; ",
                if i == 1 {
                    "0".into()
                } else {
                    format!("a{}", i - 1)
                }
            )
        })
        .collect();
    format!("r(positional line, bump = 1) = {{ {steps}a{n} }};\n")
}

#[test]
fn sums_of_a_line_or_a_count_check_in_linear_time() {
    assert_eq!(
        sig(&sums_of_a_line_or_a_count(3), "r"),
        "(int | #_, bump: int) -> int"
    );
    let units = resolved(250, sums_of_a_line_or_a_count);
    scaling::check_order("n sums of a line or a count", 250, 1, |m| {
        assert_eq!(units[&m].type_errors(), Vec::<String>::new());
    });
}

/// `f(positional x: int) = if x > 2n { 0 } else if x > 2n - 1 { 1 } … else if x > 0 && x < 0
/// { n } else { n + 1 }`, with every other test made unreachable by those before it, nested `n`
/// deep: each `if` with a comparison computes the scopes of its arms to find which no value
/// reaches, where before only a read of an int under them did (EMPTY-bottom-arm).
fn a_chain_of_tests(n: usize) -> String {
    let mut text = String::from("f(positional x: int) = ");
    for i in 0..n {
        // The odd tests ask for more than the test before them failed to give.
        let bound = if i % 2 == 0 { 2 * n - i } else { 2 * n + i };
        text.push_str(&format!("if x > {bound} {{ {i} }} else "));
    }
    text.push_str(&format!(
        "if x > 0 && x < 0 {{ {n} }} else {{ {} }};\n",
        n + 1
    ));
    text
}

#[test]
fn a_chain_of_tests_is_linear_in_its_length() {
    assert_eq!(sig(&a_chain_of_tests(4), "f"), "(int) -> 0 | 2 | 5");
    let units = resolved(64, a_chain_of_tests);
    scaling::check("a chain of n tests on one int", 64, |m| {
        let info = units[&m].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
