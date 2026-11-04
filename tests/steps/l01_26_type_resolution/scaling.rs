//! The checker at the rule of low complexity (DESIGN.md Part G). A signature search tried
//! each carrier for each untyped parameter, up to a budget, and began each run from a copy of
//! everything found so far. An untyped parameter is now a class of a union-find forest, and
//! each body is checked once.

use zed_kernel::types::Type as KType;
use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::{info, sig, sig_of, type_errors};

#[test]
fn searching_the_signatures_of_many_functions_scales() {
    // Twenty constants for each function, each adopting its literal with no search, so that
    // what the unit has found is large beside the searches.
    scaling::check(
        "the signatures of n functions beside 20n constants",
        25,
        |n| {
            let mut text: String = (0..20 * n)
                .map(|j| format!("k{j} = 0.5 + {j};\n"))
                .collect();
            text.extend((0..n).map(|i| format!("h{i}(x) = x / {};\n", i + 1)));
            let (info, _) = info(&text);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(info.sigs.len(), n);
            assert_eq!(info.adopt.len(), 21 * n);
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
    // The body is a chain of `n` additions, nested `n` deep.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(sig(&sum(3), "f"), "(T, T, T) -> T for T in int | f64 | rat");
            let wide = sig(&sum(40), "f");
            assert!(wide.ends_with(") -> T for T in int | f64 | rat"), "{wide}");
            scaling::check("a function of n untyped parameters", 400, |n| {
                let (info, _) = info(&sum(n));
                assert!(info.errors.is_empty(), "{:?}", info.errors);
            });
        })
        .unwrap()
        .join()
        .unwrap();
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
    scaling::check("a chain of n functions", 400, |n| {
        let (info, _) = info(&chain(n));
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.sigs.len(), n);
    });
}

#[test]
fn many_else_patterns_scale() {
    // Each `else` with a pattern read every binder of the unit to find its own.
    scaling::check("n bindings each with an else pattern", 1000, |n| {
        let text: String = (0..n)
            .map(|i| format!("v{i} = #e(code: {i}) else #e(code:) -> code;\n"))
            .collect();
        let (info, _) = info(&text);
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
    scaling::check("a signature of n type variables", 1000, |n| {
        let (info, _) = info(&tuple(n));
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

/// The texts of [`fan`] at `n` and `FACTOR * n`, built before the timing.
fn fans(n: usize) -> std::collections::BTreeMap<usize, String> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, fan(m)))
        .collect()
}

#[test]
fn needs_replayed_through_a_fan_of_calls_scale() {
    // Each of the two calls met the needs of the one before anew, so they doubled at each
    // function; a use met twice now gives what it gave the first time.
    let s = sig_of(&fan(3), "g2");
    assert_eq!(s.to_string(), "(_) -> U for U in int | f64 | rat");
    assert_eq!(s.needs.len(), 1, "one need, met once for both calls");
    let texts = fans(250);
    scaling::check(
        "needs replayed through n functions, each calling the one before twice",
        250,
        |n| {
            let (info, _) = info(&texts[&n]);
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
            let shape = Shape {
                items: Vec::new(),
                fields: [(format!("f{i}").into(), Ty::empty())]
                    .into_iter()
                    .collect(),
            };
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

/// Checks each program of `shapes` on a 2 MiB stack, `n` deep and `8n` deep, and checks the
/// time is linear. The checker recursed once per level of nesting, and overflowed this stack
/// at 1,000 deep (sums, blocks, negations, calls) or below 4,000 (`else if` chains).
fn checks_deep(shapes: &[&str], n: usize) {
    use zed_tests::deep::{on_small_stack, program, statements};
    on_small_stack(|| {
        for &shape in shapes {
            let small = statements(&program(shape, n).text);
            let large = statements(&program(shape, 8 * n).text);
            let small_res = zedc::resolve::resolve(&small).unwrap();
            let large_res = zedc::resolve::resolve(&large).unwrap();
            scaling::check_order(&format!("checking {shape}"), n, 1, |k| {
                let (stmts, res) = if k == n {
                    (&small, &small_res)
                } else {
                    (&large, &large_res)
                };
                let info = zedc::check::check(stmts, res);
                assert!(info.errors.is_empty(), "{shape}: {:?}", info.errors);
            });
        }
    });
}

#[test]
fn blocks_nested_100000_deep_check_on_a_2_mib_stack() {
    checks_deep(&["nested blocks"], 12_500);
}

// The shapes below cost about a million instructions for each `+` and a third of that for each
// negation, branch or call, in the kernel's type algebra (`Type::new`, `Type::zip`, `Lits`),
// before and after the walk moved to a heap stack. The checker built the scalar types and
// their meets anew at each node; they are now made once and read off one split
// (CHK-node-cost), and a `+` costs about 140,000 instructions, a negation or call about 70,000
// to 80,000. They are checked 8,000 deep, eight times past the depth that overflowed.

#[test]
fn sums_8000_deep_check_on_a_2_mib_stack() {
    checks_deep(&["a left-nested sum", "a sum nested in parentheses"], 1_000);
}

#[test]
fn long_bodies_and_else_if_chains_8000_deep_check_on_a_2_mib_stack() {
    checks_deep(
        &["a long sum in a function's body", "an `else if` chain"],
        1_000,
    );
}

#[test]
fn negations_and_calls_8000_deep_check_on_a_2_mib_stack() {
    checks_deep(&["nested negations", "nested calls"], 1_000);
}

/// Checks the program of `shape` 1,000 deep on a 2 MiB stack, then `n` and `8n` deep and
/// checks the time is linear, on a 512 MiB stack: printing a type recurses on its nesting
/// (`Ty::write`, for the text of each binding's origin), and overflows 2 MiB below 8,000 deep.
fn checks_linear(shape: &str, n: usize) {
    use zed_tests::deep::{on_small_stack, program, statements};
    let stmts = statements(&program(shape, 1_000).text);
    let res = zedc::resolve::resolve(&stmts).unwrap();
    on_small_stack(|| assert!(zedc::check::check(&stmts, &res).errors.is_empty()));
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(1 << 29);
        thread
            .spawn_scoped(scope, || {
                let small = statements(&program(shape, n).text);
                let large = statements(&program(shape, 8 * n).text);
                let small_res = zedc::resolve::resolve(&small).unwrap();
                let large_res = zedc::resolve::resolve(&large).unwrap();
                scaling::check_order(&format!("checking {shape}"), n, 1, |k| {
                    let (stmts, res) = if k == n {
                        (&small, &small_res)
                    } else {
                        (&large, &large_res)
                    };
                    let info = zedc::check::check(stmts, res);
                    assert!(info.errors.is_empty(), "{shape}: {:?}", info.errors);
                });
            })
            .unwrap()
            .join()
            .unwrap()
    });
}

#[test]
fn lambdas_nested_8000_deep_check_in_linear_time() {
    // Each lambda's signature was walked again, copied and dropped by each lambda around it,
    // to name its variables and to replace the classes it was solved to, so the time was
    // quadratic, and `Ty::replace` overflowed a 2 MiB stack near 4,000 deep. A signature held
    // in a type now keeps the variables it holds (`Sig::facts`, CHK-lambda), and one that
    // holds none of those replaced is shared whole.
    checks_linear("nested lambdas", 1_000);
}

#[test]
fn tuples_nested_8000_deep_check_in_linear_time() {
    // Whether a tuple's components may hold a variable, the unknown or a function was found by
    // a walk of the components at each level, so the time grew as n^2 and more (CHK-tuple). A
    // tuple shape now keeps those facts (`ty::Row`).
    checks_linear("nested tuples", 1_000);
}

/// `f(positional x) = ((… (x, 1) …, 1), 1);`, a variable `n` tuples deep.
fn nested_around(n: usize) -> String {
    format!(
        "f(positional x) = {}x{};\n",
        "(".repeat(n),
        ", 1)".repeat(n)
    )
}

#[test]
fn a_variable_nested_in_tuples_checks_in_linear_time() {
    assert_eq!(sig(&nested_around(2), "f"), "(_) -> ((_, 1), 1)");
    let texts: std::collections::BTreeMap<usize, String> = [500, scaling::FACTOR * 500]
        .into_iter()
        .map(|m| (m, nested_around(m)))
        .collect();
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(move || {
            scaling::check_order("a variable nested in n tuples", 500, 1, |n| {
                let (info, _) = info(&texts[&n]);
                assert!(info.errors.is_empty(), "{:?}", info.errors);
            });
        })
        .unwrap()
        .join()
        .unwrap();
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
    scaling::on_a_thread(1 << 29, || {
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
            let info = zedc::check::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
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
    scaling::on_a_thread(1 << 29, || {
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
                let info = zedc::check::check(stmts, res);
                assert!(info.errors.is_empty(), "{:?}", info.errors);
            },
        );
    });
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
    // rejected, once.
    let (info, _) = super::info(&curried_tested(2));
    assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    assert_eq!(info.tops["r"].to_string(), "1");
    let n = 100;
    scaling::on_a_thread(1 << 29, || {
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
            let info = zedc::check::check(stmts, res);
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

/// `x = bitAnd(bitAnd(… bitAnd(1, 1) …, 1), 1);`, `n` calls of the bit word nested.
fn bit_words(n: usize) -> String {
    format!("x = {}1{};\n", "bitAnd(".repeat(n), ", 1)".repeat(n))
}

#[test]
fn bit_words_8000_deep_check_on_a_2_mib_stack() {
    // A bit word's arguments are checked from the walk's frame `Bits`, so the nesting keeps
    // no frame of the thread's stack per call. Checked by a recursive call per argument, this
    // overflowed the stack below 1,000 deep. 1,000,000 deep does not fit the 60 s limit of a
    // test: measured at 100,000 deep (linear from 12,500), parsing takes 10 s and checking
    // 16 s, about 100 us and 160 us a call, the checker's in the kernel's type algebra as for
    // the calls above; 1,000,000 deep would take about 100 s to parse and 160 s to check.
    use zed_tests::deep::{on_small_stack, statements};
    let n = 1_000;
    let small = statements(&bit_words(n));
    let large = statements(&bit_words(8 * n));
    let small_res = zedc::resolve::resolve(&small).unwrap();
    let large_res = zedc::resolve::resolve(&large).unwrap();
    on_small_stack(|| {
        scaling::check_order("checking nested bit words", n, 1, |k| {
            let (stmts, res) = if k == n {
                (&small, &small_res)
            } else {
                (&large, &large_res)
            };
            let info = zedc::check::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
}

/// A function whose undeclared parameter `line` is tested against `n` atoms, each test bound
/// to a name, then trimmed.
fn tests_of_atoms(n: usize) -> String {
    let tests: String = (0..n).map(|i| format!("b{i} = line is #a{i}; ")).collect();
    format!("r(positional line) = {{ {tests}trim(line) }};\n")
}

#[test]
fn a_parameter_tested_against_many_atoms_scales() {
    // Each test adds its atom to the parameter's set, the small set into the large one.
    let (i, _) = info(&tests_of_atoms(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    // The atoms `trim` passes by reach the result, so the second arrow takes them; the first,
    // for a parameter with none, gives none.
    let arrows = i.sigs.values().next().unwrap().expand();
    assert_eq!(arrows.len(), 2);
    assert!(arrows[0].params[0].atoms().is_empty());
    assert!(!arrows[1].params[0].atoms().is_empty());
    scaling::check("a parameter tested against n atoms", 400, |n| {
        let (info, _) = info(&tests_of_atoms(n));
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// A function whose undeclared parameter `line` is bound to `n` names in a chain, written
/// last first, each tested against an atom of its own, the last trimmed.
fn chain_of_names(n: usize) -> String {
    let names: String = (1..n)
        .rev()
        .map(|i| format!("s{i} = s{}; b{i} = s{i} is #a{i}; ", i - 1))
        .collect();
    format!(
        "r(positional line) = {{ {names}s0 = line; b0 = s0 is #a0; trim(s{}) }};\n",
        n - 1
    )
}

#[test]
fn a_parameter_bound_to_a_chain_of_names_scales() {
    // The union-find joins each name to the chain's class in near-constant time, whatever
    // order the bindings are written in, and each test then adds its atom to the class's set.
    let (i, _) = info(&chain_of_names(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let a = i.sigs.values().next().unwrap().expand().pop().unwrap();
    for k in 0..3 {
        let atom = Ty::set(KType::atom(&format!("a{k}")));
        assert!(atom.subtype(&a.params[0]), "{}", a.params[0]);
    }
    scaling::check("a parameter bound to a chain of n names", 400, |n| {
        let (info, _) = info(&chain_of_names(n));
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// A function whose undeclared parameter `line` has its loose atoms handled by an `else`, and
/// whose result is `line` trimmed after a chain of `n` names, each the one before it or an
/// atom of its own: the atoms of the chain reach the result from elsewhere than `line`.
fn chain_of_own_atoms(n: usize) -> String {
    let names: String = (1..=n)
        .map(|i| {
            format!(
                "x{i} = if (line else \"\") == \"{i}\" {{ #a{i} }} else {{ x{} }}; ",
                i - 1
            )
        })
        .collect();
    format!("r(positional line) = {{ x0 = line; {names}trim(x{n}) }};\n")
}

#[test]
fn a_chain_of_atoms_from_elsewhere_than_the_parameter_scales() {
    // Each name passes on the atoms of the one before it from elsewhere than `line`, and adds
    // its own, the small set into the large one. The first arrow, for a `line` with no atom,
    // gives the chain's atoms and not `line`'s.
    let (i, _) = info(&chain_of_own_atoms(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let arrows = i.sigs.values().next().unwrap().expand();
    assert_eq!(arrows.len(), 2);
    for k in 1..=3 {
        let atom = Ty::set(KType::atom(&format!("a{k}")));
        assert!(atom.subtype(&arrows[0].result), "{}", arrows[0].result);
    }
    let other = Ty::set(KType::atom("notFound"));
    assert!(!other.subtype(&arrows[0].result), "{}", arrows[0].result);
    assert!(other.subtype(&arrows[1].result), "{}", arrows[1].result);
    scaling::check("a chain of n names each adding an atom", 200, |n| {
        let (info, _) = info(&chain_of_own_atoms(n));
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.sigs.values().next().unwrap().arrows.len(), 2);
    });
}

/// `n` functions, each handling the atoms of its undeclared parameter `x` with an `else` and
/// passing `x` on to the one before it, the first trimming `x` or giving "empty".
fn chain_of_handlers(n: usize) -> String {
    chain_of_handlers_calling(n, |i| format!("h{}(x)", i - 1))
}

/// [`chain_of_handlers`], each function calling the one before it as `call(i)` writes it.
fn chain_of_handlers_calling(n: usize, call: impl Fn(usize) -> String) -> String {
    let mut src = String::from(
        "h0(positional x) = if (x else \"\") == \"\" { \"empty\" } else { trim(x) };\n",
    );
    for i in 1..n {
        src.push_str(&format!(
            "h{i}(positional x) = if (x else \"\") == \"{i}\" {{ \"d\" }} else {{ {} }};\n",
            call(i)
        ));
    }
    src
}

#[test]
fn a_chain_of_functions_passing_a_handled_parameter_on_scales() {
    // Each function's call of the one before it, with `x` holding no atom, takes that one's
    // first arrow, which gives no atom; so each function's first arrow gives a `String` alone.
    let (i, names) = info(&chain_of_handlers(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    for k in 0..3 {
        let (_, s) = i
            .sigs
            .iter()
            .find(|(id, _)| names[**id] == format!("h{k}"))
            .unwrap();
        let arrows = s.expand();
        assert_eq!(arrows.len(), 2, "h{k}");
        assert!(
            arrows[0].result.atoms().is_empty(),
            "h{k}: {}",
            arrows[0].result
        );
        let other = Ty::set(KType::atom("notFound"));
        assert!(
            other.subtype(&arrows[1].params[0]),
            "h{k}: {}",
            arrows[1].params[0]
        );
    }
    scaling::check(
        "a chain of n functions passing a handled parameter on",
        200,
        |n| {
            let (info, _) = info(&chain_of_handlers(n));
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn a_chain_of_functions_passing_a_handled_parameter_on_as_a_receiver_scales() {
    // `x.h0()` is `h0(x)`: the receiver fills the first parameter, so each function's first
    // arrow gives a `String` alone, as in the chain of calls written `h0(x)`.
    let method = |i: usize| format!("x.h{}()", i - 1);
    let (i, names) = info(&chain_of_handlers_calling(3, method));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    for k in 0..3 {
        let (_, s) = i
            .sigs
            .iter()
            .find(|(id, _)| names[**id] == format!("h{k}"))
            .unwrap();
        let arrows = s.expand();
        assert_eq!(arrows.len(), 2, "h{k}");
        assert!(
            arrows[0].result.atoms().is_empty(),
            "h{k}: {}",
            arrows[0].result
        );
    }
    scaling::check(
        "a chain of n functions passing a handled parameter on as a receiver",
        200,
        |n| {
            let (info, _) = info(&chain_of_handlers_calling(n, method));
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn many_calls_passing_a_handled_parameter_on_scale() {
    // One function calls `r` n times on its handled parameter, as `r(x)`, `x.r()`, `x.r`,
    // through the higher-order `ap` and through a computed callee, and passes `x` to a lambda
    // through `ap`, whose atoms then pass by at the call of `ap`; each call takes `r`'s first
    // arrow from outside, so `g`'s first arrow gives a `String` alone. Each call whose
    // argument holds a loose atom is applied once more, on the atoms from outside alone.
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n\
             ap(positional f, positional v) = f(v);\n";
    let calls = |n: usize, call: &str| {
        let body: String = (0..n).map(|i| format!("a{i} = {call}; ")).collect();
        format!("{r}g(positional x) = {{ d = x else \"\"; {body}a0 }};\n")
    };
    for call in [
        "r(x)",
        "x.r()",
        "x.r",
        "ap(r, x)",
        "(if true { r } else { r })(x)",
        "ap((positional y) -> trim(y), x)",
    ] {
        let first = sig_of(&calls(3, call), "g").expand()[0].result.clone();
        assert!(first.atoms().is_empty(), "{call}: {first}");
        scaling::check(
            &format!("one function calling `{call}` n times"),
            200,
            |n| {
                let (info, _) = info(&calls(n, call));
                assert!(info.errors.is_empty(), "{:?}", info.errors);
            },
        );
    }
}

#[test]
fn a_chain_of_method_calls_without_parentheses_scales() {
    // `x.r.r` … `.r`, n deep: each call is applied once more on the atoms from outside, and
    // that application takes its receiver's type as found, so the chain is checked in time
    // linear in n. The first arrow of `g` gives a `String` alone.
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n";
    let chain = |n: usize| {
        format!(
            "{r}g(positional x) = {{ d = x else \"\"; x{} }};\n",
            ".r".repeat(n)
        )
    };
    let first = sig_of(&chain(3), "g").expand()[0].result.clone();
    assert!(first.atoms().is_empty(), "{first}");
    scaling::check("a chain of n method calls without parentheses", 1000, |n| {
        let (info, _) = info(&chain(n));
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// `n` functions, each testing its undeclared parameter `x` against an atom of its own and
/// passing `x` on to the one before it, and a function calling the last on a value that may
/// be a string, the first function's atom or another.
fn chain_of_atom_tests(n: usize) -> String {
    let mut src = String::from("h0(positional x) = if x is #a0 { \"0\" } else { trim(x) };\n");
    for i in 1..n {
        src.push_str(&format!(
            "h{i}(positional x) = if x is #a{i} {{ \"{i}\" }} else {{ h{}(x) }};\n",
            i - 1
        ));
    }
    format!(
        "{src}g(positional k) = h{}(if k == 1 {{ #a0 }} else {{ if k == 2 {{ #b }} else {{ \"s\" }} }});\n",
        n - 1
    )
}

#[test]
fn a_chain_of_functions_each_testing_an_atom_of_its_own_scales() {
    // Each `h{i}` takes `#a{i}` alone, so its call of the one before it, which omits that atom,
    // passes it by; the call in `g` passes `#a0` and `#b` by, which no arrow of the last takes,
    // and gives the string to its first arrow. Each pass-by costs a set difference per arrow.
    let (i, _) = info(&chain_of_atom_tests(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    scaling::check(
        "a chain of n functions each testing an atom of its own",
        100,
        |n| {
            let (info, _) = info(&chain_of_atom_tests(n));
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn many_calls_passing_some_atoms_of_their_argument_by_scale() {
    // `v` may be a string, `#a` or `#b`. `h` takes `#a` and omits `#b`, so each call `h(v)`
    // passes `#b` by and gives `#a` to the arrow that takes it; the lambda takes no atom, so
    // each call of `ap` passes both by, at that call, whose argument gave them.
    let defs = "h(positional x) = if x is #a { \"a\" } else { trim(x) };\n\
                ap(positional f, positional v) = f(v);\n";
    let calls = |n: usize, call: &str| {
        let body: String = (0..n).map(|i| format!("c{i} = {call}; ")).collect();
        format!(
            "{defs}g(positional k) = {{ v = if k == 1 {{ #a }} else {{ if k == 2 {{ #b }} else {{ \"s\" }} }}; {body}c0 }};\n"
        )
    };
    for call in ["h(v)", "ap((positional y) -> trim(y), v)"] {
        let (i, _) = info(&calls(3, call));
        assert!(i.errors.is_empty(), "{call}: {:?}", i.errors);
        assert_eq!(i.passes.len(), 3, "{call}");
        scaling::check(
            &format!("one function calling `{call}` n times"),
            200,
            |n| {
                let (info, _) = info(&calls(n, call));
                assert!(info.errors.is_empty(), "{:?}", info.errors);
            },
        );
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
    scaling::on_a_thread(1 << 29, || {
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
            let info = zedc::check::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
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
    let n = 200;
    let inputs = [(n, overloads(n)), (8 * n, overloads(8 * n))];
    scaling::check(
        "an overload of n arrows passed to a slot of n arrows",
        n,
        |m| {
            let text = &inputs
                .iter()
                .find(|(k, _)| *k == m)
                .expect("a built size")
                .1;
            let (info, _) = info(text);
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
    let n = 100;
    let inputs = [(n, wider_overloads(n)), (8 * n, wider_overloads(8 * n))];
    scaling::check(
        "an overload of n arrows passed to a slot of n other arrows",
        n,
        |m| {
            let text = &inputs
                .iter()
                .find(|(k, _)| *k == m)
                .expect("a built size")
                .1;
            let (info, _) = info(text);
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
    let n = 100;
    let inputs = [(n, shared_overloads(n)), (8 * n, shared_overloads(8 * n))];
    scaling::check(
        "an overload of n arrows sharing a parameter piece passed to a slot of n arrows",
        n,
        |m| {
            let text = &inputs
                .iter()
                .find(|(k, _)| *k == m)
                .expect("a built size")
                .1;
            let (info, _) = info(text);
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
    let n = 100;
    let inputs = [(n, nested_overload(n)), (8 * n, nested_overload(8 * n))];
    scaling::check("a slot of n arrows nested n deep in parentheses", n, |m| {
        let text = &inputs
            .iter()
            .find(|(k, _)| *k == m)
            .expect("a built size")
            .1;
        let (info, _) = info(text);
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
    let n = 100;
    let inputs = [(n, covering_overload(n)), (8 * n, covering_overload(8 * n))];
    scaling::check("an overload of n arrows covering a slot together", n, |m| {
        let text = &inputs
            .iter()
            .find(|(k, _)| *k == m)
            .expect("a built size")
            .1;
        assert_eq!(type_errors(text), Vec::<String>::new());
    });
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
    let n = 100;
    let inputs = [(n, wide_arrows(n)), (8 * n, wide_arrows(8 * n))];
    scaling::check(
        "an arrow of w parameters that misses the slot's last",
        n,
        |m| {
            let text = &inputs
                .iter()
                .find(|(k, _)| *k == m)
                .expect("a built size")
                .1;
            assert_eq!(type_errors(text).len(), 1, "{:?}", type_errors(text));
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

/// Runs `want` on the source `text(m)` at `n` and `8 * n`, both built before either is run.
fn scales(what: &str, n: usize, text: impl Fn(usize) -> String, want: impl Fn(&str) + Sync) {
    let inputs = [(n, text(n)), (8 * n, text(8 * n))];
    scaling::check(what, n, |m| {
        let text = &inputs
            .iter()
            .find(|(k, _)| *k == m)
            .expect("a built size")
            .1;
        want(text);
    });
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
    scales("n arrows met and n within", 100, text, |text| {
        assert_eq!(type_errors(text), Vec::<String>::new());
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
        |text| {
            let errors = type_errors(text);
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert!(errors[0].contains("Orthogonal Vectors"), "{errors:?}");
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
        |text| {
            assert_eq!(type_errors(text), Vec::<String>::new());
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
    scales("a bounded variable at w parameters", 100, text, |text| {
        let errors = type_errors(text);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("places the arguments give"),
            "{errors:?}"
        );
    });
}
