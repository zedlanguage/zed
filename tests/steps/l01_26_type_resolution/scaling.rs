//! The checker at the rule of low complexity (DESIGN.md Part G). A signature search tried
//! each carrier for each untyped parameter, up to a budget, and began each run from a copy of
//! everything found so far. An untyped parameter is now a class of a union-find forest, and
//! each body is checked once.

use zed_tests::scaling;

use super::{info, sig};

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
            text.extend((0..n).map(|i| format!("f{i}(x) = x / {};\n", i + 1)));
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
    assert_eq!(sig(&tuple(2), "f"), "(T, U) -> (T, U)");
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
    assert_eq!(sig(&fan(3), "g2"), "(T) -> U for U in int | f64 | rat");
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
// before and after the walk moved to a heap stack, so 100,000 deep would take minutes. They
// are checked 8,000 deep, eight times past the depth that overflowed.

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

#[test]
fn lambdas_nested_1000_deep_check_on_a_2_mib_stack() {
    // The walk keeps no frame of the thread's stack per lambda; `Ty::replace` and
    // `Sig::replace` still recurse on the nesting of the type, and overflow this stack near
    // 4,000. The time is quadratic, from the deep clones of `Ty` (both open).
    use zed_tests::deep::{on_small_stack, program, statements};
    let stmts = statements(&program("nested lambdas", 1_000).text);
    let res = zedc::resolve::resolve(&stmts).unwrap();
    on_small_stack(|| assert!(zedc::check::check(&stmts, &res).errors.is_empty()));
}
