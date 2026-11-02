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
/// taking a component of it; with `all`, each calls every one before it instead.
fn fan(n: usize, all: bool) -> String {
    let mut src = "g0(positional t) = t[0];\n".to_string();
    for i in 1..n {
        let calls: Vec<String> = if all {
            (0..i).map(|j| format!("g{j}(t)")).collect()
        } else {
            vec![format!("g{}(t)", i - 1); 2]
        };
        src += &format!("g{i}(positional t) = {};\n", calls.join(" + "));
    }
    src
}

/// The texts of [`fan`] at `n` and `FACTOR * n`, built before the timing.
fn fans(n: usize, all: bool) -> std::collections::BTreeMap<usize, String> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, fan(m, all)))
        .collect()
}

#[test]
fn needs_replayed_through_a_fan_of_calls_scale() {
    // Each of the two calls met the needs of the one before anew, so they doubled at each
    // function; a use met twice now gives what it gave the first time.
    assert_eq!(
        sig(&fan(3, false), "g2"),
        "(T) -> U for U in int | f64 | rat"
    );
    let texts = fans(250, false);
    scaling::check(
        "needs replayed through n functions, each calling the one before twice",
        250,
        |n| {
            let (info, _) = info(&texts[&n]);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn control_the_scaling_check_catches_calls_that_grow_with_the_depth() {
    // Each function calls every one before it: n² calls in n functions.
    let texts = fans(10, true);
    let caught = std::panic::catch_unwind(|| {
        scaling::check("n functions, each calling every one before", 10, |n| {
            let (info, _) = info(&texts[&n]);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
    assert!(caught.is_err(), "the check passed n² calls");
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
