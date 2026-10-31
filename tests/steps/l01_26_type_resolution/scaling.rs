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
