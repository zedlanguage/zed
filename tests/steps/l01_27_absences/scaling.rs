//! The checker on a chain of loose atoms, at the rule of low complexity (DESIGN.md Part G).
//! `e else d` and each operator strip the loose atoms of their operands; the strip
//! complemented every loose atom so far, so a chain of n failures took O(n²) (COMPLEXITY.md
//! F21). Each run checks the chain twice: the emptiness results were kept from one unit to
//! the next, and the second check compared each of its types in full with an equal kept one,
//! which also took O(n²) (COMPLEXITY.md F32).

use zed_tests::scaling;

use crate::l01_26_type_resolution::info;

/// `x = #e0 + #e1 + … + #e(n-1);`
fn chain(n: usize) -> String {
    let atoms: Vec<String> = (0..n).map(|i| format!("#e{i}")).collect();
    format!("x = {};\n", atoms.join(" + "))
}

#[test]
fn a_chain_of_many_failure_atoms_scales() {
    // The parser and checker recurse once per operator, so the chain runs on a large stack.
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 29)
            .spawn_scoped(s, || {
                scaling::check("a chain of n failure atoms, checked twice", 1000, |n| {
                    let text = chain(n);
                    for _ in 0..2 {
                        let (info, _) = info(&text);
                        assert!(info.errors.is_empty(), "{:?}", info.errors);
                    }
                })
            })
            .unwrap()
            .join()
            .unwrap()
    })
}
