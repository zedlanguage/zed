//! The checker at the rule of low complexity (DESIGN.md Part G). Each run of a signature's
//! search began from a copy of everything found in the unit so far, so a unit of `n`
//! functions with untyped parameters took `O(n²)`; a run now undoes only what it wrote.

use zed_tests::scaling;

use super::info;

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
