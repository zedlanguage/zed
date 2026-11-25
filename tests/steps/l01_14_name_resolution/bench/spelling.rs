//! The benchmark of step L1.14a, the row "Name that resolves to nothing": its correctness test
//! is `spelling::misspelled_uses_among_many_names_offer_each_its_name`.

use zed_tests::scaling;

use crate::spelling::misspelled;

#[test]
fn misspelled_uses_scale() {
    // n uses that resolve to nothing among n names, each near one of them: each use's lookup
    // goes through the spelling index (`SpellingIndex::near_all`), O(L³) for a name of length
    // L, where a test of each name in scope would cost O(n) a use and O(n²) in all.
    let n = 500;
    scaling::check_order_inputs(
        "n misspelled uses among n names",
        n,
        1,
        misspelled,
        |stmts| {
            let errors = zedc::resolve::resolve(stmts).unwrap_err();
            assert!(
                errors.iter().all(|e| e.notes.len() == 3),
                "{:?}",
                errors.first()
            );
        },
    );
}
