use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::standing_twice::{printed_names, read_sig};

/// A signature of `n` parameters, the parameter `i` of each kind the generated signatures of
/// `standing_twice` hold in turn, over the variables `Ti` and `Ui`: tuples, payloads, held
/// functions and unions, with a result that names each `Ti` again.
fn wide(n: usize) -> String {
    let params: Vec<String> = (0..n)
        .map(|i| match i % 4 {
            0 => format!("a{i}: (T{i}, U{i})"),
            1 => format!("a{i}: #a(T{i})"),
            2 => format!("a{i}: ((z: T{i}) -> U{i})"),
            _ => format!("a{i}: T{i} | U{i}"),
        })
        .collect();
    let result: Vec<String> = (0..n).map(|i| format!("T{i}")).collect();
    format!("({}) -> ({})", params.join(", "), result.join(", "))
}

/// Besides its ratio: the variables it gives are as many as the names the printer writes.
/// Small instance: `standing_twice::the_variables_standing_twice_are_the_ones_printed_by_name`.
#[test]
fn the_variables_standing_twice_are_counted_in_linear_time() {
    let sigs: BTreeMap<usize, _> = [2000, scaling::FACTOR * 2000]
        .into_iter()
        .map(|n| (n, read_sig(&wide(n))))
        .collect();
    for s in sigs.values() {
        assert_eq!(s.standing_twice().len(), printed_names(s).len());
    }
    scaling::check(
        "the variables of a signature of n parameters standing twice",
        2000,
        |n| {
            assert!(!sigs[&n].standing_twice().is_empty());
        },
    );
}
