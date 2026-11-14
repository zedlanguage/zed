use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::tuple_keys::wide;
use super::super::{Resolved, type_errors};

#[test]
fn indexing_a_wide_tuple_scales() {
    assert_eq!(type_errors(&wide(4)), Vec::<String>::new(), "{}", wide(4));
    let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
        .into_iter()
        .map(|m| (m, Resolved::new(&wide(m))))
        .collect();
    scaling::check_order(
        "a tuple of n components indexed by a computed key",
        500,
        1,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}
