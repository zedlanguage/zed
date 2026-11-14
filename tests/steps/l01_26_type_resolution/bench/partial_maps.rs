use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::partial_maps::{bounded, many};
use super::super::{Resolved, sig, type_errors};

#[test]
fn checking_many_and_deep_partial_maps_scales() {
    assert_eq!(type_errors(&many(3)), Vec::<String>::new(), "{}", many(3));
    assert_eq!(sig(&many(2), "g"), "(m: String ->? String ->? int) -> int");
    let units: BTreeMap<usize, Resolved> = [2500, scaling::FACTOR * 2500]
        .into_iter()
        .map(|m| (m, Resolved::new(&many(m))))
        .collect();
    scaling::check_order(
        "n partial maps, and one nested n deep, looked up",
        2500,
        1,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn checking_and_printing_many_and_deep_bounded_maps_scales() {
    assert_eq!(
        type_errors(&bounded(3)),
        Vec::<String>::new(),
        "{}",
        bounded(3)
    );
    assert_eq!(
        sig(&bounded(2), "g"),
        "type T1 = int | String;\n(m: int .. T1 -> int .. T1 -> bool, k: int) -> bool"
    );
    let units: BTreeMap<usize, Resolved> = [1600, scaling::FACTOR * 1600]
        .into_iter()
        .map(|m| (m, Resolved::new(&bounded(m))))
        .collect();
    scaling::check_order(
        "n bounded maps, and one nested n deep, looked up and printed",
        1600,
        1,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            let printed: usize = info.sigs.values().map(|s| s.to_string().len()).sum();
            assert!(printed > n, "{printed}");
        },
    );
}
