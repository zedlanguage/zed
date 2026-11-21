use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::partial_maps::{bounded, many, maps_in_tuples};
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
        "type Part1 = int | String;\n(m: int .. Part1 -> int .. Part1 -> bool, k: int) -> bool"
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

#[test]
fn checking_a_map_nested_deep_in_a_tuple_parameter_scales() {
    // PERF-keyed-part-path-d-squared: one need, on the map `d` levels down, whose path of `d`
    // steps each of the three calls follows (`Ck::part_of`), asking at each step whether the
    // argument there is a map declared on a parameter (`Ck::keyed_place`).
    let units: BTreeMap<usize, Resolved> = [256, scaling::FACTOR * 256]
        .into_iter()
        .map(|m| (m, Resolved::new(&maps_in_tuples(m, false))))
        .collect();
    scaling::check(
        "a map d deep in a tuple parameter, passed three ways",
        256,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn checking_maps_at_every_level_of_a_tuple_parameter_scales() {
    // PERF-keyed-part-path-d-squared: `d` needs, one on the map at each level, of paths of 1
    // to `d` steps.
    let units: BTreeMap<usize, Resolved> = [256, scaling::FACTOR * 256]
        .into_iter()
        .map(|m| (m, Resolved::new(&maps_in_tuples(m, true))))
        .collect();
    scaling::check(
        "maps at each of d levels of a tuple parameter, passed three ways",
        256,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}
