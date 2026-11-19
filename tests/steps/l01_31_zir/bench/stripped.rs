//! Stripping a graph of its facts is linear in its size as the binary form counts it: the
//! benchmarks of `stripped.rs`, whose tests strip at small sizes and on a 2 MiB stack.

use zed_tests::deep::on_small_stack;
use zed_tests::scaling::check_order;
use zedc::zir::strip::strip;

use crate::scaling::nested_ifs;
use crate::stripped::doubly_shared;

#[test]
fn stripping_a_deep_graph_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(12_500), nested_ifs(100_000));
        check_order("stripping nested `if` regions", 12_500, 1, |k| {
            drop(strip(if k == 12_500 { &small } else { &large }));
        });
    });
}

#[test]
fn stripping_a_shared_graph_is_linear_in_its_regions_not_its_tree() {
    on_small_stack(|| {
        // Depth d has d regions and a tree of 2^d leaves.
        let (small, large) = (doubly_shared(12_500), doubly_shared(100_000));
        check_order(
            "stripping `if` regions shared by both arms",
            12_500,
            1,
            |k| {
                drop(strip(if k == 12_500 { &small } else { &large }));
            },
        );
    });
}
