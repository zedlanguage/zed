//! The order sweep of `group_oracle` over the cells of seeds 0 to 6000, in twelve tests of 500
//! seeds. Each test takes 6.9 to 8.9 s alone, so the twelve in `group_oracle`'s piece made it
//! run 20.0 to 36 s against its limit of 20 s (b22-mem40's merge checks, 2026-11-22). Here, in a
//! module named in the `split` list of tools/run_tests.sh, each test is a piece of its own, and
//! `group_oracle` keeps the tests that take under 1.3 s each (TEST-group-oracle-seed-split).

use super::group_oracle::order_sweep_asserts;

#[test]
fn the_cells_of_seeds_0_500_agree_exactly_in_every_order() {
    order_sweep_asserts(0..500);
}

#[test]
fn the_cells_of_seeds_500_1000_agree_exactly_in_every_order() {
    order_sweep_asserts(500..1000);
}

// The three ranges below found order differences before GROUP-order-cpoly-merge (cells 1140,
// 1558, 1696 and 1908 with tuple components reversed).
#[test]
fn the_cells_of_seeds_1000_1500_agree_exactly_in_every_order() {
    order_sweep_asserts(1000..1500);
}

#[test]
fn the_cells_of_seeds_1500_2000_agree_exactly_in_every_order() {
    order_sweep_asserts(1500..2000);
}

#[test]
fn the_cells_of_seeds_2000_2500_agree_exactly_in_every_order() {
    order_sweep_asserts(2000..2500);
}

#[test]
fn the_cells_of_seeds_2500_3000_agree_exactly_in_every_order() {
    order_sweep_asserts(2500..3000);
}

#[test]
fn the_cells_of_seeds_3000_3500_agree_exactly_in_every_order() {
    order_sweep_asserts(3000..3500);
}

#[test]
fn the_cells_of_seeds_3500_4000_agree_exactly_in_every_order() {
    order_sweep_asserts(3500..4000);
}

#[test]
fn the_cells_of_seeds_4000_4500_agree_exactly_in_every_order() {
    order_sweep_asserts(4000..4500);
}

#[test]
fn the_cells_of_seeds_4500_5000_agree_exactly_in_every_order() {
    order_sweep_asserts(4500..5000);
}

#[test]
fn the_cells_of_seeds_5000_5500_agree_exactly_in_every_order() {
    order_sweep_asserts(5000..5500);
}

#[test]
fn the_cells_of_seeds_5500_6000_agree_exactly_in_every_order() {
    order_sweep_asserts(5500..6000);
}
