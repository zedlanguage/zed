//! The rule of low complexity (DESIGN.md Part G): each family of `scaling.rs` at n and 8n, the
//! work held to the order of its output. Each run asserts the identity proved.

use zed_tests::scaling;

use crate::scaling::{
    binomial, commute, factors, gapped_square, grid, linear, linear_chain, proved, ring_of_names,
    square,
};

#[test]
fn the_square_of_a_sum_of_k_powers() {
    let ins = scaling::inputs(1000, square);
    scaling::check("(1 + x + ... + x ^ k) ^ 2 of k terms", 1000, |n| {
        proved(&ins[&n])
    });
}

#[test]
fn a_dense_product_of_n_terms_commuted() {
    let ins = scaling::inputs(1000, commute);
    scaling::check("A * B == B * A, n terms each", 1000, |n| proved(&ins[&n]));
}

#[test]
fn a_sum_of_n_names_times_a_sum() {
    let ins = scaling::inputs(500, linear);
    scaling::check("(x0 + ... + xn) * (y + z)", 500, |n| proved(&ins[&n]));
}

#[test]
fn a_written_chain_of_n_names_times_a_sum() {
    let ins = scaling::inputs(500, linear_chain);
    scaling::check(
        "x0 + ... + xn written as a chain, times (y + z)",
        500,
        |n| proved(&ins[&n]),
    );
}

#[test]
fn a_sum_of_n_monomials_in_n_names() {
    let ins = scaling::inputs(1000, ring_of_names);
    scaling::check("x0 * x1 * c0 + ... + x(n-1) * x0 * c(n-1)", 1000, |n| {
        proved(&ins[&n])
    });
}

#[test]
fn a_grid_of_n_squared_monomials() {
    let ins = scaling::inputs(30, grid);
    scaling::check_order("(sum x ^ i) * (sum y ^ j), n terms each", 30, 2, |n| {
        proved(&ins[&n])
    });
}

#[test]
fn a_product_of_powers_of_n_factors() {
    let ins = scaling::inputs(500, factors);
    scaling::check(
        "(x0 + y) * ... * (xn + y) ^ n, n factors read as powers",
        500,
        |n| proved(&ins[&n]),
    );
}

#[test]
fn a_power_of_a_sum_of_two_names() {
    let ins = scaling::inputs(500, binomial);
    scaling::check_order("(x + y) ^ k, k + 1 monomials of k bits", 500, 2, |n| {
        proved(&ins[&n])
    });
}

#[test]
fn the_square_of_a_power_of_a_sum_beside_one_name() {
    // At k = 2048 the square is about 2 s of work, refused (QUESTIONS A99); 8 * 32 = 256 is
    // about 50 ms.
    let ins = scaling::inputs(32, gapped_square);
    scaling::check_order(
        "((x + y) ^ k + x) ^ 2, 3k + 3 monomials of 2k bits",
        32,
        2,
        |n| proved(&ins[&n]),
    );
}
