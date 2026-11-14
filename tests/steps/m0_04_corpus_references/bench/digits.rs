//! Numbers of 100,000 and 20,000 digits (author P178: a large input is a benchmark). The tests
//! of `int_reading.rs` make the same checks either side of 4300 digits.

use zed_tests::instances::Rng;

use crate::int_reading::{reads_a_number_of_length, zeros_nines_and_a_power_of_ten};

#[test]
fn a_number_of_100000_digits_reads_as_num_bigint_and_the_kernel_read_it() {
    reads_a_number_of_length(&mut Rng::new(4301), 100_000);
}

#[test]
fn zeros_nines_and_a_power_of_ten_of_20000_digits_read_exactly() {
    zeros_nines_and_a_power_of_ten(20_000);
}
