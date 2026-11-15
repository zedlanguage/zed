//! The ZIR address of a string held in parts costs its bytes (ZIR-string-tree-address): the
//! benchmark of `string_trees.rs`, whose tests give one string in three trees one address.

use zed_kernel::term::build::lit;
use zed_kernel::text::Text;
use zed_kernel::value::Value;
use zed_tests::scaling::{check_order, inputs};
use zedc::zir::Region;
use zedc::zir::canon::address;

/// A graph whose one constant is `n` bytes held as blocks of 300 bytes joined from the left,
/// each block distinct, so the address writes the string as one block of `n` bytes.
fn joined(n: usize) -> Region {
    let mut t = Text::from("");
    for i in 0..n / 300 {
        t = Text::join(&t, &Text::from(format!("{i:0>300}"))).expect("under 2^64 bytes");
    }
    zedc::zir::lower::lower(&lit(Value::Str(t))).expect("lowered")
}

#[test]
fn a_string_held_in_parts_is_addressed_in_time_linear_in_its_bytes() {
    let n = 300 << 9;
    let graphs = inputs(n, joined);
    check_order("the ZIR address of a joined string", n, 1, |k| {
        address(&graphs[&k]).expect("memory for the address");
    });
}
