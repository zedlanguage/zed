//! Printing a type is of order n in its size: the benchmark of `layout.rs`, whose test prints
//! the same union type at small sizes.

use zed_tests::scaling;

use crate::layout::union_type;

#[test]
fn printing_a_type_scales_with_its_size() {
    let types = scaling::inputs(200, union_type);
    scaling::check("printing a union type, by atoms", 200, |n| {
        zedc::format::format_type(&types[&n]);
    });
}
