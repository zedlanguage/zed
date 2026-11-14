//! The tree a literal prints as (`ast/show.rs`): an integer keeps its radix prefix, a float the
//! format its suffix forces (DESIGN.md sec:lexical, the number rows).

use super::check;

#[test]
fn a_literal_prints_with_its_radix_and_its_forced_format() {
    check(&[
        ("x + 0b101", "(+ x 0b101)"),
        ("x + 0o17", "(+ x 0o17)"),
        ("x + 0x1f", "(+ x 0x1f)"),
        ("x + 1.5f32", "(+ x 1.5f32)"),
        ("x + 1.5f64", "(+ x 1.5f64)"),
        ("x + 1.5", "(+ x 1.5)"),
    ]);
}
