//! A bit word at the end of a long chain of bindings, on the 8 MiB stack of a main thread. The
//! checker reads the operand's domain back through every binder of the chain; it reads on an
//! explicit stack, so the depth of the chain does not bound the program.

use zed_tests::deep::on_main_sized_stack;

#[test]
fn a_bit_word_reads_through_a_chain_of_20000_bindings() {
    // `y0 = 255; y1 = y0 + 1; …; y20000 = y19999 + 1; z = popCount(y20000);`. Read by a
    // recursive call per binder, this overflows the 8 MiB stack at this depth.
    let mut src = String::from("y0 = 255;\n");
    for i in 1..=20_000 {
        src.push_str(&format!("y{i} = y{} + 1;\n", i - 1));
    }
    src.push_str("z = popCount(y20000);\n");
    let src = super::program(&src);
    on_main_sized_stack(|| zedc::run::load(src.as_bytes()).map(drop))
        .unwrap_or_else(|e| panic!("{e}"));
}
