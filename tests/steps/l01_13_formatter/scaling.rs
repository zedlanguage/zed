//! The formatter at the rule of low complexity (DESIGN.md Part G).

use zed_tests::scaling;

/// `f(c) = if c { if c { … { a = 1; a } … } else { 0 } } else { 0 };`, nested `depth` deep.
fn nested(depth: usize) -> String {
    let mut b = "{ a = 1; a }".to_string();
    for _ in 0..depth {
        b = format!("{{ if c {b} else {{ 0 }} }}");
    }
    format!("f(c) = if c {b} else {{ 0 }};\n")
}

#[test]
fn nested_one_statement_blocks_scale() {
    // A block of one statement written on several lines was rendered once to try one line and
    // again on its own lines, so `d` such blocks nested cost `2^d` renders (8 s at `d = 20`).
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("nested one-statement blocks, by depth", 2, |d| {
                zedc::format::format_source(nested(d).as_bytes()).unwrap();
            });
            let out = zedc::format::format_source(nested(1).as_bytes()).unwrap();
            assert_eq!(
                out,
                "f(c) = if c {\n  if c {\n    a = 1;\n    a\n  } else { 0 }\n} else { 0 };\n"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
