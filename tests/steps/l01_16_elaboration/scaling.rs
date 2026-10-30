//! Elaboration at the rule of low complexity (DESIGN.md Part G).

use super::{elab, term, value};

/// `f0(x = 1) = x;` and `f{i}(x = f{i-1}() + f{i-1}()) = x;` up to `k`, and `main = f{k}();`.
fn chain(k: usize) -> String {
    let mut src = "f0(x = 1) = x;\n".to_string();
    for i in 1..=k {
        src += &format!("f{i}(x = f{j}() + f{j}()) = x;\n", j = i - 1);
    }
    src + &format!("main = f{k}();\n")
}

#[test]
fn defaults_calling_functions_with_defaults_scale() {
    // A call leaving a parameter out held a copy of its default, and the copy's own calls
    // copies of theirs, so the chain's term doubled with each function (2.9 million
    // characters for `main` at `k = 16`).
    zed_tests::scaling::check("a chain of defaults, by length", 8, |k| {
        let u = elab(&chain(k)).unwrap();
        let main = u.defs.iter().find(|d| d.name == "main").unwrap();
        assert!(main.term.to_string().len() < 40, "{}", main.term);
    });
    assert_eq!(value(&chain(3), "main"), "8");
    assert_eq!(term(&chain(3), "main"), "{ x@4 = f3$x@4(); f3(x@4) }");
    assert_eq!(
        term(&chain(3), "f3$x@4"),
        "() -> ({ x@3 = f2$x@3(); f2(x@3) } + { x@3 = f2$x@3(); f2(x@3) })"
    );
}

#[test]
fn a_compound_default_reads_the_parameters_it_names() {
    let src = "area(positional w, h = w + 1) = w * h;\na = area(3);\nb = area(3, h: 2);\n";
    assert_eq!(value(src, "a"), "12");
    assert_eq!(value(src, "b"), "6");
    assert_eq!(term(src, "a"), "{ w = 3; h = area$h(w); area(w, h) }");
    assert_eq!(term(src, "area$h"), "w -> (w + 1)");
}
