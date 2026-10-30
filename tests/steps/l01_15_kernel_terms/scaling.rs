//! The printer at the rule of low complexity (DESIGN.md Part G).

use std::sync::Arc;

use zed_kernel::Term;
use zed_kernel::print::pretty;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

/// Shape `k` nested `d` deep: lambdas, calls in argument position, calls in head position.
fn shape(k: usize, d: usize) -> Term {
    (0..d).fold(var(["x", "x", "f"][k]), |t, _| match k {
        0 => Term::Lam(vec!["y".into()], Arc::new(t)),
        1 => Term::App(Arc::new(var("g")), vec![t, var("z")]),
        _ => Term::App(Arc::new(t), vec![var("a")]),
    })
}

const SHAPES: [&str; 3] = [
    "lambdas",
    "calls in argument position",
    "calls in head position",
];

#[test]
fn the_printer_scales_with_depth() {
    // Every node a broken layout visited computed its subtree's one-line text, and each level
    // of the one-line text copied the text of the level inside it.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            for (k, what) in SHAPES.iter().enumerate() {
                let one_line = format!("one line, nested {what}, by depth");
                // A call's head was copied into the text of the call around it, a cost that
                // shows only past a few thousand levels. Between 8,000 and 16,000 levels of
                // heads the recursion leaves the cache, the cost per level stepping up from
                // 0.4 to 1.1 µs and flat again after, so both sizes are past it.
                let n = if k == 2 { 16_000 } else { 500 };
                zed_tests::scaling::check(&one_line, n, |d| {
                    std::hint::black_box(shape(k, d).to_string());
                });
                // Broken, calls nested in argument position put depth `i` at indentation `2i`,
                // so their text is quadratic in the depth: they are measured by the text's
                // length, the depth growing as its square root.
                let (n, depth): (usize, fn(usize) -> usize) = match k {
                    1 => (250_000, |m| m.isqrt()),
                    _ => (500, |m| m),
                };
                let broken = format!("width 80, nested {what}, by text");
                zed_tests::scaling::check(&broken, n, |m| {
                    std::hint::black_box(pretty(&shape(k, depth(m)), 80));
                });
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn nested_shapes_break_as_before() {
    let [lam, arg, head] = [0, 1, 2].map(|k| shape(k, 3));
    assert_eq!(lam.to_string(), "y -> y -> y -> x");
    assert_eq!(arg.to_string(), "g(g(g(x, z), z), z)");
    assert_eq!(head.to_string(), "((f(a))(a))(a)");
    assert_eq!(
        pretty(&arg, 12),
        "g(\n  g(\n    g(x, z),\n    z\n  ),\n  z\n)"
    );
    assert_eq!(pretty(&head, 8), "((f(a))(a))(\n  a\n)");
    assert_eq!(pretty(&lam, 10), "y -> y -> y -> x");
}
