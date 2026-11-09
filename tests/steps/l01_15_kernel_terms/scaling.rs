//! The printer at the rule of low complexity (DESIGN.md Part G).

use std::sync::Mutex;
use zed_kernel::Shared;

use zed_kernel::Term;
use zed_kernel::print::pretty;
use zed_tests::scaling;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

/// Shape `k` nested `d` deep: lambdas, calls in argument position, calls in head position.
fn shape(k: usize, d: usize) -> Term {
    (0..d).fold(var(["x", "x", "f"][k]), |t, _| match k {
        0 => Term::Lam(vec!["y".into()], Shared::new(t)),
        1 => Term::App(Shared::new(var("g")), vec![t, var("z")]),
        _ => Term::App(Shared::new(t), vec![var("a")]),
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
    zed_tests::deep::on_small_stack(|| {
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
    });
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

/// Each shape of term dropped, `n` nodes: four nested `n` deep, through an `Arc` (`let` bodies,
/// lambda bodies, `else` branches) or a `Vec` of arguments (a left-nested sum), and two
/// branching, a balanced tree of sums and one tuple of `n` parts.
fn dropped_shapes(n: usize) -> Vec<(&'static str, Term)> {
    use zed_kernel::term::Prim;
    use zed_kernel::term::build::{if_, lam, let_, lit, prim};
    let chain = (0..n).fold(var("x"), |body, _| let_("x", lit(1), body));
    let lams = (0..n).fold(var("x"), |body, _| lam(&["x"], body));
    let sum = (0..n).fold(lit(0), |a, _| prim(Prim::Add, vec![a, lit(1)]));
    let ifs = (0..n).fold(lit(0), |b, _| if_(var("c"), lit(1), b));
    // Built a level at a time, pairs of the level below, so the builder does not recurse.
    let mut level: Vec<Term> = (0..n.div_ceil(2)).map(|_| lit(1)).collect();
    while level.len() > 1 {
        let mut parts = std::mem::take(&mut level).into_iter();
        while let Some(a) = parts.next() {
            level.push(match parts.next() {
                Some(b) => prim(Prim::Add, vec![a, b]),
                None => a,
            });
        }
    }
    let tree = level.pop().expect("one root");
    let wide = prim(
        Prim::Tuple,
        (0..n).map(|_| prim(Prim::Neg, vec![lit(1)])).collect(),
    );
    vec![
        ("a `let` chain", chain),
        ("nested lambdas", lams),
        ("a left-nested sum", sum),
        ("nested `else` branches", ifs),
        ("a balanced tree of sums", tree),
        ("a tuple of n negations", wide),
    ]
}

#[test]
fn dropping_deep_and_wide_terms_scales() {
    // `Term`'s drop keeps the parts still to free on a heap stack (COMPLEXITY.md F62), each part
    // moved there once. Only the drop is measured: each run frees a term built before any run.
    let n = 12_500;
    zed_tests::deep::on_small_stack(|| {
        let (small_runs, large_runs) = scaling::Meter::new().runs();
        let pools = |k: usize, runs: usize| -> Vec<(&'static str, Mutex<Vec<Term>>)> {
            let built: Vec<_> = dropped_shapes(k)
                .into_iter()
                .map(|(what, t)| (what, Mutex::new(vec![t])))
                .collect();
            for _ in 1..runs {
                for ((_, pool), (_, t)) in built.iter().zip(dropped_shapes(k)) {
                    pool.lock().expect("no run panicked").push(t);
                }
            }
            built
        };
        let (small, large) = (pools(n, small_runs), pools(8 * n, large_runs));
        for ((what, s), (_, l)) in small.iter().zip(&large) {
            scaling::check(&format!("dropping {what}"), n, |k| {
                let pool = if k == n { s } else { l };
                drop(
                    pool.lock()
                        .expect("no run panicked")
                        .pop()
                        .expect("a term built for each run"),
                );
            });
        }
    });
}

/// How many `Lam`s are nested at the top of `t`.
fn lambda_depth(mut t: &Term) -> usize {
    let mut d = 0;
    while let Term::Lam(_, body) = t {
        d += 1;
        t = body;
    }
    d
}

#[test]
fn a_term_far_deeper_than_the_stack_drops_and_keeps_its_shared_parts() {
    // A recursive drop overflows a 2 MiB stack near 10,000 levels. A part another owner still
    // holds is left whole, and its own drop later frees it the same way.
    let n = 1_000_000;
    zed_tests::deep::on_small_stack(|| {
        let inner =
            Shared::new((0..n).fold(var("x"), |b, _| Term::Lam(vec!["y".into()], Shared::new(b))));
        let outer = (0..n).fold(Term::Lam(vec!["z".into()], inner.clone()), |b, _| {
            Term::Lam(vec!["y".into()], Shared::new(b))
        });
        assert_eq!(lambda_depth(&outer), 2 * n + 1);
        drop(outer);
        assert_eq!(Shared::strong_count(&inner), 1);
        assert_eq!(lambda_depth(&inner), n);
        drop(inner);
        let wide = Term::Prim(
            zed_kernel::term::Prim::Tuple,
            (0..n)
                .map(|_| Term::Lam(vec!["y".into()], Shared::new(var("x"))))
                .collect(),
        );
        drop(wide);
    });
}

/// Negations and indices nested `d` deep: `-(-(-x))` and `t[0][0][0]`, each operand checked
/// for parentheses once (repair PRIM-hidden-names).
fn prefix_shape(k: usize, d: usize) -> Term {
    use zed_kernel::term::Prim;
    use zed_kernel::term::build::{lit, prim};
    (0..d).fold(var("x"), |t, _| match k {
        0 => prim(Prim::Neg, vec![t]),
        _ => prim(Prim::TupleGet, vec![t, lit(0)]),
    })
}

#[test]
fn negations_and_indices_print_in_linear_time() {
    zed_tests::deep::on_small_stack(|| {
        let n = 2_000;
        for (k, what) in ["negations", "indices"].into_iter().enumerate() {
            let (small, large) = (prefix_shape(k, n), prefix_shape(k, 8 * n));
            scaling::check(&format!("one line, nested {what}, by depth"), n, |d| {
                let t = if d == n { &small } else { &large };
                std::hint::black_box(t.to_string());
            });
            scaling::check(&format!("width 80, nested {what}, by depth"), n, |d| {
                let t = if d == n { &small } else { &large };
                std::hint::black_box(pretty(t, 80));
            });
        }
    });
    assert_eq!(prefix_shape(0, 3).to_string(), "-(-(-x))");
    assert_eq!(prefix_shape(1, 3).to_string(), "x[0][0][0]");
}

/// Item PRINT-group-site-defs: a term whose n type tests each write a part twice,
/// `is (int | #x{k}, int | #x{k})`, is written with n declarations before it, in time
/// linear in the term (COMPLEXITY.md K92).
#[test]
fn a_term_declaring_its_shared_parts_scales() {
    use zed_kernel::Pattern;
    use zed_kernel::types::Type;
    scaling::check_order(
        "a term with n type tests that each write a part twice",
        100,
        1,
        |n| {
            let arms = (0..n)
                .map(|k| {
                    let part = &Type::int() | &Type::atom(&format!("x{k}"));
                    let pair = Type::tuple(vec![part.clone(), part]);
                    (Pattern::Is(pair), zed_kernel::term::build::lit(k as i64))
                })
                .collect();
            let text = Term::Match(Shared::new(var("v")), arms).to_string();
            assert_eq!(text.matches("type T").count(), n);
            std::hint::black_box(text);
        },
    );
}
