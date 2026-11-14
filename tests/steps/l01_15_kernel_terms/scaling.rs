//! The printer and the drop of terms on deep and wide terms: the shapes the benchmarks of
//! `bench.rs` measure, and a small instance of each check they make besides the ratio
//! (TEST-bench-split, P170).

use zed_kernel::Shared;

use zed_kernel::Term;
use zed_kernel::print::pretty;

pub(super) fn var(x: &str) -> Term {
    Term::Var(x.into())
}

/// Shape `k` nested `d` deep: lambdas, calls in argument position, calls in head position.
pub(super) fn shape(k: usize, d: usize) -> Term {
    (0..d).fold(var(["x", "x", "f"][k]), |t, _| match k {
        0 => Term::Lam(vec!["y".into()], Shared::new(t)),
        1 => Term::App(Shared::new(var("g")), vec![t, var("z")]),
        _ => Term::App(Shared::new(t), vec![var("a")]),
    })
}

pub(super) const SHAPES: [&str; 3] = [
    "lambdas",
    "calls in argument position",
    "calls in head position",
];

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

/// Each shape `bench::the_printer_scales_with_depth` prints, on a small stack, at the larger
/// depths it reaches: on one line with one level of text per level, and broken at width 80.
#[test]
fn each_shape_prints_deep_on_a_small_stack() {
    zed_tests::deep::on_small_stack(|| {
        for (k, depth) in [(0, 4_000), (1, 1_000), (2, 16_000)] {
            let t = shape(k, depth);
            let marks = [" -> ", "g(", "(a)"][k];
            assert_eq!(t.to_string().matches(marks).count(), depth, "{}", SHAPES[k]);
            std::hint::black_box(pretty(&shape(k, depth.min(4_000)), 80));
        }
    });
}

/// Each shape of term dropped, `n` nodes: four nested `n` deep, through an `Arc` (`let` bodies,
/// lambda bodies, `else` branches) or a `Vec` of arguments (a left-nested sum), and two
/// branching, a balanced tree of sums and one tuple of `n` parts.
pub(super) fn dropped_shapes(n: usize) -> Vec<(&'static str, Term)> {
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

/// Every shape `bench::dropping_deep_and_wide_terms_scales` drops, at its smaller size, 12,500,
/// past the near 10,000 levels where a recursive drop overflows a 2 MiB stack.
#[test]
fn each_shape_drops_on_a_small_stack() {
    zed_tests::deep::on_small_stack(|| {
        for (_, t) in dropped_shapes(12_500) {
            drop(t);
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
pub(super) fn prefix_shape(k: usize, d: usize) -> Term {
    use zed_kernel::term::Prim;
    use zed_kernel::term::build::{lit, prim};
    (0..d).fold(var("x"), |t, _| match k {
        0 => prim(Prim::Neg, vec![t]),
        _ => prim(Prim::TupleGet, vec![t, lit(0)]),
    })
}

/// The texts of `bench::negations_and_indices_print_in_linear_time`'s shapes, and both printed
/// at its smaller depth on a small stack.
#[test]
fn negations_and_indices_print_as_before() {
    assert_eq!(prefix_shape(0, 3).to_string(), "-(-(-x))");
    assert_eq!(prefix_shape(1, 3).to_string(), "x[0][0][0]");
    zed_tests::deep::on_small_stack(|| {
        for k in 0..2 {
            let t = prefix_shape(k, 2_000);
            assert_eq!(t.to_string().matches(["-", "[0]"][k]).count(), 2_000);
            std::hint::black_box(pretty(&t, 80));
        }
    });
}

/// Item PRINT-group-site-defs: a match on `v` with `n` type tests that each write a part twice,
/// `is (int | #x{k}, int | #x{k})`.
pub(super) fn declaring_shared_parts(n: usize) -> Term {
    use zed_kernel::Pattern;
    use zed_kernel::types::Type;
    let arms = (0..n)
        .map(|k| {
            let part = &Type::int() | &Type::atom(&format!("x{k}"));
            let pair = Type::tuple(vec![part.clone(), part]);
            (Pattern::Is(pair), zed_kernel::term::build::lit(k as i64))
        })
        .collect();
    Term::Match(Shared::new(var("v")), arms)
}

/// The term of `bench::a_term_declaring_its_shared_parts_scales` is written with one
/// declaration for each part written twice.
#[test]
fn a_term_with_type_tests_that_write_a_part_twice_declares_each_part() {
    for n in [1, 3] {
        let text = declaring_shared_parts(n).to_string();
        assert_eq!(text.matches("type T").count(), n, "{text}");
    }
}
