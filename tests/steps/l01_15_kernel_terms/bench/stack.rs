//! Terms far deeper than a plain recursion fits on a thread of the default 2 MiB stack (author
//! P178: an unusual size is a benchmark). A derived `Clone`, `==`, `Debug` or `Drop`, or a
//! printer that recursed over its layout, overflows that stack near 10,000 levels; each keeps
//! its own stack on the heap (COMPLEXITY.md K39). The same checks at small depths are in
//! `deep.rs` and `scaling.rs`.

use zed_kernel::print::pretty;
use zed_kernel::term::Pattern;
use zed_kernel::{Shared, Term};

use crate::deep::{dag, indents, nested, printed};
use crate::scaling::{SHAPES, dropped_shapes, lambda_depth, prefix_shape, shape, var};

#[test]
fn a_term_far_deeper_than_the_stack_copies_compares_and_prints() {
    // A derived `Clone`, `==` or `Debug` overflows a 2 MiB stack near 10,000 levels.
    let n = 100_000;
    zed_tests::deep::on_small_stack(|| {
        for ((what, a), (_, b)) in nested(n).into_iter().zip(nested(n)) {
            let copy = a.clone();
            assert!(copy == a, "{what}: a copy equals its original");
            assert!(a == b, "{what}: two builds are equal");
            let text = format!("{a:?}");
            assert_eq!(text, format!("{b:?}"), "{what}");
            assert_eq!(text, format!("{copy:?}"), "{what}");
            assert!(text.len() > n, "{what}: {} bytes", text.len());
        }
        // One leaf changed at the bottom is found.
        let differ = (0..n).fold(var("z"), |b, _| Term::Lam(vec!["y".into()], Shared::new(b)));
        let (_, lams) = nested(n).swap_remove(0);
        assert!(lams != differ);
    });
}

#[test]
fn equal_dags_compare_once_per_shared_pair() {
    // Two DAGs built apart share no subterm, so no pair is equal by its id alone: a walk of
    // the paths reads 3^60 of them.
    zed_tests::deep::on_small_stack(|| {
        assert!(dag(60) == dag(60));
        assert!(dag(60) != dag(59));
        // Each level holds its one subterm three times, so the drop of a level was the last
        // holder of the level below inside its own drop, which recursed: a deep DAG
        // overflowed the stack.
        drop(dag(100_000));
    });
}

#[test]
fn a_term_far_deeper_than_the_stack_is_displayed_and_broken() {
    // The printer recursed over a tree of its layout and overflowed a 2 MiB stack near 10,000
    // levels.
    let n = 100_000;
    zed_tests::deep::on_small_stack(|| {
        for (what, t) in nested(n).into_iter().chain(printed(n)) {
            let flat = t.to_string();
            assert!(flat.len() > n, "{what}: {} bytes", flat.len());
            assert_eq!(pretty(&t, usize::MAX), flat, "{what}");
            if !indents(what) {
                let broken = pretty(&t, 80);
                assert_eq!(
                    broken.split_whitespace().collect::<String>(),
                    flat.split_whitespace().collect::<String>(),
                    "{what}"
                );
            }
        }
        let tuple = (0..n).fold(Pattern::Bind("p".into()), |p, _| {
            Pattern::Tuple(vec![p, Pattern::Wild])
        });
        assert_eq!(tuple.to_string().len(), "p".len() + n * "(, _)".len());
    });
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

/// Both shapes of `bench::negations_and_indices_print_in_linear_time` printed at its smaller
/// depth, on one line and broken to a width.
#[test]
fn negations_and_indices_print_2000_deep_on_a_small_stack() {
    zed_tests::deep::on_small_stack(|| {
        for k in 0..2 {
            let t = prefix_shape(k, 2_000);
            assert_eq!(t.to_string().matches(["-", "[0]"][k]).count(), 2_000);
            std::hint::black_box(pretty(&t, 80));
        }
    });
}
