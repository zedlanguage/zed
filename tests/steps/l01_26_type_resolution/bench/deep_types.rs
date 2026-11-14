//! The time of replacing variables in, and comparing, types with `2^n` paths through `n` nodes.

use zed_tests::deep::on_small_stack;
use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::super::deep_types::{replaced_each_way, shared};

#[test]
fn replacements_in_a_shared_type_take_linear_time() {
    // Each run builds its type: `Sig::settle` keeps what it made in the signature, so a second
    // run on one type would not settle it again.
    on_small_stack(|| {
        scaling::check_order("each replacement in a shared type n deep", 4000, 1, |n| {
            let made = replaced_each_way(&shared(n));
            let (tys, held) = made.split_at(5);
            assert!(tys.iter().all(|t| t.tuples.len() == 1), "{n} deep");
            assert_eq!(held[0].fns.len(), 1, "{n} deep");
        });
    });
}

#[test]
fn shared_types_built_apart_compare_in_linear_time() {
    // Each side holds `2^n` paths through `n` nodes, and no node is shared between the sides:
    // a comparison that followed the paths took `2^n` time.
    let n = 2000;
    let pairs: std::collections::BTreeMap<usize, (Ty, Ty)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|k| (k, (shared(k), shared(k))))
        .collect();
    on_small_stack(|| {
        scaling::check_order("== on two shared types n deep built apart", n, 1, |k| {
            let (a, b) = &pairs[&k];
            assert!(a == b, "{k} deep");
        });
    });
}
