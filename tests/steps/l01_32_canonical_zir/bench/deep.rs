//! A graph nested 20,000 deep, whose deepest region matches a value against a pattern that
//! binds a written name, canonicalized on a thread of the default 2 MiB stack (author P178: an
//! unusual size is a benchmark). A plain recursion takes at least 112 bytes a level (measured
//! at opt-level 2), so 20,000 levels, 2.2 MB, would overflow that stack. The same checks at
//! small depths are in `scaling.rs`.

use zed_tests::deep::on_small_stack;
use zedc::zir::canon::{address, canonicalize, key, ranks, step};

use crate::scaling::deep_match;

#[test]
fn a_graph_nested_20000_deep_is_canonicalized_on_a_2_mib_stack() {
    on_small_stack(|| {
        let mut g = deep_match(20_000, "x");
        assert_eq!(ranks(&g)[0], 1, "one written binder");
        assert_eq!(
            address(&g).expect("memory for the address"),
            address(&deep_match(20_000, "y")).expect("memory for the address")
        );
        assert_eq!(
            key(&canonicalize(&g)).expect("memory for the key"),
            key(&canonicalize(&deep_match(20_000, "y"))).expect("memory for the key")
        );
        let normal = canonicalize(&g);
        while step(&mut g).is_some() {}
        assert_eq!(g, normal);
    });
}
