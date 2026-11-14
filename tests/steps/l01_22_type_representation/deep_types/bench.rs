//! The benchmarks of `deep_types.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `deep_types.rs`.

use super::*;

#[test]
fn the_debug_text_of_a_deep_type_scales() {
    scales_at(
        "the Debug text of a list type n deep",
        2_000,
        |n, i| list_on(i, n),
        |n, t| {
            let text = format!("{t:?}");
            assert!(text.len() > n);
            (t, text.len())
        },
    );
}

#[test]
fn building_a_deep_type_scales() {
    scales("a list type n deep, built", |_, i| i, |n, i| list_on(i, n));
}

#[test]
fn printing_a_deep_type_scales() {
    scales(
        "the text of a list type n deep",
        |n, i| list_on(i, n),
        |n, t| {
            let text = t.to_string();
            assert!(text.len() > n);
            (t, text)
        },
    );
}

#[test]
fn releasing_deep_types_terms_and_patterns_scales() {
    // The thread's tables of diagram nodes hold a type's parts until the thread ends, so a type
    // dropped on this thread frees nearly nothing. Built and dropped on a thread of its own, it
    // is freed when that thread ends, and the freeing is measured with the building.
    let on_a_thread = |make: fn(usize, usize) -> Type| {
        move |n: usize, i: usize| scaling::on_a_thread(2 << 20, || drop(make(i, n)))
    };
    scales(
        "a list type n deep, built and released on a thread of its own",
        |_, i| i,
        on_a_thread(list_on),
    );
    scales(
        "a numeral type n deep, built and released on a thread of its own",
        |_, i| i,
        on_a_thread(|i, n| {
            let leaf = Type::lit(&Value::Int(i as i64)).expect("an integer literal is a type");
            (0..n).fold(leaf, |t, _| Type::atom_with("succ", &Type::tuple(vec![t])))
        }),
    );
    scales(
        "a block of n lets, released",
        |n, _| block(n),
        |_, t| drop(t),
    );
    scales(
        "a pattern n deep, released",
        |n, _| pattern(n),
        |_, p| drop(p),
    );
    scales(
        "a definition body n deep, released",
        |n, _| bodies(n),
        |_, b| drop(b),
    );
}

#[test]
fn printing_a_recursive_type_nested_deep_in_its_own_arguments_scales() {
    // Each input is built from a group of its own, so no run finds the names of another made.
    scales_at(
        "the text of Tree(Tree(..)) n deep",
        500,
        |n, i| trees(&tree(&format!("T{i}x{n}"), "A"), Type::int(), n),
        |n, t| {
            let text = t.to_string();
            assert!(text.len() > n);
            (t, text)
        },
    );
}

#[test]
fn instantiating_a_group_scales() {
    // An instance was found by a scan of every instance made at definitions of the same text,
    // keyed by the text of the definitions made anew at each call: nested instances took time
    // quadratic in their depth, and a body of size s instantiated s times took s² (ledger
    // INST-bucket). Each run has a group of its own, so no run finds another's instances.
    scales_at(
        "Tree(Tree(..)) n deep, instantiated",
        1000,
        |n, i| tree(&format!("N{i}x{n}"), "A"),
        |n, g| trees(&g, Type::int(), n),
    );
    let lits = |s: usize| -> Vec<Type> {
        (0..s)
            .map(|k| Type::lit(&Value::Int(k as i64)).expect("an integer literal is a type"))
            .collect()
    };
    scales_at(
        "a body of size n at n different arguments",
        500,
        |n, i| (big(&format!("D{i}x{n}"), n), lits(n)),
        |_, (g, args)| {
            let made: Vec<Type> = args
                .into_iter()
                .map(|a| g.instance(vec![a]).remove(0))
                .collect();
            made
        },
    );
    scales_at(
        "a body of size n at one argument n times",
        500,
        |n, i| big(&format!("S{i}x{n}"), n),
        |n, g| {
            let first = g.instance(vec![Type::int()]).remove(0);
            for _ in 1..n {
                assert!(g.instance(vec![Type::int()])[0] == first);
            }
            first
        },
    );
}

#[test]
fn releasing_a_recursive_type_nested_deep_in_its_own_arguments_scales() {
    // Built and freed on a thread of its own, at the end of its unit, from a group of its own.
    scales_at(
        "Tree(Tree(..)) n deep, built and released at the end of its unit",
        1000,
        |_, i| i,
        |n, i| {
            scaling::on_a_thread(2 << 20, || {
                drop(trees(&tree(&format!("R{i}x{n}"), "A"), Type::int(), n));
                Type::forget_emptiness();
            })
        },
    );
}

#[test]
fn the_debug_text_of_an_xor_chain_scales() {
    scales_at(
        "the Debug text of an xor chain",
        2_000,
        |n, i| xor_chain(i * 1_000_000, n),
        |_, t| format!("{t:?}"),
    );
}

#[test]
fn the_debug_text_of_a_shared_type_scales() {
    scales_at(
        "the Debug text of a type with each level shared",
        2_000,
        |n, i| doubled(i * 1_000_000 + n, n),
        |_, t| format!("{t:?}"),
    );
}
