//! The benchmarks of `deep_types.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `deep_types.rs`.

use super::*;

#[test]
fn the_debug_text_of_a_deep_type_scales() {
    // TEST-bench-move-l0123 (author P169): n was 2,000, now 32,000; 1x measured 166 ms
    // (ns=165833473) at load 26.77 on 2026-11-14.
    scales_at(
        "the Debug text of a list type n deep",
        32_000,
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
    // TEST-bench-move-l0123 (author P169): n was 20,000, now 100,000; 1x measured 251 ms
    // (ns=250947441) at load 26.71 on 2026-11-14.
    scales_at(
        "a list type n deep, built",
        100_000,
        |_, i| i,
        |n, i| list_on(i, n),
    );
}

#[test]
fn printing_a_deep_type_scales() {
    // TEST-bench-move-l0123 (author P169): n was 20,000, now 26,000; 1x measured 217 ms
    // (ns=216811154) at load 26.71 on 2026-11-14.
    scales_at(
        "the text of a list type n deep",
        26_000,
        |n, i| list_on(i, n),
        |n, t| {
            let text = t.to_string();
            assert!(text.len() > n);
            (t, text)
        },
    );
}

// Releasing deep types, terms and patterns scales. The five checks were one test,
// `releasing_deep_types_terms_and_patterns_scales`, until TEST-bench-move-l0123 (author P169)
// split it so that each runs within the time of one test.
//
// The thread's tables of diagram nodes hold a type's parts until the thread ends, so a type
// dropped on this thread frees nearly nothing. Built and dropped on a thread of its own, it
// is freed when that thread ends, and the freeing is measured with the building.

/// Builds `make(i, n)` and drops it on a thread of its own, of a 2 MiB stack.
fn released_on_a_thread(make: fn(usize, usize) -> Type) -> impl Fn(usize, usize) + Sync {
    move |n: usize, i: usize| scaling::on_a_thread(2 << 20, || drop(make(i, n)))
}

#[test]
fn releasing_a_deep_list_type_scales() {
    // TEST-bench-move-l0123 (author P169): n was 20,000, now 50,000; 1x measured 154 ms
    // (ns=154361446) at load 26.71 on 2026-11-14.
    scales_at(
        "a list type n deep, built and released on a thread of its own",
        50_000,
        |_, i| i,
        released_on_a_thread(list_on),
    );
}

#[test]
fn releasing_a_deep_numeral_type_scales() {
    // TEST-bench-move-l0123 (author P169): n was 20,000, now 36,000; 1x measured 305 ms
    // (ns=304691587) at load 27.06 on 2026-11-14.
    scales_at(
        "a numeral type n deep, built and released on a thread of its own",
        36_000,
        |_, i| i,
        released_on_a_thread(|i, n| {
            let leaf = Type::lit(&Value::Int(i as i64)).expect("an integer literal is a type");
            (0..n).fold(leaf, |t, _| Type::atom_with("succ", &Type::tuple(vec![t])))
        }),
    );
}

#[test]
fn releasing_a_block_of_many_lets_scales() {
    // TEST-bench-move-l0123 (author P169): n was 20,000, now 400,000; 1x measured 122 ms
    // (ns=121690563) at load 27.06 on 2026-11-14.
    scales_at(
        "a block of n lets, released",
        400_000,
        |n, _| block(n),
        |_, t| drop(t),
    );
}

#[test]
fn releasing_a_deep_pattern_scales() {
    // TEST-bench-move-l0123 (author P169): n was 20,000, now 1,000,000; 1x measured 115 ms
    // (ns=114738880) at load 27.06 on 2026-11-14.
    scales_at(
        "a pattern n deep, released",
        1_000_000,
        |n, _| pattern(n),
        |_, p| drop(p),
    );
}

#[test]
fn releasing_a_deep_definition_body_scales() {
    // TEST-bench-move-l0123 (author P169): n was 20,000, now 1,000,000; 1x measured 169 ms
    // (ns=168893585) at load 27.06 on 2026-11-14.
    scales_at(
        "a definition body n deep, released",
        1_000_000,
        |n, _| bodies(n),
        |_, b| drop(b),
    );
}

#[test]
fn printing_a_recursive_type_nested_deep_in_its_own_arguments_scales() {
    // Each input is built from a group of its own, so no run finds the names of another made.
    // TEST-bench-move-l0123 (author P169): n was 500, now 32,000; 1x measured 103 ms (ns=103382085)
    // at load 29.08 on 2026-11-14.
    scales_at(
        "the text of Tree(Tree(..)) n deep",
        32_000,
        |n, i| trees(&tree(&format!("T{i}x{n}"), "A"), Type::int(), n),
        |n, t| {
            let text = t.to_string();
            assert!(text.len() > n);
            (t, text)
        },
    );
}

// Instantiating a group scales. The three checks were one test, `instantiating_a_group_scales`,
// until TEST-bench-move-l0123 (author P169) split it so that each runs within the time of one
// test.
//
// An instance was found by a scan of every instance made at definitions of the same text,
// keyed by the text of the definitions made anew at each call: nested instances took time
// quadratic in their depth, and a body of size s instantiated s times took s² (ledger
// INST-bucket). Each run has a group of its own, so no run finds another's instances.

#[test]
fn instantiating_a_group_nested_deep_scales() {
    // TEST-bench-move-l0123 (author P169): n was 1,000, now 32,000; 1x measured 109 ms
    // (ns=108988546) at load 29.08 on 2026-11-14.
    scales_at(
        "Tree(Tree(..)) n deep, instantiated",
        32_000,
        |n, i| tree(&format!("N{i}x{n}"), "A"),
        |n, g| trees(&g, Type::int(), n),
    );
}

#[test]
fn instantiating_a_large_body_at_many_arguments_scales() {
    // TEST-bench-move-l0123 (author P169): n was 500, now 24,000; 1x measured 139 ms (ns=139362835)
    // at load 29.08 on 2026-11-14.
    let lits = |s: usize| -> Vec<Type> {
        (0..s)
            .map(|k| Type::lit(&Value::Int(k as i64)).expect("an integer literal is a type"))
            .collect()
    };
    scales_at(
        "a body of size n at n different arguments",
        24_000,
        |n, i| (big(&format!("D{i}x{n}"), n), lits(n)),
        |_, (g, args)| {
            let made: Vec<Type> = args
                .into_iter()
                .map(|a| g.instance(vec![a]).remove(0))
                .collect();
            made
        },
    );
}

#[test]
fn instantiating_a_large_body_at_one_argument_many_times_scales() {
    // TEST-bench-move-l0123 (author P169): n was 500, now 40,000; 1x measured 165 ms (ns=165053845)
    // at load 29.08 on 2026-11-14.
    scales_at(
        "a body of size n at one argument n times",
        40_000,
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
    // TEST-bench-move-l0123 (author P169): n was 1,000, now 64,000; 1x measured 213 ms
    // (ns=212752729) at load 29.08 on 2026-11-14.
    scales_at(
        "Tree(Tree(..)) n deep, built and released at the end of its unit",
        64_000,
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
    // TEST-bench-move-l0123 (author P169): n was 2,000, now 4,000; 1x measured 91 ms (ns=91250481)
    // at load 29.64 on 2026-11-14. Its 1x stays under 0.5 s: building the inputs takes most of the
    // wall time (11.6 s at 4,000; 12,000 ran over 25 s).
    scales_at(
        "the Debug text of an xor chain",
        4_000,
        |n, i| xor_chain(i * 1_000_000, n),
        |_, t| format!("{t:?}"),
    );
}

#[test]
fn the_debug_text_of_a_shared_type_scales() {
    // TEST-bench-move-l0123 (author P169): n was 2,000, now 28,000; 1x measured 209 ms
    // (ns=209225536) at load 29.64 on 2026-11-14.
    scales_at(
        "the Debug text of a type with each level shared",
        28_000,
        |n, i| doubled(i * 1_000_000 + n, n),
        |_, t| format!("{t:?}"),
    );
}

// The deep tests of `deep_types.rs`, moved here as they stood by TEST-bench-move-l0123 (author
// P178: a test that needs an unusual size, a deep nesting, a stack of its own or many cases,
// is a benchmark). Each has a small instance on the default thread in `deep_types.rs`, named
// in its comment there.

/// How deep the types, terms, patterns and definition bodies go: 100,000, the depth at which
/// each overflowed the 2 MiB stack when its release, comparison or text was a recursion (file
/// header, COMPLEXITY.md K39), the smallest depth that record shows overflowing. It was 200,000
/// for types and 1,000,000 for terms, patterns and bodies, which took 4 to 10 s a test under
/// load (TEST-bench-move-l0123, author P169: a deep-stack test uses the smallest depth that
/// still overflows a default stack). At 1,000,000 every test here passes too.
const DEPTH: usize = 100_000;

/// How deep the chains of morphism types go: each level costs about 127,000 instructions to
/// build, 25 times a tuple's.
const MORPHISMS: usize = 100_000;

/// A list type [`DEPTH`] deep built twice, compared, and released, on a thread of the usual
/// 2 MiB stack of its own, so that the thread's tables of diagram nodes free the type when the
/// thread ends, as `releasing_a_deep_list_type_scales` frees it. TEST-bench-move-l0123 (author
/// P169): was 200,000 deep on the test's own thread; now 100,000 deep (see [`DEPTH`]), and
/// released at the end of a thread of its own, a path that only the benchmark checked before.
#[test]
fn a_list_type_nested_deep_is_built_compared_and_released() {
    scaling::on_a_thread(2 << 20, || {
        let (a, b) = (list(DEPTH), list(DEPTH));
        assert_eq!(a, b);
        assert!(a.subtype(&b));
        assert!(a.contains(&list_value(DEPTH)));
        assert!(!a.contains(&list_value(DEPTH - 1)));
        assert!((&a - &b).is_empty());
    });
}

/// TEST-bench-move-l0123 (author P169): was 200,000 deep, now 100,000 (see [`DEPTH`]).
#[test]
fn the_text_of_a_list_type_nested_deep_is_made() {
    let t = list(DEPTH);
    let text = t.to_string();
    assert!(text.starts_with("(tuple (tuple (tuple"));
    assert!(text.ends_with("int) int) int)"));
    assert_eq!(text.matches("tuple").count(), DEPTH);
    assert!(t.surface().to_string().len() > DEPTH);
}

/// How deep the types whose `Debug` text is made go: each level of a list type writes about
/// 1,000 bytes. The recursion of the derived `Debug`s overflowed the 2 MiB stack at 2,000 levels of a list or a
/// curried function and at 1,000 of a numeral. TEST-bench-move-l0123 (author P169): was
/// 20,000; now 2,000, the smallest depth this record shows overflowing for each of the three.
/// The text of each nests as deep as when the derived `Debug`s overflowed: measured on the
/// code of 2026-11-14, the text nests 16,005 brackets deep for a list 2,000 deep, 28,005 for a
/// numeral (14,005 at 1,000) and 12,005 for a curried function.
const DEBUG_DEPTH: usize = 2_000;

/// TEST-bench-move-l0123 (author P169): was 20,000 levels, now 2,000 (see [`DEBUG_DEPTH`]).
#[test]
fn the_debug_text_of_types_nested_deep_is_made() {
    let text = format!("{:?}", list(DEBUG_DEPTH));
    // Each level is a type with one tuple length, and the integers of each row are one more.
    assert_eq!(text.matches("Type(").count(), 2 * DEBUG_DEPTH + 1);
    assert!(text.ends_with("morphisms: Bdd(false) }))"));
    let text = format!("{:?}", numeral(DEBUG_DEPTH));
    assert_eq!(text.matches("\"succ\": AtomPart").count(), DEBUG_DEPTH);
    let text = format!("{:?}", curried(DEBUG_DEPTH));
    assert_eq!(text.matches("Morphism { guarantee: ").count(), DEBUG_DEPTH);
}

/// A numeral type [`DEPTH`] deep built twice, compared, printed and released, on a thread of the
/// usual 2 MiB stack of its own, so that the thread's tables free it when the thread ends, as
/// `releasing_a_deep_numeral_type_scales` frees it. TEST-bench-move-l0123 (author P169): was
/// 200,000 deep on the test's own thread; now 100,000 deep (see [`DEPTH`]), and released at the
/// end of a thread of its own, a path only the benchmark checked before.
#[test]
fn a_numeral_type_nested_deep_is_built_compared_and_released() {
    scaling::on_a_thread(2 << 20, || {
        let n = numeral(DEPTH);
        assert_eq!(n, numeral(DEPTH));
        assert_eq!(n.to_string().matches("#succ").count(), DEPTH);
    });
}

#[test]
fn a_curried_function_type_is_built_compared_printed_and_released() {
    let f = curried(MORPHISMS);
    assert_eq!(f, curried(MORPHISMS));
    assert!(f.surface().to_string().len() > MORPHISMS);
}

/// TEST-bench-move-l0123 (author P169): was 1,000,000 deep, now [`DEPTH`], 100,000, the depth
/// at which a term and a pattern overflowed the 2 MiB stack when their release was a recursion
/// (COMPLEXITY.md K39).
#[test]
fn a_program_and_a_pattern_nested_deep_are_released() {
    drop(block(DEPTH));
    drop(matches(DEPTH));
    drop(pattern(DEPTH));
    drop(Term::App(
        Shared::new(Term::Var("f".into())),
        vec![block(DEPTH), matches(DEPTH)],
    ));
}

/// TEST-bench-move-l0123 (author P169): was 1,000,000 deep, now [`DEPTH`], 100,000, the depth
/// at which a definition body overflowed the 2 MiB stack when its release was a recursion
/// (COMPLEXITY.md K39).
#[test]
fn the_body_of_a_definition_nested_deep_is_released() {
    drop(bodies(DEPTH));
}

/// TEST-bench-move-l0123 (author P169): was 4,000 types from the fixed seed 11; now 1,000 types
/// from a new seed each run, printed (`ZED_SEED=<seed>` repeats it).
#[test]
fn the_text_of_a_type_made_from_the_outside_in_is_its_text_made_from_the_inside_out() {
    outside_in_is_inside_out(1000);
}

/// How deep [`trees`] nests.
const TREES: usize = 10_000;

#[test]
fn a_recursive_type_nested_deep_in_its_own_arguments_is_printed() {
    // The name of each `Tree(…)` holds the text of its argument, another `Tree(…)` whose name
    // is not made yet: the loop that makes texts takes each name as an item of its stack.
    let t = trees(&tree("Tree", "A"), Type::int(), TREES);
    let text = t.to_string();
    assert_eq!(
        text,
        format!("{}int{}", "Tree(".repeat(TREES), ")".repeat(TREES))
    );
    let pair = Type::tuple(vec![t, Type::int()]).to_string();
    assert_eq!(pair, format!("(tuple {text} int)"));
}

#[test]
fn a_recursive_type_nested_deep_in_its_own_arguments_is_released() {
    // Each `Tree(…)` holds its argument, the instance below it, and was dropped by a recursion as
    // deep as the nesting once the end of its unit or of its thread freed it (repair
    // DEEP-types-regress). Freed both ways, on a thread of the usual 2 MiB stack.
    scaling::on_a_thread(2 << 20, || {
        drop(trees(&tree("Ended", "A"), Type::int(), TREES));
        Type::forget_emptiness();
    });
    scaling::on_a_thread(2 << 20, || {
        drop(trees(&tree("Exited", "A"), Type::int(), TREES));
    });
}

#[test]
fn the_text_of_a_type_with_recursive_types_is_the_same_made_outside_in_and_inside_out() {
    outside_in_is_inside_out_with_trees(1500);
}

/// How deep [`doubled`] goes on the default stack. The `Debug` that wrote a type once per path
/// wrote `2^d` copies of the leaf; this depth would never end.
const DOUBLINGS: usize = 20_000;

#[test]
fn the_debug_text_of_a_shared_type_writes_it_once() {
    let text = format!("{:?}", doubled(0, DOUBLINGS));
    // Each `t_k` below the top is numbered where first written and referred to once after.
    assert_eq!(text.matches('=').count(), DOUBLINGS - 1);
    assert_eq!(text.matches('#').count(), 3 * (DOUBLINGS - 1));
    assert!(text.len() < 1_000 * DOUBLINGS);
}
