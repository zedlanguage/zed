//! Printing and reading back types of `n` parts, at `n` and `8n` (`printed.rs`).

use zed_kernel::types::Type as KType;
use zed_tests::scaling;

use crate::printed::*;

/// Printing the kernel's meet of `n` function types, alone and in a union with another arrow:
/// the printer writes each as the one arrow it is (FAIL-types-meet-exact-arrows-differing-
/// domains), from one union of the guarantees, one meet of the permissions and of the values,
/// and one subtype test, so the work is that of those kernel operations on `n` types.
#[test]
fn printing_a_meet_of_many_function_types_scales() {
    let n = 16_000;
    let inputs = scaling::inputs(n, |m| {
        let met = KType::meet_all((0..m).map(|i| {
            KType::partial(
                &KType::atom(&format!("a{i}")) | &KType::int(),
                KType::bool(),
            )
        }));
        let met = &met & &KType::exact(KType::int(), KType::bool());
        let other = KType::partial(KType::f64(), KType::atom("b"));
        let union = &met | &other;
        (met, union)
    });
    scaling::check("printing a meet of n function types", n, |size| {
        let (met, union) = &inputs[&size];
        assert_eq!(met.surface().root, "int -> bool");
        assert_eq!(union.surface().root, "(f64 ->? #b) | (int -> bool)");
    });
}

#[test]
fn reading_a_printed_type_back_scales() {
    let n = 16_000;
    let inputs = scaling::inputs(n, wide);
    scaling::check(
        "reading back a union of n atoms and a tuple of n components",
        n,
        |size| a_printed_type_read_back(&inputs[&size], size),
    );
}

/// Printing a union of `n` atoms, each with its payload type, and reading the text back, each
/// timed alone: the printer takes the payload atoms out of the kernel set in one difference.
#[test]
fn printing_atoms_with_payloads_scales() {
    let n = 2800;
    let inputs = scaling::inputs(n, |m| {
        let t = atoms_with_payloads(m);
        let text = t.to_string();
        (t, text)
    });
    scaling::check("printing a union of n atoms with payloads", n, |size| {
        atoms_with_payloads_printed(&inputs[&size].0, size);
    });
    scaling::check("reading back a union of n atoms with payloads", n, |size| {
        let (t, text) = &inputs[&size];
        assert_eq!(&back(text), t);
    });
}

/// Reading back an intersection of `n` function types of one parameter list: the parameter
/// lists are compared with the first once each, and the arrows joined into one signature.
#[test]
fn reading_an_overload_of_many_arrows_back_scales() {
    let n = 7100;
    let inputs = scaling::inputs(n, overload);
    scaling::check("reading back an overload of n arrows", n, |size| {
        an_overload_read_back(&inputs[&size], size);
    });
}

/// Reading back an overload of `n` arrows nested `n` deep in parentheses, to the left and to
/// the right: each intersection is read once, with the one around it, so the cost is linear
/// and not a walk of the inner arrows at each depth.
#[test]
fn reading_an_overload_nested_in_parentheses_back_scales() {
    let n = 3200;
    for (side, left) in [("left", true), ("right", false)] {
        let inputs = scaling::inputs(n, |m| nested_overload(m, left));
        scaling::check(
            &format!("reading back an overload of n arrows nested n deep to the {side}"),
            n,
            |size| an_overload_read_back(&inputs[&size], size),
        );
    }
}

/// Printing a union that leaves a bounds clause to its end as an arrow's key, nested `n` deep
/// through the key of a member arrow: each union writes its clause before its own `)`, once
/// (FAIL-parens-wrong-is-empty-seed), so the text and the work are linear in `n`.
#[test]
fn printing_key_unions_that_keep_their_clauses_nested_scales() {
    let n = 500;
    let inputs = scaling::inputs(n, |m| {
        let text = format!(
            "{}int{}",
            "((rat) | ((((T) -> T for T in int | f64)) & ((f64) -> (_))) | ((".repeat(m),
            ") -> int)) -> int".repeat(m)
        );
        back(&text)
    });
    scaling::check("printing n nested key unions with clauses", n, |size| {
        let printed = inputs[&size].to_string();
        assert_eq!(printed.matches(" for ").count(), size, "{printed}");
    });
}

/// Reading back a tuple of `n` families with their keys exactly and printing it again (row
/// RANGE-keys-in-printed-type): each key is two int leaves read in O(digits) and each family
/// is denoted and printed in O(1) besides, so the work is linear in the text.
#[test]
fn reading_back_families_with_their_keys_scales() {
    let n = 4000;
    let inputs = scaling::inputs(n, keyed_families);
    scaling::check(
        "reading back a tuple of n families with their keys",
        n,
        |size| keyed_families_read_back(&inputs[&size], size),
    );
}
