//! Strings are ropes: a concatenation of two strings links them in a new cell without
//! copying, the length of a rope is counted without flattening it, and the bytes are copied
//! once, when the value leaves the program.

use zed_kernel::Prim;
use zed_kernel::term::build::{let_, lit, prim, var};

use super::{kernel, native};

#[test]
fn concatenation_links_ropes_and_copies_once_at_the_end() {
    // ((("ab" ++ "cd") ++ "ef") ++ "gh"), and its length.
    let mut s = lit("ab");
    for part in ["cd", "ef", "gh"] {
        s = prim(Prim::Concat, vec![s, lit(part)]);
    }
    let o = native(&s).unwrap();
    assert_eq!(o.value, kernel(&s).unwrap());
    assert_eq!((o.kernel_calls, o.stats.copied), (0, 8));
    let n = native(&prim(Prim::Len, vec![s.clone()])).unwrap();
    assert_eq!(n.value.to_string(), "8");
    assert_eq!((n.kernel_calls, n.stats.copied), (0, 0));
}

#[test]
fn a_string_two_uses_borrow_is_neither_counted_nor_copied() {
    let t = let_(
        "s",
        prim(Prim::Concat, vec![lit("na"), lit("ïve")]),
        prim(
            Prim::Tuple,
            vec![
                prim(Prim::Len, vec![var("s")]),
                prim(Prim::Upper, vec![var("s")]),
            ],
        ),
    );
    let o = native(&t).unwrap();
    assert_eq!(o.value, kernel(&t).unwrap());
    assert_eq!(o.value.to_string(), "(5, \"NAÏVE\")");
    // Both uses borrow the string, so its count is never written above 1; Upper runs in the
    // kernel, the one kernel call.
    assert_eq!(
        (o.kernel_calls, o.stats.shared, o.stats.increments),
        (1, 0, 0)
    );
}

#[test]
fn a_string_owned_twice_is_shared_not_copied() {
    let t = let_(
        "s",
        prim(Prim::Concat, vec![lit("ab"), lit("c")]),
        prim(Prim::Tuple, vec![var("s"), var("s")]),
    );
    let o = native(&t).unwrap();
    assert_eq!(o.value.to_string(), "(\"abc\", \"abc\")");
    assert_eq!(
        (o.kernel_calls, o.stats.shared, o.stats.increments),
        (0, 1, 1)
    );
}
