//! A call of a bit word whose arguments do not fit its parameters (FAIL-bitword-arity-message,
//! found by TEST-complete-reduced, author P189): an argument missing, in the wrong form, of an
//! unknown name, given twice or one too many. It is reported as the same call of a function
//! is, by the word's name, as `bitReverse`, not by its type `(int, width: int) -> int`, with
//! the repairs; a word has no declaration, so no repair edits one or declares a function in
//! its place. A call ending in `...` that leaves no parameter out is reported once. DESIGN
//! sec:values_morphisms: "a missing argument with no default is an arity error whose menu names
//! the default, the curried call and the lambda"; the plain-message rule: the program's words.

use super::rejected;

#[test]
fn a_malformed_call_of_a_word_names_the_word_and_its_repairs() {
    for (src, word, repair) in [
        (
            "x = bitReverse(1);\n",
            "bitReverse",
            "repair: pass a value for `width`",
        ),
        (
            "x = mulHi(1, 2);\n",
            "mulHi",
            "repair: pass a value for `width`",
        ),
        ("x = bitAnd(1);\n", "bitAnd", "repair: pass a value for `b`"),
        (
            "x = bitReverse(1, 8);\n",
            "bitReverse",
            "repair: pass `width` by name",
        ),
        (
            "x = bitReverse(1, w: 8);\n",
            "bitReverse",
            "repair: remove this argument",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains(&format!("`{word}`")), "{src}: {out}");
        assert!(!out.contains("(int, width: int) -> int`"), "{src}: {out}");
        assert!(out.contains(repair), "{src}: {out}");
    }
    // One message for one wrong `...`.
    let out = rejected("x = pdep(1, 3, ...);\n");
    assert_eq!(out.matches("ends in `...`").count(), 1, "{out}");
}

#[test]
fn each_misfit_of_a_word_names_the_word_and_offers_no_declaration_edit() {
    for (src, word, repair) in [
        ("x = bitAnd(1, 2, 3);\n", "bitAnd", "remove"),
        (
            "x = bitReverse(x: 1, width: 8);\n",
            "bitReverse",
            "repair: pass `x` by position",
        ),
        (
            "x = shl(1, k: 2, width: 8);\n",
            "shl",
            "repair: pass `k` by position",
        ),
        (
            "x = 1.bitReverse();\n",
            "bitReverse",
            "repair: pass a value for `width`",
        ),
        ("x = 1.popCount(2);\n", "popCount", "remove"),
        (
            "x = bitReverse(1, w: 8);\n",
            "bitReverse",
            "repair: write the name of a parameter of `bitReverse` in place of `w`",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains(&format!("`{word}`")), "{src}: {out}");
        assert!(!out.contains("-> int`"), "{src}: {out}");
        assert!(out.contains(repair), "{src}: {out}");
        assert!(!out.contains("declaration"), "{src}: {out}");
        assert!(!out.contains("declare a named function"), "{src}: {out}");
    }
    // A wrong `...`: a positional operand left out, and one message for it.
    let out = rejected("x = pdep(1, ...);\n");
    assert!(out.contains("`pdep`"), "{out}");
    assert!(out.contains("repair: remove the `...`"), "{out}");
    assert!(!out.contains("-> int`"), "{out}");
}
