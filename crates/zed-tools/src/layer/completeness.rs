//! The cases of the pieces the unit test of `layer` exercises that it leaves out (row
//! TEST-complete-crates): a row of the table "Defined words by layer" (DESIGN.md sec:layers),
//! the backtick spans of a cell, the layer of a word, and the `// layer Lk` label. The tool as a
//! whole is tested by tests/steps/m0_03_grammar_tools/layer_roles.rs.

use super::{WordTable, label_at, spans};

fn row(l: &str) -> Result<WordTable, String> {
    let mut t = WordTable::default();
    t.read_row(l)?;
    Ok(t)
}

#[test]
fn a_cell_holds_its_non_empty_backtick_spans_in_order() {
    assert_eq!(spans("`a`, `b c` and `d`"), ["a", "b c", "d"]);
    assert_eq!(spans("`a``b`"), ["a", "b"]);
    assert_eq!(spans("``"), Vec::<&str>::new());
    assert_eq!(spans("—"), Vec::<&str>::new());
    assert_eq!(spans(""), Vec::<&str>::new());
    // A backtick with no partner opens nothing.
    assert_eq!(spans("`a` and `b"), ["a"]);
    assert_eq!(spans("`"), Vec::<&str>::new());
}

#[test]
fn each_column_and_prefix_puts_a_word_in_its_own_kind() {
    let t = row("| L5 | `@a`, `w` | `f`, `#x` | `g`, `x::len`, `x::y::z` |").unwrap();
    assert_eq!(t.annots.get("@a"), Some(&5));
    // A plain word is a facet only in the facet column; in the others it is a form.
    assert_eq!(t.forms.get("w"), Some(&5));
    assert_eq!(t.facets.get("f"), Some(&5));
    assert_eq!(t.forms.get("g"), Some(&5));
    assert!(!t.facets.contains_key("w") && !t.facets.contains_key("g"));
    assert!(!t.forms.contains_key("f"));
    // An atom is an atom in any column.
    assert_eq!(t.atoms.get("#x"), Some(&5));
    // A `::` read is the word right after the first `::`.
    assert_eq!(t.reads.get("len"), Some(&5));
    assert_eq!(t.reads.get("y"), Some(&5));
    assert!(!t.reads.contains_key("z"));
    // Columns after the third are not read.
    let t = row("| L5 | — | — | `g` | `h` |").unwrap();
    assert_eq!(t.forms.get("g"), Some(&5));
    assert!(!t.forms.contains_key("h"));
}

#[test]
fn spans_that_name_no_word_of_source_are_skipped() {
    let t =
        row("| L2 | — | `with x` | `.fold`, `abs`, `zedc build --total`, `n:`, `f(…)` |").unwrap();
    assert!(t.annots.is_empty() && t.facets.is_empty() && t.forms.is_empty());
    assert!(t.reads.is_empty() && t.atoms.is_empty());
    // Only a word before `:` or `(…)` is an argument or a call: anything else is refused.
    for bad in ["`a b:`", "`a b(…)`", "`f()`", "`1x`", "`a-b`", "`é`"] {
        assert!(row(&format!("| L2 | — | — | {bad} |")).is_err(), "{bad}");
    }
}

#[test]
fn a_row_with_too_few_columns_or_no_layer_is_refused() {
    assert_eq!(
        row("| L2 | `@a` | `f` |").err(),
        Some("a table row with too few columns: | L2 | `@a` | `f` |".into())
    );
    for l in [
        "| 2x | — | — | — |",
        "| L | — | — | — |",
        "| — | — | — | — |",
    ] {
        assert_eq!(
            row(l).err(),
            Some(format!("a table row with no layer: {l}")),
            "{l}"
        );
    }
    // The `L` is optional.
    assert_eq!(row("| 4 | — | — | `w` |").unwrap().forms.get("w"), Some(&4));
}

#[test]
fn a_word_keeps_the_first_layer_that_names_it_and_its_lowest_kind() {
    let mut t = WordTable::default();
    t.read_row("| L3 | — | — | `w` |").unwrap();
    t.read_row("| L9 | — | `w` | `w` |").unwrap();
    assert_eq!(t.forms.get("w"), Some(&3));
    assert_eq!(t.facets.get("w"), Some(&9));
    // A word of two kinds has the lower layer.
    assert_eq!(t.layer_of("w"), Some(3));
    assert_eq!(t.layer_of("v"), None);
}

#[test]
fn the_words_a_row_names_in_prose_are_forms_of_their_layer() {
    let t = row("| L13 | — | — | — |").unwrap();
    assert_eq!(t.forms.get("sanitize"), Some(&13));
    let t = row("| L20 | — | — | — |").unwrap();
    for w in ["serialize", "Json", "Csv"] {
        assert_eq!(t.forms.get(w), Some(&20), "{w}");
    }
    assert!(row("| L12 | — | — | — |").unwrap().forms.is_empty());
}

#[test]
fn a_label_is_the_layer_comment_at_the_start_whose_number_ends_its_word() {
    assert_eq!(label_at("// layer L3\nmain"), Some(3));
    assert_eq!(label_at("// layer L12 (ports)"), Some(12));
    assert_eq!(label_at("// layer L0"), Some(0));
    assert_eq!(label_at("// layer L7."), Some(7));
    for s in [
        "// layer L3a",
        "// layer L3_",
        "// layer L",
        "// layer Lx",
        " // layer L3",
        "//layer L3",
        "// Layer L3",
        "x\n// layer L3",
        "",
        "// layer L99999999999",
    ] {
        assert_eq!(label_at(s), None, "{s:?}");
    }
}
