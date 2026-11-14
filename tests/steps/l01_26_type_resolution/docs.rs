//! Doc comments after parsing (DESIGN.md sec:grammar, comments): a block of `///` lines
//! attaches to the declaration that follows it, a block that attaches to none is reported,
//! and a `[name]` link in one must resolve.

use zedc::run::load;

/// The errors of loading the program `src`, one per line as `line:col: why`, or "" when it
/// loads.
fn load_errors(src: &str) -> String {
    match load(src.as_bytes()) {
        Ok(_) => String::new(),
        Err(e) => e,
    }
}

const MAIN: &str =
    "main(m: MainArgs) {\n  m.stdout <- String(total(price: 3.0f64, qty: 2.0f64));\n}\n";

#[test]
fn a_doc_block_attaches_to_the_declaration_after_it() {
    let src = format!(
        "/// The price of `qty` items at `price` each, before [tax].\n\
         /// See [String] for how [main] prints it.\n\
         total(price: f64, qty: f64) = price * qty;\n\
         /// The sales tax, as a fraction.\n\
         tax = 0.08f64;\n{MAIN}"
    );
    assert_eq!(load_errors(&src), "");
}

#[test]
fn a_doc_block_inside_a_body_attaches_to_a_local_binding() {
    let src = "/// Writes the total.\n\
               main(m: MainArgs) {\n  \
               /// Two items at 3.0 each.\n  \
               t = 3.0f64 * 2.0f64;\n  \
               m.stdout <- String(t);\n}\n";
    assert_eq!(load_errors(src), "");
}

#[test]
fn a_doc_block_before_no_declaration_is_reported() {
    // At the end of the unit.
    let src = format!("total(price: f64, qty: f64) = price * qty;\n{MAIN}/// Unfinished.\n");
    assert_eq!(
        load_errors(&src),
        "5:1: this doc comment documents no declaration; it is at the end of the unit."
    );
    // Before a push, which declares nothing.
    let src = "total(price: f64, qty: f64) = price * qty;\n\
               main(m: MainArgs) {\n  \
               /// The receipt line.\n  \
               m.stdout <- String(total(price: 3.0f64, qty: 2.0f64));\n}\n";
    assert_eq!(
        load_errors(src),
        "3:3: this doc comment documents no declaration; a `///` block comes right before a \
         binding, a function or another declaration."
    );
}

#[test]
fn a_block_is_reported_once_and_a_four_slash_comment_is_no_doc() {
    let src = format!(
        "total(price: f64, qty: f64) = price * qty;\n{MAIN}/// One.\n/// Two.\n//// Not a doc.\n"
    );
    assert_eq!(load_errors(&src).lines().count(), 1);
    let src =
        format!("//// A banner, not a doc.\n\ntotal(price: f64, qty: f64) = price * qty;\n{MAIN}");
    assert_eq!(load_errors(&src), "");
}

#[test]
fn a_link_that_names_nothing_is_rejected() {
    let src = format!(
        "/// The price before [discount], from [total].\n\
         total(price: f64, qty: f64) = price * qty;\n{MAIN}"
    );
    assert_eq!(
        load_errors(&src),
        "1:22: The doc link `[discount]` names nothing in scope."
    );
}

#[test]
fn code_spans_markdown_links_and_non_names_are_not_links() {
    let src = format!(
        "/// Indexes as `xs[i]`, see [the guide](https://example.com), keys [1] and [].\n\
         total(price: f64, qty: f64) = price * qty;\n{MAIN}"
    );
    assert_eq!(load_errors(&src), "");
}

#[test]
fn doc_errors_join_the_elaboration_errors() {
    let src = format!(
        "/// See [nowhere].\n\
         total(price: f64, qty: f64) = price * qty;\n\
         far = 1e400f64;\n{MAIN}"
    );
    let e = load_errors(&src);
    assert_eq!(e.lines().count(), 2, "{e}");
    assert!(e.starts_with("1:9: The doc link `[nowhere]`"), "{e}");
    assert!(
        e.contains("3:7: `1e400` is larger than the largest f64"),
        "{e}"
    );
}

/// `n` documented functions, each doc block linking to the next function and to itself in
/// backquotes, and a `main` calling the first.
pub(super) fn doc_blocks_with_links(n: usize) -> String {
    let mut s = String::new();
    for i in 0..n {
        s.push_str(&format!(
            "/// Step {i} of the pipeline; see [h{}] and `[h{i}]`.\nh{i}(x: int) = x + {i};\n",
            (i + 1) % n
        ));
    }
    s.push_str("main(m: MainArgs) {\n  m.stdout <- String(h0(x: 1));\n}\n");
    s
}

#[test]
fn doc_blocks_linking_to_each_other_load() {
    // A small instance of the benchmark `bench::docs::checking_n_doc_blocks_with_links_scales`.
    assert_eq!(load_errors(&doc_blocks_with_links(3)), "");
}

/// A string's hole holds code, so a `///` comment in it is a doc comment, which attaches to the
/// declaration after it in the same hole or else is reported (FAIL-lex-doc-in-hole, found by
/// TEST-complete-lex, author P189). One at the end of a hole, at the top level or in a body, or
/// in a hole of a string in a hole, documents no declaration; a doc block before the binding of
/// that string still attaches.
#[test]
fn a_doc_comment_in_a_hole_that_documents_nothing_is_reported() {
    let none = "this doc comment documents no declaration; a `///` block comes right before a \
                binding, a function or another declaration.";
    for (src, at) in [
        (
            "s = \"\"\"\n${1 /// d\n}\n\"\"\";\nmain(m: MainArgs) {\n  m.stdout <- s;\n}\n",
            "2:5",
        ),
        (
            "s = \"\"\"\n  a ${1 /// d\n} b\n  \"\"\";\nmain(m: MainArgs) {\n  m.stdout <- s;\n}\n",
            "2:9",
        ),
        (
            "main(m: MainArgs) {\n  /// The text.\n  s = \"\"\"\n${1 /// d\n}\n\"\"\";\n  \
             m.stdout <- s;\n}\n",
            "4:5",
        ),
        (
            "s = \"\"\"\n${\"\"\"\n${1 /// d\n}\n\"\"\"}\n\"\"\";\nmain(m: MainArgs) {\n  \
             m.stdout <- s;\n}\n",
            "3:5",
        ),
    ] {
        assert_eq!(load_errors(src), format!("{at}: {none}"), "{src:?}");
    }
}

/// A doc comment in a hole before a local binding of a function body in that hole attaches to
/// that binding, as it would outside the string.
#[test]
fn a_doc_comment_in_a_hole_attaches_to_a_binding_in_the_hole() {
    let src = "f = (x: int) -> \"\"\"\n${((y: int) -> {\n  /// One more than `y`.\n  \
               z = y + 1;\n  z\n})(x)}\n\"\"\";\nmain(m: MainArgs) {\n  m.stdout <- f(1);\n}\n";
    assert_eq!(load_errors(src), "");
}
