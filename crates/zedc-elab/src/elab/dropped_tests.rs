//! Unit tests of [`Elab::check_dropped`](super::state::Elab::check_dropped)
//! (PROOF-block-body-kept-when-named), which switch
//! [`Instancing::written_named`](super::instances::Instancing::written_named) off to make the
//! reference it would miss. They
//! are a file of their own, declared in `elab.rs`, so that `bodies.rs` imports nothing of
//! `elab.rs`, which imports it (step S.1f).

use zedc_syntax::ast::unit;
use zedc_syntax::lex::lex_fence;
use zedc_syntax::parse::{TOP, parse};

use super::elaborate_text;
use super::instances::MISS_WRITTEN_NAMED;

/// `top`, a fold by `max` whose identity its calls decide; `mi["a"]` an empty `int` level and
/// `m["a"]` an empty `f64` level.
const AT: &str = "top(positional xs) = xs >< max;\n\
    m = { \"a\" -> [1.0] }.map(r -> r.where(v -> v > 3.0));\n\
    mi = { \"a\" -> [1] }.map(r -> r.where(v -> v > 3));\n";

/// The errors of elaborating `body` after [`AT`], with [`MISS_WRITTEN_NAMED`] set to `miss`,
/// each as its message followed by its notes' texts.
fn errors(body: &str, miss: bool) -> Vec<String> {
    let text = format!("{AT}{body}");
    let tokens = lex_fence(&text).unwrap();
    let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(&text, &tokens, &tree).unwrap();
    let res = zedc_resolve::resolve::resolve(&stmts).unwrap();
    MISS_WRITTEN_NAMED.set(miss);
    let out = elaborate_text(&stmts, &res, Some(&text), None);
    MISS_WRITTEN_NAMED.set(false);
    let es = out.err().unwrap_or_default();
    (es.iter())
        .map(|e| {
            let notes: Vec<&str> = e.notes.iter().map(|n| &*n.text).collect();
            format!("{} | {}", e.message, notes.join(" | "))
        })
        .collect()
}

/// The words the checker gives the fold of `top` run at `int` and at `f64`.
const FOLD: &str = "a fold `><` that the calls of one function run on entries of type `int` \
                    and `f64`, where an empty level folds to `#empty` at `int` and `-inf` at \
                    `f64`";

#[test]
fn a_kept_term_that_names_a_dropped_written_body_is_refused() {
    // `(h, 0)[0]` names `h`'s written body, whose fold no call decides, so it is kept and its
    // fold refused. Were that reference missed, the body would be dropped while `p` names
    // it, and `check_dropped` refuses the program, naming `h`, rather than leave `p`
    // unbound.
    let body = "a = { h(positional q) = top(q); p = (h, 0)[0]; (h(mi[\"a\"]), p(m[\"a\"])) };\n";
    let seen = errors(body, false);
    assert_eq!(seen.len(), 1, "{seen:?}");
    assert!(seen[0].starts_with(FOLD), "{seen:?}");
    // The call `p(m["a"])`, which no body took, is refused at the fold as before.
    let dropped = |missed: &[String]| -> String {
        let named: Vec<&String> = (missed.iter())
            .filter(|e| e.starts_with("`h` used as a value"))
            .collect();
        assert_eq!(named.len(), 1, "{missed:?}");
        named[0].clone()
    };
    let e = dropped(&errors(body, true));
    assert!(
        e.starts_with(
            "`h` used as a value while its calls run a fold at more than one type, is part \
             of the Zed language"
        ),
        "{e}"
    );
    assert!(e.contains(&format!("`h` runs this fold: {FOLD}")), "{e}");
    assert!(
        e.contains("repair: call `h` where it is used, as `h(q)`, or write `h` once"),
        "{e}"
    );
    // The repair's call passes each parameter with no default, a named one by name.
    let body = "a = { h(positional q, by: int, d = 0) = (top(q), by, d); p = (h, 0)[0]; \
                (h(mi[\"a\"], by: 1), p(m[\"a\"], by: 2)) };\n";
    let e = dropped(&errors(body, true));
    assert!(e.contains("as `h(q, by: by)`"), "{e}");
}

#[test]
fn a_dropped_written_body_no_term_names_is_not_refused() {
    // `h` called by name at each type: each call runs a body made at its identity, the
    // written body is dropped, and nothing names it, with the reference search on or off.
    let body = "a = { h(positional q) = top(q); (h(mi[\"a\"]), h(m[\"a\"])) };\n";
    assert_eq!(errors(body, false), Vec::<String>::new());
    assert_eq!(errors(body, true), Vec::<String>::new());
}
