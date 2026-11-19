//! The syntax of a remap: one node `(remap of (as binders…) (into levels…))`, with `as`
//! alone the identity remap that names levels, `into` alone binding the source's levels by
//! name, and both halves together, written in one chain or with the `as` in parentheses.

use zed_tests::step_helpers::l01_10_lambdas_types_else_tuples::sx;
use zed_tests::step_helpers::l01_13_formatter::fmt;
use zed_tests::tables::check;

#[test]
fn as_alone_names_the_levels() {
    check(
        &[
            ("m as (k -> v)", "(remap m (as k v))"),
            (
                "m as (region -> day -> sku -> q)",
                "(remap m (as region day sku q))",
            ),
            ("m as (_ -> v)", "(remap m (as _ v))"),
            ("xs as (i -> v)", "(remap xs (as i v))"),
        ],
        sx,
    );
}

#[test]
fn into_alone_rebuilds_the_keypath() {
    check(
        &[
            ("m into (v -> k)", "(remap m (into v k))"),
            ("m into (k -> _)", "(remap m (into k _))"),
            (
                "m into (day -> region -> q)",
                "(remap m (into day region q))",
            ),
            ("xs into (i + 1 -> v)", "(remap xs (into (+ i 1) v))"),
            ("m into ((a, b) -> v)", "(remap m (into (tuple a b) v))"),
            ("m into (f(k) -> k -> v)", "(remap m (into (call f k) k v))"),
            (
                "m into (k div 4 -> k mod 4 -> v)",
                "(remap m (into (div k 4) (mod k 4) v))",
            ),
        ],
        sx,
    );
}

#[test]
fn as_and_into_make_one_remap() {
    check(
        &[
            (
                "m as (k -> v) into (v -> k)",
                "(remap m (as k v) (into v k))",
            ),
            (
                "(m as (k -> v)) into (v -> k)",
                "(remap m (as k v) (into v k))",
            ),
            (
                "m as (r -> d -> s -> q) into (d -> r -> s -> q)",
                "(remap m (as r d s q) (into d r s q))",
            ),
            (
                "xs as (i -> v) into (i + 1 -> v)",
                "(remap xs (as i v) (into (+ i 1) v))",
            ),
            // A second `into` remaps the first one's result.
            (
                "m into (b -> a -> v) into (a -> b -> v)",
                "(remap (remap m (into b a v)) (into a b v))",
            ),
        ],
        sx,
    );
}

#[test]
fn a_level_reduces_with_its_operator() {
    check(
        &[
            (
                "m into (d -> k >< (+) -> v)",
                "(remap m (into d (>< k (section +)) v))",
            ),
            ("m into (k >< g -> v)", "(remap m (into (>< k g) v))"),
            (
                "m as (r -> d -> s -> q) into (r -> d -> s >< (+) -> q)",
                "(remap m (as r d s q) (into r d (>< s (section +)) q))",
            ),
        ],
        sx,
    );
}

#[test]
fn a_remap_takes_suffixes_and_operators() {
    check(
        &[
            ("m into (v -> k).len", "(. (remap m (into v k)) len)"),
            (
                "m into (v -> k) >< (+)",
                "(>< (remap m (into v k)) (section +))",
            ),
            (
                "m as (k -> v) into (v -> k)[1]",
                "(index (remap m (as k v) (into v k)) 1)",
            ),
            ("m into (v -> k) == n", "(== (remap m (into v k)) n)"),
            ("m + n into (v -> k)", "(remap (+ m n) (into v k))"),
        ],
        sx,
    );
}

/// Each form of a later step is refused at the parser, naming what it is: a sort key (L8.1), a
/// join of keys (L8.2), a named key (L8.2b), a reduction policy (L9).
#[test]
fn later_forms_are_named() {
    for (text, want) in [
        (
            "m into (desc s -> n -> s)",
            zed_tests::not_yet!("the sort key `desc s`"),
        ),
        (
            "m into (asc s -> v)",
            zed_tests::not_yet!("the sort key `asc s`"),
        ),
        (
            "m into (a == b -> v)",
            zed_tests::not_yet!("the join `a == b`"),
        ),
        (
            "m into (a || b -> v)",
            zed_tests::not_yet!("the join `a || b`"),
        ),
        (
            "m into (day: d -> v)",
            zed_tests::not_yet!("the named key `day: d`"),
        ),
        (
            "m into (k >< f unordered -> v)",
            zed_tests::not_yet!("the reduction order `unordered`"),
        ),
    ] {
        assert_eq!(sx(text), format!("error: {want}"), "{text}");
    }
}

#[test]
fn each_form_formats_back() {
    check(
        &[
            ("f(m) = m  as(k->v);", "f(m) = m as (k -> v);\n"),
            ("f(m) = m into(v->k);", "f(m) = m into (v -> k);\n"),
            (
                "f(m) = m as (k->v)into(v ->k);",
                "f(m) = m as (k -> v) into (v -> k);\n",
            ),
            (
                "f(m) = (m as (k->v)) into (v->k);",
                "f(m) = m as (k -> v) into (v -> k);\n",
            ),
            ("f(m) = m into (k -> _);", "f(m) = m into (k -> _);\n"),
            (
                "f(m) = m into (d -> k ><(+) -> v);",
                "f(m) = m into (d -> k >< (+) -> v);\n",
            ),
            (
                "f(m) = m into ((a,b) -> v);",
                "f(m) = m into ((a, b) -> v);\n",
            ),
            (
                "f(m) = m into (i+1 -> v).len;",
                "f(m) = m into (i + 1 -> v).len;\n",
            ),
            (
                "f(m) = (m into (v->k)) >< (+);",
                "f(m) = m into (v -> k) >< (+);\n",
            ),
            // `into` binds looser than `+`, so `m + n` is the source without parentheses.
            (
                "f(m, n) = (m + n) into (v->k);",
                "f(m, n) = m + n into (v -> k);\n",
            ),
            (
                "f(m, n) = m + (n into (v->k));",
                "f(m, n) = m + (n into (v -> k));\n",
            ),
            ("f(m) = (m as (k->v)).len;", "f(m) = m as (k -> v).len;\n"),
            ("f(m) = (m into (v->k))(1);", "f(m) = m into (v -> k)(1);\n"),
            (
                "f(m) = (m into (v->k))::len;",
                "f(m) = m into (v -> k)::len;\n",
            ),
            (
                "f(m) = (m into (v->k)).w into (k->v);",
                "f(m) = m into (v -> k).w into (k -> v);\n",
            ),
        ],
        fmt,
    );
}
