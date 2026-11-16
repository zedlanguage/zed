//! Function types and the variance faults of Dart (author, 2026-11-15, P286: "contravariance is
//! the root of numerous very hard-to-understand type errors in Dart, and some runtime errors.
//! Make sure Zed is not going to fall to the same problems").
//!
//! Dart treats a generic type as covariant even where its type parameter is a function's
//! parameter type, so `C<num> c = C<int>((i) => i.isEven); c.fun(10);` passes the checker and
//! fails at run time (dart.dev, lint `unsafe_variance`); `covariant` on an override and an
//! implicit downcast from `dynamic` move a check to run time the same way. In Zed a plain
//! function type `K -> V` is exact, so its domain neither widens nor narrows (DESIGN.md
//! sec:type_language, "Morphism types carry two domain bounds"); only a partial type `K ->? V`
//! varies, taking any function whose domain lies within `K`. A container or struct holding a
//! function inherits that rule, which makes it invariant in the function's domain, as Dart's
//! lint asks for and cannot enforce. Each case below is a verdict only: the messages for the
//! sound programs that exact domains reject are row MSG-fn-domain-wider-repair.

use super::type_errors;

/// `src` is accepted.
fn accepted(src: &str) {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
}

/// `src` gives exactly one error.
fn rejected(src: &str) {
    assert_eq!(type_errors(src).len(), 1, "{src}: {:?}", type_errors(src));
}

/// A function with a narrower domain where a wider one is wanted would be called outside its
/// domain, the run-time fault of Dart's `covariant`: rejected, at any depth.
#[test]
fn a_narrower_domain_is_rejected_where_a_wider_one_is_called() {
    rejected(
        "small(x: int) = 1;\napply(f: (x: int | f64) -> int) = f(x: 3);\nr = apply(f: small);\n",
    );
    rejected("tag(x: #a) = 1;\napply(f: (x: #a | #b) -> int) = f(x: #b);\nr = apply(f: tag);\n");
    rejected(
        "small(x: int) = 1;\nuseWide(b: ((x: int | f64) -> int,)) = 0;\nr = useWide(b: (small,));\n",
    );
    // An empty domain is not a subtype of an exact one: the bottom-type fault of Dart.
    rejected("none(x: Never) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: none);\n");
}

/// A wider result than the slot's is rejected; a narrower one is accepted.
#[test]
fn results_are_covariant() {
    accepted("one(x: int) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: one);\n");
    rejected(
        "both(x: int) = rat(x) / 2;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: both);\n",
    );
}

/// A partial slot `K ->? V` takes a function whose domain lies within `K`, the empty one too:
/// its caller handles `#notFound`, so no call reaches a value outside the domain.
#[test]
fn a_partial_slot_takes_a_narrower_domain() {
    accepted(
        "small(x: int) = 1;\napply(f: (x: int | f64) ->? int) = f(x: 3) else 0;\nr = apply(f: small);\n",
    );
    accepted(
        "none(x: Never) = 1;\napply(f: (x: int) ->? int) = f(x: 3) else 0;\nr = apply(f: none);\n",
    );
}

/// A wider exact domain is not a narrower one, as a domain is observable (`::domain`), and not
/// within a partial slot's `K` either. These programs never fail at run time, and they are
/// rejected; a lambda written at the slot adopts its domain (sec:type_resolution, rule 2), so
/// `x -> inc(x: x)` is the repair, and `xs.map(inc)` is accepted.
#[test]
fn a_wider_domain_is_rejected_and_its_lambda_accepted() {
    rejected("inc(x: int | f64) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: inc);\n");
    rejected("tag(x: #a | #b) = 1;\napply(f: (x: #a) -> int) = f(x: #a);\nr = apply(f: tag);\n");
    rejected(
        "inc(x: int | f64) = 1;\napply(f: (x: int) ->? int) = f(x: 3) else 0;\nr = apply(f: inc);\n",
    );
    rejected(
        "inc(x: int | f64) = 1;\nuseNarrow(b: ((x: int) -> int,)) = 0;\nr = useNarrow(b: (inc,));\n",
    );
    rejected(
        "useF(g: (x: int) -> int) = g(x: 1);\nouter(h: (g: (x: int | f64) -> int) -> int) = 0;\nr = outer(h: useF);\n",
    );
    accepted(
        "inc(x: int | f64) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: x -> inc(x: x));\n",
    );
    accepted("apply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: x -> 1);\n");
    accepted("inc(x: int) = 1;\nuse(b: ((x: int) -> int,)) = 0;\nr = use(b: (inc,));\n");
    accepted("inc(x: int | f64) = 1;\nxs = [1, 2, 3];\nys = xs.map(inc);\n");
}

/// Row MSG-fn-domain-wider-repair, part (1): a function whose exact domain is wider than the
/// slot's, where the lambda that calls it on the slot's arguments fits, is refused with a
/// headline that says the domain is wider, naming each parameter, and ends with the call
/// rewritten with that lambda, as code. The lambda each repair writes is accepted (the
/// `accepted` cases), and none is offered where it would be refused too: a narrower domain,
/// and a result the slot's arrow does not take (`x -> inc(x: x)` gives `int | f64` there).
#[test]
fn a_wider_domain_says_so_and_offers_its_lambda_as_code() {
    assert_eq!(
        type_errors(
            "inc(x: int | f64) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: inc);\n"
        ),
        vec![
            "`inc` is `(x: int | f64) -> 1`, not `(x: int) -> int`: its domain is wider than \
             `(x: int) -> int`'s, `x` in `int | f64` where `(x: int) -> int` takes `int`, and a \
             function passed as `(x: int) -> int` must take exactly that domain. Try \
             `apply(f: x -> inc(x: x))` instead. [inc]"
        ]
    );
    assert_eq!(
        type_errors(
            "inc(positional a: int | f64, b: int) = 1;\napply(f: (positional p: int, b: int) -> int) = f(3, b: 4);\nr = apply(f: inc);\n"
        ),
        vec![
            "`inc` is `(int | f64, b: int) -> 1`, not `(int, b: int) -> int`: its domain is \
             wider than `(int, b: int) -> int`'s, `p` in `int | f64` where \
             `(int, b: int) -> int` takes `int`, and a function passed as \
             `(int, b: int) -> int` must take exactly that domain. Try \
             `apply(f: (p, b) -> inc(p, b: b))` instead. [inc]"
        ]
    );
    accepted(
        "inc(positional a: int | f64, b: int) = 1;\napply(f: (positional p: int, b: int) -> int) = f(3, b: 4);\nr = apply(f: (p, b) -> inc(p, b: b));\n",
    );
    for src in [
        "inc(x: int) = 1;\napply(f: (x: int | f64) -> int) = 0;\nr = apply(f: inc);\n",
        "inc(x: int | f64) = x;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: inc);\n",
    ] {
        let errors = type_errors(src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(
            !errors[0].contains("Try") && errors[0].contains("does not fit that one"),
            "{src}: {errors:?}"
        );
    }
    rejected(
        "inc(x: int | f64) = x;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: x -> inc(x: x));\n",
    );
}
