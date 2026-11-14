//! A group the default trivial-model report stopped in is printed as not decided, also after
//! the search found a model (FAIL-trivial-stop-after-model, found by TEST-complete-misc).

use super::brute::{expand, models};
use super::trivial::{End, Mode, Theory, render, report};

/// DESIGN: "it lists models until it has two or meets the first choice that leads to no model,
/// and at that choice it stops, prints the group as not decided, the chain of laws that rules
/// the choice out, and the menu." This holds as well when the search found one model before
/// the stop: whether the group has one model or several is then not decided.
///
/// Fields `f`, `c`, `d` in that order, with `c != d` and, for every `a`, `f(c) != d || c == a`;
/// since `a` takes both values, `f(c) != d` must hold, so `f(c) == c`. The models are `f: #a`
/// with `c: #a`, `f: #b` with `c: #b`, and `f: (x -> x)` with either, four in all. In declaration
/// order the search takes `f: #a`, `c: #a`, `d: #b`, a model; then `c: #b`, which leaves `d`
/// only `#a`, where `f(c) != d` fails: a choice that leads to no model. (Found among the random
/// theories of `brute::random_theory`, seed 62, and rewritten with plain names.)
#[test]
fn a_stop_after_one_model_prints_the_group_as_not_decided() {
    let mut t = Theory::new("Stop");
    t.field("f", 1)
        .field("c", 0)
        .field("d", 0)
        .law("apart", "", "c != d")
        .law("fixed", "a", "f(c) != d || c == a");
    let mut all = models(&t);
    all.sort();
    assert_eq!(all.len(), 4);
    assert_eq!(expand(&t, &report(&t, Mode::Exhaustive)), all);
    let r = report(&t, Mode::Default);
    let text = render(&t, &r);
    assert!(
        matches!(r.groups[0].end, End::Stopped(_)) && r.groups[0].models == [vec![0, 0, 1]],
        "the search stops after the model f: #a, c: #a, d: #b\n{text}"
    );
    assert!(
        text.contains("    f, c, d, linked by laws apart, fixed: not decided.\n"),
        "{text}"
    );
    assert!(
        text.contains("        @exhaustive interface Stop(positional T) { ... }\n"),
        "{text}"
    );
    assert!(!text.contains("models on two values"), "{text}");
}
