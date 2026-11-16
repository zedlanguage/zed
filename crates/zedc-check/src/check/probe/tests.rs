//! Tests of the counters of `probe.rs`: each checks a small unit and reads the report.

use super::last_report;

/// The probe's report for the unit `text`, checked alone.
fn report(text: &str) -> String {
    let tokens = zedc_syntax::lex::lex(text).expect("the unit lexes");
    let (tree, errors) = zedc_syntax::parse::parse_unit(text, &tokens, zedc_syntax::parse::TOP);
    assert!(errors.is_empty(), "the unit parses");
    let unit = zedc_syntax::ast::unit(text, &tokens, &tree).expect("the unit builds");
    let res = zedc_resolve::resolve::resolve(&unit).expect("the unit resolves");
    let info = crate::check::walk::check(&unit, &res);
    assert!(info.errors.is_empty(), "the unit checks");
    last_report()
}

fn forwards(r: &str) -> Vec<&str> {
    r.lines().filter(|l| l.starts_with("F ")).collect()
}

/// `h1` calls `h0`, whose one need is a call of its parameter `f`: the call is admitted
/// (its arguments are `h1`'s own parameters), its needs record one need, nothing reads
/// the record before `h1` ends, and `h1`'s end keeps it. The call of `h1` at the top
/// passes a lambda and a literal, no classes, and is not admitted.
#[test]
fn a_call_of_a_generic_function_on_parameters_is_admitted_and_kept() {
    let r = report(
        "h0(positional f, positional x) = f(x);\n\
         h1(positional f, positional x) = h0(f, x);\n\
         a = h1(y -> y + 1, 1);\n",
    );
    assert!(r.starts_with("A F2-arg-not-class=1 admit=1\n"), "{r}");
    assert!(r.contains("\nS scalar[] same_use=0 errors=0\n"), "{r}");
    let fs = forwards(&r);
    assert_eq!(fs.len(), 1, "{r}");
    assert!(
        fs[0].contains(" level=1 size=1 internal=1 end=kept "),
        "{r}"
    );
    assert!(!fs[0].contains("E:need"), "{r}");
}

/// A second `m.map(f)` after the call of `h0` is a need equal to the one the forward
/// recorded on `m`'s class: eager finds it in `known`, so D must force there. (A map need
/// and not a call need: a call need's key holds the place of its call in the body, so
/// `f(x)` in `h1` is a different key from `f(x)` in `h0`, FAIL-elab-named-call-generic-param.)
#[test]
fn a_need_equal_to_a_deferred_one_collides() {
    let r = report(
        "h0(positional f, positional m) = m.map(f);\n\
         h1(positional f, positional m) = (h0(f, m), m.map(f));\n\
         a = h1(y -> y + 1, {\"k\" -> 0});\n",
    );
    let fs = forwards(&r);
    assert_eq!(fs.len(), 1, "{r}");
    assert!(fs[0].contains("E:need-collide"), "{r}");
}

/// Negative control: no function calls a generic function on classes, so no call is
/// admitted and no forward is made.
#[test]
fn no_generic_call_on_classes_makes_no_forward() {
    let r = report(
        "h0(positional f, positional x) = f(x);\n\
         a = h0(y -> y + 1, 1);\n",
    );
    assert!(r.starts_with("A F2-arg-not-class=1\n"), "{r}");
    assert!(forwards(&r).is_empty(), "{r}");
}

/// The lambda's parameter `y` is a class of level 2, `m` one of level 1. The call
/// `h0(y, m)` is admitted, and its need `m.map(y)` records the key `Map { f: $y }` on
/// `m`'s class, so `need` lowers `y`'s class to `m`'s level (`lower` to the level of the
/// root, walk.rs `need`): a scalar field of an older class written by the check of an
/// admitted call, which D's claim says never happens. The class is then no longer of the
/// call's level, so the forward escapes.
#[test]
fn a_key_naming_a_deeper_class_lowers_it() {
    let r = report(
        "h0(positional f, positional m) = m.map(f);\n\
         g(positional m) = y -> h0(y, m);\n\
         a = g({\"k\" -> 0});\n",
    );
    assert!(r.starts_with("A F2-arg-not-class=1 admit=1\n"), "{r}");
    assert!(
        r.contains("\nS scalar[level=1] same_use=0 errors=0\n"),
        "{r}"
    );
    let fs = forwards(&r);
    assert_eq!(fs.len(), 1, "{r}");
    assert!(fs[0].contains(" end=escaped "), "{r}");
}
