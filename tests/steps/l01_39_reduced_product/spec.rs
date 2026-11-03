//! The design's examples (DESIGN.md Part G, step L1.39).

use zedc::query::Db;
use zedc::store::product::forward;

use super::*;

/// The front end accepts `src` with no diagnostic.
fn accepted(src: &str) {
    if let Err(ds) = &*Db::new().front(src) {
        panic!("{src}: rejected: {ds:?}");
    }
}

#[test]
fn an_arm_that_fixes_n_mod_4_within_0_to_10_holds_1_to_9() {
    let src = "ok = (n) -> if n >= 0 && n <= 10 && n mod 4 == 1 { n } else { 0 };";
    accepted(src);
    let (_, _, a) = arms_of(src);
    let then = arm(&a, "((n mod 4) == 1)", true);
    let n = then.scope.get("n");
    // The hull is `int[1..=9]`, and the congruence keeps the members exactly: 1, 5 and 9.
    assert_eq!(n.ints().hull().to_string(), "[1..=9]");
    assert_eq!(n.cell.congruence.element.to_string(), "1 mod 4");
    // The other arm loses the two ends; 5 is not listed, so it is kept.
    let other = arm(&a, "((n mod 4) == 1)", false).scope.get("n");
    assert_eq!(other.ints().to_string(), "[..=0, 2..=8, 10..]");
}

#[test]
fn an_arm_no_value_reaches_is_unreachable_and_the_program_is_accepted() {
    let src = "ok = (n) -> if n >= 2 && n <= 4 && n mod 4 == 1 { n } else { 0 };";
    accepted(src);
    let (_, _, a) = arms_of(src);
    let then = arm(&a, "((n mod 4) == 1)", true);
    assert!(!then.reachable());
    assert_eq!(then.scope.to_string(), "unreachable\n");
    // The other arm is reached by every integer.
    let other = arm(&a, "((n mod 4) == 1)", false);
    assert!(other.reachable());
    assert_eq!(other.scope.get("n").to_string(), "ints [..]\ntype int\n");
}

#[test]
fn a_binding_read_from_a_static_if_is_static() {
    let src = "debug = false;\nmode = if debug { 1 } else { 2 };";
    accepted(src);
    let t = binding(src, "mode");
    let a = arms(&t, &Scope::new([]));
    assert_eq!(a.len(), 2);
    assert!(!arm(&a, "debug", true).reachable());
    assert_eq!(
        arm(&a, "debug", false).scope.to_string(),
        "debug:\n  finite {false}\n  type false\n  time build\n"
    );
    let mode = forward(&t, &mut Scope::new([]));
    assert_eq!(
        mode.to_string(),
        "ints [2..=2]\ncongruence 2\nfinite {2}\ntype 2\ntime build\n"
    );
}

#[test]
fn a_negated_equality_excludes_the_literal_by_complement() {
    // Types, intervals and finite sets are exact, so `!=` removes the one value from each.
    let src = "ok = (n) -> if n >= 0 && n <= 3 { if n != 2 { n } else { 0 } } else { 0 };";
    accepted(src);
    let (_, _, a) = arms_of(src);
    let n = arm(&a, "(n != 2)", true).scope.get("n");
    assert_eq!(n.ints().to_string(), "[0..=1, 3..=3]");
    assert_eq!(n.to_string().lines().nth(1), Some("finite {0, 1, 3}"));
    let two = arm(&a, "(n != 2)", false).scope.get("n");
    assert_eq!(two.value(), Some(&zed_kernel::Value::Int(2)));
}

#[test]
fn a_relation_between_two_names_bounds_each() {
    // `x < y` and `y <= 5` with `x >= 3` leave `x` in `3..=4` and `y` in `4..=5`.
    let src = "ok = (x, y) -> if x >= 3 && x < y && y <= 5 { x + y } else { 0 };";
    accepted(src);
    let (_, _, a) = arms_of(src);
    let s = &arm(&a, "(y <= 5)", true).scope;
    assert_eq!(s.get("x").ints().to_string(), "[3..=4]");
    assert_eq!(s.get("y").ints().to_string(), "[4..=5]");
    assert!(s.to_string().contains("relation "), "{s}");
}

#[test]
fn a_meet_takes_the_earlier_binding_time_and_a_join_the_later() {
    use zedc::store::lattice::Lattice;
    use zedc::store::product::Time;
    assert_eq!(Time::Build.meet(&Time::Run), Time::Build);
    assert_eq!(Time::Build.join(&Time::Run), Time::Run);
    assert_eq!(Time::bottom(), Time::Never);
    // A binding computed from a parameter is known only when the program runs.
    let (_, _, a) = arms_of("ok = (n) -> { k = n + 1; if k > 0 { k } else { 0 } };");
    let k = arm(&a, "(k > 0)", true).scope.get("k");
    assert_eq!(k.time.element, Time::Run);
    assert_eq!(k.ints().to_string(), "[1..]");
}

#[test]
fn a_join_keeps_the_affine_relation_of_its_sides() {
    // Each side fixes `i` to one value, so `i + j == n` holds on both; the join keeps it.
    let src = "ok = (i, j, n) -> if (i == 0 && j == n) || (i == 1 && j == n - 1) { if i + j != n { 1 } else { 2 } } else { 0 };";
    accepted(src);
    let (_, _, a) = arms_of(src);
    assert!(!arm(&a, "((i + j) != n)", true).reachable());
    assert!(arm(&a, "((i + j) != n)", false).reachable());
}

#[test]
fn a_negated_equality_with_i64_max_keeps_the_integers_past_it() {
    // Kernel integers are unbounded: `n` may be `i64::MAX + 1`, which is not `i64::MAX`, so the
    // arm `n >= i64::MAX` under `n != i64::MAX` is reachable (S22c).
    let m = i64::MAX;
    let src =
        format!("ok = (n) -> if n != {m} {{ if n >= {m} {{ 1 }} else {{ 2 }} }} else {{ 0 }};");
    accepted(&src);
    let (_, _, a) = arms_of(&src);
    assert!(arm(&a, &format!("(n >= {m})"), true).reachable());
    assert!(arm(&a, &format!("(n >= {m})"), false).reachable());
}
