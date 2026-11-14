//! A disjunct whose projection is refused is left out, which leaves the hull wider but sound,
//! and its cause is returned with the hulls, so that the scope records it.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, Shared, project_each};
use zedc::store::product::{Asked, Kept, Refused, Scope};

fn sym(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

/// `Σ c·s + k >= 0`.
fn ge(terms: &[(&str, i128)], k: i128) -> Formula {
    let lin = terms.iter().fold(Lin::constant(k), |l, (s, c)| {
        l.plus(&Lin::atom(sym(s)).times(*c))
    });
    Formula::Con(Con::ge(&lin, &Lin::constant(0)))
}

/// Four constraints on four names whose integer points are not decided (the system of
/// `Refusal::Growth` in tests/steps/l01_38_presburger/omega.rs).
fn growth() -> Formula {
    Formula::and(vec![
        ge(&[("x", 4), ("w", -12), ("y", -10), ("z", -12)], 11),
        ge(&[("w", 4), ("x", 10), ("y", -10), ("z", -11)], -28),
        ge(&[("w", 11), ("x", 4), ("y", -1), ("z", 12)], -28),
        ge(&[("w", -8), ("x", -5), ("y", 12), ("z", -1)], 31),
    ])
}

#[test]
fn the_cause_of_a_refused_disjunct_is_returned() {
    let f = Formula::and(vec![
        ge(&[("v", 1)], 0),
        Formula::Or(Shared::new(vec![growth(), ge(&[("v", 1)], -5)])),
    ]);
    let (hulls, skipped) = project_each(&f, &[sym("v")]).expect("the base has a point");
    assert_eq!(skipped, vec![Refusal::Growth], "{hulls:?}");
    assert!(hulls[0].is_ok(), "{hulls:?}");
    // Without the refused disjunct, nothing is skipped.
    let f = Formula::and(vec![
        ge(&[("v", 1)], 0),
        Formula::Or(Shared::new(vec![ge(&[("v", 1)], -9), ge(&[("v", 1)], -5)])),
    ]);
    let (_, skipped) = project_each(&f, &[sym("v")]).expect("a point");
    assert!(skipped.is_empty(), "{skipped:?}");
}

/// The four constraints of [`growth`] as a Zed test, on the names `x`, `y`, `z` and `w`
/// renamed by `names`.
fn growth_test(names: [&str; 4]) -> String {
    let [x, y, z, w] = names;
    format!(
        "4 * {x} - 12 * {w} - 10 * {y} - 12 * {z} + 11 >= 0 \
         && 4 * {w} + 10 * {x} - 10 * {y} - 11 * {z} - 28 >= 0 \
         && 11 * {w} + 4 * {x} - {y} + 12 * {z} - 28 >= 0 \
         && 0 - 8 * {w} - 5 * {x} + 12 * {y} - {z} + 31 >= 0"
    )
}

/// The scope of the arm of `ok = (x, y, z, w, a, b, c, d) -> if <test> { 1 } else { 0 }`
/// taken by `outcome`.
fn arm_scope(test: &str, outcome: bool) -> Scope {
    let src = format!("ok = (x, y, z, w, a, b, c, d) -> if {test} {{ 1 }} else {{ 0 }};");
    let (_, _, arms) = super::arms_of(&src);
    super::arm(&arms, ">= 0", outcome).scope.clone()
}

fn texts(s: &Scope) -> Vec<String> {
    s.warnings().iter().map(|w| w.to_string()).collect()
}

const GROWTH: &str = "to find whole numbers that meet these conditions, the checker removes one \
                      variable at a time, putting in place of the conditions on it conditions on \
                      the variables left. Here four variables or more are left, and removing any \
                      one of them would leave more conditions than there are now, so the work \
                      could grow without end";

/// The sentence that closes [`GROWTH`] where the checker kept bounds `source` that rule out no
/// value of `names`.
fn none_ruled_out(source: &str, names: &str) -> String {
    format!(
        "{GROWTH}. The checker stopped there, and {source} rule out no value: {names} may still \
         be any whole number"
    )
}

/// The bounds a refused projection keeps.
const EACH: &str =
    "the bounds that each condition gives each variable from the bounds of the others";

/// The bounds a refused test keeps.
const FOUND: &str = "the bounds it found on the test's variables";

/// The first line of a warning about the conditions that hold in a scope.
const WIDER: &str = "warning: Cannot find exactly which values meet the conditions here";

/// What the step that says what a scope keeps ends with.
const SOUND: &str = "; so the checker may reject or warn about code here that is correct, and it \
                     does not accept code that is wrong";

/// The repair a warning ends with: a value stated for `v`, put before `conditions`, which the
/// warning calls `what`.
fn value(v: &str, what: &str, conditions: &str) -> String {
    format!(
        "\n  [4] repair: if `{v}` is meant to take only one value in {what}, state that value, and \
         the checker removes `{v}` from the question: `{v} == 0 && {conditions}`, with the value \
         in place of `0`"
    )
}

/// A test whose integer points the solver does not decide gives the arm it guards one
/// warning, which names the test's constraints, what was not decided and why, and what the
/// scope keeps.
#[test]
fn a_refused_test_gives_one_warning_at_its_test() {
    let s = arm_scope(&growth_test(["x", "y", "z", "w"]), true);
    let constraints = "12 * w + 10 * y + 12 * z <= 4 * x + 11 && 8 * w + 5 * x + z <= 12 * y + 31 \
                       && 4 * w + 10 * x >= 10 * y + 11 * z + 28 && 11 * w + 4 * x + 12 * z >= y + 28";
    assert_eq!(
        texts(&s),
        vec![format!(
            "{WIDER}\
             \n  [1] here the conditions `{constraints}` hold\
             \n  [2] the checker could not work out which values each of their variables can take: {}\
             \n  [3] so here each of their variables keeps only those bounds, which may be wider than the conditions allow{SOUND}{}",
            none_ruled_out(EACH, "`w`, `x`, `y` and `z`"),
            value("w", "the conditions", constraints)
        )]
    );
}

/// A test that calls a helper is narrowed through the helper's body as one test, whose preimage
/// asks the solver the helper's four constraints at once: refused, it gives a warning for
/// each outcome, which names the test and the outcome assumed. The test is named as the
/// program wrote it, `g(x, y, z, w)`, and the constraints by the names it wrote: neither by the
/// names elaboration gave the binders (`x@2`, the `x` of `ok` beside the `x` of `g`) nor
/// closed over the helper, a let of a lambda that is not syntax the program can write.
#[test]
fn a_refused_test_through_a_helper_names_the_test_and_its_outcome() {
    let src = format!(
        "g(positional x: int, positional y: int, positional z: int, positional w: int) = {};\n\
         ok(x, y, z, w) = if g(x, y, z, w) {{ 1 }} else {{ 0 }};",
        growth_test(["x", "y", "z", "w"])
    );
    let (_, _, arms) = super::arms_of(&src);
    let test = "g(x, y, z, w)";
    let at = |outcome: bool| {
        format!(
            "warning: Cannot find exactly which values make `{test}` {outcome}\
                 \n  [1] here the test `{test}` is {outcome}\
                 \n  [2] the checker could not work out which values its variables can take when it is {outcome}: {}\
                 \n  [3] so the test narrows the values of its variables here only to those bounds, which may be wider than it allows{SOUND}{}",
            none_ruled_out(FOUND, "`w`, `x`, `y` and `z`"),
            value("x", "the test", test)
        )
    };
    // Taken true, the helper's constraints also hold in the scope, and their projection is
    // refused too, which gives a second warning; taken false, only the preimage is refused.
    let constraints = "12 * w + 10 * y + 12 * z <= 4 * x + 11 \
                       && 8 * w + 5 * x + z <= 12 * y + 31 \
                       && 4 * w + 10 * x >= 10 * y + 11 * z + 28 \
                       && 11 * w + 4 * x + 12 * z >= y + 28";
    let projection = format!(
        "{WIDER}\
         \n  [1] here the conditions `{constraints}` hold\
         \n  [2] the checker could not work out which values each of their variables can take: {}\
         \n  [3] so here each of their variables keeps only those bounds, which may be wider than the conditions allow{SOUND}{}",
        none_ruled_out(EACH, "`w`, `x`, `y` and `z`"),
        value("w", "the conditions", constraints)
    );
    assert_eq!(
        texts(&super::arm(&arms, "g(", true).scope),
        vec![projection, at(true)]
    );
    assert_eq!(
        texts(&super::arm(&arms, "g(", false).scope),
        vec![at(false)]
    );
}

/// The same four constraints with no constants have the point zero, so their projection is
/// taken, but the projection onto each name is refused: one warning for each name, in the
/// order of the names. The projection onto a name adds a bound on it to the four constraints
/// and asks the solver again (`hull_from` in `presburger.rs`), so all four names stay live and
/// the refusal is the one for four variables or more; no fifth name is needed (cross-review
/// XR3 expected one, reading the projection as fixing the name).
#[test]
fn a_refused_projection_onto_each_name_gives_one_warning_for_each() {
    let test = "4 * x - 12 * w - 10 * y - 12 * z >= 0 && 4 * w + 10 * x - 10 * y - 11 * z >= 0 \
                && 11 * w + 4 * x - y + 12 * z >= 0 && 0 - 8 * w - 5 * x + 12 * y - z >= 0";
    let constraints = "12 * w + 10 * y + 12 * z <= 4 * x && 8 * w + 5 * x + z <= 12 * y \
                       && 4 * w + 10 * x >= 10 * y + 11 * z && 11 * w + 4 * x + 12 * z >= y";
    let expected: Vec<String> = ["w", "x", "y", "z"]
        .map(|n| {
            format!(
                "warning: Cannot find exactly which values `{n}` can take here\
                 \n  [1] here the conditions `{constraints}` hold\
                 \n  [2] the checker could not work out which values `{n}` can take: {}\
                 \n  [3] so here that variable keeps only those bounds, which may be wider than the conditions allow{SOUND}{}",
                none_ruled_out(
                    &format!("the bounds that each condition gives `{n}` from the bounds of the others"),
                    &format!("`{n}`")
                ),
                value("w", "the conditions", constraints)
            )
        })
        .into();
    assert_eq!(texts(&arm_scope(test, true)), expected);
    // Through a helper whose parameters have the names of the caller's, so that elaboration
    // renames both (`x@1`, `x@2`): the constraints and the name projected onto are written
    // as the program wrote them.
    let src = format!(
        "g(positional x: int, positional y: int, positional z: int, positional w: int) = {test};\n\
         ok(x, y, z, w) = if g(x, y, z, w) {{ 1 }} else {{ 0 }};"
    );
    let (_, _, arms) = super::arms_of(&src);
    let through = texts(&super::arm(&arms, "g(", true).scope);
    for w in &expected {
        assert!(through.contains(w), "{through:#?}");
    }
    assert!(through.iter().all(|w| !w.contains('@')), "{through:#?}");
}

/// The join of two scopes reports each one's refusal, in an order that depends neither on
/// which side is joined to which nor on the order the tests were assumed in.
#[test]
fn two_refused_arms_joined_give_both_warnings_in_one_order() {
    let left = arm_scope(&growth_test(["x", "y", "z", "w"]), true);
    let right = arm_scope(&growth_test(["a", "b", "c", "d"]), true);
    let joined = texts(&left.join(&right));
    assert_eq!(joined.len(), 2, "{joined:#?}");
    assert_eq!(joined, texts(&right.join(&left)));
    // By the printed constraints: `12 * w …` before `5 * a …`.
    assert!(joined[0].contains("12 * w + 10 * y"), "{joined:#?}");
    assert!(joined[1].contains("5 * a + c"), "{joined:#?}");
    for (w, s) in joined.iter().zip([&left, &right]) {
        assert_eq!(w, &texts(s)[0]);
    }
    // A test that is the disjunction of the two joins its cases' scopes in the same way, and
    // adds the warning of the whole disjunction, whose projection leaves the refused
    // disjunction out.
    let g1 = growth_test(["x", "y", "z", "w"]);
    let g2 = growth_test(["a", "b", "c", "d"]);
    let either = texts(&arm_scope(&format!("({g1}) || ({g2})"), true));
    assert_eq!(either.len(), 3, "{either:#?}");
    assert!(
        either[0].contains("so it set that case aside"),
        "{either:#?}"
    );
    assert_eq!(either[1..], joined[..]);
    assert_eq!(
        either,
        texts(&arm_scope(&format!("({g2}) || ({g1})"), true))
    );
}

/// A scope whose questions the solver decides reports nothing: the false arm of the refused
/// test (a disjunction of single constraints), and a test of two names.
#[test]
fn a_scope_with_no_refusal_gives_no_warning() {
    assert!(texts(&arm_scope(&growth_test(["x", "y", "z", "w"]), false)).is_empty());
    for outcome in [true, false] {
        let s = arm_scope("x + y >= 3 && x - y <= 1 && a - b >= 0", outcome);
        assert!(texts(&s).is_empty(), "{s}");
    }
}

/// The repair each warning above ends with, applied to the program's test, ends the warning
/// on both arms: a value stated for one variable leaves the solver three, which it decides.
#[test]
fn following_the_repair_of_each_warning_ends_it() {
    let g = growth_test(["x", "y", "z", "w"]);
    let zero = "4 * x - 12 * w - 10 * y - 12 * z >= 0 && 4 * w + 10 * x - 10 * y - 11 * z >= 0 \
                && 11 * w + 4 * x - y + 12 * z >= 0 && 0 - 8 * w - 5 * x + 12 * y - z >= 0";
    for test in [g.clone(), zero.to_string()] {
        assert!(!texts(&arm_scope(&test, true)).is_empty(), "{test}");
        for outcome in [true, false] {
            let s = arm_scope(&format!("w == 0 && {test}"), outcome);
            assert!(texts(&s).is_empty(), "{test}, {outcome}: {s}");
        }
    }
    let src = format!(
        "g(positional x: int, positional y: int, positional z: int, positional w: int) = {g};\n\
         ok(x, y, z, w) = if x == 0 && g(x, y, z, w) {{ 1 }} else {{ 0 }};"
    );
    let (_, _, arms) = super::arms_of(&src);
    for outcome in [true, false] {
        let s = &super::arm(&arms, "g(", outcome).scope;
        assert!(texts(s).is_empty(), "{outcome}: {s}");
    }
}

/// The names of `k` refused tests on disjoint names, four to a test.
fn refused_names(k: usize) -> Vec<Arc<str>> {
    (0..4 * k).map(|i| format!("v{i}").into()).collect()
}

/// The refused tests ([`growth_term`]) on `names`, four names to a test.
fn refused_guards(names: &[Arc<str>]) -> Vec<Term> {
    names.chunks(4).map(growth_term).collect()
}

/// Three refused tests on disjoint names, assumed one after another: one refusal and one
/// warning each.
#[test]
fn a_few_refused_tests_on_disjoint_names_give_one_warning_each() {
    use zedc::store::cell::Premises;
    let none = Premises::new();
    let k = 3;
    let ns = refused_names(k);
    let s = refused_guards(&ns)
        .iter()
        .fold(super::ints(&ns), |s, g| s.assume(g, true, &none));
    assert_eq!(s.warnings().len(), k);
    assert_eq!(s.refusals.len(), k);
}

/// Three refusals on disjoint names, each kept with the sets of its names: the scope keeps
/// each once.
#[test]
fn a_few_refusals_are_each_kept() {
    let names = refused_names(3);
    let s = names.chunks(4).fold(super::ints(&[]), |mut s, c| {
        let r = Refused {
            constraint: growth_test([&*c[0], &*c[1], &*c[2], &*c[3]]).into(),
            asked: Asked::Test { outcome: true },
            cause: Refusal::Growth.into(),
        };
        let sets = c.iter().map(|n| (n.clone(), IntervalSet::top()));
        s.refuse(r, Arc::new(sets.collect()), c);
        s
    });
    assert_eq!(s.refusals.len(), 3);
}

/// Two arms that share two refused tests on disjoint names and add one each: their join keeps
/// each of the four refusals once, with one warning each, whichever side is joined to which.
#[test]
fn the_join_of_arms_sharing_refused_tests_keeps_each_once() {
    use zedc::store::cell::Premises;
    let none = Premises::new();
    let k = 4;
    let ns = refused_names(k);
    let gs = refused_guards(&ns);
    let shared = gs[..k - 2]
        .iter()
        .fold(super::ints(&ns), |s, g| s.assume(g, true, &none));
    let [l, r] = [k - 2, k - 1].map(|i| shared.assume(&gs[i], true, &none));
    let joined = l.join(&r);
    assert_eq!(joined.refusals.len(), k);
    assert_eq!(joined.warnings().len(), k);
    assert_eq!(texts(&joined), texts(&r.join(&l)));
}

// The tests of `k` refused tests on disjoint names below were one test until
// SPLIT-reduced-refused (2026-11-10). That test took 15 to 16 s alone with malloc's cache per thread
// and 26 to 27 s without it, as tools/run_tests.sh runs it (load 28 to 36), and once ran past its
// piece's limit of 83 s at load 44 to 64. About 88% of it is building the arms of the join
// check: 2,304 `Scope::assume` calls, each about 42M instructions. Each test is a piece of its
// own (tools/run_tests.sh).

/// A scope with `k` refusals on disjoint names, each found by a name of its constraint: the
/// questions behind a rejection that reads the name (DESIGN.md L1.39). One look-up finds its
/// one question, a name of no question finds none, and each name of a question finds it.
#[test]
fn the_refusals_on_a_name_are_found_by_that_name() {
    let names = refused_names(3);
    let s = names.chunks(4).fold(super::ints(&[]), |mut s, c| {
        let r = Refused {
            constraint: growth_test([&*c[0], &*c[1], &*c[2], &*c[3]]).into(),
            asked: Asked::Test { outcome: true },
            cause: Refusal::Growth.into(),
        };
        s.refuse(r, Arc::new(Default::default()), c);
        s
    });
    let found = |ns: &[&str]| -> Vec<String> {
        (s.refused_on(ns.iter().copied()).into_iter())
            .map(|(r, _)| r.constraint.to_string())
            .collect()
    };
    let test = |i: usize| growth_test([0, 1, 2, 3].map(|j| &*names[4 * i + j]));
    assert_eq!(found(&["v5"]), [test(1)]);
    // A name of the scope is matched by its binding: `v5@7`, a binder written `v5` that
    // shadows the `v5` of the question, is another name, and finds no question.
    assert!(found(&["v5@7"]).is_empty());
    assert_eq!(found(&["v0", "v3", "v9"]), [test(0), test(2)]);
    assert_eq!(found(&["v1", "v2"]), [test(0)], "one question once");
    assert!(found(&["v12", "v"]).is_empty());
    // A join keeps the questions of both sides under their names.
    let other = names[..4].chunks(4).fold(super::ints(&[]), |mut o, c| {
        let r = Refused {
            constraint: growth_test([&*c[3], &*c[2], &*c[1], &*c[0]]).into(),
            asked: Asked::Test { outcome: false },
            cause: Refusal::Growth.into(),
        };
        o.refuse(r, Arc::new(Default::default()), c);
        o
    });
    let joined = other.join(&s);
    assert_eq!(joined.refused_on(["v9"]).len(), 1);
    assert_eq!(joined.refused_on(["v0"]).len(), 2);
}

/// A question whose text reads alike may be asked of an outer name and again of an inner name
/// that shadows it, `v0` and `v0@3`: it is kept once and found by both bindings, and not by a
/// third, `v0@4`. A join keeps each binding a side found it under, whichever side.
#[test]
fn a_question_asked_of_two_bindings_of_one_name_is_found_by_each() {
    let outer: Vec<Arc<str>> = ["v0", "v1", "v2", "v3"].map(Arc::from).into();
    let inner: Vec<Arc<str>> = ["v0@3", "v1", "v2", "v3"].map(Arc::from).into();
    let r = Refused {
        constraint: growth_test(["v0", "v1", "v2", "v3"]).into(),
        asked: Asked::Test { outcome: true },
        cause: Refusal::Growth.into(),
    };
    let asked = |on: &[&[Arc<str>]]| {
        on.iter().fold(super::ints(&[]), |mut s, names| {
            s.refuse(r.clone(), Arc::new(Default::default()), names);
            s
        })
    };
    let found = |s: &Scope, n: &str| s.refused_on([n]).len();
    let both = asked(&[&outer, &inner]);
    assert_eq!(both.refusals.len(), 1);
    assert_eq!(
        ["v0", "v0@3", "v0@4", "v1"].map(|n| found(&both, n)),
        [1, 1, 0, 1]
    );
    let (o, i) = (asked(&[&outer]), asked(&[&inner]));
    assert_eq!(["v0", "v0@3"].map(|n| found(&o, n)), [1, 0]);
    for joined in [o.join(&i), i.join(&o)] {
        assert_eq!(joined.refusals.len(), 1);
        assert_eq!(["v0", "v0@3", "v0@4"].map(|n| found(&joined, n)), [1, 1, 0]);
    }
}

/// The limit of [`one_refused_test_costs_at_most_a_fixed_number_of_instructions`]: 1.1 times
/// the 26.3M measured with the allocator settings of `tools/run_tests.sh` (no thread cache;
/// 20.6M with it), load 49. Negative control, run once and not committed: five extra copies
/// of the set in each `IntervalSet::sign_parts` give 30.0M, and the test fails; one copy gives
/// 27.0M, under the limit.
const ASSUME_LIMIT: u64 = 29_000_000;

/// [`growth_test`] as a kernel term on `names`, in the order `x`, `y`, `z`, `w`.
fn growth_term(names: &[Arc<str>]) -> Term {
    let row = |cs: [i64; 4], k: i64| {
        let sum = names
            .iter()
            .zip(cs)
            .fold(Term::Lit(Value::Int(k)), |t, (n, c)| {
                let m = Term::Prim(
                    Prim::Mul,
                    vec![Term::Lit(Value::Int(c)), Term::Var(n.clone())],
                );
                Term::Prim(Prim::Add, vec![t, m])
            });
        Term::Prim(Prim::Ge, vec![sum, Term::Lit(Value::Int(0))])
    };
    [
        row([4, -10, -12, -12], 11),
        row([10, -10, -11, 4], -28),
        row([4, -1, 12, 11], -28),
        row([-5, 12, -1, -8], 31),
    ]
    .into_iter()
    .reduce(|a, b| Term::Prim(Prim::And, vec![a, b]))
    .expect("four rows")
}

/// A refused projection whose variables have bounds names the bounds the box stage kept, each
/// in the program's names and as a type the program can write, and those it left every whole
/// number; the warning no longer says that nothing was ruled out (item
/// MSG-growth-projection-cause).
#[test]
fn a_refused_projection_names_the_bounds_it_kept() {
    let constraints = "12 * w + 10 * y + 12 * z <= 4 * x + 11 && 8 * w + 5 * x + z <= 12 * y + 31 \
                       && 4 * w + 10 * x >= 10 * y + 11 * z + 28 && 11 * w + 4 * x + 12 * z >= y + 28";
    let warning = |bounds: &str| {
        format!(
            "{WIDER}\
             \n  [1] here the conditions `{constraints}` hold\
             \n  [2] the checker could not work out which values each of their variables can take: {GROWTH}. The checker stopped there, with {EACH}: {bounds}\
             \n  [3] so here each of their variables keeps only those bounds, which may be wider than the conditions allow{SOUND}{}",
            value("w", "the conditions", constraints)
        )
    };
    let g = growth_test(["x", "y", "z", "w"]);
    let s = arm_scope(
        &format!("x >= 0 && x <= 9 && y >= -5 && z <= 20 && {g}"),
        true,
    );
    assert_eq!(
        texts(&s),
        vec![warning(
            "`w: int[-23..]`, `x: int[0..=9]`, `y: int[-5..]` and `z: int[..=20]`"
        )]
    );
    let s = arm_scope(&format!("x >= 0 && x <= 9 && {g}"), true);
    assert_eq!(
        texts(&s),
        vec![warning(
            "`x: int[0..=9]`; `w`, `y` and `z` may still be any whole number"
        )]
    );
}

/// Case 272 of seed 17 (`pendants::WRITTEN`) within its boxes, without `z0` (its one row
/// `a + c >= z0 - 12` and its bounds) and without `c <= 8`, which change none of these
/// warnings and take 0.63 of the 0.85 s the whole case takes (TEST-slow-l0139-refused-sums;
/// the whole case is checked by `pendants`): the projection onto `b`, `z1` and `z2` is
/// refused, and each warning names the bounds the box stage kept for its variable; a case of
/// an alternative set aside keeps no bounds, since the box stage does not read it, and still
/// says that its search found no values and ruled none out. `b` is refused only in the case
/// with no alternative left, where `z2 <= 4` and so `b <= 13`; in the cases with an
/// alternative its values are found exactly (PRES-project-each-cost).
#[test]
fn a_refused_projection_onto_one_name_names_its_bounds() {
    let case = "a + 2 * c >= -4 && (2 * a + b >= 7 || z2 <= 8) && a + 2 * b + c + z1 >= 4 \
                && a >= b + z1 - 6 && (b >= c - 11 || z2 <= 4) && a + b + c >= z1 + 2 \
                && a + z1 <= b + c + 9 && a + b + 2 * c == z2 + 5";
    let bounds = "a >= 2 && a <= 3 && b >= -4 && z1 >= -7 && z1 <= 13 && z2 >= -10 && z2 <= 6";
    let src = format!("ok(a, b, c, z1, z2) = if {bounds} && {case} {{ 1 }} else {{ 0 }};");
    let (_, _, arms) = super::arms_of(&src);
    let got = texts(&super::arm(&arms, "z2 + 5", true).scope);
    for (n, set) in [("b", "[-4..=13]"), ("z1", "[-7..=13]"), ("z2", "[-10..=6]")] {
        let want = format!(
            "{GROWTH}. The checker stopped there, with the bounds that each condition gives `{n}` \
             from the bounds of the others: `{n}: int{set}`\n"
        );
        assert!(got.iter().any(|w| w.contains(&want)), "{n}: {got:#?}");
    }
    let aside = format!(
        "so it set that case aside: {GROWTH}. The checker stopped there, with no values found \
         and none ruled out\n"
    );
    assert_eq!(
        got.iter().filter(|w| w.contains(&aside)).count(),
        2,
        "{got:#?}"
    );
    assert!(
        got.iter()
            .all(|w| w.contains(&aside) || !w.contains("none ruled out")),
        "{got:#?}"
    );
}

/// The sets a refusal keeps do not depend on the order the questions were met in: the same
/// question refused twice in a scope keeps the meet of its sets, a name only one time bounds
/// keeping that bound; refused on both sides of a join, the join of its sets; refused on one
/// side only, that side's sets.
#[test]
fn the_bounds_of_a_refusal_do_not_depend_on_the_order_it_was_met_in() {
    let r = Refused {
        constraint: "u + v >= 0".into(),
        asked: Asked::Projection,
        cause: Refusal::Growth.into(),
    };
    let kept = |sets: &[(&str, i64, i64)]| -> Kept {
        Arc::new(
            (sets.iter())
                .map(|&(n, lo, hi)| (Arc::from(n), IntervalSet::of(lo, hi)))
                .collect(),
        )
    };
    let names: Vec<Arc<str>> = ["u", "v"].map(Arc::from).into();
    let refused = |sets: &[&Kept]| {
        sets.iter().fold(super::ints(&names), |mut s, k| {
            s.refuse(r.clone(), (*k).clone(), &names);
            s
        })
    };
    let bounds = |s: &Scope| {
        let w = texts(s);
        assert_eq!(w.len(), 1, "{w:#?}");
        let (_, rest) = w[0].split_once(&format!("with {EACH}: ")).expect("bounds");
        rest.split_once('\n').expect("a step after").0.to_string()
    };
    let (a, b) = (kept(&[("v", 0, 9)]), kept(&[("u", -3, 3), ("v", 5, 20)]));
    let met = "`u: int[-3..=3]` and `v: int[5..=9]`";
    assert_eq!(bounds(&refused(&[&a, &b])), met);
    assert_eq!(bounds(&refused(&[&b, &a])), met);
    assert_eq!(bounds(&refused(&[&b, &a, &b])), met);
    let (l, r2) = (
        refused(&[&kept(&[("v", 0, 3)])]),
        refused(&[&kept(&[("v", 7, 9)])]),
    );
    let joined = "`v: int[0..=3, 7..=9]`";
    assert_eq!(bounds(&l.join(&r2)), joined);
    assert_eq!(bounds(&r2.join(&l)), joined);
    let none = super::ints(&names);
    assert_eq!(bounds(&l.join(&none)), "`v: int[0..=3]`");
    assert_eq!(bounds(&none.join(&l)), "`v: int[0..=3]`");
}

mod bench;
