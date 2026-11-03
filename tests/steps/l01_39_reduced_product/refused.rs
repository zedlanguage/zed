//! A disjunct whose projection is refused is left out, which leaves the hull wider but sound,
//! and its cause is returned with the hulls, so that the scope records it.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, project_each};
use zedc::store::product::Scope;

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
        Formula::Or(vec![growth(), ge(&[("v", 1)], -5)]),
    ]);
    let (hulls, skipped) = project_each(&f, &[sym("v")]).expect("the base has a point");
    assert_eq!(skipped, vec![Refusal::Growth], "{hulls:?}");
    assert!(hulls[0].is_ok(), "{hulls:?}");
    // Without the refused disjunct, nothing is skipped.
    let f = Formula::and(vec![
        ge(&[("v", 1)], 0),
        Formula::Or(vec![ge(&[("v", 1)], -9), ge(&[("v", 1)], -5)]),
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

const GROWTH: &str = "the integer constraints have three variables or more, each of whose \
                      elimination would enlarge them, so whether they hold at an integer point \
                      is not decided";

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
            "warning: the scope is wider than its constraints make it\
             \n  [1] the constraints `{constraints}` hold in the scope\
             \n  [2] their projection onto their names is not decided: {GROWTH}\
             \n  [3] the names of the constraints are not narrowed by them"
        )]
    );
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
        either[0].contains("a disjunction among them is left out of their projection"),
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

/// `k` refused tests on disjoint names: assuming them one after another records one refusal
/// each, and the join of two arms that share those tests and add one refused test each, with
/// its warnings, costs near linear in `k`.
#[test]
fn warnings_of_many_refused_tests_scale() {
    use zed_tests::scaling::{self, FACTOR};
    use zedc::store::cell::Premises;
    let none = Premises::new();
    let names =
        |k: usize| -> Vec<Arc<str>> { (0..4 * k).map(|i| format!("v{i}").into()).collect() };
    let guards = |names: &[Arc<str>]| -> Vec<Term> { names.chunks(4).map(growth_term).collect() };
    let n = 16;
    let inputs = [n, FACTOR * n].map(|k| {
        let ns = names(k);
        (super::ints(&ns), guards(&ns))
    });
    scaling::check("narrowing by refused tests", n, |k| {
        let (scope, guards) = &inputs[usize::from(k != n)];
        let s = guards
            .iter()
            .fold(scope.clone(), |s, g| s.assume(g, true, &none));
        assert_eq!(s.warnings().len(), k);
    });
    // At sizes n and 8n: the scope after k - 2 shared tests, then each arm after one more.
    // Two arms that each add many tests the other lacks are not measured here: that join is
    // superlinear whether the tests are refused or not (COMPLEXITY.md S26); ledger item ST-join
    // owns that case.
    let n = 64;
    let arms = [n, FACTOR * n].map(|k| {
        let ns = names(k);
        let gs = guards(&ns);
        let shared = gs[..k - 2]
            .iter()
            .fold(super::ints(&ns), |s, g| s.assume(g, true, &none));
        [k - 2, k - 1].map(|i| shared.assume(&gs[i], true, &none))
    });
    scaling::check("the join of refused arms", n, |k| {
        let [l, r] = &arms[usize::from(k != n)];
        assert_eq!(l.join(r).refusals.len(), k);
    });
    // The warnings of the joins, built before they are measured.
    let joins = arms.map(|[l, r]| l.join(&r));
    scaling::check("the warnings of a join of refused arms", n, |k| {
        assert_eq!(joins[usize::from(k != n)].warnings().len(), k);
    });
}

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
