//! The answers of the linear questions read through a callee's projection, against the
//! interpreter at every point of a small box (test audit 2026-11-08, row 2,
//! TESTS-coverage-projection-paths). Two paths project a callee's summary: the face of a kept
//! conjunction that still holds a disjunction after its holes are placed
//! (`presburger::extend`, `projected`, `project`, `split`; LOAD-disj-residue), and a call
//! with an argument that is not a name, of a callee whose canonical formula is not one
//! constraint, when another call holds the callee's claim (`preimage::Walk::projection` and
//! `value_projection`, which call `presburger::eliminated`; LOAD-call-relation). The tests of
//! `one_scope` compare those answers with the solver's on the relation written whole; these
//! compare them with the program run by the interpreter on every value of a box that holds
//! every point where a function's value changes, so the oracle does not share the solver.
//!
//! DESIGN.md step L1.38 (sec:constraints rule 2): each part is decided alone, in exact integer
//! arithmetic, so a decided question is the one the program's values give; and step L1.39: a
//! test that never holds is an unreachable arm, not a rejection, so the checker rejects a
//! function only where a question is refused.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::{Shared, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zedc::elab::{Cones, Unit};
use zedc::interp::prelude;
use zedc::store::preimage::Scoped;
use zedc::store::presburger::extend::Extending;
use zedc::store::presburger::{Formula, decide};

/// The seed of the random programs; each program's own seed is printed with a failure.
pub(super) const SEED: u64 = 0x7c9_0001;

/// The box every function of a program is run on: each function's value is the same at both
/// ends and at every point past them, which the programs below are built to make so.
const LO: i64 = -15;
const HI: i64 = 45;

/// The prelude and every definition of the unit as one chain of lets, as
/// `front::linear_questions` builds it.
fn lets(unit: &Unit) -> Term {
    prelude(
        unit.defs
            .iter()
            .rev()
            .fold(Term::Lit(Value::Bool(true)), |body, d| {
                Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
            }),
    )
}

/// The functions of the unit: each definition that is a lambda, by name, with its parameters
/// and body.
fn functions(unit: &Unit) -> Vec<(&str, &[Arc<str>], &Term)> {
    unit.defs
        .iter()
        .filter_map(|d| match &*d.term {
            Term::Lam(ps, body) => Some((d.name.as_str(), ps.as_slice(), &**body)),
            _ => None,
        })
        .collect()
}

/// Whether the function of one parameter can be true and whether it can be false, found by
/// running it on each integer of the box `LO..=HI`; its value at both ends must agree, since
/// it stands for every point past them.
fn run_on_the_box(cones: &Cones<'_>, ps: &[Arc<str>], body: &Term, what: &str) -> (bool, bool) {
    let closed = prelude(cones.close(body.clone()));
    let (mut holds, mut fails) = (false, false);
    let mut ends = Vec::new();
    for v in LO..=HI {
        let b = super::holds(&closed, ps, &[v]);
        (holds, fails) = (holds || b, fails || !b);
        if v == LO || v == HI {
            ends.push(b);
        }
    }
    assert_eq!(
        ends[0], ends[1],
        "{what}: the box does not hold its changes"
    );
    (holds, fails)
}

/// What a program gave against the interpreter.
#[derive(Default)]
struct Tally {
    /// Answers the checker decided, each equal to the interpreter's.
    decided: usize,
    /// Questions refused, each a rejection of its function.
    refused: usize,
}

/// Checks each linear question of `src`, a unit of functions of one `int` parameter each, as
/// `front::linear_questions` answers it (`Extending::defined_with` over one scope, a refused
/// question asked again over the relation written out), against the interpreter on the box:
/// a decided answer is the interpreter's, in the unit's order and in the reverse; and the
/// functions `front::linear_questions` rejects are those whose question stays refused in the
/// unit's order, which is the order it asks them in. `case` names the program in a failure.
/// The integer functions, named `v{j}`, are read only through their calls.
fn answers_are_the_interpreters(src: &str, case: &str) -> Tally {
    let unit = elab(src).unwrap_or_else(|e| panic!("{case}: {e:?}\n{src}"));
    let cones = Cones::new(&unit);
    let lets = lets(&unit);
    let fs: Vec<_> = (functions(&unit).into_iter())
        .filter(|f| !f.0.starts_with('v'))
        .collect();
    let truth: Vec<(bool, bool)> = (fs.iter())
        .map(|(name, ps, body)| run_on_the_box(&cones, ps, body, &format!("{case}: `{name}`")))
        .collect();
    let mut tally = Tally::default();
    let mut refused_in_order = BTreeSet::new();
    for (k, order) in [
        (0..fs.len()).collect::<Vec<_>>(),
        (0..fs.len()).rev().collect(),
    ]
    .into_iter()
    .enumerate()
    {
        let mut scoped = Scoped::new(&lets);
        let mut extending = Extending::new();
        for i in order {
            let (name, ps, body) = fs[i];
            let r = (scoped.relation(body, ps, ps, true))
                .unwrap_or_else(|| panic!("{case}: `{name}` has no relation\n{src}"));
            let mut a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            if a.holds.is_err() || a.fails.is_err() {
                let w = scoped.written(&r);
                let with = |f| Formula::and(vec![w.defined(), f]);
                a.holds = decide(&with(w.body.clone()));
                a.fails = decide(&with(Formula::negate(w.body.clone())));
            }
            let (holds, fails) = truth[i];
            for (side, got, want) in [("holds", &a.holds, holds), ("fails", &a.fails, fails)] {
                match got {
                    Ok(g) => {
                        assert_eq!(
                            *g,
                            want,
                            "{case}: `{name}` {side} in the {} order, against the interpreter \
                             on {LO}..={HI}, in\n{src}\n{}",
                            ["unit's", "reverse"][k],
                            scoped.written(&r)
                        );
                        tally.decided += 1;
                    }
                    Err(_) => {
                        tally.refused += 1;
                        if k == 0 {
                            refused_in_order.insert(name.to_string());
                        }
                    }
                }
            }
        }
    }
    let stmts = zed_tests::deep::statements(src);
    let tokens = zedc::lex::lex_fence(src).unwrap();
    let rejected: BTreeSet<String> = zedc::front::linear_questions(src, &tokens, &stmts, &unit)
        .iter()
        .map(|e| {
            (fs.iter().map(|f| f.0))
                .find(|n| e.message.contains(&format!("the condition of `{n}`")))
                .unwrap_or_else(|| panic!("{case}: a rejection names no function: {e:?}"))
                .to_string()
        })
        .collect();
    assert_eq!(
        rejected, refused_in_order,
        "{case}: rejected functions in\n{src}"
    );
    tally
}

/// `n` as Zed writes it: a negative number as a difference, since a literal has no sign.
fn lit(n: i64) -> String {
    match n < 0 {
        true => format!("(0 - {})", -n),
        false => n.to_string(),
    }
}

/// A random test of `x`: a remainder equal or unequal to a constant, which may lie outside the
/// remainder's range, or a bound inside the box.
fn random_case(rng: &mut Rng) -> String {
    let m = rng.int(2, 7);
    match rng.below(4) {
        0 => format!("x mod {m} == {}", rng.int(0, m)),
        1 => format!("x mod {m} != {}", rng.int(0, m - 1)),
        2 => format!("x < {}", lit(rng.int(-10, 40))),
        _ => format!("x > {}", lit(rng.int(-10, 40))),
    }
}

/// A random unit whose questions reach both projections. A callee `q` holds one or two
/// disjunctions beside a range inside `-5..=35`, and may hold a remainder of its own, which
/// its projection keeps over a quotient and a remainder; a chain of links `p{i}(x) = q(x: x)
/// && p{i-1}(x: x + k) && x < c`, each of which may hold a disjunction of its own and a bound
/// on an integer function `v{j}(x: x + k)` of a chain `v{j}(x) = v{j-1}(x: x + k) + x mod m`
/// or `x div m`, and a call `g2(x: x + k)` of a chain of callees that keep a congruence, as
/// `g2(x) = g1(x: x + k) && x mod n == s` over `g1(x) = g0(x: x) && x mod m == r`, reads `q`
/// through the face of the chain beside it, which keeps `q`'s disjunctions as clauses; and
/// tests `n{i}(x) = !p{i}(x: x + k)` call a link, whose canonical formula is a conjunction,
/// at an argument that is not a name, after the next link's call of it holds its claim. Every
/// test is constant outside `-10..=40`, inside the box.
fn random_unit(rng: &mut Rng) -> String {
    let a = rng.int(-5, 5);
    let b = a + rng.int(0, 30);
    let mut q = format!("({} || {})", random_case(rng), random_case(rng));
    if rng.below(2) == 0 {
        q.push_str(&format!(
            " && ({} || {})",
            random_case(rng),
            random_case(rng)
        ));
    }
    if rng.below(2) == 0 {
        let m = rng.int(2, 5);
        q.push_str(&format!(" && x mod {m} == {}", rng.int(0, m - 1)));
    }
    let c = rng.int(-10, 10);
    let mut src = format!(
        "q(x: int) = {q} && x > {} && x < {};\np0(x: int) = x > {} && x < {};\n",
        lit(a),
        lit(b),
        lit(c),
        lit(c + rng.int(0, 30)),
    );
    let (lo, hi) = (rng.int(-10, 0), rng.int(10, 35));
    let (m, n) = (rng.int(2, 5), rng.int(2, 5));
    src.push_str(&format!(
        "g0(x: int) = x > {} && x < {hi};\ng1(x: int) = g0(x: x) && x mod {m} == {} && x < {};\n\
         g2(x: int) = g1(x: x + {}) && x mod {n} == {};\n",
        lit(lo),
        rng.int(0, m - 1),
        hi - 1,
        lit(rng.int(-2, 2)),
        rng.int(0, n - 1),
    ));
    let vs = rng.int(1, 4);
    src.push_str(&format!("v0(x: int) = x mod {};\n", rng.int(2, 5)));
    for j in 1..vs {
        src.push_str(&format!(
            "v{j}(x: int) = v{}(x: x + {}) + x {} {};\n",
            j - 1,
            lit(rng.int(-3, 3)),
            ["mod", "div"][rng.below(2)],
            rng.int(2, 5),
        ));
    }
    let links = rng.int(2, 7);
    for i in 1..links {
        let mut own = match rng.below(3) {
            0 => format!(" && ({} || {})", random_case(rng), random_case(rng)),
            _ => String::new(),
        };
        if rng.below(2) == 0 {
            own.push_str(&format!(" && g2(x: x + {})", lit(rng.int(-3, 3))));
        }
        if rng.below(2) == 0 {
            own.push_str(&format!(
                " && v{}(x: x + {}) < {}",
                rng.int(0, vs - 1),
                lit(rng.int(-4, 4)),
                lit(rng.int(-2, 12)),
            ));
        }
        src.push_str(&format!(
            "p{i}(x: int) = q(x: x) && p{}(x: x + {}) && x < {}{own};\n",
            i - 1,
            lit(rng.int(-4, 4)),
            lit(rng.int(-10, 40)),
        ));
    }
    for i in 1..links {
        if rng.below(2) == 0 {
            src.push_str(&format!(
                "n{i}(x: int) = !p{i}(x: x + {});\n",
                lit(rng.int(-4, 4))
            ));
        }
    }
    src
}

/// The units the tests below check, written out: a callee of two disjunctions that share a
/// remainder, which its face keeps (LOAD-disj-residue); a callee of a range and a remainder,
/// called at moved arguments by a chain and by tests of its links; and, as
/// `one_scope::each_answer_through_a_projection_kept_over_pairs_is_the_answer_of_the_relation_whole`
/// builds them, a chain of integer functions over remainders and quotients, and a chain of
/// callees that keep a congruence, each read through its projection at moved arguments
/// (LOAD-call-relation).
const UNITS: &[&str] = &[
    "q(x: int) = (x mod 6 == 1 || x > 30) && (x mod 6 == 5 || x < 10) && x > 0 && x < 35;\n\
     p0(x: int) = x > 0 && x < 30;\n\
     p1(x: int) = q(x: x) && p0(x: x + 3) && x < 32;\n\
     p2(x: int) = q(x: x) && p1(x: x - 2) && x < 34 && (x mod 4 == 3 || x < 5);\n\
     p3(x: int) = q(x: x) && p2(x: x + 1) && x < 33;\n\
     n2(x: int) = !p2(x: x + 2);\nn3(x: int) = !p3(x: x - 1);\n",
    "q(x: int) = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x < 30;\n\
     p0(x: int) = x > 2 && x < 25;\n\
     p1(x: int) = q(x: x) && p0(x: x + 3) && x < 28;\n\
     p2(x: int) = q(x: x) && p1(x: x + 3) && x < 26;\n\
     p3(x: int) = q(x: x) && p2(x: x + 3) && x < 24;\n\
     n1(x: int) = !p1(x: x + 1);\nn3(x: int) = !p3(x: x + 2);\n",
    "q(x: int) = (x < 10 || x > 20) && x > 0 && x < 35;\n\
     p0(x: int) = x > (0 - 5) && x < 40;\n\
     p1(x: int) = q(x: x) && p0(x: x + 4) && x < 30;\n\
     p2(x: int) = q(x: x) && p1(x: x + 4) && x < 25;\n\
     n2(x: int) = !p2(x: x - 3);\n",
    "v0(x: int) = x mod 3;\nv1(x: int) = v0(x: x) + x div 2;\n\
     v2(x: int) = v1(x: x + 1) + x mod 5;\n\
     p0(x: int) = x > 0 && x < 40;\n\
     p1(x: int) = v2(x: x) < 9 && p0(x: x + 1) && x < 40;\n\
     p2(x: int) = v2(x: x - 2) == 7 && p1(x: x + 1) && x < 30;\n\
     p3(x: int) = (v1(x: x) + v2(x: x + 3) > 20 || p2(x: x)) && x < 40;\n\
     n3(x: int) = !p3(x: x + 2);\n",
    "h0(x: int) = x > (0 - 10) && x < 35;\n\
     h1(x: int) = h0(x: x) && x mod 4 == 1 && x < 34;\n\
     h2(x: int) = h1(x: x + 1) && x mod 3 == 2;\n\
     p0(x: int) = x > 0 && x < 40;\n\
     p1(x: int) = h2(x: x) && p0(x: x + 1) && x < 30;\n\
     p2(x: int) = h2(x: x + 4) && p1(x: x + 1) && x < 28;\n\
     p3(x: int) = (h2(x: 2 * x) || p2(x: x - 1)) && x > (0 - 10);\n\
     n2(x: int) = !p2(x: x - 1);\n",
];

#[test]
fn each_answer_through_a_projected_callee_is_the_interpreters_on_a_box() {
    for (i, src) in UNITS.iter().enumerate() {
        let t = answers_are_the_interpreters(src, &format!("unit {i}"));
        eprintln!(
            "unit {i}: {} answers decided, {} refused",
            t.decided, t.refused
        );
        assert!(t.decided >= 16, "unit {i}: {} answers decided", t.decided);
    }
}

#[test]
fn each_answer_of_a_random_unit_through_projected_callees_is_the_interpreters_on_a_box() {
    // Four programs, at the seeds that follow a new seed each run; ZED_TEST_SEED with the
    // printed seed repeats the run. The 60 programs of `SEED` are in `bench::projection_oracle`
    // (6.7 s at load 25). About 20 answers per program are decided there.
    let (_, first) = Rng::fresh("random units through projected callees");
    let (decided, refused) = random_units_are_the_interpreters(first, 4);
    assert!(
        decided >= 20,
        "{decided} answers decided, {refused} refused"
    );
}

/// [`answers_are_the_interpreters`] on the `count` random programs of the seeds from `first`
/// on: the answers decided and refused.
pub(super) fn random_units_are_the_interpreters(first: u64, count: u64) -> (usize, usize) {
    // Each program's seed is its index's, so a failure is rerun alone by the test's name and
    // reproduced by the seed it prints.
    let (mut decided, mut refused) = (0, 0);
    for i in 0..count {
        let seed = first.wrapping_add(i);
        let src = random_unit(&mut Rng::new(seed));
        let case = format!(
            "seed {seed:#x} (program {i} from {first:#x}); rerun the test that printed {first} \
             with ZED_TEST_SEED={first}"
        );
        let t = answers_are_the_interpreters(&src, &case);
        (decided, refused) = (decided + t.decided, refused + t.refused);
    }
    eprintln!("{decided} answers decided, {refused} refused");
    (decided, refused)
}

/// A callee whose body states its remainder's own definition, `x == 4 * (x div 4) + x mod 4`,
/// before a bound on `x`. Written over its pair, that equation is the first row and the
/// pair's definition rows that repeat it or are looser are dropped, so the bound `x <= 9` is
/// the last row `presburger::eliminated` returns to `projected`, and the one row of the
/// projection that is not the pair's own definition. `p3` asks for `x + 2 <= 9` and `x > 7`,
/// which no `x` meets only because of that bound: without it, `x = 11` would meet `h1(x: 13)`.
const BOUND_LAST: &str = "h1(x: int) = x == 4 * (x div 4) + x mod 4 && x mod 4 >= 1 && x mod 4 <= 2 && x > (0 - 12) && x < 10;\n\
     p0(x: int) = x > (0 - 12) && x < 40;\n\
     p1(x: int) = h1(x: x) && p0(x: x + 1);\n\
     p2(x: int) = h1(x: x + 4) && p1(x: x + 1);\n\
     p3(x: int) = h1(x: x + 2) && x > 7;\n";

#[test]
fn a_bound_written_after_the_remainders_definition_stays_in_the_callees_projection() {
    let t = answers_are_the_interpreters(BOUND_LAST, "bound last");
    assert_eq!(
        (t.decided, t.refused),
        (20, 0),
        "bound last: answers decided, refused"
    );
    let unit = elab(BOUND_LAST).unwrap();
    let lets = lets(&unit);
    let mut scoped = Scoped::new(&lets);
    let mut extending = Extending::new();
    let mut got = Vec::new();
    for (name, ps, body) in functions(&unit) {
        let r = scoped.relation(body, ps, ps, true).unwrap();
        let a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
        got.push((name, a.holds, a.fails));
    }
    let t = |name| (name, Ok(true), Ok(true));
    assert_eq!(
        got,
        [
            t("h1"),
            t("p0"),
            t("p1"),
            t("p2"),
            ("p3", Ok(false), Ok(true))
        ]
    );
}
