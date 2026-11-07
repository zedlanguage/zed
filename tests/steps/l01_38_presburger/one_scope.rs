//! The linear questions of a unit read every function's body under one scope of the unit's
//! definitions (`preimage::Scoped`, LOAD-chain): each relation is the one the body closed
//! over the definitions it reaches gives, in any order of the bodies, and a chain of n
//! functions, each calling the one before, is read in O(n), where closing each body over its
//! cone read it in O(n²).

use std::sync::Arc;

use zed_kernel::{Shared, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zedc::elab::{Cones, Unit};
use zedc::interp::prelude;
use zedc::store::preimage::{Scoped, relations};
use zedc::store::presburger::Relation;

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

/// The relation of a body closed over the definitions it reaches, as the questions were
/// read before LOAD-chain.
fn closed(cones: &Cones<'_>, ps: &[Arc<str>], body: &Term) -> Option<Relation> {
    let body = prelude(cones.close(body.clone()));
    relations(&[&body], ps, true).map(|mut rs| rs.remove(0))
}

const UNITS: &[&str] = &[
    // A helper with `div` and `mod`, whose auxiliary variables each relation numbers afresh.
    "h(x: int) = x div 3 + x mod 5;\nok(x: int, y: int) = h(x: x) <= y && y < h(x: y + 1);\n\
     two(x: int) = h(x: x) == h(x: x + 2);",
    // A function called before its own question is asked, and after.
    "g(x: int) = f(y: x + 1) && x > 2;\nf(y: int) = y mod 4 == 1 && y < 9;\n\
     k(z: int) = f(y: z) || g(x: z);",
    // Bodies outside the linear-relation domain, between bodies inside it.
    "a(x: int) = x > 1;\nfl(x: int, y: f64) = y > 1.5 && a(x: x);\nb(x: int) = a(x: x + 1) && x < 4;\n\
     s(t: String, x: int) = len(t) == x && a(x: x);\nc(x: int) = a(x: x) || b(x: x - 1);",
    // Branches over a helper.
    "m(x: int) = if x < 0 { 0 - x } else { x };\nw(x: int, y: int) = if m(x: x) > y { m(x: y) == 2 } else { x == y };",
    // Products of two names, atoms of the relation.
    "p(x: int, y: int) = x * y == 6 && x + y == 5;\nq(x: int, y: int) = p(x: y, y: x) && x * y > 0;",
    // A chain, each function calling the one before.
    "c0(x: int) = x > 0;\nc1(x: int) = c0(x: x) && x > 1;\nc2(x: int) = c1(x: x + 1) && x > 2;\n\
     c3(x: int) = c2(x: x) || c0(x: x - 3);",
];

#[test]
fn a_relation_read_under_the_unit_scope_is_the_relation_of_the_closed_body() {
    let (mut some, mut none) = (0, 0);
    for src in UNITS {
        let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let cones = Cones::new(&unit);
        let fs = functions(&unit);
        let expected: Vec<Option<Relation>> =
            fs.iter().map(|&(_, ps, b)| closed(&cones, ps, b)).collect();
        some += expected.iter().flatten().count();
        none += expected.iter().filter(|r| r.is_none()).count();
        let lets = lets(&unit);
        // The bodies in the unit's order and in the reverse, so that each definition is read
        // first from another body, and from its own.
        for order in [
            (0..fs.len()).collect::<Vec<_>>(),
            (0..fs.len()).rev().collect(),
        ] {
            let mut scoped = Scoped::new(&lets);
            for i in order {
                let (name, ps, body) = fs[i];
                assert_eq!(
                    scoped.relation(body, ps, ps, true),
                    expected[i],
                    "`{name}` in\n{src}"
                );
            }
        }
    }
    // Most bodies are in the linear-relation domain, so the relations are compared, not only
    // their absence; and some are not, so a body outside it is followed by others.
    assert!(some >= 12, "{some} relations");
    assert!(none >= 1, "{none} outside");
}

#[test]
fn the_scope_holds_what_the_bodies_found_of_it_alone() {
    // `p{i}(x) = p{i-1}(x: x) && x > i`: each body reads the i bodies before it, each in a
    // scope its call binds, so the bodies together read O(n²) terms in scopes. What depends on
    // a body is dropped when it is read, so the scope holds O(n) entries; keeping them held
    // O(n²) (927 MB at 800 functions, against 39 MB when each body was closed over its cone).
    let held = |n: usize| {
        let mut src = String::from("p0(x: int) = x > 0;\n");
        for i in 1..n {
            src.push_str(&format!("p{i}(x: int) = p{}(x: x) && x > {i};\n", i - 1));
        }
        let unit = elab(&src).unwrap();
        let lets = lets(&unit);
        let mut scoped = Scoped::new(&lets);
        for (name, ps, body) in functions(&unit) {
            assert!(scoped.relation(body, ps, ps, true).is_some(), "{name}");
        }
        scoped.held()
    };
    let (n, m) = (25, 25 * zed_tests::scaling::FACTOR);
    let (small, large) = (held(n), held(m));
    // Linear growth gives FACTOR; the slack covers the prelude's share at the small size.
    assert!(
        large <= small * zed_tests::scaling::FACTOR * 3 / 2,
        "{small} entries at {n} functions, {large} at {m}"
    );
}

#[test]
fn the_questions_of_a_chain_of_calls_scale() {
    // `step{i}(x) = step{i-1}(x: x) + i`, the chain LOAD-chain found (5.4 s at 100 functions
    // and 17.7 s at 200 when each body was closed over its cone). The questions are timed
    // alone, on units elaborated before the timing.
    let unit = |n: usize| {
        let mut src = String::from("step0(x: int) = x;\n");
        for i in 1..n {
            src.push_str(&format!("step{i}(x: int) = step{}(x: x) + {i};\n", i - 1));
        }
        src
    };
    let n = 100;
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            (m, (zed_tests::deep::statements(&src), elab(&src).unwrap()))
        })
        .collect();
    zed_tests::scaling::check("the linear questions of a chain of n calls", n, |m| {
        let (stmts, unit) = &units[&m];
        let refused = zedc::front::linear_questions(stmts, unit);
        assert!(refused.is_empty(), "{refused:?}");
    });
}

/// Times the linear questions of a unit of `first` and the links `link(1)` to `link(m - 1)`, at
/// m = `n` and 8n, on units elaborated before the timing; no question is refused.
fn questions_scale(what: &str, n: usize, first: &str, link: fn(usize) -> String) {
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src: String = std::iter::once(first.to_string())
                .chain((1..m).map(link))
                .collect();
            (m, (zed_tests::deep::statements(&src), elab(&src).unwrap()))
        })
        .collect();
    zed_tests::scaling::check(what, n, |m| {
        let (stmts, unit) = &units[&m];
        let refused = zedc::front::linear_questions(stmts, unit);
        assert!(refused.is_empty(), "{refused:?}");
    });
}

#[test]
fn the_questions_of_a_chain_of_tests_scale() {
    // `p{i}(x) = p{i-1}(x: x) && x > i`, the chain of LOAD-chain-share: 62.6 times the bytes
    // for 8 times the functions (100 to 800) when each body translated the chain again, 8.1
    // times when each takes its callee's translation as made for the body before.
    questions_scale("a chain of tests", 100, "p0(x: int) = x > 0;\n", |i| {
        format!("p{i}(x: int) = p{}(x: x) && x > {i};\n", i - 1)
    });
}

#[test]
fn the_questions_of_a_chain_over_two_variables_scale() {
    // `p{i}(x, y) = p{i-1}(x: x, y: y) && x + i * y < 1000 i`: the relation of `p{i}` holds i
    // constraints, none tighter than another. 195.6 times the bytes for 8 times the functions
    // (50 to 400) when each relation was copied out of its callee's and decided whole, 7.8
    // times when it holds its callee's as a shared part and is decided from its answers.
    questions_scale(
        "a chain of tests over two variables",
        50,
        "p0(x: int, y: int) = x > y && y >= 0;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x, y: y) && x + {i} * y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn each_answer_from_a_callee_is_the_answer_of_the_relation_alone() {
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Formula, decide};
    let units = [
        // Two callers of one callee, and callers of each.
        "base(x: int, y: int) = x > y && y >= 0;\nup(x: int, y: int) = base(x: x, y: y) && x < 100;\n\
         down(x: int, y: int) = base(x: x, y: y) && x + y > 300;\n\
         upup(x: int, y: int) = up(x: x, y: y) && y < 5;\ndownup(x: int, y: int) = down(x: x, y: y) && up(x: x, y: y);\n\
         never(x: int, y: int) = up(x: x, y: y) && y < 0;\nnever2(x: int, y: int) = never(x: x, y: y) && x > 0;",
        // A chain over two variables, each link holding its callee's point or not.
        "c0(x: int, y: int) = x > y && y >= 0;\nc1(x: int, y: int) = c0(x: x, y: y) && x + y < 50;\n\
         c2(x: int, y: int) = c1(x: x, y: y) && x + 2 * y > 30;\nc3(x: int, y: int) = c2(x: x, y: y) && x - y < 3;\n\
         c4(x: int, y: int) = c3(x: y, y: x) && x > 0;",
        // A callee that holds everywhere.
        "any(x: int, y: int) = (x > 0 || x <= 0) && (y > 0 || y <= 0);\nsome(x: int, y: int) = any(x: x, y: y) && x > 3;\n\
         all(x: int, y: int) = any(x: x, y: y) && (x > 3 || x <= 3);",
    ];
    for src in units {
        let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let lets = lets(&unit);
        let fs = functions(&unit);
        // In the unit's order and in the reverse, so that a caller is asked before its callee.
        for order in [
            (0..fs.len()).collect::<Vec<_>>(),
            (0..fs.len()).rev().collect(),
        ] {
            let mut scoped = Scoped::new(&lets);
            let mut extending = Extending::new();
            for i in order {
                let (name, ps, body) = fs[i];
                let r = scoped.relation(body, ps, ps, true).expect(name);
                assert!(r.defs.is_empty(), "{name}");
                let a = extending.answers(&r.body);
                assert_eq!(a.holds, decide(&r.body), "`{name}` can hold in\n{src}");
                assert_eq!(
                    a.fails,
                    decide(&Formula::negate(r.body.clone())),
                    "`{name}` can fail in\n{src}"
                );
            }
        }
    }
}
