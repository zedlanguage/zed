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

/// `r` written with its auxiliary variables numbered in the order they are first met: in the
/// body, then in the definitions met, each after the one before. A relation one body reads
/// through definitions made for another numbers them in the order they were made
/// (`Scoped::written`), so two relations equal but for that numbering have one shape.
fn shape(r: &Relation) -> String {
    use std::collections::HashMap;
    // Each `Aux(n)`, and each `q{n}` that a definition's written term names, renamed by `at`,
    // numbering a new one in order.
    fn renamed(s: &str, at: &mut HashMap<u32, usize>, order: &mut Vec<u32>) -> String {
        let (mut out, mut rest) = (String::new(), s);
        while !rest.is_empty() {
            let named = |p: &str| -> Option<(usize, usize)> {
                let digits = rest.strip_prefix(p)?;
                let k = digits
                    .find(|c: char| !c.is_ascii_digit())
                    .unwrap_or(digits.len());
                (k > 0).then_some((p.len(), k))
            };
            let start = out
                .chars()
                .last()
                .is_none_or(|c| !c.is_alphanumeric() && c != '_');
            let hit = named("Aux(").or_else(|| named("q").filter(|_| start));
            match hit {
                Some((p, k)) => {
                    let n: u32 = rest[p..p + k].parse().unwrap();
                    let i = *at.entry(n).or_insert_with(|| {
                        order.push(n);
                        order.len() - 1
                    });
                    out.push_str(&format!("{}{i}", &rest[..p]));
                    rest = &rest[p + k..];
                }
                None => {
                    let c = rest.chars().next().unwrap();
                    out.push(c);
                    rest = &rest[c.len_utf8()..];
                }
            }
        }
        out
    }
    let defs: HashMap<u32, String> = (r.defs.iter())
        .map(|(n, w, f)| (*n, format!("{w}: {f:?}")))
        .collect();
    let (mut at, mut order) = (HashMap::new(), Vec::new());
    let mut out = vec![renamed(&format!("{:?}", r.body), &mut at, &mut order)];
    let mut next = 0;
    loop {
        while next < order.len() {
            let d = &defs[&order[next]];
            out.push(format!("{next} = {}", renamed(d, &mut at, &mut order)));
            next += 1;
        }
        // A definition no formula met names, but whose own formula names one met (the `div`
        // holding the constraints of a `mod`), taken by the first met atom it names.
        let more = order.iter().find_map(|m| {
            (r.defs.iter()).find(|(n, _, f)| {
                !at.contains_key(n) && format!("{f:?}").contains(&format!("Aux({m})"))
            })
        });
        let Some((n, _, _)) = more else { break };
        at.insert(*n, order.len());
        order.push(*n);
    }
    assert_eq!(order.len(), r.defs.len(), "every definition met: {r:?}");
    out.join("\n")
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
        // first from another body, and from its own. A body that takes a callee's definitions
        // as another body made them numbers them as they were made (LOAD-chain-affine: `k`
        // reads `f(y: z + 1)` through `g`'s translation), so the relations are compared by
        // their shape.
        for order in [
            (0..fs.len()).collect::<Vec<_>>(),
            (0..fs.len()).rev().collect(),
        ] {
            let mut scoped = Scoped::new(&lets);
            for i in order {
                let (name, ps, body) = fs[i];
                let got = scoped.relation(body, ps, ps, true);
                assert_eq!(
                    got.map(|b| shape(&scoped.written(&b))),
                    expected[i].as_ref().map(shape),
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
                assert!(scoped.written(&r).defs.is_empty(), "{name}");
                let a = extending.answers(&r);
                assert_eq!(a.holds, decide(&r), "`{name}` can hold in\n{src}");
                assert_eq!(
                    a.fails,
                    decide(&Formula::negate(r.clone())),
                    "`{name}` can fail in\n{src}"
                );
            }
        }
    }
}

#[test]
fn each_answer_with_auxiliary_variables_is_the_answer_of_the_relation_alone() {
    // LOAD-chain-aux: the auxiliary variables are numbered once for the scope, and each
    // answer, found from the callee's and the definitions the new parts reach, is the one
    // the relation with all its definitions has.
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Formula, decide};
    let units = [
        // A chain whose links each define a remainder, a link that holds its callee's
        // point and one that excludes it.
        "c0(x: int) = x div 3 > 0;\nc1(x: int) = c0(x: x) && x mod 7 + 1 > 0;\n\
         c2(x: int) = c1(x: x) && x mod 7 == 5;\nc3(x: int) = c2(x: x) && x div 3 < 0;\n\
         c4(x: int) = c3(x: x) || x mod 2 == 1;",
        // Nested `div` and `mod`, a divisor that is a term, and a callee read twice.
        "n0(x: int, y: int) = (x div 3) mod 5 == 2 && y > 0;\n\
         n1(x: int, y: int) = n0(x: x, y: y) && (x mod 15) div 4 == y;\n\
         n2(x: int, y: int) = n1(x: x, y: y) && x div y > 1 && x mod y == 0;\n\
         n3(x: int, y: int) = n2(x: x, y: y) && n0(x: x, y: y) && min(x, y) + abs(y) > 2;",
        // A callee whose value is defined by a branch and a remainder, called by tests.
        "v(x: int) = if x mod 4 == 0 { x div 4 } else { 0 - x };\nt1(x: int) = v(x: x) > 3;\n\
         t2(x: int) = t1(x: x) && v(x: x) < 9;\nt3(x: int) = t2(x: x) && x mod 3 == 1;",
        // A chain of one function: no callee.
        "e0(x: int) = x mod 3 == 1;",
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
            let mut defined = 0;
            for i in order {
                let (name, ps, body) = fs[i];
                let Some(r) = scoped.relation(body, ps, ps, true) else {
                    continue;
                };
                let a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
                let w = scoped.written(&r);
                defined += usize::from(!w.defs.is_empty());
                let with = |f: Formula| Formula::and(vec![w.defined(), f]);
                assert_eq!(
                    a.holds,
                    decide(&with(w.body.clone())),
                    "`{name}` can hold in\n{src}\n{w}"
                );
                assert_eq!(
                    a.fails,
                    decide(&with(Formula::negate(w.body.clone()))),
                    "`{name}` can fail in\n{src}\n{w}"
                );
            }
            assert!(defined >= 1, "{src}");
        }
    }
}

#[test]
fn the_questions_of_a_chain_defining_auxiliary_variables_scale() {
    // `p{i}(x) = p{i-1}(x: x) && x mod 7 + i > 0`, the chain of LOAD-chain-aux: each link
    // defines a quotient and a remainder. When a body that defined one dropped its
    // translations, each link translated the chain again and each relation was decided whole
    // with all its definitions, O(n²): 90.9 times the bytes for 8 times the functions (50 to
    // 400) on main, 7.9 times now.
    questions_scale(
        "a chain of tests defining auxiliary variables",
        50,
        "p0(x: int) = x div 3 > 0;\n",
        |i| format!("p{i}(x: int) = p{}(x: x) && x mod 7 + {i} > 0;\n", i - 1),
    );
}

#[test]
fn each_answer_through_arguments_that_are_not_names_is_the_answer_of_the_relation_whole() {
    // LOAD-chain-args: a body whose call passes its callee a parameter moved by a constant
    // (`x + 1`) or another parameter's name (`y: x`) is read in its callee's coordinates, so
    // that it shares the callee's translation; each answer is the one the body closed over
    // the definitions it reaches has, decided whole over the names the user wrote.
    // No cycle of substitutions is written here: a function defined in terms of itself is
    // rejected below layer L6 ("recursion arrives at layer L6").
    let units = [
        // A chain whose links move the argument, each by another constant.
        "s0(x: int) = x > 0 && x < 50;\ns1(x: int) = s0(x: x + 1) && x mod 3 == 0;\n\
         s2(x: int) = s1(x: x - 4) && x > 5;\ns3(x: int) = s2(x: x + 2) || x < 0 - 10;",
        // Links that rename the parameter, one way and back.
        "a0(x: int) = x > 2;\na1(y: int) = a0(x: y) && y < 10;\n\
         a2(x: int) = a1(y: x + 1) && x mod 2 == 1;\na3(y: int) = a2(x: y) && y > 4;",
        // Links that swap and move two parameters, each link substituting twice, and a link
        // that calls its callee at two substitutions.
        "t0(x: int, y: int) = x > y && y >= 0;\n\
         t1(x: int, y: int) = t0(x: y + 1, y: x - 2) && x + y < 40;\n\
         t2(x: int, y: int) = t1(x: y - 3, y: x + 3) && x < 30;\n\
         t3(x: int, y: int) = t2(x: x, y: y) && t2(x: x + 1, y: y);",
        // Nested `div` and `mod` under a moved argument.
        "d0(x: int) = (x div 3) mod 5 == 2;\nd1(x: int) = d0(x: x + 7) && (x mod 15) div 4 == 1;\n\
         d2(x: int) = d1(x: x - 7) && x > 0;",
        // Arguments that are no substitution of the parameters: a parameter passed twice, a
        // multiple, a constant.
        "k0(x: int, y: int) = x > y + 1;\nk1(x: int, y: int) = k0(x: x, y: x) || y > 0;\n\
         k2(x: int) = k0(x: 2 * x, y: 3);\nk3(x: int, y: int) = k0(x: y, y: y + x);",
        // A function with no call: a chain of one.
        "e0(x: int) = x mod 3 == 1;",
        // LOAD-chain-affine: a callee called with two keys by two callers, a map that is not
        // one-to-one, and a callee read over its parameters' class and bound by another call.
        "q(x: int) = x mod 2 == 0;\nm0(x: int) = q(x: x) && x < 9;\nm1(x: int) = q(x: x) && m0(x: x + 1);\n\
         m2(x: int) = m1(x: 2 * x) && q(x: x + 3) && m0(x: x);",
        // A function whose parameter, read in its question, is bound in a relation the same
        // question reaches: `a`'s question must not bind its own atom through `e`.
        "b(x: int) = x > 2 && x < 7;\ne(x: int) = b(x: x);\na(x: int) = b(x: x) && e(x: x + 1);",
        // A diamond: `h0` reached by `h1` and through `p1`, each passing its parameter.
        "h0(x: int) = x mod 3;\nh1(x: int) = h0(x: x) div 2 + 1;\np0(x: int) = h0(x: x) > 0;\n\
         p1(x: int) = p0(x: x) && h1(x: x) > 1 && h0(x: x + 1) == 2;",
        // A chain whose link moves its callee's point below a test beside it: `p{i-1}`'s point
        // is its lowest `x`, which `x + 3` takes below `q`'s range, so the link extends `q`'s
        // point instead (`Extending::extend`).
        "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\np0(x: int) = x > 0;\n\
         p1(x: int) = q(x: x) && p0(x: x + 3) && x < 1000;\np2(x: int) = q(x: x) && p1(x: x + 3) && x < 2000;\n\
         p3(x: int) = q(x: x) && p2(x: x + 3) && x < 3000;\np4(x: int) = q(x: x) && p3(x: x + 3) && x < 4;",
        // LOAD-affine-cone: a callee of several constraints over `div` and `mod`, claimed by
        // its first call and written at each other call's arguments with its quotients and
        // remainders and the bindings of its own calls eliminated; a call at a moved
        // argument, and one whose callee holds no point.
        "g0(x: int) = x < 50;\ng1(x: int) = g0(x: x) && x mod 3 + 1 < 3;\n\
         g2(x: int) = g1(x: x) && x div 2 > 1;\nc0(x: int) = x > 0;\n\
         c1(x: int) = g2(x: x) && c0(x: x + 1) && x < 30;\n\
         c2(x: int) = g2(x: x) && c1(x: x + 1) && x mod 5 != 2;\n\
         c3(x: int) = g2(x: x + 7) && c2(x: x - 3);\n\
         z(x: int) = x mod 2 == 0 && x mod 4 == 1;\nc4(x: int) = z(x: x) || x > 3;\n\
         c5(x: int) = z(x: x + 1) || c4(x: x - 2);",
        // A callee of one point (22) called by each link of a chain whose links move the
        // argument, so that the calls below the first are written at their arguments and each
        // answer turns on those rows: no point, every point, one point.
        "n0(x: int) = x div 3 == 7 && x mod 3 == 1;\nn1(x: int) = n0(x: x) && x > 0;\n\
         r0(x: int) = x > 0;\nr1(x: int) = n1(x: x) && r0(x: x + 1);\n\
         r2(x: int) = n1(x: x) && r1(x: x + 4);\nr3(x: int) = n1(x: x) || r2(x: x - 1);\n\
         r4(x: int) = n1(x: x) && r1(x: x - 1) || r3(x: x + 2) && x > 18;",
        // Two parameters, one of them a constant at one call and a term of the other at
        // another, and a callee with a disjunction, which no elimination writes, read again.
        "w0(x: int, y: int) = x div 2 == y && y > 0;\nw1(x: int, y: int) = w0(x: x, y: y) && x < 20;\n\
         u1(x: int) = w1(x: x, y: 3) && w1(x: x + 1, y: x - 4);\n\
         v0(x: int) = x != 2 && x != 5;\nv1(x: int) = v0(x: x) && v0(x: x + 1) && x > 0 && x < 9;",
    ];
    for src in units {
        answers_are_those_of_the_whole(src);
    }
}

/// Checks that each answer of each function of `src`, read under one scope and decided from the
/// answers of the conjunctions it extends, with each kept part read through its face where one
/// is made (`Extending::defined_with`), is the one the body closed over the definitions it
/// reaches has, decided whole over the names the user wrote; in the unit's order and in the
/// reverse.
fn answers_are_those_of_the_whole(src: &str) {
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Formula, decide};
    let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let cones = Cones::new(&unit);
    let lets = lets(&unit);
    let fs = functions(&unit);
    let whole = |r: &Relation, f: Formula| decide(&Formula::and(vec![r.defined(), f]));
    // In the unit's order and in the reverse, so that a caller is asked before its callee.
    for order in [
        (0..fs.len()).collect::<Vec<_>>(),
        (0..fs.len()).rev().collect(),
    ] {
        let mut scoped = Scoped::new(&lets);
        let mut extending = Extending::new();
        for i in order {
            let (name, ps, body) = fs[i];
            let (expected, r) = match (
                closed(&cones, ps, body),
                scoped.relation(body, ps, ps, true),
            ) {
                (Some(e), Some(r)) => (e, r),
                (None, None) => continue,
                (e, r) => panic!("`{name}`: {e:?} whole, {} read in the scope", r.is_some()),
            };
            let a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            let w = scoped.written(&r);
            for (got, f) in [
                (&a.holds, expected.body.clone()),
                (&a.fails, Formula::negate(expected.body.clone())),
            ] {
                assert_eq!(*got, whole(&expected, f), "`{name}` in\n{src}\n{w}");
            }
            assert_eq!(
                whole(&w, w.body.clone()),
                a.holds,
                "`{name}` as written in\n{src}\n{w}"
            );
        }
    }
}

/// Checks that each answer of each function of `src`, read under one scope and decided from the
/// answers of the conjunctions it extends, is the same, refusals too, when each kept part is
/// read through its face where one is made (`Extending::defined_with`) as when none is
/// (`Extending::defined`), and is the one the body closed over the definitions it reaches has,
/// decided whole, where that is decided too; in the unit's order and in the reverse. The
/// solver refuses some of these questions decided whole and not decided from parts, and some
/// the other way (`x mod 4 != 1 && (x mod 6 == 2 || x mod 10 == 3)` beside a chain moving it
/// by 3, `p2`), with and without faces alike.
fn answers_with_faces_are_those_without(src: &str) {
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Formula, decide};
    let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let cones = Cones::new(&unit);
    let lets = lets(&unit);
    let fs = functions(&unit);
    let whole = |r: &Relation, f: Formula| decide(&Formula::and(vec![r.defined(), f]));
    for order in [
        (0..fs.len()).collect::<Vec<_>>(),
        (0..fs.len()).rev().collect(),
    ] {
        let mut scoped = Scoped::new(&lets);
        let (mut faced, mut plain) = (Extending::new(), Extending::new());
        for i in order {
            let (name, ps, body) = fs[i];
            let (expected, r) = match (
                closed(&cones, ps, body),
                scoped.relation(body, ps, ps, true),
            ) {
                (Some(e), Some(r)) => (e, r),
                (None, None) => continue,
                (e, r) => panic!("`{name}`: {e:?} whole, {} read in the scope", r.is_some()),
            };
            let a = faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            let b = plain.defined(&r, &|n| scoped.def(n));
            let w = scoped.written(&r);
            assert_eq!(a, b, "`{name}` with faces and without in\n{src}\n{w}");
            for (got, f) in [
                (&a.holds, expected.body.clone()),
                (&a.fails, Formula::negate(expected.body.clone())),
            ] {
                if let (Ok(got), Ok(want)) = (got, whole(&expected, f)) {
                    assert_eq!(*got, want, "`{name}` in\n{src}\n{w}");
                }
            }
        }
    }
}

/// The drifting chain of LOAD-call-summary, `q` and `p0` followed by `p{i}(x) = q(x: x) &&
/// p{i-1}(x: x + 3) && x < 1000 i` for `i` in 1..n: `p{i-1}`'s point is its lowest `x`, which
/// `x + 3` takes below `q`'s range, so each link extends `q`'s point with the chain beside it.
fn drifting_chain(q: &str, n: usize) -> String {
    let mut src = format!("{q}p0(x: int) = x > 0;\n");
    for i in 1..n {
        src.push_str(&drifting_link(i));
    }
    src
}

fn drifting_link(i: usize) -> String {
    format!(
        "p{i}(x: int) = q(x: x) && p{}(x: x + 3) && x < {};\n",
        i - 1,
        1000 * i
    )
}

/// `n` as Zed writes it: a negative number as a difference, since a literal has no sign.
fn lit(n: i64) -> String {
    match n < 0 {
        true => format!("(0 - {})", -n),
        false => n.to_string(),
    }
}

/// A random chain of conjunctions in the shape of the drifting chain: a callee `q` of a range
/// and a remainder, which may hold nowhere, and links that move the argument by a random
/// constant, bound it above, and may test a remainder or a quotient of their own, so that
/// links hold or fail, and their points extend the chain's, `q`'s, or neither.
fn random_chain(rng: &mut zed_tests::instances::Rng) -> String {
    let a = rng.int(-5, 5);
    let b = a + rng.int(-2, 60);
    let m = rng.int(2, 5);
    let mut src = format!(
        "r(x: int) = x > {} && x < {};\nq(x: int) = r(x: x) && x mod {m} == {};\n\
         p0(x: int) = x > {};\n",
        lit(a),
        lit(b),
        rng.int(0, m),
        lit(rng.int(-10, 10)),
    );
    for i in 1..rng.int(2, 7) {
        let own = match rng.below(4) {
            0 => {
                let m = rng.int(2, 4);
                format!(" && x mod {m} == {}", rng.int(0, m - 1))
            }
            1 => format!(" && x div 2 > {}", lit(rng.int(-5, 20))),
            _ => String::new(),
        };
        src.push_str(&format!(
            "p{i}(x: int) = q(x: x) && p{}(x: x + {}) && x < {}{own};\n",
            i - 1,
            lit(rng.int(-4, 4)),
            lit(rng.int(-10, 120)),
        ));
    }
    src
}

#[test]
fn each_answer_of_a_chain_read_through_faces_is_the_answer_of_the_relation_whole() {
    // LOAD-call-summary: chains whose links extend the point of a small callee beside the
    // chain, which they read through its face. The drifting chain; the same with a
    // disjunction in its callee, whose face keeps it as a clause (LOAD-disj-residue); a chain
    // moving a second parameter beside a callee of the first; and random chains of the
    // drifting chain's shape.
    let r = "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\n";
    answers_are_those_of_the_whole(&drifting_chain(r, 30));
    let disjunction = "q(x: int) = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x < 1000000;\n";
    answers_are_those_of_the_whole(&drifting_chain(disjunction, 30));
    let mut second =
        String::from("s(x: int) = x > 0 && x mod 3 == 1;\np0(y: int, x: int) = y > 0 && x > 0;\n");
    for i in 1..30 {
        second.push_str(&format!(
            "p{i}(y: int, x: int) = s(x: x) && p{}(y: y + 3, x: x) && y < {};\n",
            i - 1,
            1000 * i
        ));
    }
    answers_are_those_of_the_whole(&second);
    let mut rng = zed_tests::instances::Rng::new(0x1c5a);
    for _ in 0..60 {
        answers_are_those_of_the_whole(&random_chain(&mut rng));
    }
}

#[test]
fn the_questions_of_a_drifting_chain_scale() {
    // `p{i}(x) = q(x: x) && p{i-1}(x: x + 3) && x < 1000 i` beside `q(x) = r(x: x) && x mod 3
    // == 1` (LOAD-call-summary): each link extends `q`'s point, which it read with the whole
    // chain beside it before; now with the chain's face, `x >= 1`, `x mod 3 == 1` and the
    // link's bound. 40 → 320: 83.9 times the bytes before, the chain read at each link (190
    // MB → 15.9 GB, measured once), 8.2 now (40.9 MB → 334 MB).
    questions_scale(
        "a chain whose links extend a callee's point beside the chain",
        40,
        "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\n\
         p0(x: int) = x > 0;\n",
        drifting_link,
    );
}

/// A random test of `x` that a disjunction may hold: a remainder equal or unequal to a
/// constant, which may lie outside the remainder's range, or a bound.
fn random_case(rng: &mut zed_tests::instances::Rng) -> String {
    let m = rng.int(2, 7);
    match rng.below(4) {
        0 => format!("x mod {m} == {}", rng.int(0, m)),
        1 => format!("x mod {m} != {}", rng.int(0, m - 1)),
        2 => format!("x < {}", lit(rng.int(-10, 40))),
        _ => format!("x > {}", lit(rng.int(-10, 40))),
    }
}

/// A random chain in the shape of the drifting chain whose callee `q` holds one or two
/// disjunctions of [`random_case`]s beside a range, which may share a remainder, and whose
/// links move the argument by a random constant, bound it above, and may hold a disjunction of
/// their own (LOAD-disj-residue): clauses that repeat, that do not, that share a projected
/// atom, and links that hold or fail.
fn random_disjunctive_chain(rng: &mut zed_tests::instances::Rng) -> String {
    let a = rng.int(-5, 5);
    let b = a + rng.int(-2, 80);
    let mut q = format!("({} || {})", random_case(rng), random_case(rng));
    if rng.below(2) == 0 {
        q.push_str(&format!(
            " && ({} || {})",
            random_case(rng),
            random_case(rng)
        ));
    }
    let mut src = format!(
        "q(x: int) = {q} && x > {} && x < {};\np0(x: int) = x > {};\n",
        lit(a),
        lit(b),
        lit(rng.int(-10, 10)),
    );
    for i in 1..rng.int(2, 9) {
        let own = match rng.below(3) {
            0 => format!(" && ({} || {})", random_case(rng), random_case(rng)),
            _ => String::new(),
        };
        src.push_str(&format!(
            "p{i}(x: int) = q(x: x) && p{}(x: x + {}) && x < {}{own};\n",
            i - 1,
            lit(rng.int(-4, 4)),
            lit(rng.int(-10, 160)),
        ));
    }
    src
}

#[test]
fn each_answer_of_a_random_disjunctive_chain_is_the_answer_of_the_relation_whole() {
    // LOAD-disj-residue: the face of a callee with a disjunction keeps it as clauses, each said
    // once. Drifting chains whose clauses repeat every few links (residues modulo 5), never
    // repeat (modulo 1009), move a bound (the holes of `x < 10 || x > 20`), or share a
    // remainder between two disjunctions, which keeps it; and random chains of that shape. Each
    // is checked against the answers made with no face, refusals too, and against the whole
    // where the whole is decided, since the solver refuses some of these questions one way and
    // not the other.
    for q in [
        "(x mod 3 == 1 || x mod 5 == 2)",
        "(x mod 1009 == 0 || x mod 3 == 1)",
        "(x < 10 || x > 20)",
        "(x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50)",
        "x mod 4 != 1 && (x mod 6 == 2 || x mod 10 == 3)",
    ] {
        let q = format!("q(x: int) = {q} && x > 0 && x < 1000000;\n");
        answers_with_faces_are_those_without(&drifting_chain(&q, 30));
    }
    let mut rng = zed_tests::instances::Rng::new(0xd15e);
    for _ in 0..80 {
        answers_with_faces_are_those_without(&random_disjunctive_chain(&mut rng));
    }
}

#[test]
fn the_questions_of_a_drifting_disjunctive_chain_scale() {
    // The drifting chain beside `q(x) = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x <
    // 1000000` (LOAD-disj-residue): each link's face keeps one clause for each residue of the
    // shift modulo 5, five at most, where before the chain was read whole at each link (0.244,
    // 1.005, 5.399 s at 40, 80, 160 links, debug, measured once).
    questions_scale(
        "a chain whose links extend a callee's point beside a chain of disjunctions",
        40,
        "q(x: int) = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x < 1000000;\n\
         p0(x: int) = x > 0;\n",
        drifting_link,
    );
}

#[test]
fn the_questions_of_a_chain_moving_its_argument_scale() {
    // `p{i}(x) = p{i-1}(x: x + 1) && x + 2 i > 0`, the chain of LOAD-chain-args: each link
    // passes its callee another term than its own parameter. 50 → 400: 61.5 times the bytes
    // before (57.2 MB → 3.52 GB, each call translated again), 8.1 now (7.9 MB → 63.9 MB).
    questions_scale(
        "a chain of tests moving the argument",
        50,
        "p0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = p{}(x: x + 1) && x + {} > 0;\n",
                i - 1,
                2 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_renaming_its_argument_scale() {
    // `p{i}(x) = p{i-1}(y: x) && x > -i`, the parameter named `x` and `y` by turns: each link
    // passes its callee its own parameter under the callee's name. 50 → 400: 60.7 times the
    // bytes before (45.4 MB → 2.76 GB), 8.0 now (6.3 MB → 50.9 MB).
    questions_scale(
        "a chain of tests renaming the argument",
        50,
        "p0(x: int) = x > 0;\n",
        |i| {
            let (own, callee) = if i % 2 == 0 { ("x", "y") } else { ("y", "x") };
            format!(
                "p{i}({own}: int) = p{}({callee}: {own}) && {own} > 0 - {i};\n",
                i - 1
            )
        },
    );
}

#[test]
fn each_answer_through_a_chain_of_definitions_is_the_answer_of_the_relation_alone() {
    // LOAD-chain-defs: a link whose new constraint reads a chain of int-returning functions
    // (`h{i}(x) = h{i-1}(x: x) div 2 + 1`) is decided from its callee's point with only the
    // definitions its link added; each answer is the one the relation with all its
    // definitions has, in both orders of the bodies.
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Formula, decide};
    let units = [
        // Halvings read by a chain of tests: a link that holds at its callee's point, one that
        // excludes it, and one that holds nowhere.
        "h0(x: int) = x;\nh1(x: int) = h0(x: x) div 2 + 1;\nh2(x: int) = h1(x: x) div 2 + 1;\n\
         h3(x: int) = h2(x: x) div 3 - 1;\np0(x: int) = x > 0;\np1(x: int) = p0(x: x) && h1(x: x) > 0;\n\
         p2(x: int) = p1(x: x) && h2(x: x) > 2;\np3(x: int) = p2(x: x) && h3(x: x) < 0;\n\
         p4(x: int) = p2(x: x) && h1(x: x) < 0;",
        // Mixed operations, each also reading the input, and a link reading two members of
        // the chain and a product of one with the input.
        "g0(x: int) = x;\ng1(x: int) = g0(x: x) mod 7 + x;\ng2(x: int) = min(g1(x: x), 9) + 1;\n\
         g3(x: int) = abs(g2(x: x)) - x div 3;\nq0(x: int) = x > 0 - 20;\n\
         q1(x: int) = q0(x: x) && g1(x: x) > 0 - 5;\nq2(x: int) = q1(x: x) && g2(x: x) < 8;\n\
         q3(x: int) = q2(x: x) && g3(x: x) + g1(x: x) > 4;\nq4(x: int) = q3(x: x) && g2(x: x) * x > 3;",
        // A root and links that hold everywhere, then a link that fails somewhere, and one
        // that holds nowhere: the negation is decided from the new definitions alone.
        "k0(x: int) = x;\nk1(x: int) = k0(x: x) div 2 + 1;\nk2(x: int) = k1(x: x) div 2 + 1;\n\
         a0(x: int) = x > 0 || x <= 0;\na1(x: int) = a0(x: x) && abs(k1(x: x)) >= 0;\n\
         a2(x: int) = a1(x: x) && abs(k2(x: x)) >= 0;\na3(x: int) = a2(x: x) && k2(x: x) > 1;\n\
         a4(x: int) = a2(x: x) && abs(k2(x: x)) < 0;",
    ];
    let (mut nowhere, mut everywhere) = (0, 0);
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
                let Some(r) = scoped.relation(body, ps, ps, true) else {
                    continue;
                };
                let a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
                let w = scoped.written(&r);
                let with = |f: Formula| Formula::and(vec![w.defined(), f]);
                assert_eq!(
                    a.holds,
                    decide(&with(w.body.clone())),
                    "`{name}` can hold in\n{src}\n{w}"
                );
                assert_eq!(
                    a.fails,
                    decide(&with(Formula::negate(w.body.clone()))),
                    "`{name}` can fail in\n{src}\n{w}"
                );
                nowhere += usize::from(a.holds == Ok(false));
                everywhere += usize::from(a.fails == Ok(false));
            }
        }
    }
    // Both shortcuts' other sides are met: relations that hold nowhere and that hold everywhere.
    assert!(nowhere >= 2, "{nowhere} hold nowhere");
    assert!(everywhere >= 2, "{everywhere} hold everywhere");
}

#[test]
fn the_questions_of_a_chain_of_tests_over_a_chain_of_definitions_scale() {
    // `p{i}(x) = p{i-1}(x: x) && h{i}(x: x) > 0` with `h{i}(x) = h{i-1}(x: x) div 2 + 1`: each
    // link's new constraint reaches the i definitions of `h{i}`. When each link read them all,
    // 74.6 times the instructions and 66.8 times the bytes for 8 times the links (25 to 200);
    // 8.1 and 8.0 times when it reads past those its callee's point gives a value.
    questions_scale(
        "a chain of tests over a chain of halvings",
        25,
        "h0(x: int) = x;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "h{i}(x: int) = h{}(x: x) div 2 + 1;\np{i}(x: int) = p{}(x: x) && h{i}(x: x) > 0;\n",
                i - 1,
                i - 1
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_of_tests_over_mixed_definitions_scale() {
    // As above, the definitions by turns a quotient, a remainder plus the input, a minimum and
    // an absolute value less a quotient: 103.2 times the instructions and 98.5 times the bytes
    // from 25 to 200 links when each link read the chain, about 8.2 times now.
    questions_scale(
        "a chain of tests over mixed definitions",
        25,
        "h0(x: int) = x;\np0(x: int) = x > 0;\n",
        |i| {
            let h = i - 1;
            let op = match i % 4 {
                0 => format!("h{h}(x: x) div 2"),
                1 => format!("h{h}(x: x) mod 7 + x"),
                2 => format!("min(h{h}(x: x), {i}) + 1"),
                _ => format!("abs(h{h}(x: x)) - x div 3"),
            };
            format!("h{i}(x: int) = {op};\np{i}(x: int) = p{h}(x: x) && h{i}(x: x) > 0 - {i};\n")
        },
    );
}

#[test]
fn the_questions_of_a_chain_of_tests_holding_everywhere_scale() {
    // A root and links that hold everywhere, `p{i}(x) = p{i-1}(x: x) && abs(h{i}(x: x)) >= 0`:
    // each link's negation is decided from the definitions its link added, which never hold
    // with it. 85.4 times the instructions and 73.0 times the bytes from 25 to 200 links when
    // it read the chain (81.1 and 62.7 times with only the side that holds reading past the
    // point), 7.7 times now.
    questions_scale(
        "a chain of tests holding everywhere over a chain of halvings",
        25,
        "h0(x: int) = x;\np0(x: int) = x > 0 || x <= 0;\n",
        |i| {
            format!(
                "h{i}(x: int) = h{}(x: x) div 2 + 1;\np{i}(x: int) = p{}(x: x) && abs(h{i}(x: x)) >= 0;\n",
                i - 1,
                i - 1
            )
        },
    );
}

#[test]
fn separate_tests_over_the_links_of_one_chain_of_definitions_scale() {
    // LOAD-chain-sep: `t{i}(x) = h{i}(x: x) > 0` with `h{i}(x) = h{i-1}(x: x) div 2 + 1`, each
    // test a question of its own over the i definitions of `h{i}`, with no kept part. Each was
    // decided with all i definitions, O(n²): 80.4 times the bytes for 8 times the functions (25
    // to 200) on main; read through the summary of `h{i}`'s definition, made from that of
    // `h{i-1}`'s, 8.4 times the bytes and 9.0 times the instructions now.
    questions_scale(
        "separate tests over one chain of halvings",
        25,
        "h0(x: int) = x;\nt0(x: int) = x > 0;\n",
        |i| {
            format!(
                "h{i}(x: int) = h{}(x: x) div 2 + 1;\nt{i}(x: int) = h{i}(x: x) > 0;\n",
                i - 1
            )
        },
    );
}

#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions() {
    // LOAD-chain-sep: a question with no kept part reads each definition's chain through its
    // summary, projected exactly. Each answer is the one the relation with all its definitions
    // has, asked in the unit's order, in the reverse, and alone, so that the answers do not
    // depend on what was asked before (batch and single-file checking agree). Where the solver
    // refuses the whole (its shadows disagree), the smaller question of the summaries may be
    // answered: the answer is then checked against the values of `x` from -300 to 300.
    use zedc::store::presburger::extend::{Answers, Extending};
    use zedc::store::presburger::{Atom, Con, Formula, Lin, decide};
    // The answer `got` of whether `f` holds somewhere: [`decide`]'s, or, where it refuses,
    // one the values of `x` from -300 to 300 do not contradict.
    let agrees = |f: Formula, got: &Result<bool, zedc::store::presburger::Refusal>, what: &str| {
        let whole = decide(&f);
        if whole.is_ok() {
            assert_eq!(*got, whole, "{what}");
            return;
        }
        let Ok(got) = got else { return };
        let x = (f.atoms().into_iter())
            .find(|a| matches!(a, Atom::Sym(_)))
            .expect("an input");
        let at = |v: i64| {
            let fixed = Formula::Con(Con::eq(&Lin::atom(x.clone()), &Lin::constant(v)));
            decide(&Formula::and(vec![f.clone(), fixed])) == Ok(true)
        };
        assert!(*got || !(-300..=300).any(at), "{what}: holds nowhere");
        assert!(!*got || (-300..=300).any(at), "{what}: holds somewhere");
    };
    let chain = |step: &str, test: &str, n: usize| {
        let mut src = "h0(x: int) = x;\n".to_string();
        for i in 1..=n {
            src += &format!(
                "h{i}(x: int) = {};\n",
                step.replace("H", &format!("h{}(x: x)", i - 1))
            );
            src += &format!(
                "t{i}(x: int) = {};\n",
                test.replace("H", &format!("h{i}(x: x)"))
            );
        }
        src
    };
    let units = [
        // The chain of the scaling test, and other steps: by 3, a remainder, a step that
        // reverses the sign, one that grows its input, and one that reads it twice.
        chain("H div 2 + 1", "H > 0", 7),
        chain("H div 3 - 2", "H > 0", 6),
        chain("H mod 7 + H", "H == 9", 5),
        chain("(0 - H) div 2", "H > 1", 6),
        chain("(3 * H + 1) div 2", "H < 0 - 4", 6),
        chain("H div 2 + H div 3", "H > 5", 5),
        // Steps whose projections are not exact (`3·q` of `x div 2` skips values), where no
        // summary is made, and tests that ask for one value or one remainder.
        chain("(3 * H) div 2", "H == 4", 5),
        chain("(3 * H) div 2", "H == 2", 4),
        chain("(3 * H) div 2", "H == 2 || H == 5", 4),
        chain("(3 * H) div 2 + 1", "H mod 2 == 1 && x < 7 && x > 0 - 7", 5),
        chain("(5 * H + 2) div 3", "H == 7 || H == 12", 4),
        chain("2 * H", "H mod 3 == 1", 5),
        chain("(2 * H) div 3", "3 * H == 2 * x", 4),
        // Tests that hold everywhere or nowhere, and tests over two links of one chain and
        // over two chains.
        chain("H div 2 + 1", "H * 2 <= x + 2 || H * 2 > x + 2", 6),
        chain("H div 2", "H * 2 > x + 1 && x >= 0", 6),
        chain("H div 2 + 1", "H > h1(x: x)", 6),
        chain("H div 2 + 1", "H + h1(x: x + 1) > 3", 6),
        // A branch, a smallest value and an absolute value in a link: no summary is made
        // past them.
        chain("if H > 3 { H div 2 } else { H + 1 }", "H > 2", 5),
        chain("min(H div 2, x)", "H > 0", 5),
        chain("abs(H div 2 - 3)", "H > 1", 5),
        // A division by a variable.
        chain("H div x", "H > 0", 4),
    ];
    for src in &units {
        let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let lets = lets(&unit);
        let fs = functions(&unit);
        let n = fs.len();
        // The answers of each function, asked in an order of one `Extending`.
        let ask = |order: Vec<usize>| -> Vec<Option<Answers>> {
            let mut scoped = Scoped::new(&lets);
            let mut extending = Extending::new();
            let mut out = vec![None; n];
            for i in order {
                let (name, ps, body) = fs[i];
                let Some(r) = scoped.relation(body, ps, ps, true) else {
                    continue;
                };
                let a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
                let w = scoped.written(&r);
                let with = |f: Formula| Formula::and(vec![w.defined(), f]);
                agrees(
                    with(w.body.clone()),
                    &a.holds,
                    &format!("`{name}` can hold in\n{src}\n{w}"),
                );
                agrees(
                    with(Formula::negate(w.body.clone())),
                    &a.fails,
                    &format!("`{name}` can fail in\n{src}\n{w}"),
                );
                out[i] = Some(a);
            }
            out
        };
        let forward = ask((0..n).collect());
        assert!(forward.iter().any(Option::is_some), "{src}");
        assert_eq!(forward, ask((0..n).rev().collect()), "{src}");
        for i in 0..n {
            assert_eq!(forward[i], ask(vec![i])[i], "{src}: `{}` alone", fs[i].0);
        }
    }
}

/// Times the relations, translated alone, of a unit of `first` and the links `link(1)` to
/// `link(m - 1)`, at m = `n` and 8n, on units elaborated before the timing: for chains whose
/// questions are decided whole because each link's constraints exclude the point found for
/// the link it calls (`presburger::extend`, COMPLEXITY.md row LOAD-chain-share).
fn relations_scale(what: &str, n: usize, first: &str, link: fn(usize) -> String) {
    let units: std::collections::BTreeMap<usize, Unit> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src: String = std::iter::once(first.to_string())
                .chain((1..m).map(link))
                .collect();
            (m, elab(&src).unwrap())
        })
        .collect();
    zed_tests::scaling::check(what, n, |m| {
        let unit = &units[&m];
        let lets = lets(unit);
        let mut scoped = Scoped::new(&lets);
        for (name, ps, body) in functions(unit) {
            assert!(scoped.relation(body, ps, ps, true).is_some(), "{name}");
        }
    });
}

#[test]
fn the_questions_of_a_chain_doubling_its_argument_scale() {
    // `p{i}(x) = p{i-1}(x: 2 * x) && x < 1000 i`, LOAD-chain-affine: a map of the parameter
    // that is not a move. 50 → 400: 59.3 times the bytes when each call was translated again
    // at its argument; each body is now read once over its canonical atom, and a call binds
    // that atom to its argument.
    questions_scale(
        "a chain of tests doubling the argument",
        50,
        "p0(x: int) = x > 0;\n",
        |i| format!("p{i}(x: int) = p{}(x: 2 * x) && x < {};\n", i - 1, 1000 * i),
    );
}

#[test]
fn the_questions_of_a_chain_negating_its_argument_scale() {
    // `p{i}(x) = p{i-1}(x: 0 - x) && x < 1000 i`: a map with a negative factor. Linear before
    // LOAD-chain-affine too; kept so that the canonical reading stays so.
    questions_scale(
        "a chain of tests negating the argument",
        50,
        "p0(x: int) = x > 0;\n",
        |i| format!("p{i}(x: int) = p{}(x: 0 - x) && x < {};\n", i - 1, 1000 * i),
    );
}

#[test]
fn the_questions_of_a_chain_passing_a_constant_scale() {
    // `p{i}(x, y) = p{i-1}(x: x, y: 5) && x + y < 1000 i`: a constant argument beside a
    // parameter passed as it is. Linear before LOAD-chain-affine too (the moved case is
    // `the_relations_of_a_chain_passing_a_moved_parameter_and_a_constant_scale`).
    questions_scale(
        "a chain of tests passing a constant",
        50,
        "p0(x: int, y: int) = x > y;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x, y: 5) && x + y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_passing_a_parameter_twice_scale() {
    // `p{i}(x, y) = p{i-1}(x: x, y: x) && x + y < 1000 i`: a map that is not one-to-one; the
    // join of `x` to both of the callee's parameters is refused once per link
    // (`preimage::identity_classes`). Linear before LOAD-chain-affine too (the moved case is
    // `the_relations_of_a_chain_passing_a_moved_parameter_twice_scale`).
    questions_scale(
        "a chain of tests passing a parameter twice",
        50,
        "p0(x: int, y: int) = x >= y;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x, y: x) && x + y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_with_a_second_call_scale() {
    // `p{i}(x) = q(x: x) && p{i-1}(x: x + 1) && x < 1000 i`: one function, `q`, called by
    // every link with another argument; its relation, one constraint, is written at each
    // call's argument. 50 → 400: 60.1 times the bytes when each link read the chain below
    // it again.
    questions_scale(
        "a chain of tests with a second call",
        50,
        "q(x: int) = x < 1000000;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_calling_its_helpers_in_a_diamond_scale() {
    // `h{i}(x) = h{i-1}(x: x) div 2 + 1; p{i}(x) = p{i-1}(x: x) && h{i}(x: x) > 0`: `h{i-1}`
    // is called by `h{i}` and through `p{i-1}`, each passing its parameter as it is; one class
    // of parameters holds them all (`preimage::identity_classes`), so each body is read once.
    // Linear before LOAD-chain-affine too; kept so that the classes keep it so.
    questions_scale(
        "a chain of tests calling its helpers in a diamond",
        25,
        "h0(x: int) = x;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "h{i}(x: int) = h{}(x: x) div 2 + 1;\np{i}(x: int) = p{}(x: x) && h{i}(x: x) > 0;\n",
                i - 1,
                i - 1
            )
        },
    );
}

// Chains whose questions are decided whole, because each link's constraints exclude the point
// of the link it calls (COMPLEXITY.md row LOAD-chain-share): their translation alone is O(n).

#[test]
fn the_relations_of_a_chain_with_a_second_call_whose_points_move_scale() {
    // 50 → 400: 62.5 times the bytes when each call was translated again.
    relations_scale(
        "the relations of a chain with a second call whose points move",
        50,
        "q(x: int) = x > 0;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_passing_a_moved_parameter_twice_scale() {
    // A map that is not one-to-one, of a moved parameter. 50 → 400: 62.5 times the bytes when
    // each call was translated again.
    relations_scale(
        "the relations of a chain passing a moved parameter twice",
        50,
        "p0(x: int, y: int) = x >= y;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x + 1, y: x + 1) && x + y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_passing_a_moved_parameter_and_a_constant_scale() {
    // A constant beside a moved parameter. 50 → 400: 62.4 times the bytes when each call was
    // translated again.
    relations_scale(
        "the relations of a chain passing a moved parameter and a constant",
        50,
        "p0(x: int, y: int) = x > y;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x + 1, y: 5) && x + y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_with_a_second_call_of_two_constraints_scale() {
    // `q` of two constraints is claimed by its first call and bound by each other. 50 → 400:
    // 61.1 times the bytes when each call was translated again.
    relations_scale(
        "the relations of a chain with a second call of two constraints",
        50,
        "q(x: int) = x > 0 && x < 1000000;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_with_a_second_call_of_a_call_scale() {
    // `q` calls `r` with its parameter as it is, so the two are one class
    // (`preimage::identity_classes`), read once. 50 → 400: 59.2 times the bytes when each call
    // was translated again.
    relations_scale(
        "the relations of a chain with a second call of a call",
        50,
        "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\n\
         p0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_with_a_second_call_of_a_call_scale() {
    // `p{i}(x) = q(x: x) && p{i-1}(x: x + 1) && x < 1000 i`, `q` calling `r`, with upper bounds
    // alone, so each link's point extends its callee's. Each conjunction keeps its largest
    // part, `p{i-1}`'s relation, and reads `q`'s beside it (`presburger::extend`); keeping the
    // first, `q`'s, read the chain again at each link. 50 → 400: 59.1 times the bytes when each
    // link translated the chain below it again.
    questions_scale(
        "a chain of tests with a second call of a call",
        50,
        "r(x: int) = x < 2000000;\nq(x: int) = r(x: x) && x < 1000000;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_with_a_second_call_of_a_large_callee_scale() {
    // `p{i}(x) = h{n-1}(x: x) && p{i-1}(x: x + 1) && x < 1000 i`, `h{j}(x) = h{j-1}(x: x) &&
    // x mod 3 + j < 2000000` a chain of n links (LOAD-affine-cone): one callee whose cone
    // grows with the chain, called by every link with another argument. Its first call claims
    // it; each other is its relation with the quotients and remainders and the bindings of its
    // calls eliminated, made once and written at the call's argument in O(its rows). 50 → 400:
    // 51.6 times the bytes when each such call read the callee's cone again (304 MB → 15.7 GB,
    // measured once), 8.0 now (45.2 MB → 361 MB).
    let unit = |n: usize| {
        let mut src = String::from("h0(x: int) = x < 2000000;\n");
        for j in 1..n {
            src.push_str(&format!(
                "h{j}(x: int) = h{}(x: x) && x mod 3 + {j} < 2000000;\n",
                j - 1
            ));
        }
        src.push_str("p0(x: int) = x > 0;\n");
        for i in 1..n {
            src.push_str(&format!(
                "p{i}(x: int) = h{}(x: x) && p{}(x: x + 1) && x < {};\n",
                n - 1,
                i - 1,
                1000 * i
            ));
        }
        src
    };
    let n = 50;
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            (m, (zed_tests::deep::statements(&src), elab(&src).unwrap()))
        })
        .collect();
    zed_tests::scaling::check(
        "the linear questions of a chain with a second call of a large callee",
        n,
        |m| {
            let (stmts, unit) = &units[&m];
            let refused = zedc::front::linear_questions(stmts, unit);
            assert!(refused.is_empty(), "{refused:?}");
        },
    );
}

/// A random unit of callees that keep a congruence and integer functions over remainders and
/// quotients (LOAD-call-relation), each called by more than one caller at moved arguments, so
/// that all but the first call of each are written from its projection at their arguments:
/// tests `g{j}` each calling the one before at a moved argument beside a remainder, a quotient
/// or a bound; integer functions `v{j}` each adding a remainder or a quotient of its argument
/// to the one before; a test `w` of two parameters; and callers `c{i}` that call them, and the
/// caller before, at random moves, bounds and constants, so that calls hold, fail, or are
/// refused.
fn random_congruence_unit(rng: &mut zed_tests::instances::Rng) -> String {
    let m = rng.int(2, 5);
    let mut src = format!(
        "g0(x: int) = x mod {m} == {} && x < {};\n",
        rng.int(0, m - 1),
        lit(rng.int(-5, 80)),
    );
    let gs = rng.int(1, 4);
    for j in 1..gs {
        let m = rng.int(2, 6);
        let own = match rng.below(3) {
            0 => format!("x mod {m} == {}", rng.int(0, m)),
            1 => format!("x div {m} > {}", lit(rng.int(-5, 10))),
            _ => format!("x > {}", lit(rng.int(-10, 10))),
        };
        src.push_str(&format!(
            "g{j}(x: int) = g{}(x: x + {}) && {own};\n",
            j - 1,
            lit(rng.int(-3, 3)),
        ));
    }
    let m = rng.int(2, 5);
    src.push_str(&format!("v0(x: int) = x mod {m};\n"));
    let vs = rng.int(1, 4);
    for j in 1..vs {
        let op = ["mod", "div"][rng.below(2)];
        src.push_str(&format!(
            "v{j}(x: int) = v{}(x: x + {}) + x {op} {};\n",
            j - 1,
            lit(rng.int(-3, 3)),
            rng.int(2, 5),
        ));
    }
    let m = rng.int(2, 4);
    src.push_str(&format!(
        "w(x: int, y: int) = x mod {m} == y mod {m} && x < y + {};\nc0(x: int) = x > {};\n",
        rng.int(0, 20),
        lit(rng.int(-10, 10)),
    ));
    for i in 1..rng.int(2, 6) {
        let mut parts = vec![format!(
            "g{}(x: x + {})",
            rng.int(0, gs - 1),
            lit(rng.int(-4, 4))
        )];
        if rng.below(2) == 0 {
            parts.push(format!(
                "v{}(x: x + {}) < {}",
                rng.int(0, vs - 1),
                lit(rng.int(-4, 4)),
                lit(rng.int(-2, 12)),
            ));
        }
        if rng.below(3) == 0 {
            parts.push(format!(
                "w(x: x + {}, y: {})",
                lit(rng.int(-2, 2)),
                ["x".to_string(), lit(rng.int(-3, 9))][rng.below(2)],
            ));
        }
        parts.push(format!(
            "c{}(x: x + {}) && x < {}",
            i - 1,
            lit(rng.int(-3, 3)),
            lit(rng.int(-10, 120)),
        ));
        let join = [" && ", " || "][usize::from(rng.below(4) == 0)];
        src.push_str(&format!("c{i}(x: int) = {};\n", parts.join(join)));
    }
    src
}

#[test]
fn each_answer_through_a_projection_kept_over_pairs_is_the_answer_of_the_relation_whole() {
    // LOAD-call-relation: a call that does not hold its callee's claim writes the callee's
    // projection at its arguments; where the projection keeps a congruence, it keeps the
    // quotients and remainders by constants, written at the call as the pairs of the
    // arguments; an integer function's value is written so too. Each relation and answer,
    // refusals too, is the one read with each such call reading its callee's body again, and
    // the one the body closed over the definitions it reaches has, decided whole, where both
    // are decided. A chain of congruences, an integer chain, and random units.
    answers_are_those_reading_bodies(
        "h0(x: int) = x < 200;\nh1(x: int) = h0(x: x) && x mod 4 == 1 && x < 199;\n\
         h2(x: int) = h1(x: x + 1) && x mod 3 == 2;\np0(x: int) = x > 0;\n\
         p1(x: int) = h2(x: x) && p0(x: x + 1) && x < 100;\n\
         p2(x: int) = h2(x: x + 4) && p1(x: x + 1) && x < 90;\n\
         p3(x: int) = h2(x: 2 * x) || p2(x: x - 1);",
    );
    answers_are_those_reading_bodies(
        "v0(x: int) = x mod 3;\nv1(x: int) = v0(x: x) + x div 2;\nv2(x: int) = v1(x: x + 1) + x mod 5;\n\
         p0(x: int) = x > 0;\np1(x: int) = v2(x: x) < 9 && p0(x: x + 1) && x < 40;\n\
         p2(x: int) = v2(x: x - 2) == 7 && p1(x: x + 1) && x < 30;\n\
         p3(x: int) = v1(x: x) + v2(x: x + 3) > 20 || p2(x: x);",
    );
    let mut rng = zed_tests::instances::Rng::new(0x1c4e);
    for _ in 0..80 {
        answers_are_those_reading_bodies(&random_congruence_unit(&mut rng));
    }
}

/// Times the relations, translated alone, of the tests `p{i}` of the units `unit(n)` and
/// `unit(8n)`, elaborated before the timing: their integer functions are read through their
/// calls.
fn unit_relations_scale(what: &str, n: usize, unit: fn(usize) -> String) {
    let units: std::collections::BTreeMap<usize, Unit> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| (m, elab(&unit(m)).unwrap()))
        .collect();
    zed_tests::scaling::check(what, n, |m| {
        let unit = &units[&m];
        let lets = lets(unit);
        let mut scoped = Scoped::new(&lets);
        for (name, ps, body) in functions(unit) {
            if !name.starts_with('p') {
                continue;
            }
            assert!(scoped.relation(body, ps, ps, true).is_some(), "{name}");
        }
    });
}

#[test]
fn the_questions_of_a_chain_calling_a_callee_that_keeps_a_congruence_scale() {
    // `p{i}(x) = h{n-1}(x: x) && p{i-1}(x: x + 1) && x < 1000 i` beside `h{j}(x) =
    // h{j-1}(x: x) && x mod 4 == 1 && x < 2000000 - j` (LOAD-call-relation): no elimination
    // over `x` alone writes `h{n-1}`, so each call but the first read its cone again, O(n) a
    // call (0.207, 0.882, 3.297 s for the relations at 50, 100, 200 links; 50 → 400:
    // 141.1 times the bytes, 363 MB → 51.2 GB; measured once). Its projection
    // now keeps the one pair `x div 4`, `x mod 4` the chain's links share, and a call writes it
    // at its argument in O(its rows): 11.8 times (73.6 MB → 864 MB).
    questions_scale_unit(
        "a chain calling a callee that keeps a congruence",
        50,
        |n| {
            let mut src = String::from("h0(x: int) = x < 2000000;\n");
            for j in 1..n {
                src.push_str(&format!(
                    "h{j}(x: int) = h{}(x: x) && x mod 4 == 1 && x < {};\n",
                    j - 1,
                    2000000 - j
                ));
            }
            src.push_str("p0(x: int) = x > 0;\n");
            for i in 1..n {
                src.push_str(&format!(
                    "p{i}(x: int) = h{}(x: x) && p{}(x: x + 1) && x < {};\n",
                    n - 1,
                    i - 1,
                    1000 * i
                ));
            }
            src
        },
    );
}

#[test]
fn the_relations_of_a_chain_calling_an_integer_function_scale() {
    // `p{i}(x) = h{n-1}(x: x) < 3n && p{i-1}(x: x + 1) && x < 1000 i` beside `h{j}(x) =
    // h{j-1}(x: x) + x mod 3` (LOAD-call-relation): each call but the first read the integer
    // function's cone again, O(n) a call (0.062, 0.238, 1.082 s for the relations at 50, 100,
    // 200 links; 50 → 400: 60.2 times the bytes, 88.2 MB → 5.31 GB; measured once). Its
    // value is now written once over its argument's pairs and, at a call, at the argument: 8.1
    // times (13.6 MB → 111 MB). Only the relations are timed: deciding these
    // questions (`Extending::defined_with`) grows faster than n log n with the remainders
    // along the chain (10.7 s at 400 links), which item LOAD-call-relation returns.
    unit_relations_scale(
        "the relations of a chain calling an integer function",
        50,
        |n| {
            let mut src = String::from("h0(x: int) = x mod 3;\n");
            for j in 1..n {
                src.push_str(&format!("h{j}(x: int) = h{}(x: x) + x mod 3;\n", j - 1));
            }
            src.push_str("p0(x: int) = x > 0;\n");
            for i in 1..n {
                src.push_str(&format!(
                    "p{i}(x: int) = h{}(x: x) < {} && p{}(x: x + 1) && x < {};\n",
                    n - 1,
                    3 * n,
                    i - 1,
                    1000 * i
                ));
            }
            src
        },
    );
}

/// Times the linear questions of the units `unit(n)` and `unit(8n)`, elaborated before the
/// timing; none is refused.
fn questions_scale_unit(what: &str, n: usize, unit: fn(usize) -> String) {
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            (m, (zed_tests::deep::statements(&src), elab(&src).unwrap()))
        })
        .collect();
    zed_tests::scaling::check(what, n, |m| {
        let (stmts, unit) = &units[&m];
        let refused = zedc::front::linear_questions(stmts, unit);
        assert!(refused.is_empty(), "{refused:?}");
    });
}

/// Checks that each relation and answer of each function of `src`, read under one scope and
/// decided from the answers of the conjunctions it extends (`Extending::defined_with`), is the
/// same, refusals too, when each call that does not hold its callee's claim writes the
/// callee's projection over quotients and remainders as when it reads the callee's body again
/// (`Scoped::reading_bodies`, LOAD-call-relation), and is the one the body closed over the
/// definitions it reaches has, decided whole, where that is decided too; in the unit's order
/// and in the reverse.
fn answers_are_those_reading_bodies(src: &str) {
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Formula, decide};
    let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let cones = Cones::new(&unit);
    let lets = lets(&unit);
    let fs = functions(&unit);
    let whole = |r: &Relation, f: Formula| decide(&Formula::and(vec![r.defined(), f]));
    for order in [
        (0..fs.len()).collect::<Vec<_>>(),
        (0..fs.len()).rev().collect(),
    ] {
        let (mut scoped, mut again) = (Scoped::new(&lets), Scoped::new(&lets).reading_bodies());
        let (mut ext, mut ext_again) = (Extending::new(), Extending::new());
        for i in order {
            let (name, ps, body) = fs[i];
            let (expected, r, s) = match (
                closed(&cones, ps, body),
                scoped.relation(body, ps, ps, true),
                again.relation(body, ps, ps, true),
            ) {
                (Some(e), Some(r), Some(s)) => (e, r, s),
                (None, None, None) => continue,
                (e, r, s) => panic!(
                    "`{name}` in\n{src}\n{e:?} whole, {} read, {} read with the bodies",
                    r.is_some(),
                    s.is_some()
                ),
            };
            let a = ext.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            let b = ext_again.defined_with(&s, &|n| again.def(n), &|g| again.interface(g));
            let w = scoped.written(&r);
            assert_eq!(
                a,
                b,
                "`{name}` in\n{src}\n{w}\nwith the bodies:\n{}",
                again.written(&s)
            );
            for (got, f) in [
                (&a.holds, expected.body.clone()),
                (&a.fails, Formula::negate(expected.body.clone())),
            ] {
                if let (Ok(got), Ok(want)) = (got, whole(&expected, f)) {
                    assert_eq!(*got, want, "`{name}` in\n{src}\n{w}");
                }
            }
        }
    }
}
