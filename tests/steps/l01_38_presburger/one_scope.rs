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
/// (`Scoped::written`), so two relations equal but for that numbering have one shape. A
/// definition no formula meets is left out: the closed relation keeps those of a quotient its
/// body folds away (`(x mod n) * 0 == 0` is `n != 0`), which constrain nothing.
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
    DIVIDING,
];

/// Quotients and remainders by terms, which fail where the divisor is 0, read at the
/// functions' places and through calls: a call that holds its callee's claim (`u3`), calls
/// that do not, written at their arguments (`u5`), a callee with an `if` on a remainder (`u6`
/// of `u4`), and a callee whose condition reads a remainder, which a call that does not hold
/// the claim reads at its place (`u8` of `u7`) (RUNG2-definedness). `u1` holds the divisor
/// 0 among others: under `n == 0` alone the remainder would always fail, which the checker
/// rejects (row "Operation that always fails").
const DIVIDING: &str = "u1(x: int, n: int) = n <= 0 && x mod n == 5;\n\
     u2(x: int, n: int) = (x mod n) * 0 == 0;\n\
     u3(x: int, n: int) = u2(x: x, n: n) && x div n >= 0;\n\
     u4(x: int, n: int) = if x mod n >= 1 { x div n > 0 } else { true };\n\
     u5(x: int, n: int) = u2(x: x + 1, n: n - 1) && u2(x: x, n: n + 2);\n\
     u6(x: int, n: int) = u4(x: x + 1, n: n) || u4(x: x, n: n - 1);\n\
     u7(x: int, n: int) = if x mod n >= 1 { x mod (n + 1) > 0 } else { true };\n\
     u8(x: int, n: int) = u7(x: x + 1, n: n) && u7(x: x, n: n - 1);";

#[test]
fn a_relation_that_divides_by_a_term_holds_where_the_interpreter_gives_true() {
    // The path `front::linear_questions` reads, with products: at each point of a window the
    // relation, as written, holds exactly where the body closed over the unit gives `true`
    // (DESIGN.md M0.9 (a)), in the unit's order and in the reverse. The point is written into
    // the relation and its definitions, so that a product of a parameter and a quotient is
    // linear there.
    use std::collections::HashMap;
    use zedc::store::presburger::{Atom, Con, Factor, Formula, Lin, decide};
    let at_point = |f: &Formula, p: &HashMap<Arc<str>, i64>| {
        let atom = |x: &Factor| match x {
            Factor::Sym(s) => match p.get(s) {
                Some(v) => Lin::constant(*v),
                None => Lin::atom(Atom::Sym(s.clone())),
            },
            Factor::Aux(n) => Lin::atom(Atom::Aux(*n)),
        };
        f.map_cons(&|c: &Con| {
            let mut lin = Lin {
                terms: Default::default(),
                constant: c.lin.constant.clone(),
            };
            for (a, k) in &c.lin.terms {
                let term = match a {
                    Atom::Sym(s) => atom(&Factor::Sym(s.clone())),
                    Atom::Aux(n) => Lin::atom(Atom::Aux(*n)),
                    Atom::Product(x, y) => match (atom(x), atom(y)) {
                        (x, y) if x.terms.is_empty() => y.times(x.constant),
                        (x, y) if y.terms.is_empty() => x.times(y.constant),
                        _ => Lin::atom(a.clone()),
                    },
                };
                lin = lin.plus(&term.times(k.clone()));
            }
            Formula::Con(Con { lin, rel: c.rel })
        })
    };
    let unit = elab(DIVIDING).unwrap();
    let cones = Cones::new(&unit);
    let lets = lets(&unit);
    let fs = functions(&unit);
    for order in [
        (0..fs.len()).collect::<Vec<_>>(),
        (0..fs.len()).rev().collect(),
    ] {
        let mut scoped = Scoped::new(&lets);
        for i in order {
            let (name, ps, body) = fs[i];
            let r = scoped.relation(body, ps, ps, true).expect(name);
            let w = scoped.written(&r);
            let closed = prelude(cones.close(body.clone()));
            for p in super::window(ps.len(), -4, 4) {
                let point = ps.iter().cloned().zip(p.iter().copied()).collect();
                let f = Formula::and(vec![w.defined(), w.body.clone()]);
                let got = decide(&at_point(&f, &point)).expect("decided");
                let want = super::holds(&closed, ps, &p);
                assert_eq!(got, want, "`{name}` at {p:?}: {w}");
            }
        }
    }
}

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
            (
                m,
                (
                    zed_tests::deep::statements(&src),
                    zedc::lex::lex_fence(&src).unwrap(),
                    elab(&src).unwrap(),
                    src,
                ),
            )
        })
        .collect();
    zed_tests::scaling::check("the linear questions of a chain of n calls", n, |m| {
        let (stmts, tokens, unit, src) = &units[&m];
        let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
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
            (
                m,
                (
                    zed_tests::deep::statements(&src),
                    zedc::lex::lex_fence(&src).unwrap(),
                    elab(&src).unwrap(),
                    src,
                ),
            )
        })
        .collect();
    zed_tests::scaling::check(what, n, |m| {
        let (stmts, tokens, unit, src) = &units[&m];
        let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
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
    // rejected below layer L6 ("which is recursion").
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
/// (`Extending::defined`), except that a face may answer where none refuses, and then its
/// answer is the one found point by point (`enumerated`; LOAD-bound-holes); a face refuses
/// where none answers only where the relation decided whole is refused too, and then the
/// answer without faces is the one found point by point. That answer extends a point the
/// parts were given in an earlier question, so it depends on the order of the questions: in
/// `p4(x) = q(x: x) && p3(x: x + 1) && x < 279` of the chain below `x < 29 || x > 43`, it is
/// refused in the unit's order and answered in the reverse; with faces it is refused in both,
/// since the points the faces give the links below extend to no point of `p4`. Each answer is the one the body closed over the definitions it
/// reaches has, decided whole, wherever that is decided: no question decided whole is refused
/// from parts (LOAD-extend-refuses); in the unit's order and in the reverse. A question the
/// solver refuses whole may be answered from parts. Returns how many answers the whole gave.
fn answers_with_faces_are_those_without(src: &str) -> usize {
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Formula, decide};
    let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let cones = Cones::new(&unit);
    let lets = lets(&unit);
    let fs = functions(&unit);
    let whole = |r: &Relation, f: Formula| decide(&Formula::and(vec![r.defined(), f]));
    let mut decided = 0;
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
            for (side, got, without) in
                [("holds", &a.holds, &b.holds), ("fails", &a.fails, &b.fails)]
            {
                match (got, without) {
                    (Ok(g), Err(_)) => {
                        let (holds, fails) = enumerated(&w);
                        let want = if side == "holds" { holds } else { fails };
                        assert_eq!(
                            *g, want,
                            "`{name}` {side} with faces, by points, in\n{src}\n{w}"
                        );
                    }
                    (Err(_), Ok(g)) => {
                        let f = match side == "holds" {
                            true => expected.body.clone(),
                            false => Formula::negate(expected.body.clone()),
                        };
                        assert!(
                            whole(&expected, f).is_err(),
                            "`{name}` {side} refused with faces, answered without and whole, in\n{src}\n{w}"
                        );
                        let (holds, fails) = enumerated(&w);
                        let want = if side == "holds" { holds } else { fails };
                        assert_eq!(
                            *g, want,
                            "`{name}` {side} without faces, by points, in\n{src}\n{w}"
                        );
                    }
                    _ => assert_eq!(
                        got, without,
                        "`{name}` {side} with faces and without in\n{src}\n{w}"
                    ),
                }
            }
            for (got, f) in [
                (&a.holds, expected.body.clone()),
                (&a.fails, Formula::negate(expected.body.clone())),
            ] {
                if let Ok(want) = whole(&expected, f) {
                    assert_eq!(*got, Ok(want), "`{name}` in\n{src}\n{w}");
                    decided += 1;
                }
            }
        }
    }
    decided
}

/// Whether the body of `w` holds somewhere and whether it fails somewhere, found point by point:
/// `w` reads one symbol, bounded below and above by rows of its body's top conjunction, and at
/// each value from the lower bound to one past the upper the definitions fix every division
/// (`satisfiable`), and the body is read at those values (`Formula::holds`). Past the upper
/// bound the body fails, and so does it below the lower; the point one past the upper stands
/// for those.
fn enumerated(w: &Relation) -> (bool, bool) {
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Rel, satisfiable};
    let syms: Vec<Atom> = (w.body.atoms().into_iter())
        .chain(w.defined().atoms())
        .filter(|a| matches!(a, Atom::Sym(_)))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    let [x] = &syms[..] else {
        panic!("{w}: reads {} symbols, not one", syms.len())
    };
    let (mut lo, mut hi) = (None::<i64>, None::<i64>);
    let mut top = vec![&w.body];
    while let Some(p) = top.pop() {
        if let Formula::And(parts) = p {
            top.extend(parts.iter());
            continue;
        }
        let Formula::Con(c) = p else { continue };
        let k = c
            .lin
            .terms
            .get(x)
            .map(|k| i64::try_from(k.to_i128().unwrap()).unwrap());
        let b = i64::try_from(c.lin.constant.to_i128().unwrap()).unwrap();
        match (c.rel, c.lin.terms.len(), k) {
            // `x + b >= 0` and `-x + b >= 0`.
            (Rel::Ge, 1, Some(1)) => lo = Some(lo.map_or(-b, |l| l.max(-b))),
            (Rel::Ge, 1, Some(-1)) => hi = Some(hi.map_or(b, |h| h.min(b))),
            _ => {}
        }
    }
    let (Some(lo), Some(hi)) = (lo, hi) else {
        panic!("{w}: no bounds on {x:?} in the top conjunction")
    };
    let defined = w.defined();
    let (mut holds, mut fails) = (false, false);
    for v in lo..=hi + 1 {
        let fixed = Formula::Con(Con::eq(&Lin::atom(x.clone()), &Lin::constant(v)));
        let m = satisfiable(&Formula::and(vec![defined.clone(), fixed.clone()]))
            .unwrap_or_else(|e| panic!("{w}: definitions refused at {v}: {e:?}"))
            .unwrap_or_else(|| panic!("{w}: no definitions at {v}"));
        assert!(defined.holds(&m) && fixed.holds(&m), "{w}: {m:?} at {v}");
        let b = w.body.holds(&m);
        (holds, fails) = (holds || b, fails || !b);
    }
    (holds, fails)
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
fn each_answer_of_a_disjunctive_chain_is_the_answer_of_the_relation_whole() {
    // LOAD-disj-residue: the face of a callee with a disjunction keeps it as clauses, each said
    // once. Drifting chains whose clauses repeat every few links (residues modulo 5), never
    // repeat (modulo 1009), move a bound (the holes of `x < 10 || x > 20`), or share a
    // remainder between two disjunctions, which keeps it. Each is checked against the answers
    // made with no face, refusals too, and against the whole where the whole is decided, since
    // the solver refuses some of these questions one way and not the other. The chain beside
    // `x mod 4 != 1 && (x mod 6 == 2 || x mod 10 == 3)` is checked the same way by
    // `a_link_decided_whole_is_answered_where_its_relation_is`; deciding its links whole takes
    // 14 to 35 s (load 28 to 37), so it is not checked twice (SPLIT-one-scope).
    for q in [
        "(x mod 3 == 1 || x mod 5 == 2)",
        "(x mod 1009 == 0 || x mod 3 == 1)",
        "(x < 10 || x > 20)",
        "(x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50)",
    ] {
        let q = format!("q(x: int) = {q} && x > 0 && x < 1000000;\n");
        answers_with_faces_are_those_without(&drifting_chain(&q, 30));
    }
}

#[test]
fn each_answer_of_a_random_disjunctive_chain_is_the_answer_of_the_relation_whole() {
    // Random chains of the shape of those above (LOAD-disj-residue), checked the same way.
    let mut rng = zed_tests::instances::Rng::new(0xd15e);
    for _ in 0..80 {
        answers_with_faces_are_those_without(&random_disjunctive_chain(&mut rng));
    }
}

#[test]
fn a_link_decided_whole_is_answered_where_its_relation_is() {
    // LOAD-extend-refuses: asked from the end of the chain, `p2(x) = q(x: x) && p1(x: x + 3)
    // && x < 2000` beside `q(x) = x mod 4 != 1 && (x mod 6 == 2 || x mod 10 == 3) && 0 < x <
    // 1000000` extends neither part's point and is decided whole. Decided over the atoms its
    // calls bind, `x@3 == x@4 + 3` beside both callees' remainders, the solver refused it
    // (Shadows), where it decided the relation written over the input (it holds). Now a
    // question refused so is asked again with each binding put in place of the atom it binds,
    // as the relation is written.
    let q =
        "q(x: int) = x mod 4 != 1 && (x mod 6 == 2 || x mod 10 == 3) && x > 0 && x < 1000000;\n";
    answers_with_faces_are_those_without(&drifting_chain(q, 30));
}

/// A random test of `x` with a negation: a remainder unequal to a constant, the negation of a
/// conjunction of a remainder and a bound, or of a disjunction of two [`random_case`]s.
fn random_negation(rng: &mut zed_tests::instances::Rng) -> String {
    let m = rng.int(2, 11);
    match rng.below(3) {
        0 => format!("x mod {m} != {}", rng.int(0, m - 1)),
        1 => format!(
            "!(x mod {m} == {} && x > {})",
            rng.int(0, m - 1),
            lit(rng.int(-10, 60))
        ),
        _ => format!("!({} || {})", random_case(rng), random_case(rng)),
    }
}

/// A random chain of the drifting chain's shape whose callee holds congruences, negations and
/// disjunctions over moduli up to 11, and whose links move the argument by a random constant
/// and may hold a negation or a disjunction of their own (LOAD-extend-refuses).
fn random_negated_chain(rng: &mut zed_tests::instances::Rng) -> String {
    let a = rng.int(-5, 5);
    let b = a + rng.int(-2, 200);
    let m = rng.int(2, 11);
    let q = format!(
        "{} && (x mod {m} == {} || {})",
        random_negation(rng),
        rng.int(0, m - 1),
        random_case(rng)
    );
    let mut src = format!(
        "q(x: int) = {q} && x > {} && x < {};\np0(x: int) = x > {};\n",
        lit(a),
        lit(b),
        lit(rng.int(-10, 10)),
    );
    for i in 1..rng.int(2, 12) {
        let own = match rng.below(4) {
            0 => format!(" && {}", random_negation(rng)),
            1 => format!(" && ({} || {})", random_case(rng), random_case(rng)),
            _ => String::new(),
        };
        src.push_str(&format!(
            "p{i}(x: int) = q(x: x) && p{}(x: x + {}) && x < {}{own};\n",
            i - 1,
            lit(rng.int(-6, 6)),
            lit(rng.int(-10, 400)),
        ));
    }
    src
}

#[test]
fn no_question_of_a_random_chain_with_negations_is_refused_where_its_relation_is_decided() {
    // LOAD-extend-refuses: random chains with congruences, negations and disjunctions, each
    // answer with faces and without equal, refusals too, and equal to `decide`'s on the
    // relation written whole wherever that is decided, in both orders of the bodies. Before
    // the fix, five of these ten chains had a question refused that the whole decided (the
    // first at its first chain); the ten take about 9 s (dev build, load about 25).
    let mut rng = zed_tests::instances::Rng::new(0x5eed1);
    let mut decided = 0;
    for _ in 0..10 {
        decided += answers_with_faces_are_those_without(&random_negated_chain(&mut rng));
    }
    assert!(decided >= 300, "{decided} answers of the whole");
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

/// Times the separate tests `t{i}(x) = {test}` over one chain `h{i}(x) = {step}`, each `H` of
/// `step` written as `h{i-1}(x: x)` and each `H` of `test` as `h{i}(x: x)`, at `n` and 8n links,
/// held to work of order `n^power` ([`zed_tests::scaling::check_order`]): each test is a
/// question of its own, with no kept part (LOAD-chain-sep-rest).
fn separate_tests_scale(what: &str, n: usize, power: u32, step: &'static str, test: &'static str) {
    separate_tests_over_inputs_scale(what, n, power, &["x"], step, test);
}

/// [`separate_tests_scale`] with the inputs `inputs` at each link, `h0` the first.
fn separate_tests_over_inputs_scale(
    what: &str,
    n: usize,
    power: u32,
    inputs: &[&str],
    step: &'static str,
    test: &'static str,
) {
    let params = (inputs.iter())
        .map(|v| format!("{v}: int"))
        .collect::<Vec<_>>()
        .join(", ");
    let args = (inputs.iter())
        .map(|v| format!("{v}: {v}"))
        .collect::<Vec<_>>()
        .join(", ");
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let mut src = format!("h0({params}) = {};\n", inputs[0]);
            for i in 1..m {
                let h = |k: usize| format!("h{k}({args})");
                src += &format!("h{i}({params}) = {};\n", step.replace('H', &h(i - 1)));
                src += &format!("t{i}({params}) = {};\n", test.replace('H', &h(i)));
            }
            (
                m,
                (
                    zed_tests::deep::statements(&src),
                    zedc::lex::lex_fence(&src).unwrap(),
                    elab(&src).unwrap(),
                    src,
                ),
            )
        })
        .collect();
    zed_tests::scaling::check_order(what, n, power, |m| {
        let (stmts, tokens, unit, src) = &units[&m];
        let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
        assert!(refused.is_empty(), "{refused:?}");
    });
}

// LOAD-chain-sep-rest: each shape below was decided with every definition each test reaches,
// O(n²) over the chain. Seconds at 50 and 100 links before (load about 35): branches 3.35 and
// 20.2, `min` 1.45 and 6.33, `max` 1.34 and 6.55, `abs(H - 5) div 2` 3.06 and 18.0, two
// inputs 18.5 and over 60, two links 0.27 and 0.66, conjunctions 0.61 and 2.21, `(2 * H) div
// 3` 0.45 and 0.82. Now read through the summaries of the definitions; at 50 and 400 links:
// see each test.

#[test]
fn separate_tests_over_a_chain_of_branches_scale() {
    // 0.042 s at 50 links, 0.387 s at 400.
    separate_tests_scale(
        "separate tests over a chain of `if`s",
        25,
        1,
        "if H > 3 { H div 2 } else { H + 1 }",
        "H > 2",
    );
}

#[test]
fn separate_tests_over_a_chain_of_smallest_values_scale() {
    // 0.100 s at 50 links, 1.58 s at 400: the summary's coefficients are `2^i` at link i.
    separate_tests_scale(
        "separate tests over a chain of `min`s",
        25,
        1,
        "min(H div 2, x)",
        "H > 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_scale() {
    // LOAD-max-div-xr: the values of `max(H div 2, x - 9)` over `x` at a link are no union of
    // polyhedra without a remainder of `x` (they hold where `x - 10 <= 2 * (x div 8)`), so no
    // summary was made, and each test was decided with every definition it reaches: n^2.4 to
    // n^2.5 from 10 to 80 links. The quotient `x div 8` is now kept beside the key, read as
    // any value, with the rows read through its division pair (Summaries::summary).
    separate_tests_scale(
        "separate tests over a chain of `max`s",
        25,
        1,
        "max(H div 2, x - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_against_a_quotient_apart_from_it_scale() {
    // Cross-review of LOAD-max-div-xr, round 2 (Claude): the first test numbers `x div 64`
    // before the later links, which then found it outside each link's summary and read every
    // link beside, so that each later test was the whole chain and was refused (`Growth`)
    // from the fourth link on. The quotient is now read beside in the link's place.
    separate_tests_scale(
        "separate tests over a chain of `max`s against a quotient apart from it",
        25,
        1,
        "max(H div 2, x - 9)",
        "H < x div 64 - 1",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_quotients_scale() {
    // LOAD-max-div-xr: `x div 3` beside `H div 2`. Its symbol `x` is kept beside the key where
    // the quotient is, so the next link meets `x div 3` again through the division pair and
    // needs no remainder of it; without that, 5.9 and 153 billion instructions at 10 and 20
    // links, n^4.7.
    separate_tests_scale(
        "separate tests over a chain of `max`s of quotients",
        25,
        1,
        "max(H div 2, x div 3 - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_remainders_scale() {
    // LOAD-max-div-xr: `x mod 3` beside `H div 2`. The variables of `x mod 3` are a function of
    // `x` alone and one fixed set, so one left by a projection stays in the piece as a symbol
    // does, and its definition's variables join the key of a summary that reads them; before,
    // no summary was made: 12.8 and 138 billion instructions at 10 and 20 links, 6 and 16
    // tests refused, n^3.4.
    separate_tests_scale(
        "separate tests over a chain of `max`s of remainders",
        25,
        1,
        "max(H div 2, x mod 3 - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_two_divisions_scale() {
    // LOAD-max-div-xr: `x mod 5 + x div 7` beside `H div 2`. Its projection left a quotient of
    // the chain in rows over both divisions; a piece is now projected again keeping the
    // symbols and the variables of definitions of symbols alone, and the bounds `x >= 2^k *
    // (q3 + q4) - 9 * 2^k` piling up at each link are cut to two ([`envelope`] in
    // presburger::extend). Before: 37.3 and 477 billion instructions at 10 and 20 links, 6 and
    // 16 tests refused, n^3.7. Now the summaries, pieces and rows grow linearly (116 summaries,
    // 746 pieces and 6041 rows at 40 links, 56, 326 and 2641 at 20), and the work by n^1.6 to
    // n^1.9 from 10 to 80 links (13.4, 40.5, 123 and 453 billion instructions; 6.7, 14.4 and 59.2
    // to 40 links since pieces of different rests merge, round 2): the solver's
    // arithmetic on the coefficients `2^i` of link i, in rows of three atoms. Held to n^2, at
    // 4 and 32 links to stay under 60 s; the item for n log n is LOAD-max-div-bits.
    separate_tests_scale(
        "separate tests over a chain of `max`s of two divisions",
        4,
        2,
        "max(H div 2, x mod 5 + x div 7 - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_two_inputs_scale() {
    // LOAD-max-div-xr (cross-review round 2, I8): `x + y - 9` beside `H div 2`. The values
    // `h{i}` takes as `x + y - 9` were cut at each link `k` where the chain took it, by `(2^k -
    // 1) x + 2^k y >= c_k` and the form of link `k - 1`, one piece more at each link: 0.25 to
    // 21.4 billion instructions from 10 to 80 links, n^2.1, 70 times from 10 to 80. Pieces next
    // to each other on one form whose rests hold on each other now merge (`merge_pieces` in
    // presburger::extend): four pieces at each link, 0.25, 0.60, 1.29 and 2.79 billion. The
    // coefficients still grow one bit a link, so the work grows by n^1.3 to n^1.6 from 80 to
    // 320 links (13.2 times from 25 to 200): held at 10 and 80 links; the item for n log n at
    // every size is LOAD-max-div-bits.
    separate_tests_over_inputs_scale(
        "separate tests over a chain of `max`s of two inputs",
        10,
        1,
        &["x", "y"],
        "max(H div 2, x + y - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_less_one_scale() {
    // LOAD-max-div-xr: `x mod 5 + x div 7` beside `H - 1`. The values `h{i}` takes as `x mod 5
    // + x div 7 - 9` are pieces equal but for the interval of `x - (x mod 5) - (x div 7)`,
    // one more at every few links, with gaps between them holding no integer point of the
    // rest (`merge_pieces` in presburger::extend now merges them). Before: 0.67, 2.09, 8.39
    // and 32.6 billion instructions at 10, 20, 40 and 80 links, n^2.0.
    separate_tests_scale(
        "separate tests over a chain of `max`s of a decrement",
        25,
        1,
        "max(H - 1, x mod 5 + x div 7 - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_reading_a_new_symbol_at_each_link_scale() {
    // LOAD-max-div-xr (cross-review round 2, I7): `q{i} = q{i-1} + s{i}`, a test `q{i} >= 0`
    // at each link. The symbols of link i's cone are i + 1; a set copied at each link stores
    // O(n^2) atoms in all (Codex measured 26.7 times the bytes from 320 to 2560 links); a
    // persistent set shares its input's tree, O(log n) at each link.
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared};
    let defs = |m: usize| -> Vec<Formula> {
        let sym = |i: usize| Lin::atom(Atom::Sym(format!("s{i}").into()));
        let aux = |i: usize| Lin::atom(Atom::Aux(i as u32));
        (0..m)
            .map(|i| {
                let rhs = if i == 0 {
                    sym(0)
                } else {
                    aux(i - 1).plus(&sym(i))
                };
                Formula::And(Shared::new(vec![Formula::Con(Con::eq(&aux(i), &rhs))]))
            })
            .collect()
    };
    let inputs = zed_tests::scaling::inputs(200, |m| {
        let asks: Vec<Formula> = (0..m)
            .map(|i| Formula::Con(Con::ge(&Lin::atom(Atom::Aux(i as u32)), &Lin::constant(0))))
            .collect();
        (defs(m), asks)
    });
    zed_tests::scaling::check(
        "separate tests over a chain reading a new symbol at each link",
        200,
        |m| {
            let (defs, asks) = &inputs[&m];
            let mut extending = Extending::new();
            for f in asks {
                let a = extending.defined(f, &|n| defs[n as usize].clone());
                assert_eq!(a.holds, Ok(true));
            }
        },
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_multiples_scale() {
    // LOAD-max-div-xr: `2 * x - 9` beside `H div 2`.
    separate_tests_scale(
        "separate tests over a chain of `max`s of multiples",
        25,
        1,
        "max(H div 2, 2 * x - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_smallest_values_against_the_input_scale() {
    // LOAD-max-div-xr: `min` against a step of the input.
    separate_tests_scale(
        "separate tests over a chain of `min`s against `x - 5`",
        25,
        1,
        "min(H div 2 + 1, x - 5)",
        "H > 3",
    );
}

#[test]
fn separate_tests_over_a_chain_of_absolute_values_scale() {
    // 0.051 s at 50 links, 0.468 s at 400.
    separate_tests_scale(
        "separate tests over a chain of `abs`s",
        25,
        1,
        "abs(H - 5) div 2",
        "H > 1",
    );
}

#[test]
fn separate_tests_over_a_chain_of_two_inputs_scale() {
    // 0.100 s at 50 links, 0.972 s at 400.
    separate_tests_scale(
        "separate tests over a chain reading two quotients of one link",
        25,
        1,
        "min(H div 2, H div 3 + 1)",
        "H > 1",
    );
}

#[test]
fn separate_tests_over_two_links_of_one_chain_scale() {
    // 0.053 s at 50 links, 0.232 s at 400.
    separate_tests_scale(
        "separate tests over two links of one chain",
        25,
        1,
        "H div 2 + 1",
        "H > h1(x: x)",
    );
}

#[test]
fn separate_conjunctions_over_the_links_of_one_chain_scale() {
    // 0.027 s at 50 links, 0.375 s at 400.
    separate_tests_scale(
        "separate conjunctions over one chain of halvings",
        25,
        1,
        "H div 2 + 1",
        "H > 0 && x < 1000",
    );
}

#[test]
fn separate_tests_over_a_chain_of_divisions_by_a_parameter_scale() {
    // LOAD-chain-sep-nonlinear: the product `x * q` of a quotient by `x` is read as an atom of
    // its own, as the solver reads it, so each definition has a summary. Before, no summary was
    // made and each test was decided with every definition it reaches: 0.58 s at 50 links, 55 s
    // at 400; 74.5 times the instructions from 10 to 80 links, and 112 times the bytes from 25
    // to 200. Now 77.0 and 641 million instructions at 25 and 200 links, 8.3 times.
    separate_tests_scale(
        "separate tests over a chain of divisions by a parameter",
        25,
        1,
        "H div x",
        "H > 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_products_scale() {
    // LOAD-chain-sep-nonlinear: the translation of each body fails at the product
    // `h{i-1}(x: x) * x`, and the failed translations of the chain below it are kept for the
    // next body (`Tx::forget`), so a body reads only its own link. Before, each body read the
    // chain below it again: 0.072 s at 50 links, 3.46 s at 400; 41.8 times the instructions
    // from 10 to 80 links, and 52 times the bytes from 25 to 200. Now 17.2 and 137 million
    // instructions at 25 and 200 links, 8.0 times.
    separate_tests_scale(
        "separate tests over a chain of products",
        25,
        1,
        "H * x + 1",
        "H > 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_nonunit_steps_scale() {
    // 0.032 s at 50 links, 0.127 s at 400: the remainder, read by no other link, is projected
    // out with the input, so `2 * H == 3 * q + r` leaves no congruence.
    separate_tests_scale(
        "separate tests over a chain of `(2 * H) div 3`",
        25,
        1,
        "(2 * H) div 3",
        "H > 0",
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
    // A chain over the inputs `x` and `y`.
    let two = |src: String| {
        src.replace("(x: int)", "(x: int, y: int)")
            .replace("(x: x)", "(x: x, y: y)")
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
        // Links of several cases (LOAD-chain-sep-rest): a summary of one piece for each case
        // and each piece below, those with no point dropped. A branch, one on a value it
        // excludes, one that clamps at zero, a smallest and a largest value against the
        // input or a constant, and absolute values.
        chain("if H > 3 { H div 2 } else { H + 1 }", "H > 2", 5),
        chain("if H > 3 { H div 2 } else { H + 1 }", "H == 3", 5),
        chain("if H != 3 { H div 2 } else { H }", "H > 0", 5),
        chain("if H > 0 { H - 1 } else { 0 }", "H > 0", 5),
        chain("if H > 0 { H - 1 } else { 0 }", "H < 0", 5),
        chain("min(H div 2, x)", "H > 0", 5),
        chain("min(H div 2, x)", "H == x", 5),
        chain("max(H div 2, x - 9)", "H < 0", 5),
        // LOAD-max-div-xr: the input, and quotients of it, kept beside the key.
        chain("max(H div 2, x - 9)", "H == x - 9 && x > 10", 6),
        chain("max(H div 2, x - 9)", "H > x div 2", 6),
        chain("max(H div 2, x div 3 - 9)", "H < 0", 5),
        chain("max(H div 2, x div 3 - 9)", "H == 2 && x > 30", 5),
        chain("max(H div 2, 2 * x - 9)", "H == 0", 5),
        chain("min(H div 2 + 1, x - 5)", "H > 3", 5),
        chain("min(H div 4, 3 * x + 7)", "H == 1", 5),
        chain("max(H div 3, x - 9)", "H < x - 9", 5),
        // A quotient of the input apart from the chain, which the first test numbers before
        // the later links (cross-review round 2, Claude): each test reads the chain through
        // its summary in every order, where before the later tests read every link beside and
        // were refused in the unit's order alone.
        chain("max(H div 2, x - 9)", "H < x div 64 - 1", 6),
        chain("max(H div 2, x mod 5 + x div 7 - 9)", "H < x div 64 - 1", 5),
        // Two inputs (cross-review round 2, I8): pieces whose rests differ, merged where
        // each rest holds on the other piece; a value of `x + y - 9` at the last link, one
        // between, and values at a bound of the merged pieces.
        two(chain("max(H div 2, x + y - 9)", "H < 0", 6)),
        two(chain(
            "max(H div 2, x + y - 9)",
            "H == x + y - 9 && x > 20 - y",
            6,
        )),
        two(chain(
            "max(H div 2, x + y - 9)",
            "2 * H > x + y - 9 && H > x + y - 9",
            6,
        )),
        two(chain("max(H div 2, x + y - 9)", "H == 3 && x + y < 13", 6)),
        two(chain("min(H div 2 + 1, x - y)", "H > 3 && x < y + 4", 5)),
        chain("min(H, 100) + 1", "H > 100", 5),
        chain("max(H - 2, 0)", "H > 0 && x < 9", 5),
        chain("abs(H div 2 - 3)", "H > 1", 5),
        chain("abs(H) div 2 + 1", "H > 2", 5),
        chain("abs(H - 5) div 2", "H == 0", 5),
        // Two inputs: two quotients of one link, read beside it down to the link, and a test
        // over a link and one below it on its path.
        chain("min(H div 2, H div 3 + 1)", "H > 1", 5),
        chain("H div 2 - H div 3", "H == 1", 5),
        chain("H div 2", "H > h1(x: x)", 6),
        chain("abs(H - 1)", "H + h2(x: x) == 4", 5),
        // Steps whose remainder no other link reads, projected out with the input.
        chain("(2 * H) div 3", "H > 0", 5),
        chain("(2 * H + 1) div 3", "H == 2", 5),
        // A division by a variable and a product (LOAD-chain-sep-nonlinear): the product is
        // an atom of its own in the summaries, as the solver reads it. Zero, negative and
        // large values, the input at zero and at -1 and 1, a value that holds nowhere, a test
        // over two links, and a product of inputs that every link and a test read.
        chain("H div x", "H > 0", 4),
        chain("H div x", "H == 0", 4),
        chain("H div x", "H < 0", 4),
        chain("H div x", "H > 1000", 4),
        chain("H div x", "H > 0 && x == 1", 4),
        chain("H div x", "H > 0 && x == 0 - 1", 4),
        chain("H div x", "H != 0 && x == 0", 4),
        chain("H div x + 1", "H < 1 && x > 0 && x < 3", 4),
        chain("H div x", "H > h1(x: x)", 5),
        chain("H * x + 1", "H > 0", 4),
        chain("H * x + 1", "H == 1", 4),
        chain("H * x + 1", "H < 0", 4),
        chain("H * x + 1", "H > 1000000", 4),
        chain("H * x + 1", "H != 1 && x == 0", 4),
        chain("x * x - H", "H < 0", 5),
        chain("x * x + H", "H == 3", 5),
        chain("H + x * x", "H < x * x", 5),
        // Conjunctions with no kept part, decided with the summaries, and tests extending
        // them, whose points are found then (`Extending::fill`).
        chain("H div 2 + 1", "H > 0 && x < 1000", 5),
        concat!(
            "h0(x: int) = x;\n",
            "h1(x: int) = h0(x: x) div 2 + 1;\n",
            "t1(x: int) = h1(x: x) > 0 && x < 1000;\n",
            "h2(x: int) = if h1(x: x) > 3 { h1(x: x) div 2 } else { h1(x: x) + 1 };\n",
            "t2(x: int) = h2(x: x) > 1 && x < 900;\n",
            "u2(x: int) = t2(x: x) && x > 5;\n",
            "v2(x: int) = t2(x: x) && h2(x: x) < 0;\n",
            "w2(x: int) = u2(x: x) && t1(x: x + 1);\n",
        )
        .to_string(),
        // A fork (cross-review of LOAD-max-div-xr, round 2): `c` reads `x` through `a` and
        // `y` through `b`, so the symbols of its cone are both; with `y` left out, the summary
        // of `c` says `t` can hold, where the whole has no point.
        concat!(
            "a(x: int) = abs(x);\n",
            "b(y: int) = abs(y);\n",
            "c(x: int, y: int) = max(a(x: x), b(y: y));\n",
            "t(x: int, y: int) = c(x: x, y: y) < y;\n",
            "u(x: int) = a(x: x) == 0;\n",
            "v(y: int) = b(y: y) == 0;\n",
        )
        .to_string(),
        // Cross-review round 2 (Gemini): a sum of four tests of quotients of two inputs, whose
        // last two (`v0 >= 1`, `v0 <= 0`) add to 1, so `t` holds nowhere. Reading the rows of
        // `v0 == (u0 + 2) div 3` through `u0`'s pair loosened them to `y <= 3 * v0 <= y + 5`,
        // and reading `v0 <= 0 && v0 >= 1` through that as a pair made `t` hold ([`by_pairs`]).
        concat!(
            "v0(x: int, y: int) = (x div 1) div 1;\n",
            "u0(x: int, y: int) = (3 * v0(x: x, y: y) + y + 1) div 2;\n",
            "h(x: int, y: int) = ((if u0(x: x, y: y) - 3 * v0(x: x, y: y) + 2 >= 0 { 1 } else { 0 }) + (if 3 * v0(x: x, y: y) - u0(x: x, y: y) >= 0 { 1 } else { 0 }) + (if v0(x: x, y: y) >= 1 { 1 } else { 0 }) + (if v0(x: x, y: y) <= 0 { 1 } else { 0 })) div 1;\n",
            "t(x: int, y: int) = h(x: x, y: y) >= 4;\n",
        )
        .to_string(),
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

#[test]
fn summaries_of_max_min_div_chains_give_the_values_of_the_chains() {
    // LOAD-max-div-xr: chains of `max`, `min` and `div` whose summaries keep the input, and the
    // quotients the next link needs, beside the key. Each test fixes `x` and asks whether
    // `h{i}` has the value computed here by integer arithmetic (`div` by a positive constant
    // rounds down), or another: the first must hold and the second not. Negative, zero and
    // large `x`, and `x` on either side of where `x - 9` and `x div 2^i` cross. Then, with `x`
    // free, the values each `h{i}` takes, found by trying every `x` in a range.
    use zedc::store::presburger::extend::Extending;
    // A link, `H` its input, and its value from `H` and `x`.
    type Step = (&'static str, fn(i64, i64) -> i64);
    let steps: [Step; 17] = [
        ("max(H div 2, x - 9)", |h, x| h.div_euclid(2).max(x - 9)),
        ("min(H div 2, x + 9)", |h, x| h.div_euclid(2).min(x + 9)),
        ("max(H div 3, x - 9)", |h, x| h.div_euclid(3).max(x - 9)),
        ("max(H div 2, 2 * x - 9)", |h, x| {
            h.div_euclid(2).max(2 * x - 9)
        }),
        ("min(H div 2 + 1, x - 5)", |h, x| {
            (h.div_euclid(2) + 1).min(x - 5)
        }),
        ("max(H div 2, x div 3 - 9)", |h, x| {
            h.div_euclid(2).max(x.div_euclid(3) - 9)
        }),
        ("max(H div 2, x div 3 - 1000)", |h, x| {
            h.div_euclid(2).max(x.div_euclid(3) - 1000)
        }),
        ("max(H div 2, 9 - x)", |h, x| h.div_euclid(2).max(9 - x)),
        ("min(H div 4, 3 * x + 7)", |h, x| {
            h.div_euclid(4).min(3 * x + 7)
        }),
        ("max(H div 2, x) - 1", |h, x| h.div_euclid(2).max(x) - 1),
        ("max(H div 2 - 1, x)", |h, x| (h.div_euclid(2) - 1).max(x)),
        ("max(H div 2, x mod 3 - 9)", |h, x| {
            h.div_euclid(2).max(x.rem_euclid(3) - 9)
        }),
        ("min(H div 2, x mod 4 + 3)", |h, x| {
            h.div_euclid(2).min(x.rem_euclid(4) + 3)
        }),
        ("max(H div 2, x mod 5 + x div 7 - 9)", |h, x| {
            h.div_euclid(2).max(x.rem_euclid(5) + x.div_euclid(7) - 9)
        }),
        ("max(H div 2, x div 5 + x div 7 - 9)", |h, x| {
            h.div_euclid(2).max(x.div_euclid(5) + x.div_euclid(7) - 9)
        }),
        ("max(H - 1, x mod 5 + x div 7 - 9)", |h, x| {
            (h - 1).max(x.rem_euclid(5) + x.div_euclid(7) - 9)
        }),
        ("max(H - 4, x mod 5 + x div 7 - 9)", |h, x| {
            (h - 4).max(x.rem_euclid(5) + x.div_euclid(7) - 9)
        }),
    ];
    let xs: [i64; 10] = [-1_000_000, -19, -1, 0, 1, 9, 10, 18, 19, 1_000_000];
    let lit = |v: i64| {
        if v < 0 {
            format!("0 - {}", -v)
        } else {
            v.to_string()
        }
    };
    for (step, value) in steps {
        let mut src = "h0(x: int) = x;\n".to_string();
        for i in 1..=5 {
            src += &format!(
                "h{i}(x: int) = {};\n",
                step.replace("H", &format!("h{}(x: x)", i - 1))
            );
        }
        let mut want = std::collections::BTreeMap::new();
        for (k, &c) in xs.iter().enumerate() {
            let mut h = c;
            for i in 1..=5 {
                h = value(h, c);
                let at = format!("x == {} && h{i}(x: x)", lit(c));
                src += &format!("e{i}k{k}(x: int) = {at} == {};\n", lit(h));
                src += &format!("n{i}k{k}(x: int) = {at} != {};\n", lit(h));
                want.insert(format!("e{i}k{k}"), true);
                want.insert(format!("n{i}k{k}"), false);
            }
        }
        // Questions with `x` free, whose keys hold `h{i}`'s variable alone: does `h{i}` take
        // the value `c`, or one below it, for some `x`? Found by trying every `x` with
        // |x| <= 200000: past that, each link here is beyond -40..=40 or repeats a value it
        // takes inside (a remainder repeats with `x`).
        let cs: [i64; 12] = [-40, -12, -10, -9, -8, -7, -1, 0, 1, 5, 10, 40];
        let mut takes = vec![std::collections::BTreeSet::new(); 6];
        for x in -200_000..=200_000 {
            let mut h = x;
            for set in &mut takes[1..] {
                h = value(h, x);
                set.insert(h);
            }
        }
        for (i, set) in takes.iter().enumerate().skip(1) {
            for (j, &c) in cs.iter().enumerate() {
                let h = format!("h{i}(x: x)");
                src += &format!("v{i}c{j}(x: int) = {h} == {};\n", lit(c));
                src += &format!("l{i}c{j}(x: int) = {h} < {};\n", lit(c));
                want.insert(format!("v{i}c{j}"), set.contains(&c));
                want.insert(format!("l{i}c{j}"), set.range(..c).next().is_some());
            }
        }
        let unit = elab(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let lets = lets(&unit);
        let mut scoped = Scoped::new(&lets);
        let mut extending = Extending::new();
        let mut asked = 0;
        for (name, ps, body) in functions(&unit) {
            let Some(&holds) = want.get(name) else {
                continue;
            };
            let r = (scoped.relation(body, ps, ps, true)).unwrap_or_else(|| panic!("{name}"));
            let a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            assert_eq!(a.holds, Ok(holds), "`{name}` in\n{src}");
            asked += 1;
        }
        assert_eq!(asked, want.len(), "{step}");
    }
}

#[test]
fn summaries_of_max_min_div_chains_of_two_inputs_give_the_values_of_the_chains() {
    // LOAD-max-div-xr (cross-review round 2, I8): chains over `x` and `y`, whose summaries
    // merge pieces with different rests (`merge_pieces` in presburger::extend). Each test fixes
    // `x` and `y` and asks whether `h{i}` has the value computed here, or another: the first
    // must hold and the second not. Pairs on either side of where `x + y - 9` and `x div 2^i`
    // cross, negative, zero and large.
    use zedc::store::presburger::extend::Extending;
    type Step = (&'static str, fn(i64, i64, i64) -> i64);
    let steps: [Step; 4] = [
        ("max(H div 2, x + y - 9)", |h, x, y| {
            h.div_euclid(2).max(x + y - 9)
        }),
        ("min(H div 2 + 1, x - y)", |h, x, y| {
            (h.div_euclid(2) + 1).min(x - y)
        }),
        ("max(H div 2, 2 * x - y)", |h, x, y| {
            h.div_euclid(2).max(2 * x - y)
        }),
        ("max(H - 1, x + y div 3)", |h, x, y| {
            (h - 1).max(x + y.div_euclid(3))
        }),
    ];
    let pairs: [(i64, i64); 9] = [
        (-1_000_000, 3),
        (-5, -7),
        (0, 0),
        (1, 8),
        (16, -6),
        (40, -29),
        (64, 0),
        (100, -95),
        (1_000_000, -999_990),
    ];
    let lit = |v: i64| {
        if v < 0 {
            format!("0 - {}", -v)
        } else {
            v.to_string()
        }
    };
    for (step, value) in steps {
        let mut src = "h0(x: int, y: int) = x;\n".to_string();
        for i in 1..=6 {
            src += &format!(
                "h{i}(x: int, y: int) = {};\n",
                step.replace("H", &format!("h{}(x: x, y: y)", i - 1))
            );
        }
        let mut want = std::collections::BTreeMap::new();
        for (k, &(x, y)) in pairs.iter().enumerate() {
            let mut h = x;
            for i in 1..=6 {
                h = value(h, x, y);
                let at = format!("x == {} && y == {} && h{i}(x: x, y: y)", lit(x), lit(y));
                src += &format!("e{i}k{k}(x: int, y: int) = {at} == {};\n", lit(h));
                src += &format!("n{i}k{k}(x: int, y: int) = {at} != {};\n", lit(h));
                want.insert(format!("e{i}k{k}"), true);
                want.insert(format!("n{i}k{k}"), false);
            }
        }
        let unit = elab(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let lets = lets(&unit);
        let mut scoped = Scoped::new(&lets);
        let mut extending = Extending::new();
        let mut asked = 0;
        for (name, ps, body) in functions(&unit) {
            let Some(&holds) = want.get(name) else {
                continue;
            };
            let r = (scoped.relation(body, ps, ps, true)).unwrap_or_else(|| panic!("{name}"));
            let a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            assert_eq!(a.holds, Ok(holds), "`{name}` in\n{src}");
            asked += 1;
        }
        assert_eq!(asked, want.len(), "{step}");
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
fn the_relations_of_a_chain_dividing_by_its_argument_scale() {
    // `q`, whose condition holds four divisors, called by every link with another argument
    // list, and each link called by the next with a moved one: the condition of a call that
    // holds no claim is its callee's, written at its arguments ([`Walk::defined_called`] in
    // preimage.rs).
    relations_scale(
        "the relations of a chain dividing by its argument",
        50,
        "q(x: int, n: int) = x mod n + x mod (n + 1) + x div (n + 2) + x div (n + 3) >= 0;\n\
         p0(x: int, n: int) = x mod n >= 0;\n",
        |i| {
            format!(
                "p{i}(x: int, n: int) = q(x: x, n: n + {i}) && p{}(x: x + 1, n: n) && x < {};\n",
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
            (
                m,
                (
                    zed_tests::deep::statements(&src),
                    zedc::lex::lex_fence(&src).unwrap(),
                    elab(&src).unwrap(),
                    src,
                ),
            )
        })
        .collect();
    zed_tests::scaling::check(
        "the linear questions of a chain with a second call of a large callee",
        n,
        |m| {
            let (stmts, tokens, unit, src) = &units[&m];
            let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
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
            (
                m,
                (
                    zed_tests::deep::statements(&src),
                    zedc::lex::lex_fence(&src).unwrap(),
                    elab(&src).unwrap(),
                    src,
                ),
            )
        })
        .collect();
    zed_tests::scaling::check(what, n, |m| {
        let (stmts, tokens, unit, src) = &units[&m];
        let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
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

/// A link of the drifting chain that moves its argument down by 30 (LOAD-bound-holes).
fn falling_link(i: usize) -> String {
    format!(
        "p{i}(x: int) = q(x: x) && p{}(x: x - 30) && x < {};\n",
        i - 1,
        1000 * i
    )
}

/// A link of the drifting chain that moves its argument up by 12, twice the modulus of the
/// callee's remainders (LOAD-bound-holes).
fn rising_link(i: usize) -> String {
    format!(
        "p{i}(x: int) = q(x: x) && p{}(x: x + 12) && x < {};\n",
        i - 1,
        1000 * i
    )
}

#[test]
fn the_questions_of_a_chain_moving_a_hole_scale() {
    // LOAD-bound-holes: the drifting chain beside `q(x) = (x < 10 || x > 20) && 0 < x <
    // 1000000`. Each link moves the hole `10..=20` by 3 and keeps it, so the face of the
    // chain at link i says `x` lies outside the union of i holes. Before, a face held one
    // clause a link and each link was decided whole: 0.39, 1.62, 7.06 s at 40, 80, 160 links
    // (debug, measured once). Now the holes are one ordered map of disjoint intervals, read
    // through each call's binding and merged in O(log n): 0.032, 0.098, 0.198 s.
    questions_scale(
        "a chain whose links move a hole of their callee",
        40,
        "q(x: int) = (x < 10 || x > 20) && x > 0 && x < 1000000;\np0(x: int) = x > 0;\n",
        drifting_link,
    );
    // The same moved down by 30, so that the holes do not overlap: 0.011, 0.021, 0.038 s.
    questions_scale(
        "a chain whose links move a hole of their callee apart",
        40,
        "q(x: int) = (x < 10 || x > 20) && x > 0 && x < 1000000;\np0(x: int) = x > 0;\n",
        falling_link,
    );
}

#[test]
fn the_questions_of_a_chain_moving_bounds_beside_a_shared_remainder_scale() {
    // LOAD-bound-holes: `q(x) = (x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50)`, whose
    // two disjunctions share the remainder of `x` by 6, in a chain moving `x` by 12. Each link
    // kept its own bound atom, quotient and remainder, and a clause each, so a link read the
    // chain: 3.06 s at 40 links, 25.4 s at 80 (debug, measured once). Now the bindings are
    // followed to the caller's atom, the divisions of one term by 6 read one remainder, and
    // the clauses `r == 5 || x <= b` keep the tightest `b`: 0.111, 0.369 s at 40, 80 links,
    // about 2.4 ms a link. Sized 8 and 64: without these three steps the cost of a link grows
    // until about link 60 and then stays, so 40 and 320 passed the limit, where 8 and 64 fail
    // it (243 times the bytes; 189, 181 and 64 times without each step alone). Link 76, the
    // first with no point, was decided whole, about 0.15 s at any length; LOAD-holes-mod
    // decides its face empty (3.5 ms), and the sizes past it are timed in
    // `the_questions_of_a_chain_of_holes_beside_one_modulus_scale`.
    questions_scale(
        "a chain whose links move bounds beside a shared remainder",
        8,
        "q(x: int) = (x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50) && x > 0 \
         && x < 1000000;\np0(x: int) = x > 0;\n",
        rising_link,
    );
}

/// A random chain of the drifting chain's shape whose callee holds a hole, and may hold two
/// disjunctions that share a remainder or one of [`random_case`]s, and whose links move the
/// argument by up to 15 either way and may hold a hole or a disjunction over the callee's
/// remainder of their own (LOAD-bound-holes): holes that overlap, touch or lie apart, rays
/// that share a remainder, and links that hold or fail.
fn random_hole_chain(rng: &mut zed_tests::instances::Rng) -> String {
    let hole = |rng: &mut zed_tests::instances::Rng| {
        let lo = rng.int(-5, 30);
        format!("(x < {} || x > {})", lit(lo), lit(lo + rng.int(-1, 15)))
    };
    let m = rng.int(2, 7);
    let mut q = hole(rng);
    match rng.below(3) {
        0 => q.push_str(&format!(
            " && (x mod {m} == {} || x > {}) && (x mod {m} == {} || x < {})",
            rng.int(0, m - 1),
            lit(rng.int(-10, 120)),
            rng.int(0, m - 1),
            lit(rng.int(-10, 120)),
        )),
        1 => q.push_str(&format!(
            " && ({} || {})",
            random_case(rng),
            random_case(rng)
        )),
        _ => {}
    }
    let a = rng.int(-5, 5);
    let mut src = format!(
        "q(x: int) = {q} && x > {} && x < {};\np0(x: int) = x > {};\n",
        lit(a),
        lit(a + rng.int(-2, 200)),
        lit(rng.int(-10, 10)),
    );
    for i in 1..rng.int(2, 13) {
        let own = match rng.below(4) {
            0 => format!(" && {}", hole(rng)),
            1 => format!(
                " && (x mod {m} == {} || x > {})",
                rng.int(0, m - 1),
                lit(rng.int(-10, 120))
            ),
            _ => String::new(),
        };
        src.push_str(&format!(
            "p{i}(x: int) = q(x: x) && p{}(x: x + {}) && x < {}{own};\n",
            i - 1,
            lit(rng.int(-15, 15)),
            lit(rng.int(-10, 400)),
        ));
    }
    src
}

#[test]
fn each_answer_of_a_random_chain_moving_holes_is_the_answer_of_the_relation_whole() {
    // LOAD-bound-holes: random chains mixing moved holes, bounds beside a shared remainder and
    // other disjunctions, each answer with faces (holes, merged bounds, one remainder for each
    // divided term) the same as without, refusals too, but where only the faces answer, and
    // then the answer found point by point; and the same as `decide`'s on the relation written
    // whole wherever that is decided, in both orders of the bodies. The 40 chains give 1510
    // answers of the whole (measured); the 16th takes most of the time, and its `p9` holds
    // where only the faces find the point (`Faces::free`).
    let mut rng = zed_tests::instances::Rng::new(0x401e5);
    let mut decided = 0;
    for _ in 0..40 {
        decided += answers_with_faces_are_those_without(&random_hole_chain(&mut rng));
    }
    assert!(decided >= 1200, "{decided} answers of the whole");
}

/// A chain of `n - 1` links over `q`: `p0(x) = {p0}`, and `p{i}(x) = q(x: x) && p{i-1}(x: x +
/// shift) && x < bound(i)` (LOAD-holes-mod).
fn moved_chain(q: &str, p0: &str, shift: i64, n: usize, bound: impl Fn(usize) -> i64) -> String {
    let mut src = format!("q(x: int) = {q};\np0(x: int) = {p0};\n");
    for i in 1..n {
        src.push_str(&format!(
            "p{i}(x: int) = q(x: x) && p{}(x: x + {shift}) && x < {};\n",
            i - 1,
            bound(i)
        ));
    }
    src
}

#[test]
fn each_answer_of_a_chain_of_holes_beside_one_modulus_is_the_answer_of_the_relation_whole() {
    // LOAD-holes-mod: the faces of these chains hold holes and the residues of one modulus;
    // where no interval between the holes meets a residue left the face is empty, answered
    // without the solver. Each answer is the one found without faces, refusals too, but where
    // only the faces answer, and then the one found point by point; and the one `decide` gives
    // the relation written whole wherever that is decided. Short chains with small bounds, as
    // without faces each link is decided whole and refused (Shadows).
    let small = |i: usize| 60 + 5 * i as i64;
    let cases = [
        // The chain of the task: no point from link 4 on.
        moved_chain(
            "(x < 10 || x > 20) && x mod 4 != 1 && x > 0 && x < 1000",
            "x > 0",
            3,
            8,
            small,
        ),
        // The same with the gap 10..=12 and links moving by 4, the modulus: the residues left
        // stay those of `q`, and the face empties only where the holes cover the range.
        moved_chain(
            "(x < 10 || x > 12) && x mod 4 != 1 && x < 1000000",
            "x > 13",
            4,
            8,
            |i| 4 * i as i64 + 10,
        ),
        // An empty face: the bounds lie inside the hole.
        moved_chain(
            "(x < 10 || x > 20) && x mod 4 == 1 && x > 11 && x < 19",
            "x > 0",
            3,
            6,
            small,
        ),
        // A full face: every residue kept.
        moved_chain(
            "(x < 10 || x > 20) && (x mod 2 == 0 || x mod 2 == 1) && x > 0 && x < 1000",
            "x > 0",
            3,
            6,
            small,
        ),
        // Modulus 1.
        moved_chain(
            "(x < 10 || x > 20) && x mod 1 == 0 && x > 0 && x < 1000",
            "x > 0",
            3,
            6,
            small,
        ),
        // Holes at the ends of the range.
        moved_chain(
            "(x < 3 || x > 25) && x mod 5 == 3 && x > 0 && x < 30",
            "x > 0",
            2,
            8,
            small,
        ),
        // Two moduli, empty only together between the holes: left to the solver.
        moved_chain(
            "(x < 10 || x > 20) && x mod 2 == 1 && x mod 3 == 1 && x > 0 && x < 1000",
            "x > 0",
            3,
            6,
            small,
        ),
    ];
    for src in &cases {
        let decided = answers_with_faces_are_those_without(src);
        assert!(decided > 0, "no answer of the whole in\n{src}");
    }
}

/// The chain of the task: `(x < 10 || x > 20) && x mod 4 != 1` moved by 3, `x < 1000 i`.
fn mod4_chain(n: usize) -> String {
    moved_chain(
        "(x < 10 || x > 20) && x mod 4 != 1 && x > 0 && x < 1000000",
        "x > 0",
        3,
        n,
        |i| 1000 * i as i64,
    )
}

/// The gap 10..=12 beside `x mod 4 != 1`, moved by 4 under `x < 4 i + 10`.
fn gapped_chain(n: usize) -> String {
    moved_chain(
        "(x < 10 || x > 12) && x mod 4 != 1 && x < 1000000",
        "x > 13",
        4,
        n,
        |i| 4 * i as i64 + 10,
    )
}

/// The chain of the shared remainder by 6 moved by 12, past link 76.
fn shared_remainder_chain(n: usize) -> String {
    let mut src = String::from(
        "q(x: int) = (x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50) && x > 0 \
         && x < 1000000;\np0(x: int) = x > 0;\n",
    );
    for i in 1..n {
        src.push_str(&rising_link(i));
    }
    src
}

#[test]
fn the_questions_of_a_chain_of_holes_beside_one_modulus_scale() {
    // LOAD-holes-mod. The chain of the task has no point from link 4 on; each link was decided
    // whole and refused (Shadows): 8.73 s at 12 links, 29.2 s at 16 (debug, measured once).
    // Now its face is read empty from its holes and the residues left by 4: 0.044 s at 12
    // links, 0.75 s at 320.
    questions_scale_unit("a chain of holes beside one modulus", 40, mod4_chain);
    // The gapped chain keeps a point until its holes cover the range: 17.6 s at 23 links
    // before, 0.071 s now, 1.68 s at 320.
    questions_scale_unit("a chain of a gap beside one modulus", 40, gapped_chain);
    // Link 76 of the shared-remainder chain is the first with no point: before, it was
    // decided whole, 0.13 s; now its face is decided empty by the solver, 3.5 ms.
    questions_scale_unit(
        "a chain moving bounds beside a shared remainder past link 76",
        40,
        shared_remainder_chain,
    );
}

/// A chain of remainders with no callee but the link below (LOAD-mod-chain): `p0(x) = x > 0`,
/// and `p{i}(x) = {test} && p{i-1}(x: x + shift) && x < 1000 i` for `i` in 1..n.
fn remainder_chain(test: &str, shift: i64, n: usize) -> String {
    let mut src = String::from("p0(x: int) = x > 0;\n");
    for i in 1..n {
        src.push_str(&format!(
            "p{i}(x: int) = {test} && p{}(x: x + {shift}) && x < {};\n",
            i - 1,
            1000 * i
        ));
    }
    src
}

/// The chain of the task: from link 3 on, no `x` has `x`, `x + 1` and `x + 2` below 2 by 3.
fn mod3_chain(n: usize) -> String {
    remainder_chain("(x mod 3) < 2", 1, n)
}

/// Below 4 by 5, moved by 1: no point from link 5 on.
fn mod5_chain(n: usize) -> String {
    remainder_chain("x mod 5 < 4", 1, n)
}

/// Not 3 by 7, moved by 2: `x + 2 k` meets every residue by 7, so no point from link 7 on.
fn mod7_chain(n: usize) -> String {
    remainder_chain("!(x mod 7 == 3)", 2, n)
}

/// Below 2 by 3, moved by 3, the modulus: every link keeps the residues 0 and 1.
fn kept_residue_chain(n: usize) -> String {
    remainder_chain("x mod 3 < 2", 3, n)
}

/// A random test of `x`'s remainder by `m`.
fn random_remainder_test(rng: &mut zed_tests::instances::Rng, m: i64) -> String {
    let r = rng.int(0, m - 1);
    match rng.below(5) {
        0 => format!("x mod {m} < {}", rng.int(1, m)),
        1 => format!("x mod {m} != {r}"),
        2 => format!("x mod {m} == {r}"),
        3 => format!("!(x mod {m} > {r})"),
        _ => format!("x mod {m} >= {r}"),
    }
}

/// A random chain of remainders: `p0` an interval, and links that test `x`'s remainder by one
/// modulus, and now and then by a second, move the argument by up to the modulus and 2 either
/// way, and bound `x` above and below, so that each answer can be found point by point. Most
/// links share one test and one move, as a chain whose links hold nowhere from some link on.
fn random_remainder_chain(rng: &mut zed_tests::instances::Rng) -> String {
    let m = rng.int(2, 7);
    let lo = rng.int(-10, 10);
    let mut src = format!(
        "p0(x: int) = x > {} && x < {};\n",
        lit(lo),
        lit(lo + rng.int(-2, 60))
    );
    let (base, shift) = (random_remainder_test(rng, m), rng.int(-m - 2, m + 2));
    for i in 1..rng.int(2, 13) {
        let mut test = match rng.below(4) {
            0 => random_remainder_test(rng, m),
            _ => base.clone(),
        };
        let shift = match rng.below(4) {
            0 => rng.int(-m - 2, m + 2),
            _ => shift,
        };
        if rng.below(4) == 0 {
            let other = rng.int(2, 7);
            test = format!("{test} && {}", random_remainder_test(rng, other));
        }
        let lo = rng.int(-20, 10);
        src.push_str(&format!(
            "p{i}(x: int) = {test} && p{}(x: x + {}) && x > {} && x < {};\n",
            i - 1,
            lit(shift),
            lit(lo),
            lit(lo + rng.int(-2, 80)),
        ));
    }
    src
}

#[test]
fn each_answer_of_a_chain_of_remainders_is_the_answer_of_the_relation_whole() {
    // LOAD-mod-chain: a link's face keeps the residues of the link below as rows over one
    // quotient, each one-sided; read together they leave the residues, and the face of the
    // first link with no point is read empty without the solver. Each answer is the one found
    // without faces, refusals too, but where only the faces answer, and then the one found
    // point by point; and the one `decide` gives the relation written whole wherever that is
    // decided; in both orders of the bodies. The chains of the scaling test, bounded below so
    // that the points can be counted, and random chains. Only the faces answer 12 questions of
    // the chain by 3 moved by 1, 12 of the one not 2 by 3 moved by 4, and 14 of the random
    // chains, which give 1156 answers of the whole (measured). Against the rows read one at a
    // time, as before, on 364 random chains of these and of holes in both orders: 48 refusals
    // became `false`, and no other answer changed (measured once).
    let bounded = |test: &str, shift: i64| {
        let mut src = String::from("p0(x: int) = x > 0 && x < 50;\n");
        for i in 1..9 {
            src.push_str(&format!(
                "p{i}(x: int) = {test} && p{}(x: x + {}) && x > 0 && x < {};\n",
                i - 1,
                lit(shift),
                40 + 5 * i
            ));
        }
        src
    };
    for (test, shift) in [
        ("(x mod 3) < 2", 1),
        ("x mod 5 < 4", 1),
        ("!(x mod 7 == 3)", 2),
        ("x mod 3 < 2", 3),
        ("x mod 3 != 2", 4),
        ("x mod 4 >= 3", -4),
    ] {
        let src = bounded(test, shift);
        let decided = answers_with_faces_are_those_without(&src);
        assert!(decided > 0, "no answer of the whole in\n{src}");
    }
    let mut rng = zed_tests::instances::Rng::new(0x40d3c);
    let mut decided = 0;
    for _ in 0..40 {
        decided += answers_with_faces_are_those_without(&random_remainder_chain(&mut rng));
    }
    assert!(decided >= 1000, "{decided} answers of the whole");
    // The chains of the scaling test, unbounded below: the answers written over quotients
    // and remainders are those reading the bodies again, and those of the whole where decided.
    for chain in [mod3_chain, mod5_chain, mod7_chain, kept_residue_chain] {
        answers_are_those_reading_bodies(&chain(10));
    }
}

#[test]
fn the_questions_of_a_chain_of_remainders_scale() {
    // LOAD-mod-chain. The chain of the task holds nowhere from link 3 on; its face kept the
    // residues of the link below as one-sided rows, read one at a time, so each link was
    // decided whole and refused (Shadows), and asked again whole: 5.5 s at 100 links, 21.9 s
    // at 200 (debug, measured once). Now the face of link 3 is read empty, and each later
    // link holds nowhere from the link below: 0.063 s at 100 links, 0.23 s at 400.
    questions_scale_unit("a chain of remainders by 3", 50, mod3_chain);
    questions_scale_unit("a chain of remainders by 5", 50, mod5_chain);
    questions_scale_unit("a chain of remainders by 7 moved by 2", 50, mod7_chain);
    questions_scale_unit(
        "a chain of remainders moved by the modulus",
        50,
        kept_residue_chain,
    );
}
