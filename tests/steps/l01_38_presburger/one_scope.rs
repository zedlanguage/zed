//! The linear questions of a unit read every function's body under one scope of the unit's
//! definitions (`preimage::Scoped`, LOAD-chain): each relation is the one the body closed
//! over the definitions it reaches gives, in any order of the bodies, and a chain of n
//! functions, each calling the one before, is read in O(n), where closing each body over its
//! cone read it in O(n²).

use std::sync::Arc;

use zed_kernel::{Shared, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zed_tests::step_helpers::l01_38_presburger::pncx::{
    modular_case, modular_case_mode, modular_case_with,
};
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

/// A chain of functions: its first functions, and its link `i` for `i >= 1`.
pub(super) type Links = (&'static str, fn(usize) -> String);

/// The unit of the first functions of `links` and its links `1` to `m - 1`.
fn chain_source((first, link): Links, m: usize) -> String {
    std::iter::once(first.to_string())
        .chain((1..m).map(link))
        .collect()
}

/// Times the linear questions of the unit of `links` at m = `n` and 8n ([`chain_source`]), on
/// units elaborated before the timing; no question is refused.
pub(super) fn questions_scale(what: &str, n: usize, links: Links) {
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = chain_source(links, m);
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
    for v in lo..=hi.max(lo) + 1 {
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

pub(super) fn drifting_link(i: usize) -> String {
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
    // chain, which they read through its face, at 12 links, and 6 random chains of the
    // drifting chain's shape of a fresh seed. The same at 30 links, as first written, and the
    // 60 random chains of seed 0x1c5a are in `bench::one_scope` (2.2 s together at load 25).
    chains_read_through_faces(12);
    let (mut rng, _) = zed_tests::instances::Rng::fresh("random chains read through faces");
    random_chains_read_through_faces(&mut rng, 6);
}

/// The drifting chain of `n` links; the same with a disjunction in its callee, whose face
/// keeps it as a clause (LOAD-disj-residue); and a chain moving a second parameter beside a
/// callee of the first: each answer is that of the relation whole.
pub(super) fn chains_read_through_faces(n: usize) {
    let r = "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\n";
    answers_are_those_of_the_whole(&drifting_chain(r, n));
    let disjunction = "q(x: int) = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x < 1000000;\n";
    answers_are_those_of_the_whole(&drifting_chain(disjunction, n));
    let mut second =
        String::from("s(x: int) = x > 0 && x mod 3 == 1;\np0(y: int, x: int) = y > 0 && x > 0;\n");
    for i in 1..n {
        second.push_str(&format!(
            "p{i}(y: int, x: int) = s(x: x) && p{}(y: y + 3, x: x) && y < {};\n",
            i - 1,
            1000 * i
        ));
    }
    answers_are_those_of_the_whole(&second);
}

/// `count` random chains of the drifting chain's shape ([`random_chain`]): each answer is that
/// of the relation whole.
pub(super) fn random_chains_read_through_faces(rng: &mut zed_tests::instances::Rng, count: usize) {
    for _ in 0..count {
        answers_are_those_of_the_whole(&random_chain(rng));
    }
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
fn each_answer_of_a_disjunctive_chain_of_residues_is_the_answer_of_the_relation_whole() {
    // LOAD-disj-residue: the face of a callee with a disjunction keeps it as clauses, each said
    // once. Drifting chains of 12 links whose clauses repeat every few links (residues modulo
    // 5) or never repeat (modulo 1009).
    disjunctive_chains_are_answered(
        &[
            "(x mod 3 == 1 || x mod 5 == 2)",
            "(x mod 1009 == 0 || x mod 3 == 1)",
        ],
        12,
    );
}

#[test]
fn each_answer_of_a_disjunctive_chain_of_bounds_is_the_answer_of_the_relation_whole() {
    // LOAD-disj-residue: drifting chains of 12 links that move a bound (the holes of `x < 10 ||
    // x > 20`), or share a remainder between two disjunctions, which keeps it.
    disjunctive_chains_are_answered(
        &[
            "(x < 10 || x > 20)",
            "(x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50)",
        ],
        12,
    );
}

/// The drifting chain of `n` links beside `q(x) = {q} && 0 < x < 1000000`, for each `q` of
/// `qs`: each answer is checked against the answers made with no face, refusals too, and
/// against the whole where the whole is decided, since the solver refuses some of these
/// questions one way and not the other; and the whole of each is decided, both questions of
/// each of its `n + 1` functions in both orders. The chains at 30 links, as first written, are
/// in `bench::one_scope` (3.2 s together at load 25). The chain beside `x mod 4 != 1 && (x mod
/// 6 == 2 || x mod 10 == 3)` is checked the same way by
/// `a_link_decided_whole_is_answered_where_its_relation_is`; deciding its links whole takes 14
/// to 35 s at 30 links (load 28 to 37), so it is not checked twice (SPLIT-one-scope).
pub(super) fn disjunctive_chains_are_answered(qs: &[&str], n: usize) {
    for q in qs {
        let src = drifting_chain(&format!("q(x: int) = {q} && x > 0 && x < 1000000;\n"), n);
        let decided = answers_with_faces_are_those_without(&src);
        assert_eq!(decided, 4 * (n + 1), "the whole decided\n{src}");
    }
}

#[test]
fn each_answer_of_a_random_disjunctive_chain_is_the_answer_of_the_relation_whole() {
    // Random chains of the shape of those above (LOAD-disj-residue), checked the same way: 4
    // of a fresh seed; the 80 of seed 0xd15e, as first written, are in `bench::one_scope` (3.4
    // s at load 25).
    let (mut rng, _) = zed_tests::instances::Rng::fresh("random disjunctive chains");
    random_disjunctive_chains_are_answered(&mut rng, 4);
}

/// `count` chains of [`random_disjunctive_chain`]: each answer with faces is that without, and
/// that of the whole where the whole is decided.
pub(super) fn random_disjunctive_chains_are_answered(
    rng: &mut zed_tests::instances::Rng,
    count: usize,
) {
    for _ in 0..count {
        answers_with_faces_are_those_without(&random_disjunctive_chain(rng));
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
    // as the relation is written. At 12 links; at 30, as first written, in `bench::one_scope`
    // (1.2 s at load 25).
    disjunctive_chains_are_answered(&[LINK_DECIDED_WHOLE], 12);
}

/// The callee of [`a_link_decided_whole_is_answered_where_its_relation_is`].
pub(super) const LINK_DECIDED_WHOLE: &str = "x mod 4 != 1 && (x mod 6 == 2 || x mod 10 == 3)";

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
    // relation written whole wherever that is decided, in both orders of the bodies: 2 chains
    // of a fresh seed. Before the fix, five of the ten chains of seed 0x5eed1 had a question
    // refused that the whole decided (the first at its first chain); those ten, as first
    // written, are in `bench::one_scope` (0.8 s at load 25). Of 160 chains of 40 seeds, the
    // least had 12 answers of the whole (2026-11-14); one of them took 8 to 16 s alone at load
    // 30 to 45, a case of PERF-negated-chain-unsolved, so a fresh seed may meet such a chain.
    let (mut rng, _) = zed_tests::instances::Rng::fresh("random chains with negations");
    let decided = random_negated_chains_decided(&mut rng, 2);
    assert!(decided >= 12, "{decided} answers of the whole");
}

/// The answers of the whole decided over `count` chains of [`random_negated_chain`], each
/// checked as [`answers_with_faces_are_those_without`] checks it.
pub(super) fn random_negated_chains_decided(
    rng: &mut zed_tests::instances::Rng,
    count: usize,
) -> usize {
    (0..count)
        .map(|_| answers_with_faces_are_those_without(&random_negated_chain(rng)))
        .sum()
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

/// Times the separate tests `t{i}(x) = {test}` over one chain `h{i}(x) = {step}`, each `H` of
/// `step` written as `h{i-1}(x: x)` and each `H` of `test` as `h{i}(x: x)`, at `n` and 8n links,
/// held to work of order `n^power` ([`zed_tests::scaling::check_order`]): each test is a
/// question of its own, with no kept part (LOAD-chain-sep-rest).
pub(super) fn separate_tests_scale(
    what: &str,
    n: usize,
    power: u32,
    step: &'static str,
    test: &'static str,
) {
    separate_tests_over_inputs_scale(what, n, power, &["x"], step, test);
}

/// [`separate_tests_scale`] with the inputs `inputs` at each link, `h0` the first.
pub(super) fn separate_tests_over_inputs_scale(
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
fn a_test_after_a_failed_test_reading_the_same_call_keeps_its_answer() {
    // T11-preimage-log: `t1` reads `m(x: x)`, which makes an auxiliary pair, and fails at the
    // product `q(x: x)`; its translation is undone (`Tx::forget`, `Tr::truncate`). `t2` reads
    // the same call again and must translate it afresh. With a `forget` that removes nothing,
    // `t2` reads the stale key of the pair that `truncate` took away and panics.
    use zedc::store::presburger::{Formula, decide};
    let units = [
        "m(x: int) = x mod 7;\nq(x: int) = x * x * x;\nt1(x: int) = m(x: x) + q(x: x) > 0;\nt2(x: int) = m(x: x) == 9;\n",
        "m(x: int) = x mod 7;\nq(x: int) = x * x * x;\nt1(x: int) = m(x: x) + q(x: x) > 0;\nu(x: int) = x div 5 == 1;\nt2(x: int) = m(x: x) == 9;\n",
        "m(x: int) = x div 7;\nq(x: int) = x * x * x;\nt1(x: int) = m(x: x) + q(x: x) > 0;\nu(x: int) = x mod 5 == 1;\nt2(x: int) = m(x: x) == 2 && x < 14;\n",
        "q(x: int) = x * x * x;\nt1(x: int) = x mod 7 + q(x: x) > 0;\nt2(x: int) = x mod 7 == 9;\n",
        "m(x: int) = x mod 7;\nq(x: int) = x * x * x;\nt1(x: int) = m(x: x + 1) + q(x: x) > 0;\nt2(x: int) = m(x: x + 1) == 9;\n",
    ];
    for src in units {
        let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let lets = lets(&unit);
        let mut scoped = Scoped::new(&lets);
        let mut answered = 0;
        for (name, ps, body) in functions(&unit) {
            let r = scoped.relation(body, ps, ps, true);
            if name != "u" && name != "t2" {
                // `m` and `q` give an `int`, and `t1` reads a product.
                assert!(r.is_none(), "{src}{name} has a relation");
                continue;
            }
            let r = r.unwrap_or_else(|| panic!("{src}{name} has no relation"));
            let w = scoped.written(&r);
            let with = |f: Formula| Formula::and(vec![w.defined(), f]);
            let somewhere = decide(&with(w.body.clone()));
            let fails_somewhere = decide(&with(Formula::negate(w.body.clone())));
            if name == "t2" {
                // `x mod 7 == 9` and `x div 7 == 2 && x < 14` hold for no `x`.
                assert_eq!(
                    (somewhere, fails_somewhere),
                    (Ok(false), Ok(true)),
                    "{src}{w}"
                );
                answered += 1;
            }
        }
        assert_eq!(answered, 1, "{src}");
    }
}

/// The units of [`definition_units`] are checked in eight parts, every eighth unit each, less the
/// twelve slowest (0.2 to 1 s each at load 35), each checked by a test of its own
/// (TEST-bench-move-l0138, TEST-corr-slow-l0138); together they check every unit. The five
/// chains of [`SHORTENED_DEFINITION_UNITS`], the slowest, are checked here one link shorter, which
/// asks a prefix of their questions in about a third of the time, and as written in
/// `bench::one_scope`. The unit of `x mod 5 + x div 7 - 9` is also checked at 5 links in
/// `bench::one_scope` (1.9 s at load 20); so are the two units of I21, at 3 links here and at 5
/// there.
#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions_part_0() {
    summaries_of_definitions_part(0);
}

#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions_part_1() {
    summaries_of_definitions_part(1);
}

#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions_part_2() {
    summaries_of_definitions_part(2);
}

#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions_part_3() {
    summaries_of_definitions_part(3);
}

#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions_part_4() {
    summaries_of_definitions_part(4);
}

#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions_part_5() {
    summaries_of_definitions_part(5);
}

#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions_part_6() {
    summaries_of_definitions_part(6);
}

#[test]
fn summaries_of_definitions_give_the_answers_of_the_definitions_part_7() {
    summaries_of_definitions_part(7);
}

#[test]
fn summaries_of_a_chain_of_three_halves_plus_one_give_its_answers() {
    summaries_of_a_shortened_unit(4);
}

#[test]
fn summaries_of_a_sum_of_two_quotients_of_a_chain_give_its_answers() {
    summaries_of_a_shortened_unit(5);
}

#[test]
fn summaries_of_a_max_against_x_less_9_beside_a_quotient_of_x_give_its_answers() {
    summaries_of_a_shortened_unit(33);
}

#[test]
fn summaries_of_a_max_against_remainders_beside_a_quotient_of_x_give_its_answers() {
    summaries_of_a_shortened_unit(34);
}

#[test]
fn summaries_of_a_branch_on_a_remainder_by_6_give_its_answers() {
    summaries_of_a_shortened_unit(77);
}

#[test]
fn summaries_of_a_max_against_a_quotient_of_x_less_9_give_its_answers() {
    summaries_of_definitions_of_unit(28);
}

#[test]
fn summaries_of_a_max_against_x_plus_y_less_9_give_the_answers_of_each_test_0() {
    summaries_of_definitions_of_unit(36);
}

#[test]
fn summaries_of_a_max_against_x_plus_y_less_9_give_the_answers_of_each_test_1() {
    summaries_of_definitions_of_unit(37);
}

#[test]
fn summaries_of_a_max_against_x_plus_y_less_9_give_the_answers_of_each_test_2() {
    summaries_of_definitions_of_unit(38);
}

#[test]
fn summaries_of_a_count_of_guards_over_two_inputs_give_its_answers() {
    summaries_of_definitions_of_unit(71);
}

#[test]
fn summaries_of_two_chains_over_different_inputs_give_their_answers() {
    summaries_of_definitions_of_unit(74);
}

#[test]
fn summaries_of_two_chains_sharing_x_and_x_div_7_give_their_answers() {
    summaries_of_definitions_of_unit(75);
}

/// The slowest units of [`definition_units`], all chains of [`definition_chain`]: index, step,
/// test and links, as written there.
pub(super) const SHORTENED_DEFINITION_UNITS: [(usize, &str, &str, usize); 5] = [
    (4, "(3 * H + 1) div 2", "H < 0 - 4", 6),
    (5, "H div 2 + H div 3", "H > 5", 5),
    (33, "max(H div 2, x - 9)", "H < x div 64 - 1", 6),
    (
        34,
        "max(H div 2, x mod 5 + x div 7 - 9)",
        "H < x div 64 - 1",
        4,
    ),
    (77, "if H mod 6 == 0 { H + 1 } else { H + 2 }", "H > 10", 8),
];

/// The next slowest units of [`definition_units`], each checked by a test of its own.
const SLOW_DEFINITION_UNITS: [usize; 7] = [28, 36, 37, 38, 71, 74, 75];

/// The units of [`definition_units`] whose index is `part` mod 8, less the slowest.
fn summaries_of_definitions_part(part: usize) {
    let units = definition_units();
    let slow = |k: &usize| {
        SLOW_DEFINITION_UNITS.contains(k) || SHORTENED_DEFINITION_UNITS.iter().any(|u| u.0 == *k)
    };
    summaries_of_definitions_give_their_answers(
        (units.iter().enumerate())
            .filter(|(k, _)| k % 8 == part && !slow(k))
            .map(|(_, src)| src.as_str()),
    );
}

/// Unit `k` of [`definition_units`].
pub(super) fn summaries_of_definitions_of_unit(k: usize) {
    summaries_of_definitions_give_their_answers([definition_units()[k].as_str()]);
}

/// Unit `k` of [`SHORTENED_DEFINITION_UNITS`] with one link fewer, after a check that the table
/// holds unit `k` as [`definition_units`] writes it.
fn summaries_of_a_shortened_unit(k: usize) {
    let &(_, step, test, n) = (SHORTENED_DEFINITION_UNITS.iter())
        .find(|u| u.0 == k)
        .expect("a shortened unit");
    assert_eq!(
        definition_units()[k],
        definition_chain(step, test, n),
        "unit {k}"
    );
    summaries_of_definitions_give_their_answers([definition_chain(step, test, n - 1).as_str()]);
}

/// The chain `h{i}(x) = step`, `i` from 1 to `n`, each `H` of `step` written as `h{i-1}(x: x)`
/// and `h0(x) = x`, with the test `t{i}(x) = test` at each link, each `H` of `test` written as
/// `h{i}(x: x)`.
pub(super) fn definition_chain(step: &str, test: &str, n: usize) -> String {
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
}

/// A chain of [`definition_chain`] over the inputs `x` and `y`.
fn over_two_inputs(src: String) -> String {
    src.replace("(x: int)", "(x: int, y: int)")
        .replace("(x: x)", "(x: x, y: y)")
}

/// The chain `g{i}(x) = max(g{i-1}(x: x) div 2, x mod 5 + x div 7 - 9)` of `links` links, the
/// chain `p2` over `y` beside it, and the tests `u` of `g{links}` and `t` of both (I21).
pub(super) fn two_chains_over_different_inputs(links: usize) -> String {
    let mut src = "g0(x: int) = x;\n".to_string();
    for i in 1..=links {
        src += &format!(
            "g{i}(x: int) = max(g{}(x: x) div 2, x mod 5 + x div 7 - 9);\n",
            i - 1
        );
    }
    src += "p0(y: int) = y;\n";
    src += "p1(y: int) = if p0(y: y) > 0 { p0(y: y) + 1 } else { p0(y: y) };\n";
    src += "p2(y: int) = if p1(y: y) > 0 { p1(y: y) + 1 } else { p1(y: y) };\n";
    src += &format!("u(x: int) = g{links}(x: x) < 0;\n");
    src += &format!("t(x: int, y: int) = p2(y: y) + g{links}(x: x) < 0 && y == 0;\n");
    src
}

/// The chain `g{i}(x) = max(g{i-1}(x: x) div 2, x div 7 - 9)` of `links` links and the chain
/// `p2` over `x` and `y` sharing `x div 7`, with the tests `u` of `g{links}` and `t` of both.
pub(super) fn two_chains_sharing_x_and_x_div_7(links: usize) -> String {
    let mut src = "g0(x: int) = x;\n".to_string();
    for i in 1..=links {
        src += &format!("g{i}(x: int) = max(g{}(x: x) div 2, x div 7 - 9);\n", i - 1);
    }
    src += "p0(x: int, y: int) = x + y;\n";
    src += "p1(x: int, y: int) = if p0(x: x, y: y) > x div 7 { p0(x: x, y: y) + 1 } else { p0(x: x, y: y) };\n";
    src += "p2(x: int, y: int) = if p1(x: x, y: y) > x div 7 { p1(x: x, y: y) + 1 } else { p1(x: x, y: y) };\n";
    src += &format!("u(x: int) = g{links}(x: x) < 0;\n");
    src += &format!("t(x: int, y: int) = p2(x: x, y: y) + g{links}(x: x) < 0 && y == 0;\n");
    src
}

/// The units whose summaries [`summaries_of_definitions_give_their_answers`] checks.
fn definition_units() -> Vec<String> {
    let chain = definition_chain;
    let two = over_two_inputs;
    vec![
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
        chain("max(H div 2, x mod 5 + x div 7 - 9)", "H < x div 64 - 1", 4),
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
        // Cross-review round 3 (Gemini): a piece unbounded below, `a <= -5 && h >= -2 * a`, and
        // one unbounded above, `a >= -3 && h >= 3 - a`, whose rests hold on each other; `a`
        // never takes -4, which a merge of the two would add ([`merge_pieces`]).
        concat!(
            "k0(k: int) = if k >= 0 { k } else { k };\n",
            "a(k: int) = if k0(k: k) <= 0 { k0(k: k) - 5 } else { k0(k: k) - 4 };\n",
            "h(k: int, y: int) = if a(k: k) <= 0 - 5 { max(y, 0 - 2 * a(k: k)) } else { max(y, 3 - a(k: k)) };\n",
            "t(k: int, y: int) = h(k: k, y: y) + a(k: k) == 4 && h(k: k, y: y) == 8;\n",
        )
        .to_string(),
        // Cross-review round 3 (Gemini): two chains over the product `x * y`, which `t` does not
        // write itself.
        concat!(
            "g1(x: int, y: int) = x * y;\n",
            "g2(x: int, y: int) = g1(x: x, y: y) + 1;\n",
            "p1(x: int, y: int) = x * y;\n",
            "p2(x: int, y: int) = p1(x: x, y: y) + 1;\n",
            "t(x: int, y: int) = g2(x: x, y: y) != p2(x: x, y: y);\n",
        )
        .to_string(),
        // Cross-review round 3 (Gemini, I21): a test `t` reading two chains over different inputs,
        // after a test `u` has numbered the links of `g{n}` before those of `p2`; 5 links as
        // first written in `bench::one_scope`.
        two_chains_over_different_inputs(3),
        // Two independent chains sharing input `x` and functional leaf `x div 7`: both cones
        // summarize with `x` kept in both keys regardless of query order; 5 links as first
        // written in `bench::one_scope`.
        two_chains_sharing_x_and_x_div_7(3),
        // Periodic remainder chains (I12, I26): answered at depth 8 without refusal in every order.
        chain("H mod 7 + H", "H < 0", 8),
        chain("if H mod 6 == 0 { H + 1 } else { H + 2 }", "H > 10", 8),
    ]
}

/// Each answer of each unit of `units` with its summaries: LOAD-chain-sep.
pub(super) fn summaries_of_definitions_give_their_answers<'a>(
    units: impl IntoIterator<Item = &'a str>,
) {
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
    for src in units {
        let unit = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let lets = lets(&unit);
        let fs = functions(&unit);
        let n = fs.len();
        // The answers of each function, asked in an order of one `Extending`, each checked
        // against the relation with all its definitions where `check`. The answers in the
        // unit's order are checked so; those in the other orders must equal them, so they are
        // not checked again (a check decides the whole and, where that is refused, at 601
        // values of `x`: checking in every order took most of the time of these tests).
        let ask = |order: Vec<usize>, check: bool| -> Vec<Option<Answers>> {
            let mut scoped = Scoped::new(&lets);
            let mut extending = Extending::new();
            let mut out = vec![None; n];
            for i in order {
                let (name, ps, body) = fs[i];
                let Some(r) = scoped.relation(body, ps, ps, true) else {
                    continue;
                };
                let a = extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
                if check {
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
                }
                out[i] = Some(a);
            }
            out
        };
        let forward = ask((0..n).collect(), true);
        assert!(forward.iter().any(Option::is_some), "{src}");
        assert_eq!(forward, ask((0..n).rev().collect(), false), "{src}");
        for i in 0..n {
            let alone = ask(vec![i], false);
            assert_eq!(forward[i], alone[i], "{src}: `{}` alone", fs[i].0);
        }
    }
}

/// A link of a chain of `max`, `min` and `div`: `H` its input, and its value from `H` and `x`.
type MaxMinDivStep = (&'static str, fn(i64, i64) -> i64);

/// The links of [`max_min_div_chains_give_their_values`].
const MAX_MIN_DIV_STEPS: [MaxMinDivStep; 19] = [
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
    ("H mod 7 + H", |h, _| h.rem_euclid(7) + h),
    ("if H mod 6 == 0 { H + 1 } else { H + 2 }", |h, _| {
        if h.rem_euclid(6) == 0 { h + 1 } else { h + 2 }
    }),
];

/// LOAD-max-div-xr: chains of `max`, `min` and `div` whose summaries keep the input, and the
/// quotients the next link needs, beside the key, one chain of 5 links per step of
/// [`MAX_MIN_DIV_STEPS`] named in `steps`. Each test fixes `x` and asks whether `h{i}` has the
/// value computed here by integer arithmetic (`div` by a positive constant rounds down), or
/// another: the first must hold and the second not. Negative, zero and large `x`, and `x` on
/// either side of where `x - 9` and `x div 2^i` cross. Then, with `x` free, the values each
/// `h{i}` takes, found by trying every `x` in a range. The 19 steps took 9.0 s in one test
/// (load 25 to 32), most of it a set of every value each link takes; the tests below split
/// them by kind, one to three steps each (TEST-corr-slow-l0138).
fn max_min_div_chains_give_their_values(steps: &[usize]) {
    use zedc::store::presburger::extend::Extending;
    let xs: [i64; 10] = [-1_000_000, -19, -1, 0, 1, 9, 10, 18, 19, 1_000_000];
    let lit = |v: i64| {
        if v < 0 {
            format!("0 - {}", -v)
        } else {
            v.to_string()
        }
    };
    for &(step, value) in steps.iter().map(|&s| &MAX_MIN_DIV_STEPS[s]) {
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
        // Per link, which of `cs` (sorted) it takes and the least value it takes: a binary
        // search and a minimum per value (15 ms a step, load 25), where inserting each value into
        // a set of the values taken made most of the 9.0 s the 19 steps took.
        let mut taken = [[false; 12]; 6];
        let mut least = [i64::MAX; 6];
        for x in -200_000..=200_000 {
            let mut h = x;
            for i in 1..=5 {
                h = value(h, x);
                least[i] = least[i].min(h);
                if let Ok(j) = cs.binary_search(&h) {
                    taken[i][j] = true;
                }
            }
        }
        for i in 1..=5 {
            for (j, &c) in cs.iter().enumerate() {
                let h = format!("h{i}(x: x)");
                src += &format!("v{i}c{j}(x: int) = {h} == {};\n", lit(c));
                src += &format!("l{i}c{j}(x: int) = {h} < {};\n", lit(c));
                want.insert(format!("v{i}c{j}"), taken[i][j]);
                want.insert(format!("l{i}c{j}"), least[i] < c);
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
fn summaries_of_max_min_div_chains_of_halves_against_x_plus_or_minus_9_give_their_values() {
    max_min_div_chains_give_their_values(&[0, 1, 2]);
}

#[test]
fn summaries_of_max_min_div_chains_against_multiples_of_x_give_their_values() {
    max_min_div_chains_give_their_values(&[3, 7, 8]);
}

#[test]
fn summaries_of_max_min_div_chains_offset_by_one_give_their_values() {
    max_min_div_chains_give_their_values(&[4, 9, 10]);
}

#[test]
fn summaries_of_max_min_div_chains_against_quotients_of_x_give_their_values() {
    max_min_div_chains_give_their_values(&[5, 6]);
}

#[test]
fn summaries_of_a_max_chain_against_x_div_5_plus_x_div_7_less_9_give_its_values() {
    max_min_div_chains_give_their_values(&[14]);
}

#[test]
fn summaries_of_max_min_div_chains_against_remainders_of_x_give_their_values() {
    max_min_div_chains_give_their_values(&[11, 12]);
}

#[test]
fn summaries_of_a_max_chain_against_x_mod_5_plus_x_div_7_less_9_give_its_values() {
    max_min_div_chains_give_their_values(&[13]);
}

#[test]
fn summaries_of_a_chain_of_h_less_1_against_x_give_its_values() {
    max_min_div_chains_give_their_values(&[15]);
}

#[test]
fn summaries_of_a_chain_of_h_less_4_against_x_give_its_values() {
    max_min_div_chains_give_their_values(&[16]);
}

#[test]
fn summaries_of_a_chain_of_h_plus_its_remainder_by_7_give_its_values() {
    max_min_div_chains_give_their_values(&[17]);
}

#[test]
fn summaries_of_a_chain_of_a_branch_on_a_remainder_by_6_give_its_values() {
    max_min_div_chains_give_their_values(&[18]);
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

/// Times the relations, translated alone, of the unit of `links` at m = `n` and 8n
/// ([`chain_source`]), on units elaborated before the timing: for chains whose
/// questions are decided whole because each link's constraints exclude the point found for
/// the link it calls (`presburger::extend`, COMPLEXITY.md row LOAD-chain-share).
pub(super) fn relations_scale(what: &str, n: usize, links: Links) {
    let units: std::collections::BTreeMap<usize, Unit> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| (m, elab(&chain_source(links, m)).unwrap()))
        .collect();
    zed_tests::scaling::check(what, n, |m| {
        assert_every_relation_read(&units[&m], |_| true)
    });
}

/// The relation of each function of `unit` whose name `wanted` takes, translated alone under
/// one scope, is read, not refused: the check of [`relations_scale`] and
/// [`unit_relations_scale`] besides the ratio.
fn assert_every_relation_read(unit: &Unit, wanted: fn(&str) -> bool) {
    let lets = lets(unit);
    let mut scoped = Scoped::new(&lets);
    for (name, ps, body) in functions(unit) {
        if wanted(name) {
            assert!(scoped.relation(body, ps, ps, true).is_some(), "{name}");
        }
    }
}

// Chains whose questions are decided whole, because each link's constraints exclude the point
// of the link it calls (COMPLEXITY.md row LOAD-chain-share): their translation alone is O(n).

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
    // are decided. A chain of congruences, an integer chain, and 4 random units of a fresh seed.
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
    let (mut rng, _) = zed_tests::instances::Rng::fresh("random units of congruences");
    random_units_read_through_projections(&mut rng, 4);
}

/// `count` units of [`random_congruence_unit`]: each answer is the one read with each call
/// reading its callee's body again, and the one of the whole where both are decided. The 80
/// of seed 0x1c4e, as first written, are in `bench::one_scope` (5.1 s with the two fixed units
/// at load 25).
pub(super) fn random_units_read_through_projections(
    rng: &mut zed_tests::instances::Rng,
    count: usize,
) {
    for _ in 0..count {
        answers_are_those_reading_bodies(&random_congruence_unit(rng));
    }
}

/// Times the relations, translated alone, of the tests `p{i}` of the units `unit(n)` and
/// `unit(8n)`, elaborated before the timing: their integer functions are read through their
/// calls.
pub(super) fn unit_relations_scale(what: &str, n: usize, unit: fn(usize) -> String) {
    let units: std::collections::BTreeMap<usize, Unit> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| (m, elab(&unit(m)).unwrap()))
        .collect();
    zed_tests::scaling::check(what, n, |m| {
        assert_every_relation_read(&units[&m], |name| name.starts_with('p'))
    });
}

/// Times the linear questions of the units `unit(n)` and `unit(8n)`, elaborated before the
/// timing; none is refused.
pub(super) fn questions_scale_unit(what: &str, n: usize, unit: fn(usize) -> String) {
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

/// No linear question of `src` is refused: the check the benchmarks of [`questions_scale_unit`]
/// make at their two sizes besides the ratio.
fn no_question_refused(what: &str, src: &str) {
    let (stmts, tokens, unit) = (
        zed_tests::deep::statements(src),
        zedc::lex::lex_fence(src).unwrap(),
        elab(src).unwrap(),
    );
    let refused = zedc::front::linear_questions(src, &tokens, &stmts, &unit);
    assert!(refused.is_empty(), "{what}: {refused:?}\n{src}");
}

/// The chains of the benchmarks of [`questions_scale_unit`] (`bench/one_scope.rs`), each at a
/// few small sizes, have no question refused (TEST-bench-move-l0138, author P170).
#[test]
fn the_chains_of_the_benchmarks_have_no_question_refused_at_small_sizes() {
    type Unit = fn(usize) -> String;
    let units: [(&str, Unit); 40] = [
        ("holes beside one modulus", mod4_chain),
        ("a gap beside one modulus", gapped_chain),
        ("bounds beside a shared remainder", shared_remainder_chain),
        ("remainders by 3", mod3_chain),
        ("remainders by 5", mod5_chain),
        ("remainders by 7 moved by 2", mod7_chain),
        ("remainders moved by the modulus", kept_residue_chain),
        ("two exceptional residues", two_guards_chain),
        ("an affine default with an exception", affine_default_chain),
        ("doubling the residue by 1000", doubling_chain),
        (
            "a default doubling the residue by 2^40",
            power_of_two_default_chain,
        ),
        ("a default unit on the coset only", nonunit_persist_chain),
        ("two intervals, by 10^18 + 9", gap_chain),
        ("two wide intervals, by 2^31 - 1", gap_wide_chain),
        ("nested cuts, by 2^31 - 1", cuts_reversed_chain),
        ("two alternating steps of cuts", two_cut_steps_chain),
        ("three steps of overlapping cuts", overlap_chain),
        ("two steps of wide overlaps, by 10^12 + 39", overlap0_chain),
        (
            "three steps of wide overlaps, by 10^12 + 39",
            overlap6_chain,
        ),
        (
            "three steps of wide overlaps, by 10^18 + 9",
            overlap19_chain,
        ),
        ("random cuts and moves", random_cuts_chain),
        ("random cuts and moves of 0 to 6", random_small_moves_chain),
        ("a step switching every five links", switching_chain),
        ("a first step apart from the rest", first_step_apart_chain),
        ("independent question frontiers", independent_frontiers),
        (
            "two branches of one common prefix",
            two_branches_of_one_prefix,
        ),
        ("scalar image of guarded increments", guarded_increments),
        ("scalar lattice image of a remainder sum", remainder_sums),
        (
            "guarded increment orbit with kept input residue",
            guarded_increments_keeping_the_input_residue,
        ),
        (
            "remainder-sum orbit with kept input residue",
            remainder_sums_keeping_the_input_residue,
        ),
        (
            "guarded increment orbit with previous link residue",
            guarded_increments_keeping_the_previous_residue,
        ),
        (
            "remainder-sum orbit with previous link residue",
            remainder_sums_keeping_the_previous_residue,
        ),
        ("negated and disjunctive residues", negated_modular_chain),
        (
            "residues over distinct primes",
            residues_over_distinct_primes,
        ),
        ("clauses over many segments", clauses_over_many_segments),
        (
            "negated residues over distinct bounds",
            negated_residues_over_distinct_bounds,
        ),
        ("a chain of calls", chain_of_calls),
        (
            "a chain with a second call of a large callee",
            chain_with_a_large_callee,
        ),
        ("two chains sharing an input", two_chains_sharing_an_input),
        ("tests that forget four chains", tests_over_four_chains),
    ];
    for (what, unit) in units {
        for n in [1, 2, 6] {
            no_question_refused(&format!("{what}, {n}"), &unit(n));
        }
    }
    // Past link 76, where the bounds move beside the shared remainder.
    no_question_refused(
        "bounds beside a shared remainder, 80",
        &shared_remainder_chain(80),
    );
}

// The chains of the benchmarks in `bench/one_scope.rs`, named so that the benchmarks and
// `the_chains_of_the_benchmarks_are_answered_at_small_sizes` build the same units
// (TEST-bench-cover-l0138).

/// `p{i}(x) = p{i-1}(x: x) && x > i` (LOAD-chain-share).
pub(super) fn a_chain_of_tests() -> Links {
    ("p0(x: int) = x > 0;\n", |i| {
        format!("p{i}(x: int) = p{}(x: x) && x > {i};\n", i - 1)
    })
}

/// `p{i}(x, y) = p{i-1}(x: x, y: y) && x + i * y < 1000 i`.
pub(super) fn a_chain_over_two_variables() -> Links {
    ("p0(x: int, y: int) = x > y && y >= 0;\n", |i| {
        format!(
            "p{i}(x: int, y: int) = p{}(x: x, y: y) && x + {i} * y < {};\n",
            i - 1,
            1000 * i
        )
    })
}

/// `p{i}(x) = p{i-1}(x: x) && x mod 7 + i > 0` (LOAD-chain-aux).
pub(super) fn a_chain_defining_auxiliary_variables() -> Links {
    ("p0(x: int) = x div 3 > 0;\n", |i| {
        format!("p{i}(x: int) = p{}(x: x) && x mod 7 + {i} > 0;\n", i - 1)
    })
}

/// The drifting chain beside `q(x) = r(x: x) && x mod 3 == 1` (LOAD-call-summary).
pub(super) fn a_drifting_chain() -> Links {
    (
        "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\n\
         p0(x: int) = x > 0;\n",
        drifting_link,
    )
}

/// The drifting chain beside a disjunction of residues (LOAD-disj-residue).
pub(super) fn a_drifting_disjunctive_chain() -> Links {
    (
        "q(x: int) = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x < 1000000;\n\
         p0(x: int) = x > 0;\n",
        drifting_link,
    )
}

/// `p{i}(x) = p{i-1}(x: x + 1) && x + 2 i > 0` (LOAD-chain-args).
pub(super) fn a_chain_moving_its_argument() -> Links {
    ("p0(x: int) = x > 0;\n", |i| {
        format!(
            "p{i}(x: int) = p{}(x: x + 1) && x + {} > 0;\n",
            i - 1,
            2 * i
        )
    })
}

/// `p{i}(x) = p{i-1}(y: x) && x > -i`, the parameter named `x` and `y` by turns.
pub(super) fn a_chain_renaming_its_argument() -> Links {
    ("p0(x: int) = x > 0;\n", |i| {
        let (own, callee) = if i % 2 == 0 { ("x", "y") } else { ("y", "x") };
        format!(
            "p{i}({own}: int) = p{}({callee}: {own}) && {own} > 0 - {i};\n",
            i - 1
        )
    })
}

/// `p{i}(x) = p{i-1}(x: x) && h{i}(x: x) > 0` with `h{i}(x) = h{i-1}(x: x) div 2 + 1`.
pub(super) fn a_chain_over_halvings() -> Links {
    ("h0(x: int) = x;\np0(x: int) = x > 0;\n", |i| {
        format!(
            "h{i}(x: int) = h{}(x: x) div 2 + 1;\np{i}(x: int) = p{}(x: x) && h{i}(x: x) > 0;\n",
            i - 1,
            i - 1
        )
    })
}

/// As [`a_chain_over_halvings`], the definitions by turns a quotient, a remainder plus the
/// input, a minimum and an absolute value less a quotient.
pub(super) fn a_chain_over_mixed_definitions() -> Links {
    ("h0(x: int) = x;\np0(x: int) = x > 0;\n", |i| {
        let h = i - 1;
        let op = match i % 4 {
            0 => format!("h{h}(x: x) div 2"),
            1 => format!("h{h}(x: x) mod 7 + x"),
            2 => format!("min(h{h}(x: x), {i}) + 1"),
            _ => format!("abs(h{h}(x: x)) - x div 3"),
        };
        format!("h{i}(x: int) = {op};\np{i}(x: int) = p{h}(x: x) && h{i}(x: x) > 0 - {i};\n")
    })
}

/// A root and links that hold everywhere, `p{i}(x) = p{i-1}(x: x) && abs(h{i}(x: x)) >= 0`.
pub(super) fn a_chain_holding_everywhere() -> Links {
    ("h0(x: int) = x;\np0(x: int) = x > 0 || x <= 0;\n", |i| {
        format!(
            "h{i}(x: int) = h{}(x: x) div 2 + 1;\np{i}(x: int) = p{}(x: x) && abs(h{i}(x: x)) >= 0;\n",
            i - 1,
            i - 1
        )
    })
}

/// `t{i}(x) = h{i}(x: x) > 0` with `h{i}(x) = h{i-1}(x: x) div 2 + 1` (LOAD-chain-sep).
pub(super) fn separate_tests_over_halvings() -> Links {
    ("h0(x: int) = x;\nt0(x: int) = x > 0;\n", |i| {
        format!(
            "h{i}(x: int) = h{}(x: x) div 2 + 1;\nt{i}(x: int) = h{i}(x: x) > 0;\n",
            i - 1
        )
    })
}

/// `p{i}(x) = p{i-1}(x: 2 * x) && x < 1000 i` (LOAD-chain-affine).
pub(super) fn a_chain_doubling_its_argument() -> Links {
    ("p0(x: int) = x > 0;\n", |i| {
        format!("p{i}(x: int) = p{}(x: 2 * x) && x < {};\n", i - 1, 1000 * i)
    })
}

/// `p{i}(x) = p{i-1}(x: 0 - x) && x < 1000 i`.
pub(super) fn a_chain_negating_its_argument() -> Links {
    ("p0(x: int) = x > 0;\n", |i| {
        format!("p{i}(x: int) = p{}(x: 0 - x) && x < {};\n", i - 1, 1000 * i)
    })
}

/// `p{i}(x, y) = p{i-1}(x: x, y: 5) && x + y < 1000 i`.
pub(super) fn a_chain_passing_a_constant() -> Links {
    ("p0(x: int, y: int) = x > y;\n", |i| {
        format!(
            "p{i}(x: int, y: int) = p{}(x: x, y: 5) && x + y < {};\n",
            i - 1,
            1000 * i
        )
    })
}

/// `p{i}(x, y) = p{i-1}(x: x, y: x) && x + y < 1000 i`.
pub(super) fn a_chain_passing_a_parameter_twice() -> Links {
    ("p0(x: int, y: int) = x >= y;\n", |i| {
        format!(
            "p{i}(x: int, y: int) = p{}(x: x, y: x) && x + y < {};\n",
            i - 1,
            1000 * i
        )
    })
}

/// `p{i}(x) = q(x: x) && p{i-1}(x: x + 1) && x < 1000 i`: a link calling `q` and the link
/// before at a moved argument.
pub(super) fn second_call_link(i: usize) -> String {
    format!(
        "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
        i - 1,
        1000 * i
    )
}

/// [`second_call_link`]s beside `q(x) = x < 1000000`.
pub(super) fn a_chain_with_a_second_call() -> Links {
    (
        "q(x: int) = x < 1000000;\np0(x: int) = x > 0;\n",
        second_call_link,
    )
}

/// [`second_call_link`]s beside `q(x) = x > 0`, whose points move.
pub(super) fn a_chain_with_a_second_call_whose_points_move() -> Links {
    (
        "q(x: int) = x > 0;\np0(x: int) = x > 0;\n",
        second_call_link,
    )
}

/// [`second_call_link`]s beside `q` of two constraints.
pub(super) fn a_chain_with_a_second_call_of_two_constraints() -> Links {
    (
        "q(x: int) = x > 0 && x < 1000000;\np0(x: int) = x > 0;\n",
        second_call_link,
    )
}

/// [`second_call_link`]s beside `q` calling `r`, each with a lower and an upper bound.
pub(super) fn a_chain_with_a_second_call_of_a_bounded_call() -> Links {
    (
        "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\n\
         p0(x: int) = x > 0;\n",
        second_call_link,
    )
}

/// [`second_call_link`]s beside `q` calling `r`, with upper bounds alone.
pub(super) fn a_chain_with_a_second_call_of_a_call() -> Links {
    (
        "r(x: int) = x < 2000000;\nq(x: int) = r(x: x) && x < 1000000;\np0(x: int) = x > 0;\n",
        second_call_link,
    )
}

/// `p{i}(x, n) = q(x: x, n: n + i) && p{i-1}(x: x + 1, n: n) && x < 1000 i`, `q` dividing by
/// four terms of `n`.
pub(super) fn a_chain_dividing_by_its_argument() -> Links {
    (
        "q(x: int, n: int) = x mod n + x mod (n + 1) + x div (n + 2) + x div (n + 3) >= 0;\n\
         p0(x: int, n: int) = x mod n >= 0;\n",
        |i| {
            format!(
                "p{i}(x: int, n: int) = q(x: x, n: n + {i}) && p{}(x: x + 1, n: n) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    )
}

/// `p{i}(x, y) = p{i-1}(x: x + 1, y: x + 1) && x + y < 1000 i`.
pub(super) fn a_chain_passing_a_moved_parameter_twice() -> Links {
    ("p0(x: int, y: int) = x >= y;\n", |i| {
        format!(
            "p{i}(x: int, y: int) = p{}(x: x + 1, y: x + 1) && x + y < {};\n",
            i - 1,
            1000 * i
        )
    })
}

/// `p{i}(x, y) = p{i-1}(x: x + 1, y: 5) && x + y < 1000 i`.
pub(super) fn a_chain_passing_a_moved_parameter_and_a_constant() -> Links {
    ("p0(x: int, y: int) = x > y;\n", |i| {
        format!(
            "p{i}(x: int, y: int) = p{}(x: x + 1, y: 5) && x + y < {};\n",
            i - 1,
            1000 * i
        )
    })
}

/// The hole `10..=20` of `q`, beside which the drifting chain moves by 3 (LOAD-bound-holes).
const HOLE: &str = "q(x: int) = (x < 10 || x > 20) && x > 0 && x < 1000000;\np0(x: int) = x > 0;\n";

/// The drifting chain beside [`HOLE`].
pub(super) fn a_chain_moving_a_hole() -> Links {
    (HOLE, drifting_link)
}

/// The chain beside [`HOLE`] moving down by 30, so that the holes do not overlap.
pub(super) fn a_chain_moving_a_hole_apart() -> Links {
    (HOLE, falling_link)
}

/// The chain moving by 12 beside two disjunctions that share the remainder by 6.
pub(super) fn a_chain_moving_bounds_beside_a_shared_remainder() -> Links {
    (
        "q(x: int) = (x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50) && x > 0 \
         && x < 1000000;\np0(x: int) = x > 0;\n",
        rising_link,
    )
}

/// `step{i}(x) = step{i-1}(x: x) + i`, the chain LOAD-chain found.
pub(super) fn chain_of_calls(n: usize) -> String {
    let mut src = String::from("step0(x: int) = x;\n");
    for i in 1..n {
        src.push_str(&format!("step{i}(x: int) = step{}(x: x) + {i};\n", i - 1));
    }
    src
}

/// `p{i}(x) = h{n-1}(x: x) && p{i-1}(x: x + 1) && x < 1000 i` beside the chain `h{j}(x) =
/// h{j-1}(x: x) && x mod 3 + j < 2000000` of `n` links (LOAD-affine-cone).
pub(super) fn chain_with_a_large_callee(n: usize) -> String {
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
}

/// `p{i}(x) = h{n-1}(x: x) < 3n && p{i-1}(x: x + 1) && x < 1000 i` beside the integer
/// function `h{j}(x) = h{j-1}(x: x) + x mod 3` (LOAD-call-relation).
pub(super) fn a_chain_calling_an_integer_function(n: usize) -> String {
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
}

/// The chains `g{i}` of largest values and `p{i}` of guarded increments of `m` links, both
/// over `x`, and tests `t{i}` reading link `i` of each.
pub(super) fn two_chains_sharing_an_input(m: usize) -> String {
    let mut src = "g0(x: int) = x;\np0(x: int, y: int) = x + y;\n".to_string();
    for i in 1..=m {
        src += &format!("g{i}(x: int) = max(g{}(x: x) div 2, x div 7 - 9);\n", i - 1);
        src += &format!(
            "p{i}(x: int, y: int) = if p{}(x: x, y: y) > x div 7 {{ p{}(x: x, y: y) + 1 }} else {{ p{}(x: x, y: y) }};\n",
            i - 1,
            i - 1,
            i - 1
        );
    }
    src += &format!("u(x: int) = g{m}(x: x) < 0;\n");
    for i in 1..=m {
        src += &format!("t{i}(x: int, y: int) = g{i}(x: x) + p{i}(x: x, y: y) < 0 && y == 0;\n");
    }
    src
}

/// Four chains `g{a}_{i}(x) = g{a}_{i-1}(x: x) + i` of `m` links and four tests comparing the
/// sum of their last links with `q(x) = x * x * x`.
pub(super) fn tests_over_four_chains(m: usize) -> String {
    let mut src = String::from("q(x: int) = x * x * x;\n");
    for a in 0..4 {
        src += &format!("g{a}_0(x: int) = x + {a};\n");
        for i in 1..m {
            src += &format!("g{a}_{i}(x: int) = g{a}_{}(x: x) + {i};\n", i - 1);
        }
    }
    let sum = (0..4)
        .map(|a| format!("g{a}_{}(x: x)", m - 1))
        .collect::<Vec<_>>()
        .join(" + ");
    for j in 0..4 {
        src += &format!("t{j}(x: int) = {sum} < q(x: x) + {j};\n");
    }
    src
}

pub(super) fn independent_frontiers(n: usize) -> String {
    r6_local_source("leaves", n)
}

pub(super) fn two_branches_of_one_prefix(n: usize) -> String {
    r6_local_source("prefix", n)
}

const GUARDED_INCREMENT: &str = "if H mod 1000 == 0 { H + 1 } else { H + 2 }";
const REMAINDER_SUM: &str = "H mod 1000 + H";

pub(super) fn guarded_increments(n: usize) -> String {
    r6_periodic_value_questions(n, GUARDED_INCREMENT, "H == 9")
}

pub(super) fn remainder_sums(n: usize) -> String {
    r6_periodic_value_questions(n, REMAINDER_SUM, "H == 0")
}

pub(super) fn guarded_increments_keeping_the_input_residue(n: usize) -> String {
    r6_periodic_value_questions(n, GUARDED_INCREMENT, "x mod 1000 == 3 && H == 9")
}

pub(super) fn remainder_sums_keeping_the_input_residue(n: usize) -> String {
    r6_periodic_value_questions(n, REMAINDER_SUM, "x mod 1000 == 3 && H == 9")
}

pub(super) fn guarded_increments_keeping_the_previous_residue(n: usize) -> String {
    r6_periodic_value_questions(n, GUARDED_INCREMENT, "P mod 1000 == 3 && H == 5")
}

pub(super) fn remainder_sums_keeping_the_previous_residue(n: usize) -> String {
    r6_periodic_value_questions(n, REMAINDER_SUM, "P mod 1000 == 3 && H == 6")
}

/// The definitions `a{i} == a{i-1} + s{i}` (`a0 == s0`) of `m` links, each reading a new
/// symbol, and the questions `a{i} >= 0`.
pub(super) fn a_chain_reading_a_new_symbol_at_each_link(
    m: usize,
) -> (
    Vec<zedc::store::presburger::Formula>,
    Vec<zedc::store::presburger::Formula>,
) {
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared};
    let sym = |i: usize| Lin::atom(Atom::Sym(format!("s{i}").into()));
    let aux = |i: usize| Lin::atom(Atom::Aux(i as u32));
    let defs = (0..m)
        .map(|i| {
            let rhs = if i == 0 {
                sym(0)
            } else {
                aux(i - 1).plus(&sym(i))
            };
            Formula::And(Shared::new(vec![Formula::Con(Con::eq(&aux(i), &rhs))]))
        })
        .collect();
    let asks = (0..m)
        .map(|i| Formula::Con(Con::ge(&aux(i), &Lin::constant(0))))
        .collect();
    (defs, asks)
}

/// The division pairs `q{i-1} + r{i-1} + s{i} == 7 q{i} + r{i}` (`s0 == 7 q0 + r0`) of `m`
/// links, each pair defined twice, and the questions `q{i} >= 0`.
pub(super) fn a_chain_reading_a_new_division_pair_at_each_link(
    m: usize,
) -> (
    Vec<zedc::store::presburger::Formula>,
    Vec<zedc::store::presburger::Formula>,
) {
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared};
    let sym = |i: usize| Lin::atom(Atom::Sym(format!("s{i}").into()));
    let q = |i: usize| Lin::atom(Atom::Aux((2 * i) as u32));
    let r = |i: usize| Lin::atom(Atom::Aux((2 * i + 1) as u32));
    let defs = (0..m)
        .flat_map(|i| {
            let dividend = if i == 0 {
                sym(0)
            } else {
                q(i - 1).plus(&r(i - 1)).plus(&sym(i))
            };
            let eq = Con::eq(&dividend, &q(i).times(7).plus(&r(i)));
            let lo = Con::ge(&r(i), &Lin::constant(0));
            let hi = Con::ge(&Lin::constant(6), &r(i));
            let d = Formula::And(Shared::new(vec![
                Formula::Con(eq),
                Formula::Con(lo),
                Formula::Con(hi),
            ]));
            [d.clone(), d]
        })
        .collect();
    let asks = (0..m)
        .map(|i| Formula::Con(Con::ge(&q(i), &Lin::constant(0))))
        .collect();
    (defs, asks)
}

/// Each of `asks`, asked in turn of one `Extending` over the definitions `defs` (definition
/// `n` for `Aux(n)`), holds.
pub(super) fn assert_each_ask_holds(
    defs: &[zedc::store::presburger::Formula],
    asks: &[zedc::store::presburger::Formula],
) {
    use zedc::store::presburger::extend::Extending;
    let mut extending = Extending::new();
    for f in asks {
        let a = extending.defined(f, &|n| defs[n as usize].clone());
        assert_eq!(a.holds, Ok(true), "{f:?}");
    }
}

/// The checks of the benchmarks of [`questions_scale`], [`relations_scale`],
/// [`unit_relations_scale`] and the other chains in `bench/one_scope.rs` besides their
/// ratios, at a few small sizes: no question refused, every relation read, each ask holding,
/// and each formula decided to hold.
#[test]
fn the_chains_of_the_benchmarks_are_answered_at_small_sizes() {
    use zedc::store::presburger::{Formula, decide};
    let questions: [(&str, Links); 20] = [
        ("a chain of tests", a_chain_of_tests()),
        ("a chain over two variables", a_chain_over_two_variables()),
        (
            "a chain defining auxiliary variables",
            a_chain_defining_auxiliary_variables(),
        ),
        ("a drifting chain", a_drifting_chain()),
        (
            "a drifting disjunctive chain",
            a_drifting_disjunctive_chain(),
        ),
        ("a chain moving its argument", a_chain_moving_its_argument()),
        (
            "a chain renaming its argument",
            a_chain_renaming_its_argument(),
        ),
        ("a chain over halvings", a_chain_over_halvings()),
        (
            "a chain over mixed definitions",
            a_chain_over_mixed_definitions(),
        ),
        ("a chain holding everywhere", a_chain_holding_everywhere()),
        (
            "separate tests over halvings",
            separate_tests_over_halvings(),
        ),
        (
            "a chain doubling its argument",
            a_chain_doubling_its_argument(),
        ),
        (
            "a chain negating its argument",
            a_chain_negating_its_argument(),
        ),
        ("a chain passing a constant", a_chain_passing_a_constant()),
        (
            "a chain passing a parameter twice",
            a_chain_passing_a_parameter_twice(),
        ),
        ("a chain with a second call", a_chain_with_a_second_call()),
        (
            "a chain with a second call of a call",
            a_chain_with_a_second_call_of_a_call(),
        ),
        ("a chain moving a hole", a_chain_moving_a_hole()),
        ("a chain moving a hole apart", a_chain_moving_a_hole_apart()),
        (
            "a chain moving bounds beside a shared remainder",
            a_chain_moving_bounds_beside_a_shared_remainder(),
        ),
    ];
    let relations: [(&str, Links); 6] = [
        (
            "a second call whose points move",
            a_chain_with_a_second_call_whose_points_move(),
        ),
        (
            "dividing by its argument",
            a_chain_dividing_by_its_argument(),
        ),
        (
            "passing a moved parameter twice",
            a_chain_passing_a_moved_parameter_twice(),
        ),
        (
            "passing a moved parameter and a constant",
            a_chain_passing_a_moved_parameter_and_a_constant(),
        ),
        (
            "a second call of two constraints",
            a_chain_with_a_second_call_of_two_constraints(),
        ),
        (
            "a second call of a bounded call",
            a_chain_with_a_second_call_of_a_bounded_call(),
        ),
    ];
    for m in [1, 2, 6] {
        for (what, links) in questions {
            no_question_refused(&format!("{what}, {m}"), &chain_source(links, m));
        }
        for (_, links) in relations {
            assert_every_relation_read(&elab(&chain_source(links, m)).unwrap(), |_| true);
        }
        assert_every_relation_read(
            &elab(&a_chain_calling_an_integer_function(m)).unwrap(),
            |name| name.starts_with('p'),
        );
        let (defs, asks) = a_chain_reading_a_new_symbol_at_each_link(m);
        assert_each_ask_holds(&defs, &asks);
        let (defs, asks) = a_chain_reading_a_new_division_pair_at_each_link(m);
        assert_each_ask_holds(&defs, &asks);
    }
    type Family = fn(usize) -> Formula;
    let formulas: [(&str, Family); 3] = [
        (
            "clauses sharing one residue condition",
            clauses_sharing_one_residue_condition,
        ),
        ("a disjunction of many moduli", a_disjunction_of_many_moduli),
        ("the fails question of pairs", the_fails_question_of_pairs),
    ];
    for (what, family) in formulas {
        for n in [1, 2, 8, 40] {
            assert_eq!(decide(&family(n)), Ok(true), "{what}, {n}");
        }
    }
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
pub(super) fn falling_link(i: usize) -> String {
    format!(
        "p{i}(x: int) = q(x: x) && p{}(x: x - 30) && x < {};\n",
        i - 1,
        1000 * i
    )
}

/// A link of the drifting chain that moves its argument up by 12, twice the modulus of the
/// callee's remainders (LOAD-bound-holes).
pub(super) fn rising_link(i: usize) -> String {
    format!(
        "p{i}(x: int) = q(x: x) && p{}(x: x + 12) && x < {};\n",
        i - 1,
        1000 * i
    )
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
    // whole wherever that is decided, in both orders of the bodies: the 16th chain of seed
    // 0x401e5, whose `p9` holds where only the faces find the point (`Faces::free`), and 3
    // chains of a fresh seed. The 40 chains of seed 0x401e5, as first written, are in
    // `bench::one_scope` (2.8 s at load 25; they give 1510 answers of the whole, measured).
    let mut rng = zed_tests::instances::Rng::new(0x401e5);
    for _ in 0..15 {
        random_hole_chain(&mut rng);
    }
    let src = random_hole_chain(&mut rng);
    assert!(
        src.contains("p9("),
        "the 16th chain of seed 0x401e5 has a `p9`\n{src}"
    );
    assert!(answers_with_faces_are_those_without(&src) > 0, "{src}");
    let (mut rng, _) = zed_tests::instances::Rng::fresh("random chains moving holes");
    let decided = random_hole_chains_decided(&mut rng, 3);
    assert!(decided >= 12, "{decided} answers of the whole");
}

/// The answers of the whole decided over `count` chains of [`random_hole_chain`], each checked
/// as [`answers_with_faces_are_those_without`] checks it.
pub(super) fn random_hole_chains_decided(
    rng: &mut zed_tests::instances::Rng,
    count: usize,
) -> usize {
    (0..count)
        .map(|_| answers_with_faces_are_those_without(&random_hole_chain(rng)))
        .sum()
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
pub(super) fn mod4_chain(n: usize) -> String {
    moved_chain(
        "(x < 10 || x > 20) && x mod 4 != 1 && x > 0 && x < 1000000",
        "x > 0",
        3,
        n,
        |i| 1000 * i as i64,
    )
}

/// The gap 10..=12 beside `x mod 4 != 1`, moved by 4 under `x < 4 i + 10`.
pub(super) fn gapped_chain(n: usize) -> String {
    moved_chain(
        "(x < 10 || x > 12) && x mod 4 != 1 && x < 1000000",
        "x > 13",
        4,
        n,
        |i| 4 * i as i64 + 10,
    )
}

/// The chain of the shared remainder by 6 moved by 12, past link 76.
pub(super) fn shared_remainder_chain(n: usize) -> String {
    let mut src = String::from(
        "q(x: int) = (x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50) && x > 0 \
         && x < 1000000;\np0(x: int) = x > 0;\n",
    );
    for i in 1..n {
        src.push_str(&rising_link(i));
    }
    src
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
pub(super) fn mod3_chain(n: usize) -> String {
    remainder_chain("(x mod 3) < 2", 1, n)
}

/// Below 4 by 5, moved by 1: no point from link 5 on.
pub(super) fn mod5_chain(n: usize) -> String {
    remainder_chain("x mod 5 < 4", 1, n)
}

/// Not 3 by 7, moved by 2: `x + 2 k` meets every residue by 7, so no point from link 7 on.
pub(super) fn mod7_chain(n: usize) -> String {
    remainder_chain("!(x mod 7 == 3)", 2, n)
}

/// Below 2 by 3, moved by 3, the modulus: every link keeps the residues 0 and 1.
pub(super) fn kept_residue_chain(n: usize) -> String {
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
    // that the points can be counted, and 4 random chains of a fresh seed. Only the faces
    // answer 12 questions of the chain by 3 moved by 1, 12 of the one not 2 by 3 moved by 4,
    // and 14 of the 40 random chains of seed 0x40d3c, which give 1156 answers of the whole
    // (measured); those 40, as first written, are in `bench::one_scope` (1.5 s with the rest at
    // load 25). Against the rows read one at a
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
    let (mut rng, _) = zed_tests::instances::Rng::fresh("random chains of remainders");
    let decided = random_remainder_chains_decided(&mut rng, 4);
    assert!(decided >= 8, "{decided} answers of the whole");
    // The chains of the scaling test, unbounded below: the answers written over quotients
    // and remainders are those reading the bodies again, and those of the whole where decided.
    for chain in [mod3_chain, mod5_chain, mod7_chain, kept_residue_chain] {
        answers_are_those_reading_bodies(&chain(10));
    }
}

/// The answers of the whole decided over `count` chains of [`random_remainder_chain`], each
/// checked as [`answers_with_faces_are_those_without`] checks it.
pub(super) fn random_remainder_chains_decided(
    rng: &mut zed_tests::instances::Rng,
    count: usize,
) -> usize {
    (0..count)
        .map(|_| answers_with_faces_are_those_without(&random_remainder_chain(rng)))
        .sum()
}

/// A chain of steps on the remainder by 10^9 + 7 (I49): `h{i}(x) = {step}` with `H` the link
/// below, one question `h{i}(x: x) == 9` for each link.
fn residue_step_chain(step: &str, n: usize) -> String {
    let mut src = String::from("h0(x: int) = x;\n");
    for i in 1..n {
        let below = format!("h{}(x: x)", i - 1);
        src += &format!("h{i}(x: int) = {};\n", step.replace('H', &below));
        src += &format!("t{i}(x: int) = h{i}(x: x) == 9;\n");
    }
    src
}

pub(super) fn two_guards_chain(n: usize) -> String {
    residue_step_chain(
        "if H mod 1000000007 == 0 { H + 1 } else { if H mod 1000000007 == 3 { H + 2 } else { H + 3 } }",
        n,
    )
}

pub(super) fn affine_default_chain(n: usize) -> String {
    residue_step_chain(
        "if H mod 1000000007 == 2 { H + 5 } else { H mod 1000000007 * 2 + H + 1 }",
        n,
    )
}

/// The steps `if H mod 1000 == 0 { H + 1 } else { H + 3 }` and `H mod 1000 + H + 1`
/// alternating: the second doubles the residue, a multiplier that is no unit mod 1000.
pub(super) fn doubling_chain(n: usize) -> String {
    let mut src = String::from("h0(x: int) = x;\n");
    for i in 1..n {
        let below = format!("h{}(x: x)", i - 1);
        let step = if i % 2 == 1 {
            "if H mod 1000 == 0 { H + 1 } else { H + 3 }"
        } else {
            "H mod 1000 + H + 1"
        };
        src += &format!("h{i}(x: int) = {};\n", step.replace('H', &below));
        src += &format!("t{i}(x: int) = h{i}(x: x) == 9;\n");
    }
    src
}

/// One exception and the default `2 r + 1` on the remainder r by 2^40, again no unit.
pub(super) fn power_of_two_default_chain(n: usize) -> String {
    let mut src = String::from("h0(x: int) = x;\n");
    for i in 1..n {
        let below = format!("h{}(x: x)", i - 1);
        let step = "if H mod 1099511627776 == 5 { H + 7 } else { H mod 1099511627776 + H + 1 }";
        src += &format!("h{i}(x: int) = {};\n", step.replace('H', &below));
        src += &format!("t{i}(x: int) = h{i}(x: x) == 9;\n");
    }
    src
}

/// The residue r by M = 2^10 3^10 5^10 doubled 12 times and multiplied by 6 12 times, so
/// the coset c + d Z has d = 2^10 3^10; then the default 2 r + 7, a unit on the coset but
/// not mod M, with an exception at a point of the coset sent to H + b outside it.
pub(super) fn nonunit_persist_chain(n: usize) -> String {
    let m: i128 = 590_490_000_000_000;
    let (mut c, mut d, mut seed): (i128, i128, i128) = (0, 1, 12345);
    let mut src = String::from("h0(x: int) = x;\n");
    for i in 1..n {
        let below = format!("h{}(x: x)", i - 1);
        let (u, step) = if i <= 12 {
            (2, format!("H mod {m} + H + 1"))
        } else if i <= 24 {
            (6, format!("5 * (H mod {m}) + H + 1"))
        } else {
            seed = (seed * 6364136223846793005 + 1442695040888963407).rem_euclid(1 << 61);
            let s = c + d * (seed % (m / d));
            let b = seed % m;
            (
                2,
                format!("if H mod {m} == {s} {{ H + {b} }} else {{ H mod {m} + H + 7 }}"),
            )
        };
        let image_c = u * c + if i <= 24 { 1 } else { 7 };
        d *= num_gcd(u, m / d);
        c = image_c.rem_euclid(d);
        src += &format!("h{i}(x: int) = {};\n", step.replace('H', &below));
        src += &format!("t{i}(x: int) = h{i}(x: x) == 9;\n");
    }
    src
}

fn num_gcd(a: i128, b: i128) -> i128 {
    if b == 0 { a } else { num_gcd(b, a % b) }
}

/// The steps of `steps` in turn, `H` the link below, one question `h{i}(x: x) == 9` for each
/// link (LOAD-max-div-unsolved).
fn residue_cycle_chain(steps: &[&str], n: usize) -> String {
    let mut src = String::from("h0(x: int) = x;\n");
    for i in 1..n {
        let below = format!("h{}(x: x)", i - 1);
        let step = steps[(i - 1) % steps.len()];
        src += &format!("h{i}(x: int) = {};\n", step.replace('H', &below));
        src += &format!("t{i}(x: int) = h{i}(x: x) == 9;\n");
    }
    src
}

pub(super) fn gap_chain(n: usize) -> String {
    residue_cycle_chain(
        &["if H mod 1000000000000000009 < 500000000000000004 { H + 2 } else { H + 3 }"],
        n,
    )
}

pub(super) fn gap_wide_chain(n: usize) -> String {
    residue_cycle_chain(
        &["if H mod 2147483647 <= 256212016 { H + 1078571416 } else { H + 1078862839 }"],
        n,
    )
}

pub(super) fn cuts_reversed_chain(n: usize) -> String {
    residue_cycle_chain(
        &["if H mod 2147483647 > 1052672391 { H - 3 } else { \
           if H mod 2147483647 >= 836588177 { H - 1 } else { H + 4 } }"],
        n,
    )
}

pub(super) fn two_cut_steps_chain(n: usize) -> String {
    residue_cycle_chain(
        &[
            "if H mod 2147483647 <= 123816978 { H + 4 } else { \
             if H mod 2147483647 <= 802667210 { H - 2 } else { \
             if H mod 2147483647 < 1292311792 { H - 1 } else { H + 1 } } }",
            "if H mod 2147483647 >= 1189548973 { H + 1 } else { \
             if H mod 2147483647 > 6544298 { H - 2 } else { H + 3 } }",
        ],
        n,
    )
}

pub(super) fn overlap_chain(n: usize) -> String {
    residue_cycle_chain(
        &[
            "if H mod 2147483647 <= 1482723311 { H + 639840854 } else { \
             if H mod 2147483647 >= 1707665179 { H + 1185233016 } else { \
             if H mod 2147483647 == 2023896565 { H - 2022907152 } else { H - 1050355654 } } }",
            "if H mod 2147483647 <= 243107963 { H - 512140849 } else { \
             if H mod 2147483647 >= 798420159 { H + 1582461185 } else { H - 1924775623 } }",
            "if H mod 2147483647 <= 1232529314 { H - 2091158630 } else { H + 187951465 }",
        ],
        n,
    )
}

/// A random step on the remainder by `m`: nested ifs on `H mod m` against a constant, by any
/// of the six comparisons, each arm `H` plus a constant.
fn random_interval_step(rng: &mut zed_tests::instances::Rng, m: i64, depth: usize) -> String {
    if depth == 0 || rng.below(3) == 0 {
        return format!("H + {}", lit(rng.int(-m - 3, m + 3)));
    }
    let op = rng.pick(&["<", "<=", ">", ">=", "==", "!="]);
    format!(
        "if H mod {m} {op} {} {{ {} }} else {{ {} }}",
        rng.int(-1, m),
        random_interval_step(rng, m, depth - 1),
        random_interval_step(rng, m, depth - 1)
    )
}

#[test]
fn each_answer_of_a_random_chain_of_residue_intervals_is_the_answer_of_the_relation_whole() {
    // LOAD-max-div-unsolved: chains of one to three random steps repeated, on a small
    // modulus, so the images of the intervals of residues are checked against the relations
    // decided whole, and against those read with the bodies, in both orders: 2 chains of a
    // fresh seed. The 30 of seed 0x1a7e5, as first written, are in `bench::one_scope` (5.5 s at
    // load 25). Of 150 chains of 150 seeds, one took 3.4 s at load 50 (2026-11-14), so a fresh
    // seed may meet such a chain.
    let (mut rng, _) = zed_tests::instances::Rng::fresh("random chains of residue intervals");
    random_residue_interval_chains_are_answered(&mut rng, 2);
}

/// `count` chains of one to three steps of [`random_interval_step`] repeated over a modulus
/// up to 12: each answer is the one read with the bodies, and that of the whole where both
/// are decided.
pub(super) fn random_residue_interval_chains_are_answered(
    rng: &mut zed_tests::instances::Rng,
    count: usize,
) {
    for _ in 0..count {
        let m = rng.int(1, 12);
        let steps: Vec<String> = (0..rng.int(1, 3))
            .map(|_| random_interval_step(rng, m, 3))
            .collect();
        let steps: Vec<&str> = steps.iter().map(String::as_str).collect();
        answers_are_those_reading_bodies(&residue_cycle_chain(&steps, 4));
    }
}

pub(super) fn overlap0_chain(n: usize) -> String {
    residue_cycle_chain(
        &[
            "if H mod 1000000000039 > 283641720628 { H + 658457579784 } else { \
             if H mod 1000000000039 <= 444468675045 { H - 692889708465 } else { \
             if H mod 1000000000039 > 562492388602 { H + 961010693720 } else { \
             if H mod 1000000000039 > 862937245619 { H + 52128689504 } else { H + 957465508997 } } } }",
            "if H mod 1000000000039 < 339933610793 { H - 44997738144 } else { \
             if H mod 1000000000039 > 892086922017 { H + 230388484144 } else { \
             if H mod 1000000000039 < 990427627782 { H - 837951606572 } else { H + 357616960509 } } }",
        ],
        n,
    )
}

pub(super) fn overlap6_chain(n: usize) -> String {
    residue_cycle_chain(
        &[
            "if H mod 1000000000039 >= 158152503 { H + 185026886314 } else { \
             if H mod 1000000000039 <= 286741537907 { H + 918689987739 } else { \
             if H mod 1000000000039 < 517915006927 { H + 74913053309 } else { \
             if H mod 1000000000039 > 726474725831 { H + 693588865577 } else { H - 820376075153 } } } }",
            "if H mod 1000000000039 == 619304154366 { H + 772530957399 } else { H + 501259649241 }",
            "if H mod 1000000000039 > 467482632953 { H - 793883504583 } else { H - 417048865213 }",
        ],
        n,
    )
}

pub(super) fn overlap19_chain(n: usize) -> String {
    residue_cycle_chain(
        &[
            "if H mod 1000000000000000009 >= 230004752257195712 { H - 332769866151521114 } else { \
             H + 809882348088634981 }",
            "if H mod 1000000000000000009 == 300263638026952312 { H - 737383897398611170 } else { \
             if H mod 1000000000000000009 > 308880175046548076 { H + 312578100660941194 } else { \
             if H mod 1000000000000000009 < 377428464882423185 { H - 249448706446524513 } else { \
             H - 658136200048325540 } } }",
            "if H mod 1000000000000000009 <= 114552447213317321 { H + 468989834948122270 } else { \
             if H mod 1000000000000000009 > 477814012591389870 { H + 922627741251193726 } else { \
             if H mod 1000000000000000009 >= 845634005800345802 { H + 517911770091984596 } else { \
             if H mod 1000000000000000009 == 925864605666647035 { H - 24213642317013158 } else { \
             H + 50558164096615570 } } } }",
        ],
        n,
    )
}

/// A chain whose link i, from 1, is `step(i)` on the link below.
fn steps_chain(n: usize, mut step: impl FnMut(usize) -> String) -> String {
    let mut src = String::from("h0(x: int) = x;\n");
    for i in 1..n {
        let below = format!("h{}(x: x)", i - 1);
        src += &format!("h{i}(x: int) = {};\n", step(i).replace('H', &below));
        src += &format!("t{i}(x: int) = h{i}(x: x) == 9;\n");
    }
    src
}

/// Two halves of the residues by 10^12 + 39, the upper moved one further than the lower.
fn half_step(b: i64) -> String {
    format!(
        "if H mod 1000000000039 < 500000000019 {{ H + {b} }} else {{ H + {} }}",
        b + 1
    )
}

pub(super) fn random_cuts_chain(n: usize) -> String {
    let mut rng = zed_tests::instances::Rng::new(0x5ca1e);
    steps_chain(n, |_| {
        let (c, a, b) = (
            rng.int(0, 2147483646),
            rng.int(0, 2147483646),
            rng.int(0, 2147483646),
        );
        format!("if H mod 2147483647 <= {c} {{ H + {a} }} else {{ H + {b} }}")
    })
}

pub(super) fn random_small_moves_chain(n: usize) -> String {
    let mut rng = zed_tests::instances::Rng::new(0x5ca1e);
    steps_chain(n, |_| {
        let (c, a, b) = (rng.int(0, 2147483646), rng.int(0, 6), rng.int(0, 6));
        format!("if H mod 2147483647 <= {c} {{ H + {a} }} else {{ H + {b} }}")
    })
}

pub(super) fn switching_chain(n: usize) -> String {
    steps_chain(n, |i| {
        half_step(if ((i - 1) / 5) % 2 == 0 { 3 } else { -7 })
    })
}

pub(super) fn first_step_apart_chain(n: usize) -> String {
    steps_chain(n, |i| half_step(if i == 1 { -7 } else { 3 }))
}

pub(super) fn r6_local_source(family: &str, m: usize) -> String {
    let mut src = String::new();
    if family == "leaves" {
        let mut params = Vec::new();
        let mut conj = Vec::new();
        for i in 0..m {
            src += &format!("a{i}(x: int) = x div 3 + {i};\n");
            src += &format!("b{i}(x: int) = a{i}(x: x) div 2 + 1;\n");
            params.push(format!("x{i}: int"));
            conj.push(format!("b{i}(x: x{i}) > 0"));
        }
        src += &format!("t({}) = {};\n", params.join(", "), conj.join(" && "));
    } else {
        src += "b0(x: int) = x;\n";
        src += "b(x: int) = max(b0(x: x) div 2, x - 9);\n";
        src += "p0(x: int) = b(x: x) + 1;\nq0(x: int) = b(x: x) - 1;\n";
        for i in 1..m {
            src += &format!("p{i}(x: int) = p{}(x: x) div 2 + 1;\n", i - 1);
            src += &format!("q{i}(x: int) = q{}(x: x) div 2 - 1;\n", i - 1);
            src += &format!("t{i}(x: int) = p{i}(x: x) + q{i}(x: x) > 0;\n");
        }
    }
    src
}

#[test]
fn division_by_minimum_i64_has_a_euclidean_remainder() {
    use zedc::store::presburger::extend::Extending;
    let src = "f(x: int) = x mod (0 - 9223372036854775808);\n\
        g(x: int) = x div (0 - 9223372036854775808);\n\
        t0(x: int) = x == 0 && f(x: x) == 0;\n\
        t1(x: int) = x == 1 && f(x: x) == 1;\n\
        t2(x: int) = x == 0 - 1 && f(x: x) == 9223372036854775807;\n\
        t3(x: int) = x == 1 && g(x: x) == 0;\n\
        t4(x: int) = x == 0 - 1 && g(x: x) == 1;\n";
    let unit = elab(src).unwrap();
    let ls = lets(&unit);
    let mut scoped = Scoped::new(&ls);
    let mut ext = Extending::new();
    let mut checked = 0;
    for (name, ps, body) in functions(&unit) {
        if !name.starts_with('t') {
            continue;
        }
        let r = scoped.relation(body, ps, ps, true).unwrap();
        let got = ext.defined_with(&r, &|n| scoped.def(n), &|f| scoped.interface(f));
        assert_eq!(got.holds, Ok(true), "{name}");
        checked += 1;
    }
    assert_eq!(checked, 5);
}

#[test]
fn periodic_joint_questions_keep_the_input_remainder_in_any_query_order() {
    use std::collections::{BTreeMap, BTreeSet};
    use zedc::store::presburger::extend::Extending;
    for m in [7i64, 1000, 1_000_000_007] {
        for skip in [false, true] {
            let mut src = "h0(x: int) = x;\n".to_string();
            let mut expected = BTreeMap::new();
            for i in 1..=8 {
                let h = format!("h{}(x: x)", i - 1);
                let step = if skip {
                    format!("if {h} mod {m} == 0 {{ {h} + 1 }} else {{ {h} + 2 }}")
                } else {
                    format!("{h} mod {m} + {h}")
                };
                src += &format!("h{i}(x: int) = {step};\n");
                for (j, r, c) in [(0, 0i64, 0i64), (1, 3, 9)] {
                    let name = format!("t{i}c{j}");
                    src += &format!("{name}(x: int) = x mod {m} == {r} && h{i}(x: x) == {c};\n");
                    // Exhaust EVERY integer preimage of c, by the inverse branches of
                    // the native recurrence. This is a complete oracle, not an x window.
                    let mut pre = BTreeSet::from([c]);
                    for _ in 0..i {
                        let mut next = BTreeSet::new();
                        for y in pre {
                            if skip {
                                if (y - 1).rem_euclid(m) == 0 {
                                    next.insert(y - 1);
                                }
                                if (y - 2).rem_euclid(m) != 0 {
                                    next.insert(y - 2);
                                }
                            } else {
                                let q = y.div_euclid(m);
                                for quotient in [q - 1, q] {
                                    let twice = y - m * quotient;
                                    if twice >= 0 && twice <= 2 * (m - 1) && twice % 2 == 0 {
                                        next.insert(m * quotient + twice / 2);
                                    }
                                }
                            }
                        }
                        pre = next;
                    }
                    expected.insert(name, pre.iter().any(|x| x.rem_euclid(m) == r));
                }
            }
            let unit = elab(&src).unwrap();
            let ls = lets(&unit);
            let functions: Vec<_> = functions(&unit)
                .into_iter()
                .filter(|(name, _, _)| name.starts_with('t'))
                .collect();
            for mode in 0..3 {
                let mut scoped = Scoped::new(&ls);
                let mut ext = Extending::new();
                let order: Vec<_> = if mode == 1 {
                    (0..functions.len()).rev().collect()
                } else {
                    (0..functions.len()).collect()
                };
                for i in order {
                    if mode == 2 {
                        scoped = Scoped::new(&ls);
                        ext = Extending::new();
                    }
                    let (name, ps, body) = functions[i];
                    let q = scoped.relation(body, ps, ps, true).unwrap();
                    let a = ext.defined_with(&q, &|n| scoped.def(n), &|f| scoped.interface(f));
                    assert_eq!(
                        a.holds,
                        Ok(expected[name]),
                        "{name}, M={m}, skip={skip}, mode={mode}"
                    );
                    assert_eq!(a.fails, Ok(true));
                }
            }
        }
    }
}

#[test]
fn monotone_clamp_equalities_of_5_7_less_9_match_inverse_cuts_in_any_query_order() {
    clamp_equalities_match_inverse_cuts(5, 7, -9, 5);
}

#[test]
fn monotone_clamp_equalities_of_1_3_plus_4_match_inverse_cuts_in_any_query_order() {
    clamp_equalities_match_inverse_cuts(1, 3, 4, 5);
}

#[test]
fn monotone_clamp_equalities_of_7_11_match_inverse_cuts_in_any_query_order() {
    clamp_equalities_match_inverse_cuts(7, 11, 0, 5);
}

/// The chain `h{k}(x) = max(h{k-1}(x: x) div 2, x div a + x div b + offset)` of `depth` links,
/// with the tests `h{k}(x: x) == c` for seven constants `c` and `x == 0 && h{k}(x: x) ==
/// h{k}(0)` at each link: each answer is the one found by the inverse cuts of the value, in the
/// unit's order, in reverse, and each test alone. The three cases of the one test first
/// written are three tests, at 5 links; at 8, as first written, they are in `bench::one_scope`
/// (2.6 s together at load 25).
pub(super) fn clamp_equalities_match_inverse_cuts(a: i128, b: i128, offset: i128, depth: usize) {
    use std::collections::BTreeMap;
    use zedc::store::presburger::extend::Extending;
    let literal = |c: i128| {
        if c < 0 {
            format!("(0 - {})", -c)
        } else {
            c.to_string()
        }
    };
    let mut src = "h0(x: int) = x;\n".to_string();
    let mut expected = BTreeMap::new();
    for k in 1..=depth {
        let h = format!("h{}(x: x)", k - 1);
        src += &format!(
            "h{k}(x: int) = max({h} div 2, x div {a} + x div {b} + {});\n",
            literal(offset)
        );
        let value = |x: i128| {
            let bound = x.div_euclid(a) + x.div_euclid(b) + offset;
            let mut h = x;
            for _ in 0..k {
                h = h.div_euclid(2).max(bound);
            }
            h
        };
        let cut = |c: i128| {
            let mut lo = -1;
            let mut hi = 1;
            while value(lo) >= c {
                lo *= 2;
            }
            while value(hi) < c {
                hi *= 2;
            }
            while hi - lo > 1 {
                let mid = (hi + lo).div_euclid(2);
                if value(mid) >= c {
                    hi = mid;
                } else {
                    lo = mid;
                }
            }
            hi
        };
        for (j, c) in [-12i128, -9, -1, 0, 1, 9, 12].into_iter().enumerate() {
            let name = format!("t{k}c{j}");
            src += &format!("{name}(x: int) = h{k}(x: x) == {};\n", literal(c));
            expected.insert(name, cut(c) < cut(c + 1));
        }
        let name = format!("t{k}joint");
        src += &format!(
            "{name}(x: int) = x == 0 && h{k}(x: x) == {};\n",
            literal(value(0))
        );
        expected.insert(name, true);
    }
    let unit = elab(&src).unwrap();
    let ls = lets(&unit);
    let functions: Vec<_> = functions(&unit)
        .into_iter()
        .filter(|(n, _, _)| n.starts_with('t'))
        .collect();
    for mode in 0..3 {
        let mut scoped = Scoped::new(&ls);
        let mut ext = Extending::new();
        let order: Vec<_> = if mode == 1 {
            (0..functions.len()).rev().collect()
        } else {
            (0..functions.len()).collect()
        };
        for i in order {
            if mode == 2 {
                scoped = Scoped::new(&ls);
                ext = Extending::new();
            }
            let (name, ps, body) = functions[i];
            let q = scoped.relation(body, ps, ps, true).unwrap();
            let answer = ext.defined_with(&q, &|n| scoped.def(n), &|f| scoped.interface(f));
            assert_eq!(
                answer.holds,
                Ok(expected[name]),
                "{name} a={a} b={b} C={offset} mode={mode}"
            );
            assert_eq!(answer.fails, Ok(true));
        }
    }
}

pub(super) fn r6_periodic_value_questions(n: usize, step: &str, test: &str) -> String {
    let mut src = "h0(x: int) = x;\n".to_string();
    for i in 1..=n {
        let previous = format!("h{}(x: x)", i - 1);
        src += &format!("h{i}(x: int) = {};\n", step.replace('H', &previous));
        let current = format!("h{i}(x: x)");
        src += &format!(
            "t{i}(x: int) = {};\n",
            test.replace('H', &current).replace('P', &previous)
        );
    }
    src
}

#[test]
fn periodic_adjacent_questions_keep_the_previous_link_remainder_in_any_order() {
    use std::collections::{BTreeMap, BTreeSet};
    use zedc::store::presburger::extend::Extending;
    for m in [7i64, 1000, 1_000_000_007] {
        for skip in [false, true] {
            let step = |h: i64| {
                if skip {
                    h + if h.rem_euclid(m) == 0 { 1 } else { 2 }
                } else {
                    h + h.rem_euclid(m)
                }
            };
            let mut src = "h0(x: int) = x;\n".to_string();
            let mut expected = BTreeMap::new();
            for k in 1..=8 {
                let h = format!("h{}(x: x)", k - 1);
                let update = if skip {
                    format!("if {h} mod {m} == 0 {{ {h} + 1 }} else {{ {h} + 2 }}")
                } else {
                    format!("{h} mod {m} + {h}")
                };
                src += &format!("h{k}(x: int) = {update};\n");
                for (j, c, r) in [(0, 0i64, 0i64), (1, 5, 3), (2, 6, 3), (3, 9, 3)] {
                    let name = format!("t{k}c{j}");
                    src += &format!("{name}(x: int) = {h} mod {m} == {r} && h{k}(x: x) == {c};\n");
                    let mut pre = BTreeSet::from([c]);
                    for i in 0..k {
                        let mut next = BTreeSet::new();
                        for y in pre {
                            if skip {
                                if (y - 1).rem_euclid(m) == 0 {
                                    next.insert(y - 1);
                                }
                                if (y - 2).rem_euclid(m) != 0 {
                                    next.insert(y - 2);
                                }
                            } else {
                                let q = y.div_euclid(m);
                                for quotient in [q - 1, q] {
                                    let twice = y - m * quotient;
                                    if twice >= 0 && twice <= 2 * (m - 1) && twice % 2 == 0 {
                                        next.insert(m * quotient + twice / 2);
                                    }
                                }
                            }
                        }
                        if i == 0 {
                            next.retain(|h| h.rem_euclid(m) == r);
                        }
                        pre = next;
                    }
                    expected.insert(name, !pre.is_empty());
                }
                let name = format!("t{k}future");
                src += &format!("{name}(x: int) = {h} == 9 && h{k}(x: x) mod {m} == 3;\n");
                let mut pre = BTreeSet::from([9i64]);
                for _ in 0..k - 1 {
                    let mut next = BTreeSet::new();
                    for y in pre {
                        if skip {
                            if (y - 1).rem_euclid(m) == 0 {
                                next.insert(y - 1);
                            }
                            if (y - 2).rem_euclid(m) != 0 {
                                next.insert(y - 2);
                            }
                        } else {
                            let q = y.div_euclid(m);
                            for quotient in [q - 1, q] {
                                let twice = y - m * quotient;
                                if twice >= 0 && twice <= 2 * (m - 1) && twice % 2 == 0 {
                                    next.insert(m * quotient + twice / 2);
                                }
                            }
                        }
                    }
                    pre = next;
                }
                expected.insert(name, !pre.is_empty() && step(9).rem_euclid(m) == 3);
            }
            let unit = elab(&src).unwrap();
            let ls = lets(&unit);
            let functions: Vec<_> = functions(&unit)
                .into_iter()
                .filter(|(name, _, _)| name.starts_with('t'))
                .collect();
            for mode in 0..3 {
                let mut scoped = Scoped::new(&ls);
                let mut ext = Extending::new();
                let order: Vec<_> = if mode == 1 {
                    (0..functions.len()).rev().collect()
                } else {
                    (0..functions.len()).collect()
                };
                for i in order {
                    if mode == 2 {
                        scoped = Scoped::new(&ls);
                        ext = Extending::new();
                    }
                    let (name, ps, body) = functions[i];
                    let q = scoped.relation(body, ps, ps, true).unwrap();
                    let answer = ext.defined_with(&q, &|n| scoped.def(n), &|f| scoped.interface(f));
                    assert_eq!(
                        answer.holds,
                        Ok(expected[name]),
                        "{name} M={m} skip={skip} mode={mode}"
                    );
                    assert_eq!(answer.fails, Ok(true));
                }
            }
        }
    }
}

#[test]
fn every_question_of_a_random_chain_with_negations_matches_enumeration() {
    // PNCX-modular: every question of chain 8 of the ten random negated chains of seed 0x5eed1
    // (PERF-negated-chain) is checked as [`negated_chain_matches_enumeration`] checks it. The
    // ten, as first written, are in `bench::one_scope` (3.5 s at load 25).
    negated_chain_matches_enumeration(8, &negated_chains_of_seed_0x5eed1()[8]);
}

/// The ten random negated chains of seed 0x5eed1 ([`random_negated_chain`]).
pub(super) fn negated_chains_of_seed_0x5eed1() -> Vec<String> {
    let mut rng = zed_tests::instances::Rng::new(0x5eed1);
    (0..10).map(|_| random_negated_chain(&mut rng)).collect()
}

/// Every question of the negated chain `src` (number `chain_idx` in messages) is decided in
/// both orders of the definitions, with faces, without faces, and decided whole, with zero
/// refusals, and each answer matches point-by-point enumeration; the number of answers.
pub(super) fn negated_chain_matches_enumeration(chain_idx: usize, src: &str) -> usize {
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Formula, decide};
    let mut total_decided = 0;
    let unit = elab(src).unwrap_or_else(|e| panic!("chain {chain_idx}: {e:?}"));
    let cones = Cones::new(&unit);
    let lets = lets(&unit);
    let fs = functions(&unit);
    let whole = |r: &Relation, f: Formula| decide(&Formula::and(vec![r.defined(), f]));
    let want_by_fn: Vec<(bool, bool)> = {
        let mut scoped = Scoped::new(&lets);
        (0..fs.len())
            .map(|i| {
                let (name, ps, body) = fs[i];
                let r = scoped.relation(body, ps, ps, true).expect(name);
                let w = scoped.written(&r);
                if name == "p0" {
                    (true, true)
                } else {
                    enumerated(&w)
                }
            })
            .collect()
    };
    for order in [
        (0..fs.len()).collect::<Vec<_>>(),
        (0..fs.len()).rev().collect(),
    ] {
        let mut scoped = Scoped::new(&lets);
        let (mut faced, mut plain) = (Extending::new(), Extending::new());
        for i in order {
            let (name, ps, body) = fs[i];
            let expected = closed(&cones, ps, body).expect(name);
            let r = scoped.relation(body, ps, ps, true).expect(name);
            let a = faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            let b = plain.defined(&r, &|n| scoped.def(n));
            let (want_holds, want_fails) = want_by_fn[i];
            assert_eq!(
                a.holds,
                Ok(want_holds),
                "chain {chain_idx} `{name}` holds (faced)"
            );
            assert_eq!(
                b.holds,
                Ok(want_holds),
                "chain {chain_idx} `{name}` holds (plain)"
            );
            assert_eq!(
                whole(&expected, expected.body.clone()),
                Ok(want_holds),
                "chain {chain_idx} `{name}` holds (whole)"
            );
            assert_eq!(
                a.fails,
                Ok(want_fails),
                "chain {chain_idx} `{name}` fails (faced)"
            );
            assert_eq!(
                b.fails,
                Ok(want_fails),
                "chain {chain_idx} `{name}` fails (plain)"
            );
            assert_eq!(
                whole(&expected, Formula::negate(expected.body.clone())),
                Ok(want_fails),
                "chain {chain_idx} `{name}` fails (whole)"
            );
            total_decided += 2;
        }
    }
    total_decided
}

// A renaming of a test formula: its label, the name of alias `k`, and the new index of
// auxiliary atom `i`.
type Naming<'a> = (&'a str, &'a dyn Fn(usize) -> String, &'a dyn Fn(u32) -> u32);
// A case of `easy_clause_systems_over_several_moduli_keep_their_answers`: pairs of moduli `(a, b)`,
// each with its residues `r` (one clause `x mod a == r || x mod b == r` per `r`), an optional
// interval of `x`, and whether the solver answers `holds`.
type ResidueCase<'a> = (Vec<((i64, i64), &'a [i64])>, Option<(i64, i64)>, bool);

#[test]
fn one_variable_modular_formulas_match_enumeration() {
    // PNCX-modular: 800 random one-variable modular formulas of a fresh seed, checked as
    // [`modular_formulas_match`] checks them. The 5,000 of seed 0x70de_c1de, as first written,
    // with their counts of refusals and of empty answers, are in `bench::one_scope` (1.5 s at
    // load 25).
    let (mut rng, _) = zed_tests::instances::Rng::fresh("one-variable modular formulas");
    let counts = modular_formulas_match(&mut rng, 800);
    assert!(
        counts.sat >= 80 && counts.unsat >= 40 && counts.empty_agreed >= 40,
        "{counts:?}"
    );
}

/// What [`modular_formulas_match`] counted: answers with a point and with none, refusals,
/// and the empty answers of the one-variable path the general path agreed with, refused, and
/// refused with `x` unbounded above.
#[derive(Debug)]
pub(super) struct ModularCounts {
    pub(super) sat: usize,
    pub(super) unsat: usize,
    pub(super) refused: usize,
    pub(super) empty_agreed: usize,
    pub(super) empty_refused: usize,
    pub(super) empty_unchecked: usize,
}

/// `count` random one-variable modular formulas of [`modular_case`] with unit equalities
/// (`x@k = ±x@{k-1} + c`), Euclidean divisions (`x + c == m * q + r && 0 <= r < m`), primes,
/// prime powers and composite moduli, negative, zero-crossing and large positive intervals,
/// short, long and semi-bounded intervals, negated conjunctions and disjunctive clauses:
/// `decide` and `satisfiable` agree with point-by-point enumeration, and every witness
/// satisfies `f`, wherever they answer.
pub(super) fn modular_formulas_match(
    rng: &mut zed_tests::instances::Rng,
    count: usize,
) -> ModularCounts {
    use zedc::store::int::Int;
    use zedc::store::presburger::{Model, decide, satisfiable, with_modular_empty_checked};
    let (mut sat_count, mut unsat_count, mut refused) = (0usize, 0usize, 0usize);
    let (mut empty_agreed, mut empty_refused, mut empty_unchecked) = (0usize, 0usize, 0usize);

    for case_idx in 0..count {
        let (f, x0, copies, divs, lo, hi, is_bounded) = modular_case(rng, case_idx);
        // Each answer of the one-variable path that a formula asked has no point is asked again
        // of the general path, which must not find one (R3-CLAUDE-6). One the general path
        // refuses is checked by the enumeration below where `x` is bounded, and by nothing
        // where it is not (`empty_unchecked`).
        let (answers, check) = with_modular_empty_checked(|| (decide(&f), satisfiable(&f)));
        assert!(
            check.wrong.is_empty(),
            "case {case_idx}: the general path finds a point of {f}"
        );
        empty_agreed += check.agreed;
        empty_refused += check.refused.len();
        if !is_bounded {
            empty_unchecked += check.refused.len();
        }
        let (Ok(dec), Ok(sat)) = answers else {
            // PNCX_SHOW: each refused case, for the list of refusals (I5.14).
            // With `x` unbounded above, enumeration runs to `lo + 100000`, past every period
            // and constant the generator writes.
            if std::env::var_os("PNCX_SHOW").is_some() {
                let top = if is_bounded { hi } else { lo + 100_000 };
                let found = (lo..=top).find(|&xv| {
                    let mut m = Model::new();
                    m.insert(x0.clone(), Int::from(xv));
                    for (a, s, off) in &copies[1..] {
                        m.insert(a.clone(), Int::from(s * xv + off));
                    }
                    for (qa, ra, mod_m, cs, coff) in &divs {
                        let u = cs * xv + coff;
                        m.insert(qa.clone(), Int::from(u.div_euclid(*mod_m)));
                        m.insert(ra.clone(), Int::from(u.rem_euclid(*mod_m)));
                    }
                    f.holds(&m)
                });
                println!(
                    "REFUSED case {case_idx} bounded={is_bounded} lo={lo} hi={hi} decide={} \
                     satisfiable={} brute={found:?}: {f}",
                    answers.0.is_ok(),
                    answers.1.is_ok()
                );
            }
            refused += 1;
            continue;
        };
        assert_eq!(dec, sat.is_some(), "case {case_idx}: decide vs satisfiable");
        if let Some(ref model) = sat {
            assert!(
                f.holds(model),
                "case {case_idx}: returned model {model:?} does not satisfy {f}"
            );
            sat_count += 1;
        } else {
            unsat_count += 1;
        }

        if is_bounded {
            let brute = (lo..=hi).any(|xv| {
                let mut m = Model::new();
                m.insert(x0.clone(), Int::from(xv));
                for (a, s, off) in &copies[1..] {
                    m.insert(a.clone(), Int::from(s * xv + off));
                }
                for (qa, ra, mod_m, cs, coff) in &divs {
                    let u = cs * xv + coff;
                    m.insert(qa.clone(), Int::from(u.div_euclid(*mod_m)));
                    m.insert(ra.clone(), Int::from(u.rem_euclid(*mod_m)));
                }
                f.holds(&m)
            });
            assert_eq!(
                dec, brute,
                "case {case_idx}: solver={dec} vs brute={brute}\n{f}"
            );
        }
    }
    ModularCounts {
        sat: sat_count,
        unsat: unsat_count,
        refused,
        empty_agreed,
        empty_refused,
        empty_unchecked,
    }
}

/// `f` with each variable `x@k` (`x` for `k = 0`) named `name(k)` and each quotient or remainder
/// `Aux(i)` numbered `aux(i)`.
fn renamed(
    f: &zedc::store::presburger::Formula,
    name: &dyn Fn(usize) -> String,
    aux: &dyn Fn(u32) -> u32,
) -> zedc::store::presburger::Formula {
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    f.map_cons(&|c: &Con| {
        let mut lin = Lin::constant(c.lin.constant.clone());
        for (a, k) in &c.lin.terms {
            let b = match a {
                Atom::Sym(s) => {
                    let k = s.strip_prefix("x@").map_or(0, |n| n.parse().unwrap());
                    Atom::Sym(Arc::from(name(k)))
                }
                Atom::Aux(i) => Atom::Aux(aux(*i)),
                other => other.clone(),
            };
            lin = lin.plus(&Lin::atom(b).times(k.clone()));
        }
        Formula::Con(Con { lin, rel: c.rel })
    })
}

#[test]
fn one_variable_answers_do_not_depend_on_names() {
    // I4.15: the one-variable path worked in the coordinate of the root of its affine
    // union-find, the lexically least name, and tried the point 1 there, so renaming an alias
    // changed a refusal into an answer. Each formula of the enumeration test is asked again
    // with its variables renamed in four patterns (aliases before and after `x`,
    // with `x` itself renamed), and with its quotients and remainders
    // numbered in reverse; `decide` and `satisfiable` give the same answer, refusal included,
    // and `satisfiable` asked first gives the same answers too. `PNCX_CASES=a..b` runs part.
    use zedc::store::presburger::{decide, satisfiable};
    let (from, to) = std::env::var("PNCX_CASES").map_or((0, 150), |s| {
        let (a, b) = s.split_once("..").unwrap();
        (a.parse().unwrap(), b.parse().unwrap())
    });
    let namings: [Naming<'_>; 4] = [
        ("aliases after", &|k| format!("x{k}"), &|i| i),
        (
            "aliases before",
            &|k| ["z", "a", "b", "c"][k].to_string(),
            &|i| i,
        ),
        (
            "interleaved",
            &|k| ["m", "z", "a", "n"][k].to_string(),
            &|i| 99 - i,
        ),
        ("reversed", &|k| format!("v{}", 9 - k), &|i| 99 - i),
    ];
    // 150 cases drawn with a new seed each run (author P169; 5,000 at one seed took 12 s).
    let (mut rng, _) = zed_tests::instances::Rng::fresh("one-variable cases renamed");
    let (mut differ, mut answered) = (Vec::new(), 0usize);
    for case_idx in 0..to {
        let (f, ..) = modular_case(&mut rng, case_idx);
        if case_idx < from {
            continue;
        }
        let answer = |g: &zedc::store::presburger::Formula, sat_first: bool| {
            let (d, s) = if sat_first {
                let s = satisfiable(g);
                (decide(g), s)
            } else {
                let d = decide(g);
                (d, satisfiable(g))
            };
            (d.ok(), s.ok().map(|m| m.is_some()))
        };
        let base = answer(&f, false);
        answered += usize::from(base.0.is_some());
        for (label, name, aux) in &namings {
            let g = renamed(&f, name, aux);
            for sat_first in [false, true] {
                let got = answer(&g, sat_first);
                if got != base {
                    differ.push(format!(
                        "case {case_idx} {label} sat_first={sat_first}: {got:?} against {base:?}\n  {g}"
                    ));
                }
            }
        }
    }
    println!(
        "renamed cases {from}..{to}: {answered} answered, {} differ",
        differ.len()
    );
    assert!(differ.is_empty(), "{}", differ.join("\n"));
}

/// `f` with `x` (the variable `x@0`) replaced by `s * x + d`.
fn moved(f: &zedc::store::presburger::Formula, s: i64, d: i64) -> zedc::store::presburger::Formula {
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    let x = Atom::Sym(Arc::from("x"));
    f.map_cons(&|c: &Con| {
        let mut lin = Lin::constant(c.lin.constant.clone());
        for (a, k) in &c.lin.terms {
            if *a == x {
                lin = lin
                    .plus(&Lin::atom(x.clone()).times(k.clone()).times(s))
                    .plus(&Lin::constant(d).times(k.clone()));
            } else {
                lin = lin.plus(&Lin::atom(a.clone()).times(k.clone()));
            }
        }
        Formula::Con(Con { lin, rel: c.rel })
    })
}

// I6.16 split the whole test, more than 20 s at load 40, into quarters of 1,500 cases with no
// bound and halves of 1,500 with one bound, at one seed. Each test now draws its cases with a
// new seed each run (author P169): 30 with no bound (the slowest kind), 100 with each bound.
#[test]
fn one_variable_answers_with_no_bound_do_not_depend_on_names() {
    one_bound_or_none_names(Some("none"), 0, 30);
}

#[test]
fn one_variable_answers_with_a_lower_bound_do_not_depend_on_names() {
    one_bound_or_none_names(Some("lo"), 0, 100);
}

#[test]
fn one_variable_answers_with_an_upper_bound_do_not_depend_on_names() {
    one_bound_or_none_names(Some("hi"), 0, 100);
}

/// The cases `from..to` of the kind of bound `only` (`none`, `lo` or `hi`; all three when
/// `None`) of the test below.
fn one_bound_or_none_names(only: Option<&str>, from: usize, to: usize) {
    // I5.3: the canonical coordinate of round 5 is chosen only where a regime has two bounds; a
    // regime with one bound or none is solved in the coordinate of the root of the affine
    // union-find, which a renaming changes. Formulas of `modular_case` with no bound on `x`, with
    // only `x >= lo` and with only `x <= hi` are asked under the four namings of
    // `one_variable_answers_do_not_depend_on_names`, in both orders, and with `x` replaced by
    // `x + d` and `-x + d`; every answer, refusal included, is the same. Each answer is checked
    // by enumeration where the period `L` (the lcm of the moduli) is at most 30,000: over
    // `[0, L)` with no bound, and over the bound and one period past the last number a clause
    // compares `x` with otherwise, which is exact because past it every clause is periodic in
    // `x` with period `L`.
    use zedc::store::int::Int;
    use zedc::store::presburger::{Model, decide, satisfiable};
    let namings: [Naming<'_>; 4] = [
        ("aliases after", &|k| format!("x{k}"), &|i| i),
        (
            "aliases before",
            &|k| ["z", "a", "b", "c"][k].to_string(),
            &|i| i,
        ),
        (
            "interleaved",
            &|k| ["m", "z", "a", "n"][k].to_string(),
            &|i| 99 - i,
        ),
        ("reversed", &|k| format!("v{}", 9 - k), &|i| 99 - i),
    ];
    let answer = |g: &zedc::store::presburger::Formula, sat_first: bool| {
        let (d, s) = if sat_first {
            let s = satisfiable(g);
            (decide(g), s)
        } else {
            let d = decide(g);
            (d, satisfiable(g))
        };
        if let Ok(Some(model)) = &s {
            assert!(g.holds(model), "a model that does not satisfy {g}");
        }
        (d.ok(), s.ok().map(|m| m.is_some()))
    };
    let gcd = |mut a: i64, mut b: i64| {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    let (mut differ, mut moved_differ) = (Vec::new(), Vec::new());
    for (label, sides) in [
        ("none", (false, false)),
        ("lo", (true, false)),
        ("hi", (false, true)),
    ] {
        if only.is_some_and(|o| o != label) {
            continue;
        }
        let (mut rng, _) =
            zed_tests::instances::Rng::fresh(&format!("one-variable cases, bound {label}"));
        let (mut sat, mut empty, mut refused, mut unchecked) = (0usize, 0usize, 0usize, 0usize);
        for case_idx in 0..to {
            let (f, x0, copies, divs, lo, hi, _) =
                modular_case_with(&mut rng, case_idx, Some(sides));
            if case_idx < from {
                continue;
            }
            // The answer by enumeration, where the period is small enough to enumerate.
            let period = divs.iter().fold(1i64, |l, d| l / gcd(l, d.2) * d.2);
            let range = match sides {
                (false, false) => 0..=period - 1,
                (true, false) => lo..=hi + 20 + period,
                _ => lo - 20 - period..=hi,
            };
            let brute = (period <= 30_000).then(|| {
                range.into_iter().any(|xv| {
                    let mut m = Model::new();
                    m.insert(x0.clone(), Int::from(xv));
                    for (a, s, off) in &copies[1..] {
                        m.insert(a.clone(), Int::from(s * xv + off));
                    }
                    for (qa, ra, mod_m, cs, coff) in &divs {
                        let u = cs * xv + coff;
                        m.insert(qa.clone(), Int::from(u.div_euclid(*mod_m)));
                        m.insert(ra.clone(), Int::from(u.rem_euclid(*mod_m)));
                    }
                    f.holds(&m)
                })
            });
            let base = answer(&f, false);
            let mut variants: Vec<(String, zedc::store::presburger::Formula, bool)> =
                vec![("as written".to_string(), f.clone(), false)];
            for (name_label, name, aux) in &namings {
                for sat_first in [false, true] {
                    variants.push((name_label.to_string(), renamed(&f, name, aux), sat_first));
                }
            }
            for (s, d) in [(1, 7), (1, -1_000_003), (-1, 0), (-1, 1_000_003)] {
                variants.push((format!("x := {s}x + {d}"), moved(&f, s, d), false));
            }
            for (what, g, sat_first) in &variants {
                let got = answer(g, *sat_first);
                if let (Some(dec), Some(b)) = (got.0, brute) {
                    assert_eq!(
                        dec, b,
                        "{label} case {case_idx} {what}: solver={dec} vs brute={b}\n{g}"
                    );
                }
                if got != base {
                    let to = if what.starts_with("x :=") {
                        &mut moved_differ
                    } else {
                        &mut differ
                    };
                    to.push(format!(
                        "{label} case {case_idx} {what} sat_first={sat_first}: {got:?} against {base:?}\n  {g}"
                    ));
                }
            }
            let Some(dec) = base.0 else {
                refused += 1;
                continue;
            };
            if dec {
                sat += 1;
            } else {
                empty += 1;
            }
            unchecked += usize::from(brute.is_none());
        }
        println!(
            "{label}: cases {from}..{to}: satisfiable={sat} empty={empty} refused={refused}, \
             {unchecked} answers with a period over 30,000 not enumerated"
        );
    }
    // A shift or reflection of `x` in the formula changes its numbers, not its names; an answer
    // that becomes a refusal there is reported, not failed (the Complexity tradeoff comment of
    // `solve_regime`).
    println!(
        "{} answers differ under renaming; {} under a shift or reflection of x:\n{}",
        differ.len(),
        moved_differ.len(),
        moved_differ.join("\n")
    );
    assert!(differ.is_empty(), "{}", differ.join("\n"));
}

/// `q(x)` as the conjunction, for each pair `(a, b)` and each `r` of `rs`, of `x mod a == r ||
/// x mod b == r`, with `lo < x < hi` where a bound is given.
fn pair_clauses(pairs: &[((i64, i64), &[i64])], bound: Option<(i64, i64)>) -> String {
    let mut parts: Vec<String> = Vec::new();
    for &((a, b), rs) in pairs {
        for r in rs {
            parts.push(format!("(x mod {a} == {r} || x mod {b} == {r})"));
        }
    }
    if let Some((lo, hi)) = bound {
        parts.push(format!("x > {} && x < {hi}", lit(lo)));
    }
    format!("q(x: int) = {};", parts.join(" && "))
}

/// Whether `pair_clauses(pairs, bound)` holds somewhere, by enumeration: over the bound where
/// there is one, and otherwise over one period of each pair, which is exact because the moduli
/// of different pairs are coprime (checked).
fn pair_clauses_hold(pairs: &[((i64, i64), &[i64])], bound: Option<(i64, i64)>) -> bool {
    let at = |x: i64, ((a, b), rs): ((i64, i64), &[i64])| {
        rs.iter()
            .all(|&r| x.rem_euclid(a) == r || x.rem_euclid(b) == r)
    };
    if let Some((lo, hi)) = bound {
        return (lo + 1..hi).any(|x| pairs.iter().all(|&p| at(x, p)));
    }
    let gcd = |mut a: i64, mut b: i64| {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    for (i, &((a, b), _)) in pairs.iter().enumerate() {
        for &((c, d), _) in &pairs[i + 1..] {
            assert!([gcd(a, c), gcd(a, d), gcd(b, c), gcd(b, d)] == [1; 4]);
        }
    }
    pairs.iter().all(|&p| (0..p.0.0 * p.0.1).any(|x| at(x, p)))
}

#[test]
fn easy_clause_systems_over_several_moduli_keep_their_answers() {
    // PNCX-modular, R2: systems of two-modulus clauses such as `(x mod 5 == 0 || x mod 7 == 0) &&
    // (x mod 5 == 1 || x mod 7 == 1)` over several pairs of moduli, which the solver's general
    // path answers in milliseconds and the first version of the one-variable path refused: each
    // is answered, in both readings of the definition, as enumeration answers it. A pair with
    // three such clauses (`r` in 0, 1, 2) holds nowhere, since each modulus meets one of them.
    let easy: &[i64] = &[0, 1];
    let three: &[i64] = &[0, 1, 2];
    let p57 = ((5, 7), easy);
    let p1113 = ((11, 13), easy);
    let p34 = ((3, 4), easy);
    let p1719 = ((17, 19), easy);
    // The least `x > 0` where `p57` and `p1113` both hold.
    let least = (1..)
        .find(|&x| pair_clauses_hold(&[p57, p1113], Some((x - 1, x + 1))))
        .unwrap();
    // The third field: whether the solver answers `holds`. The two cases with `false`, which
    // hold nowhere in a range shorter than the period of their moduli, are in
    // `easy_clause_systems_held_nowhere_short_of_their_period_are_refused` and
    // `bench::one_scope` (0.8 s and 2.7 s at load 50).
    let cases: Vec<ResidueCase<'_>> = vec![
        (vec![p57, p1113], None, true),
        (vec![p57, p1113], Some((0, 100_000)), true),
        (vec![p34, p57, p1113], None, true),
        (vec![p34, p57, p1113, p1719], None, true),
        (vec![p57, p1113], Some((0, least + 1)), true),
        (vec![p57, ((11, 13), three)], None, true),
        (vec![p34, ((5, 7), three), p1113], None, true),
        (
            vec![p34, p57, p1113, ((17, 19), three)],
            Some((0, 100_000)),
            true,
        ),
    ];
    let seen = easy_clause_systems_keep_their_answers(cases);
    assert!(seen[0] >= 3 && seen[1] >= 5, "{seen:?}");
}

#[test]
fn easy_clause_systems_held_nowhere_short_of_their_period_are_refused() {
    // PNCX-modular, R2: `(x mod 5 == 0 || x mod 7 == 0) && (x mod 5 == 1 || x mod 7 == 1)` and
    // the same over 11 and 13 hold nowhere in `[0, least]`, a range shorter than the period of
    // their moduli; the general path refuses `holds` there, as it did before the one-variable
    // path (measured on d5714627), and `fails` is answered.
    let easy: &[i64] = &[0, 1];
    let (p57, p1113) = (((5, 7), easy), ((11, 13), easy));
    let least = (1..)
        .find(|&x| pair_clauses_hold(&[p57, p1113], Some((x - 1, x + 1))))
        .unwrap();
    let seen =
        easy_clause_systems_keep_their_answers(vec![(vec![p57, p1113], Some((0, least)), false)]);
    assert_eq!(seen, [1, 0]);
}

/// Each case `(pairs, bound, answered)` of [`pair_clauses`] is answered, in both readings of
/// the definition, as enumeration answers it (`holds` refused where `answered` is false, and
/// then false by enumeration); `fails` is always answered true. The number of cases false and
/// true by enumeration.
pub(super) fn easy_clause_systems_keep_their_answers(cases: Vec<ResidueCase<'_>>) -> [usize; 2] {
    use zedc::store::presburger::extend::Extending;
    let mut seen = [0usize; 2];
    for (pairs, bound, answered) in cases {
        let src = pair_clauses(&pairs, bound);
        let want = pair_clauses_hold(&pairs, bound);
        seen[usize::from(want)] += 1;
        let unit = elab(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let lets = lets(&unit);
        let fs = functions(&unit);
        let (name, ps, body) = fs[0];
        let mut scoped = Scoped::new(&lets);
        let r = scoped.relation(body, ps, ps, true).expect(name);
        let (mut faced, mut plain) = (Extending::new(), Extending::new());
        let a = faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
        let b = plain.defined(&r, &|n| scoped.def(n));
        for (h, how) in [(&a.holds, "faced"), (&b.holds, "plain")] {
            match answered {
                true => assert_eq!(*h, Ok(want), "holds ({how})\n{src}"),
                false => assert!(h.is_err() && !want, "holds ({how}): {h:?}\n{src}"),
            }
        }
        assert_eq!(a.fails, Ok(true), "fails (faced)\n{src}");
        assert_eq!(b.fails, Ok(true), "fails (plain)\n{src}");
    }
    seen
}

#[test]
fn a_residue_set_over_two_moduli_that_share_a_factor_keeps_its_residues() {
    // PNCX-modular, R2: with `x mod 4` fixed to 2, `x mod 12 in {2, 10}` leaves `x mod 3` in
    // {1, 2}; the one-variable path moved the residues the wrong way (to {0, 1}) and answered
    // that `x mod 14 in {9, 10, 11} && x mod 12 in {2, 10}` never holds in [10025, 10047],
    // where 10034 is a solution. For each shift `c`, `holds` is the answer of enumeration.
    use zedc::store::presburger::extend::Extending;
    for c in 0..12i64 {
        let src = format!(
            "q(x: int) = x >= 10025 && x <= 10047 && (x + 5) mod 14 <= 2 \
             && ((x - {c}) mod 12 == 0 || (x - {c}) mod 12 == 8);"
        );
        let want = (10025..=10047i64)
            .any(|x| (x + 5).rem_euclid(14) <= 2 && [0, 8].contains(&(x - c).rem_euclid(12)));
        let unit = elab(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let lets = lets(&unit);
        let fs = functions(&unit);
        let (name, ps, body) = fs[0];
        let mut scoped = Scoped::new(&lets);
        let r = scoped.relation(body, ps, ps, true).expect(name);
        let (mut faced, mut plain) = (Extending::new(), Extending::new());
        let a = faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
        let b = plain.defined(&r, &|n| scoped.def(n));
        assert_eq!(a.holds, Ok(want), "holds (faced)\n{src}");
        assert_eq!(b.holds, Ok(want), "holds (plain)\n{src}");
    }
}

pub(super) fn negated_modular_chain(n: usize) -> String {
    let mut src = String::from(
        "q(x: int) = !(x mod 3 == 2 && x > 11) && (x mod 4 == 1 || x > (0 - 5)) \
         && x > 0 && x < 1000000;\n\
         p0(x: int) = x > (0 - 4);\n\
         p1(x: int) = q(x: x) && p0(x: x + 3) && x < 1200;\n\
         p2(x: int) = q(x: x) && p1(x: x + (0 - 1)) && x < 2200 && !(x mod 5 == 0 || x mod 2 == 1);\n\
         p3(x: int) = q(x: x) && p2(x: x + 0) && x < 3200 && !(x mod 5 == 2 && x > 49);\n\
         p4(x: int) = q(x: x) && p3(x: x + 6) && x < 4200 && (x > 15 || x < 18);\n\
         p5(x: int) = q(x: x) && p4(x: x + 0) && x < 5200 && !(x mod 3 == 2 && x > 25);\n",
    );
    for i in 6..n {
        let shift = match i % 4 {
            2 => "(0 - 2)",
            3 => "3",
            0 => "(0 - 1)",
            _ => "60",
        };
        let extra = if i == 6 {
            " && (x mod 2 == 2 || x mod 5 != 0)"
        } else {
            ""
        };
        src.push_str(&format!(
            "p{i}(x: int) = q(x: x) && p{}(x: x + {shift}) && x < {}{extra};\n",
            i - 1,
            200 + 1000 * i
        ));
    }
    src
}

/// `q(x)` as the conjunction of `!(x mod p == r && x > b)` for `n` distinct bounds `b`, over
/// moduli 5, 7, 11 and 13: each question that does not hold is the disjunction of `n`
/// conjunctions of a residue and a bound.
pub(super) fn negated_residues_over_distinct_bounds(n: usize) -> String {
    let lits: Vec<String> = (0..n)
        .map(|i| {
            format!(
                "!(x mod {} == {} && x > {})",
                [5, 7, 11, 13][i % 4],
                i % 3,
                100 * (i + 1)
            )
        })
        .collect();
    format!(
        "q(x: int) = {} && x > 0 && x < 100000000;\n",
        lits.join(" && ")
    )
}

/// `q(x)` as the conjunction of `x mod p != 1` over the first `n` odd primes `p`, with
/// `0 < x < 10^9`.
pub(super) fn residues_over_distinct_primes(n: usize) -> String {
    let mut ps: Vec<i64> = Vec::new();
    let mut k = 3i64;
    while ps.len() < n {
        if ps.iter().all(|p| k % p != 0) {
            ps.push(k);
        }
        k += 2;
    }
    let lits: Vec<String> = ps.iter().map(|p| format!("x mod {p} != 1")).collect();
    format!(
        "q(x: int) = {} && x > 0 && x < 1000000000;\n",
        lits.join(" && ")
    )
}

/// `q(x)` as the conjunction, for `i < n`, of `x mod 31 == i mod 31 || x mod 37 == (i / 31) mod
/// 37 || x > 100 (i + 1)`, and of three clauses over 11 and 13 that hold nowhere at or below
/// `100 (n + 1)`, with `0 < x < 10^8`: each of the `n + 1` segments between bounds has its own
/// clauses, and the walk reaches every one.
pub(super) fn clauses_over_many_segments(n: usize) -> String {
    let mut lits: Vec<String> = (0..n)
        .map(|i| {
            format!(
                "(x mod 31 == {} || x mod 37 == {} || x > {})",
                i % 31,
                (i / 31) % 37,
                100 * (i + 1)
            )
        })
        .collect();
    for r in 0..3 {
        lits.push(format!(
            "(x mod 11 == {r} || x mod 13 == {r} || x > {})",
            100 * (n + 1)
        ));
    }
    format!(
        "q(x: int) = {} && x > 0 && x < 100000000;\n",
        lits.join(" && ")
    )
}

/// The conjunction, for `0 < i <= n`, of `r == 3 || x <= 10 i - 1 || x >= 10 i + 6`, with `x ==
/// 7 q + r`, `0 <= r <= 6` and `0 < x < 10 (n + 2)`, built as a `Formula`: `n` clauses that
/// share one residue condition (`x mod 7 == 3`), whose bounds intersected one after another
/// keep up to `n + 1` pieces.
pub(super) fn clauses_sharing_one_residue_condition(n: usize) -> zedc::store::presburger::Formula {
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    let x = Lin::atom(Atom::Sym(Arc::from("x")));
    let (q, r) = (Lin::atom(Atom::Aux(0)), Lin::atom(Atom::Aux(1)));
    let c = |k: i64| Lin::constant(k);
    let mut parts = vec![
        Formula::Con(Con::eq(&x, &q.times(7).plus(&r))),
        Formula::Con(Con::ge(&r, &c(0))),
        Formula::Con(Con::ge(&c(6), &r)),
        Formula::Con(Con::ge(&x, &c(1))),
        Formula::Con(Con::ge(&c(10 * (n as i64 + 2) - 1), &x)),
    ];
    for i in 1..=n as i64 {
        parts.push(Formula::or(vec![
            Formula::Con(Con::eq(&r, &c(3))),
            Formula::Con(Con::ge(&c(10 * i - 1), &x)),
            Formula::Con(Con::ge(&x, &c(10 * i + 6))),
        ]));
    }
    Formula::and(parts)
}

/// The first `n` odd primes.
fn odd_primes(n: usize) -> Vec<i64> {
    let mut ps: Vec<i64> = Vec::with_capacity(n);
    let mut k = 3;
    while ps.len() < n {
        if ps.iter().take_while(|p| *p * *p <= k).all(|p| k % p != 0) {
            ps.push(k);
        }
        k += 2;
    }
    ps
}

/// For each `p` of `ps`, `x == p q + r` with `0 <= r <= p - 1`, as a `Formula`, the `i`th
/// quotient and remainder `Aux(2 i)` and `Aux(2 i + 1)`; with the remainders.
fn residue_definitions(
    ps: &[i64],
) -> (
    Vec<zedc::store::presburger::Formula>,
    Vec<zedc::store::presburger::Lin>,
) {
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    let x = Lin::atom(Atom::Sym(Arc::from("x")));
    let (mut defs, mut rs) = (Vec::new(), Vec::new());
    for (i, p) in ps.iter().enumerate() {
        let q = Lin::atom(Atom::Aux(2 * i as u32));
        let r = Lin::atom(Atom::Aux(2 * i as u32 + 1));
        defs.push(Formula::Con(Con::eq(&x, &q.times(*p).plus(&r))));
        defs.push(Formula::Con(Con::ge(&r, &Lin::constant(0))));
        defs.push(Formula::Con(Con::ge(&Lin::constant(p - 1), &r)));
        rs.push(r);
    }
    (defs, rs)
}

/// `(x mod p1 == 0 || ... || x mod pn == 0) && x mod 2 == 1 && 0 < x < 10^9` over the first
/// `n` primes after 2, built as a `Formula`: one clause of `n` literals.
pub(super) fn a_disjunction_of_many_moduli(n: usize) -> zedc::store::presburger::Formula {
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    let x = Lin::atom(Atom::Sym(Arc::from("x")));
    let mut ps = vec![2];
    ps.extend(odd_primes(n));
    let (mut parts, rs) = residue_definitions(&ps);
    parts.push(Formula::Con(Con::eq(&rs[0], &Lin::constant(1))));
    parts.push(Formula::or(
        rs[1..]
            .iter()
            .map(|r| Formula::Con(Con::eq(r, &Lin::constant(0))))
            .collect(),
    ));
    parts.push(Formula::Con(Con::ge(&x, &Lin::constant(1))));
    parts.push(Formula::Con(Con::ge(&Lin::constant(999_999_999), &x)));
    Formula::and(parts)
}

/// The question whether `(x mod a == 0 || x mod b == 0) && (x mod a == 1 || x mod b == 1)`
/// fails for some `x`, for `n` pairs `a, b` of distinct odd primes, built as a `Formula`: the
/// remainders' definitions and the negation of the conjunction of the `2 n` clauses.
pub(super) fn the_fails_question_of_pairs(n: usize) -> zedc::store::presburger::Formula {
    use zedc::store::presburger::{Con, Formula, Lin, Shared};
    let (mut parts, rs) = residue_definitions(&odd_primes(2 * n));
    let is = |r: &Lin, k: i64| Formula::Con(Con::eq(r, &Lin::constant(k)));
    let mut clauses = Vec::new();
    for i in 0..n {
        let (a, b) = (&rs[2 * i], &rs[2 * i + 1]);
        clauses.push(Formula::or(vec![is(a, 0), is(b, 0)]));
        clauses.push(Formula::or(vec![is(a, 1), is(b, 1)]));
    }
    parts.push(Formula::Not(Shared::new(Formula::and(clauses))));
    Formula::and(parts)
}

#[test]
fn one_variable_boundary_modes_do_not_depend_on_names() {
    // I4.15: the one-variable path worked in the coordinate of the root of its affine
    // union-find, the lexically least name, and tried the point 1 there, so renaming an alias
    // changed a refusal into an answer. Each formula of the enumeration test is asked again
    // with its variables renamed in four patterns (aliases before and after `x`,
    // with `x` itself renamed), and with its quotients and remainders
    // numbered in reverse; `decide` and `satisfiable` give the same answer, refusal included,
    // and `satisfiable` asked first gives the same answers too. `PNCX_CASES=a..b` runs part.
    use zedc::store::presburger::{decide, satisfiable};
    let (from, to) = std::env::var("PNCX_CASES").map_or((0, 100), |s| {
        let (a, b) = s.split_once("..").unwrap();
        (a.parse().unwrap(), b.parse().unwrap())
    });
    let namings: [Naming<'_>; 4] = [
        ("aliases after", &|k| format!("x{k}"), &|i| i),
        (
            "aliases before",
            &|k| ["z", "a", "b", "c"][k].to_string(),
            &|i| i,
        ),
        (
            "interleaved",
            &|k| ["m", "z", "a", "n"][k].to_string(),
            &|i| 99 - i,
        ),
        ("reversed", &|k| format!("v{}", 9 - k), &|i| 99 - i),
    ];
    // 100 cases drawn with a new seed each run (author P169; 1,000 at one seed took 4.2 s).
    let (mut rng, _) = zed_tests::instances::Rng::fresh("one-variable boundary modes renamed");
    let (mut differ, mut answered) = (Vec::new(), 0usize);
    for case_idx in 0..to {
        let (f, ..) = modular_case_mode(&mut rng, case_idx, Some((case_idx % 4) as u8));
        if case_idx < from {
            continue;
        }
        let answer = |g: &zedc::store::presburger::Formula, sat_first: bool| {
            let (d, s) = if sat_first {
                let s = satisfiable(g);
                (decide(g), s)
            } else {
                let d = decide(g);
                (d, satisfiable(g))
            };
            (d.ok(), s.ok().map(|m| m.is_some()))
        };
        let base = answer(&f, false);
        answered += usize::from(base.0.is_some());
        for (label, name, aux) in &namings {
            let g = renamed(&f, name, aux);
            for sat_first in [false, true] {
                let got = answer(&g, sat_first);
                if got != base {
                    differ.push(format!(
                        "case {case_idx} {label} sat_first={sat_first}: {got:?} against {base:?}\n  {g}"
                    ));
                }
            }
        }
    }
    println!(
        "renamed cases {from}..{to}: {answered} answered, {} differ",
        differ.len()
    );
    assert!(differ.is_empty(), "{}", differ.join("\n"));
}

#[test]
fn pncx_boundary_modes_match_complete_periods() {
    use zedc::store::int::Int;
    use zedc::store::presburger::{Model, decide, satisfiable};
    let range = std::env::var("PNCX_CASES").unwrap_or_else(|_| "0..1000".into());
    let (a, b) = range.split_once("..").expect("range");
    let (a, b): (usize, usize) = (a.parse().unwrap(), b.parse().unwrap());
    let mut rng = zed_tests::instances::Rng::new(0x70de_c1de);
    let mut checked = 0;
    for case in 0..b {
        let mode = (case % 4) as u8;
        let (f, x0, copies, divs, lo, hi, _) = modular_case_mode(&mut rng, case, Some(mode));
        if case < a {
            continue;
        }
        let mut period = 1i64;
        for (_, _, m, _, _) in &divs {
            let (mut p, mut q) = (period, *m);
            while q != 0 {
                (p, q) = (q, p % q);
            }
            period = period / p * m;
        }
        // Every written bound is between lo-5 and hi+18. Outside it the
        // condition is periodic; one full period on each permitted infinite
        // side suffices. This is an exhaustive test oracle, not solver work.
        let (start, end) = match mode {
            0 => (0, period - 1),
            1 => (lo, hi + 18 + period),
            2 => (lo - 6 - period, hi),
            _ => (lo, hi),
        };
        let truth = (start..=end).any(|v| {
            let mut model = Model::from([(x0.clone(), Int::from(v))]);
            for (atom, s, off) in &copies {
                model.insert(atom.clone(), Int::from(s * v + off));
            }
            for (q, r, m, s, off) in &divs {
                let value = s * v + off;
                model.insert(q.clone(), Int::from(value.div_euclid(*m)));
                model.insert(r.clone(), Int::from(value.rem_euclid(*m)));
            }
            f.holds(&model)
        });
        let d = decide(&f);
        let sat = satisfiable(&f);
        if let Ok(value) = d {
            assert_eq!(value, truth, "case {case}: {f}");
            checked += 1;
        }
        if let Ok(model) = sat {
            assert_eq!(model.is_some(), truth, "case {case}: {f}");
            if let Some(model) = model {
                assert!(f.holds(&model), "case {case}");
            }
            checked += 1;
        }
    }
    println!("BOUNDARY_PERIODS cases={a}..{b} checked={checked} mismatches=0");
}

#[test]
fn remainder_alias_names_keep_the_same_answers() {
    use zedc::store::presburger::extend::Extending;
    let core = "x >= (0 - 8) && x <= 26 && (x + 1) mod 10 <= 1 && (x - 5) mod 4 <= 1 && ((x - 5) mod 4 == 2 || (x - 5) mod 4 == 1 || x <= 12) && ((x + 1) mod 10 != 5 || x mod 8 != 7)";
    let witnesses: Vec<_> = (-8i64..=26)
        .filter(|&x| {
            (x + 1).rem_euclid(10) <= 1
                && (x - 5).rem_euclid(4) <= 1
                && ((x - 5).rem_euclid(4) == 2 || (x - 5).rem_euclid(4) == 1 || x <= 12)
                && ((x + 1).rem_euclid(10) != 5 || x.rem_euclid(8) != 7)
        })
        .collect();
    assert_eq!(witnesses, vec![9, 10]);
    let src =
        format!("ra(x:int,a:int)=a==x mod 101 && {core};\nrz(x:int,z:int)=z==x mod 101 && {core};");
    let unit = elab(&src).unwrap();
    let scope = lets(&unit);
    let fs = functions(&unit);
    let mut failures = Vec::new();
    for reverse in [false, true] {
        let mut scoped = Scoped::new(&scope);
        let (mut faced, mut plain) = (Extending::new(), Extending::new());
        let mut order = vec![0, 1];
        if reverse {
            order.reverse();
        }
        for i in order {
            let (name, ps, body) = fs[i];
            let r = scoped
                .relation(body, ps, ps, true)
                .expect("linear question");
            let a = faced.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
            let b = plain.defined(&r, &|n| scoped.def(n));
            let got = (a.holds.ok(), b.holds.ok(), a.fails.ok(), b.fails.ok());
            if got != (Some(true), Some(true), Some(true), Some(true)) {
                failures.push(format!("reverse={reverse} {name}: {got:?}"));
            }
            let w = scoped.written(&r);
            let f = zedc::store::presburger::Formula::and(vec![w.defined(), w.body.clone()]);
            for sat_first in [false, true] {
                use zedc::store::presburger::{decide, satisfiable};
                let (d, s) = if sat_first {
                    let s = satisfiable(&f);
                    (decide(&f), s)
                } else {
                    (decide(&f), satisfiable(&f))
                };
                if let Ok(Some(model)) = &s {
                    assert!(f.holds(model));
                }
                let got = (d.ok(), s.ok().map(|m| m.is_some()));
                if got != (Some(true), Some(true)) {
                    failures.push(format!(
                        "reverse={reverse} {name} sat_first={sat_first}: {got:?}"
                    ));
                }
            }
        }
    }
    // R6-CODEX-12: this ordinary test intentionally exposes the unresolved
    // name choice during remainder extraction, before regime normalization.
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
