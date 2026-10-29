//! Binder normalization: definitions that differ only in local names share an address, and
//! every other difference changes it. Checked by hand on ordinary definitions and against an
//! independent α-equivalence test (de Bruijn indices) on random terms.

use std::sync::Arc;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::term::{FixKind, Pattern, Prim, Term};
use zed_kernel::value::Value;
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::address::ContentAddress;
use zedc::canon::{address, binders};

use super::{addr, def};

/// `fam(lines, v -> v.qty * v.price)` folded with `+`: an invoice total.
fn invoice(v: &str) -> Term {
    let field = |f: &str| prim(Prim::Get, vec![var(v), lit(f)]);
    Term::Fold {
        family: Arc::new(Term::Fam {
            domain: Arc::new(var("lines")),
            var: v.into(),
            body: Arc::new(prim(Prim::Mul, vec![field("qty"), field("price")])),
        }),
        op: Arc::new(Term::PrimFn(Prim::Add)),
        identity: Some(Arc::new(lit(0))),
        depth: 1,
    }
}

#[test]
fn an_invoice_total_has_one_address_whatever_its_line_is_called() {
    let a = addr(&def("total", invoice("line")));
    assert_eq!(a, addr(&def("total", invoice("row"))));
    assert_eq!(a, addr(&def("total", invoice("lines"))));
    // The free name `lines`, the definition's own name and a field name are part of the
    // interface: each changes the address.
    let mut other = invoice("line");
    if let Term::Fold { family, .. } = &mut other
        && let Term::Fam { domain, .. } = Arc::make_mut(family)
    {
        *domain = Arc::new(var("items"));
    }
    assert_ne!(a, addr(&def("total", other)));
    assert_ne!(a, addr(&def("subtotal", invoice("line"))));
    let mut by_cost = invoice("line");
    if let Term::Fold { family, .. } = &mut by_cost
        && let Term::Fam { body, .. } = Arc::make_mut(family)
    {
        *body = Arc::new(prim(
            Prim::Mul,
            vec![
                prim(Prim::Get, vec![var("line"), lit("qty")]),
                prim(Prim::Get, vec![var("line"), lit("cost")]),
            ],
        ));
    }
    assert_ne!(a, addr(&def("total", by_cost)));
}

#[test]
fn shadowing_decides_which_binder_a_name_means() {
    // `fee -> (fee -> fee)` returns the inner argument, `fee -> (amount -> fee)` the outer.
    let inner = lam(&["fee"], lam(&["fee"], var("fee")));
    let outer = lam(&["fee"], lam(&["amount"], var("fee")));
    let inner2 = lam(&["a"], lam(&["b"], var("b")));
    assert_eq!(addr(&def("f", inner.clone())), addr(&def("f", inner2)));
    assert_ne!(addr(&def("f", inner)), addr(&def("f", outer)));
    // Two parameters of one name: the later one is meant.
    let twice = lam(&["x", "x"], var("x"));
    assert_eq!(
        addr(&def("snd", twice)),
        addr(&def("snd", lam(&["p", "q"], var("q"))))
    );
    // `rate = 3; rate = rate * 2; rate` reads the first rate in the second binding's value.
    let rebound = |a: &str, b: &str| {
        let_(
            a,
            lit(3),
            let_(b, prim(Prim::Mul, vec![var(a), lit(2)]), var(b)),
        )
    };
    assert_eq!(
        addr(&def("r", rebound("rate", "rate"))),
        addr(&def("r", rebound("x", "y")))
    );
    // A local that shadows a free name hides it; the free name elsewhere is still the free one.
    let shadow_free = let_("tax", lit(1), var("tax"));
    let free = let_("t", lit(1), var("tax"));
    assert_ne!(addr(&def("v", shadow_free)), addr(&def("v", free)));
}

#[test]
fn pattern_and_recursion_binders_are_normalized() {
    // `match status { (code, _) -> code, _ -> 0 }`, with the code called two ways.
    let m = |c: &str| {
        Term::Match(
            Arc::new(var("status")),
            vec![
                (
                    Pattern::Tuple(vec![Pattern::Bind(c.into()), Pattern::Wild]),
                    var(c),
                ),
                (Pattern::Wild, lit(0)),
            ],
        )
    };
    assert_eq!(addr(&def("code", m("code"))), addr(&def("code", m("c"))));
    // A pattern binding the same name twice means the later one.
    let pair = |a: &str, b: &str, use_: &str| {
        Term::Match(
            Arc::new(var("p")),
            vec![(
                Pattern::Tuple(vec![Pattern::Bind(a.into()), Pattern::Bind(b.into())]),
                var(use_),
            )],
        )
    };
    assert_eq!(
        addr(&def("s", pair("x", "x", "x"))),
        addr(&def("s", pair("a", "b", "b")))
    );
    assert_ne!(
        addr(&def("s", pair("x", "x", "x"))),
        addr(&def("s", pair("a", "b", "a")))
    );
    // Fibonacci by definedness: `this` and the key are binders of the step.
    // `call` is the name the step calls and `n` the name it reads as the key.
    let step = |this: &str, n: &str, call: &str, key: &str| Term::Fix {
        init: Arc::new(var("upTo")),
        step: Arc::new(Term::If(
            Arc::new(prim(Prim::Lt, vec![var(key), lit(2)])),
            Arc::new(var(key)),
            Arc::new(prim(
                Prim::Add,
                vec![
                    app(var(call), vec![prim(Prim::Sub, vec![var(key), lit(1)])]),
                    app(var(call), vec![prim(Prim::Sub, vec![var(key), lit(2)])]),
                ],
            )),
        )),
        this: this.into(),
        key: n.into(),
        kind: FixKind::Definedness,
    };
    let fib = |this: &str, n: &str| step(this, n, this, n);
    assert_eq!(
        addr(&def("fib", fib("fib", "n"))),
        addr(&def("fib", fib("f", "k")))
    );
    assert_ne!(
        addr(&def("fib", fib("fib", "n"))),
        addr(&def("fib", step("fib", "n", "n", "fib")))
    );
}

#[test]
fn a_dependency_change_changes_its_dependents_but_a_local_rename_does_not() {
    // `due = total * 1.08`, where `total` is the invoice definition above.
    let due = def(
        "due",
        prim(Prim::Mul, vec![var("total"), lit(Value::float(1.08))]),
    );
    let resolve = |t: ContentAddress| move |n: &str| (n == "total").then_some(t);
    let total_a = addr(&def("total", invoice("line")));
    let total_b = addr(&def("total", invoice("row")));
    let mut cheaper = invoice("line");
    if let Term::Fold { identity, .. } = &mut cheaper {
        *identity = Some(Arc::new(lit(-5)));
    }
    let total_c = addr(&def("total", cheaper));
    let at = |t| address(&due, &resolve(t));
    assert_eq!(at(total_a), at(total_b));
    assert_ne!(at(total_a), at(total_c));
    assert_ne!(at(total_a), addr(&due));
}

#[test]
fn literals_are_hashed_by_their_exact_value() {
    let l = |v: Value| addr(&def("k", Term::Lit(v)));
    assert_ne!(l(Value::float(0.0)), l(Value::float(-0.0)));
    assert_eq!(l(Value::float(f64::NAN)), l(Value::float(-f64::NAN)));
    assert_ne!(l(Value::Int(1)), l(Value::float(1.0)));
    assert_ne!(l(Value::str("empty")), l(Value::atom("empty")));
    assert_ne!(l(Value::Tuple(vec![])), l(Value::Path(vec![])));
}

#[test]
fn the_rename_step_records_the_written_name_and_its_place() {
    let t = lam(&["acc"], let_("x", var("acc"), var("x")));
    let (t, i, w) = binders::step(&t).unwrap();
    assert_eq!((i, &*w), (0, "acc"));
    let (_, i, w) = binders::step(&t).unwrap();
    assert_eq!((i, &*w), (1, "x"));
    assert_eq!(binders::level_of(&binders::level_name(7)), Some(7));
    assert_eq!(binders::level_of("x"), None);
}

// ---- Random terms against an independent α-equivalence test -------------------------------

const BOUND: [&str; 3] = ["a", "b", "x"];
const FREE: [&str; 2] = ["price", "qty"];

/// A random term over the binding forms the canonicalizer renames. `names` picks the written
/// name of each binder from its own stream, so two calls with one `shape` seed and different
/// `names` seeds give terms of one shape and different names.
fn random(shape: &mut Rng, names: &mut Rng, depth: u32, scope: &mut Vec<&'static str>) -> Term {
    let leaf = depth == 0 || shape.below(4) == 0;
    if leaf {
        return match shape.below(3) {
            0 if !scope.is_empty() => {
                // A binder by its position in scope, written by its name.
                var(scope[scope.len() - 1 - shape.below(scope.len())])
            }
            1 => var(FREE[shape.below(2)]),
            _ => lit(shape.int(0, 2)),
        };
    }
    let sub = |scope: &mut Vec<&'static str>, shape: &mut Rng, names: &mut Rng| {
        random(shape, names, depth - 1, scope)
    };
    match shape.below(6) {
        0 => {
            let n = 1 + shape.below(2);
            let ps: Vec<&'static str> = (0..n).map(|_| names.pick(&BOUND)).collect();
            scope.extend(&ps);
            let body = sub(scope, shape, names);
            scope.truncate(scope.len() - n);
            lam(&ps, body)
        }
        1 => {
            let x = names.pick(&BOUND);
            let e = sub(scope, shape, names);
            scope.push(x);
            let body = sub(scope, shape, names);
            scope.pop();
            let_(x, e, body)
        }
        2 => {
            let e = sub(scope, shape, names);
            let x = names.pick(&BOUND);
            let p = Pattern::Tuple(vec![Pattern::Bind(x.into()), Pattern::Wild]);
            scope.push(x);
            let arm = sub(scope, shape, names);
            scope.pop();
            let other = sub(scope, shape, names);
            Term::Match(Arc::new(e), vec![(p, arm), (Pattern::Wild, other)])
        }
        3 => {
            let d = sub(scope, shape, names);
            let x = names.pick(&BOUND);
            scope.push(x);
            let body = sub(scope, shape, names);
            scope.pop();
            Term::Fam {
                domain: Arc::new(d),
                var: x.into(),
                body: Arc::new(body),
            }
        }
        4 => {
            let f = sub(scope, shape, names);
            let a = sub(scope, shape, names);
            app(f, vec![a])
        }
        _ => {
            let a = sub(scope, shape, names);
            let b = sub(scope, shape, names);
            prim(Prim::Add, vec![a, b])
        }
    }
}

/// An independent rendering of a term's α-class: each bound variable written as its de
/// Bruijn index, counted outward from the use, and each free one by name.
fn indices(t: &Term, env: &mut Vec<Arc<str>>) -> String {
    let under = |names: &[Arc<str>], body: &Term, env: &mut Vec<Arc<str>>| {
        env.extend(names.iter().cloned());
        let s = indices(body, env);
        env.truncate(env.len() - names.len());
        s
    };
    match t {
        Term::Lit(v) => format!("{v}"),
        Term::Var(x) => match env.iter().rev().position(|y| y == x) {
            Some(i) => format!("#{i}"),
            None => format!("${x}"),
        },
        Term::Lam(ps, body) => format!("(\\{} {})", ps.len(), under(ps, body, env)),
        Term::App(f, args) => format!("({} {})", indices(f, env), indices(&args[0], env)),
        Term::Prim(_, args) => format!("(+ {} {})", indices(&args[0], env), indices(&args[1], env)),
        Term::Let(x, e, body) => {
            format!(
                "(let {} {})",
                indices(e, env),
                under(std::slice::from_ref(x), body, env)
            )
        }
        Term::Match(e, arms) => {
            let Pattern::Tuple(ps) = &arms[0].0 else {
                unreachable!()
            };
            let Pattern::Bind(x) = &ps[0] else {
                unreachable!()
            };
            format!(
                "(match {} {} {})",
                indices(e, env),
                under(std::slice::from_ref(x), &arms[0].1, env),
                indices(&arms[1].1, env)
            )
        }
        Term::Fam { domain, var, body } => format!(
            "(fam {} {})",
            indices(domain, env),
            under(std::slice::from_ref(var), body, env)
        ),
        _ => unreachable!("the generator makes no other form"),
    }
}

#[test]
fn addresses_agree_with_an_independent_alpha_equivalence_test() {
    let (mut same, mut differ) = (0, 0);
    for seed in 0..RANDOM_INSTANCES as u64 * 4 {
        let make = |names: u64| {
            random(
                &mut Rng::new(seed),
                &mut Rng::new(names),
                4,
                &mut Vec::new(),
            )
        };
        let (s, t) = (make(seed ^ 0x51), make(seed ^ 0x9e));
        let alpha = indices(&s, &mut vec![]) == indices(&t, &mut vec![]);
        assert_eq!(
            addr(&def("f", s.clone())) == addr(&def("f", t.clone())),
            alpha,
            "{s:?}\n{t:?}"
        );
        if alpha { same += 1 } else { differ += 1 }
    }
    // Both outcomes occur often enough for the agreement to mean something.
    assert!(
        same > 300 && differ > 300,
        "{same} alike, {differ} different"
    );
}
