//! Every axiom holds on the finite-model harness's instances of its carrier (step M0.10), run
//! on the reference evaluator; each kind of law has a false claim the same check refutes; and
//! the prelude's copy of the table is the Rust one.

use std::mem::discriminant;

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Prim, Term, Value, eval};
use zed_tests::check::agree;
use zed_tests::instances::{bmc_floats, bmc_ints, shortlex};
use zedc::axioms::{AXIOMS, Axiom, Carrier, Const, Law, Tonicity};

const PRELUDE: &str = include_str!("../../../zed/prelude/axioms.zed");

/// The harness's values of a carrier: the rung 6 integers and floats, both booleans, and the
/// strings over `a`, `b` of length at most 3.
fn values(c: Carrier) -> Vec<Value> {
    match c {
        Carrier::Int => bmc_ints().into_iter().map(Value::Int).collect(),
        Carrier::F64 => bmc_floats(),
        Carrier::Bool => vec![Value::Bool(false), Value::Bool(true)],
        Carrier::String => shortlex(&["a", "b"], 3)
            .iter()
            .map(|s| Value::str(&s.concat()))
            .collect(),
    }
}

fn constant(c: Const) -> Value {
    match c {
        Const::Int(n) => Value::Int(n),
        Const::F64(x) => Value::float(x),
        Const::Bool(b) => Value::Bool(b),
        Const::Str(s) => Value::str(s),
    }
}

/// The kernel term of `op` applied to `args`. `square` is not an operator: it is here so the
/// controls can claim a law of a unary function that does not have it.
fn call(op: &str, args: Vec<Term>) -> Term {
    let p = match op {
        "+" => Prim::Add,
        "++" => Prim::Concat,
        "-" => Prim::Sub,
        "*" => Prim::Mul,
        "neg" => Prim::Neg,
        "min" => Prim::Min,
        "max" => Prim::Max,
        "&&" => Prim::And,
        "||" => Prim::Or,
        "!" => Prim::Not,
        "==" => Prim::Eq,
        "!=" => Prim::Ne,
        "<" => Prim::Lt,
        "<=" => Prim::Le,
        ">" => Prim::Gt,
        ">=" => Prim::Ge,
        "square" => return prim(Prim::Mul, vec![args[0].clone(), args[0].clone()]),
        _ => panic!("no kernel primitive for `{op}`"),
    };
    prim(p, args)
}

fn run(op: &str, args: &[&Value]) -> Value {
    eval(&call(op, args.iter().map(|v| lit((*v).clone())).collect())).unwrap()
}

fn holds(op: &str, args: &[&Value]) -> bool {
    run(op, args) == Value::Bool(true)
}

fn le(a: &Value, b: &Value) -> bool {
    holds("<=", &[a, b])
}

/// Checks `a` on every instance; returns how many were run, or the first counterexample.
fn check(a: &Axiom) -> Result<usize, String> {
    let vs = values(a.carrier);
    let mut n = 0;
    let mut eq = |what: String, l: Term, r: Term| {
        n += 1;
        let (x, y) = (eval(&l), eval(&r));
        if agree(&x, &y) {
            Ok(())
        } else {
            Err(format!("{what}: {x:?} against {y:?}"))
        }
    };
    let (op, v) = (a.op, |x: &Value| lit(x.clone()));
    let pairs = || vs.iter().flat_map(|x| vs.iter().map(move |y| (x, y)));
    let triples = || pairs().flat_map(|(x, y)| vs.iter().map(move |z| (x, y, z)));
    match a.law {
        Law::Associative => {
            for (x, y, z) in triples() {
                let l = call(op, vec![call(op, vec![v(x), v(y)]), v(z)]);
                let r = call(op, vec![v(x), call(op, vec![v(y), v(z)])]);
                eq(format!("{x}, {y}, {z}"), l, r)?;
            }
        }
        Law::Commutative => {
            for (x, y) in pairs() {
                eq(
                    format!("{x}, {y}"),
                    call(op, vec![v(x), v(y)]),
                    call(op, vec![v(y), v(x)]),
                )?;
            }
        }
        Law::Idempotent => {
            for x in &vs {
                eq(format!("{x}"), call(op, vec![v(x), v(x)]), v(x))?;
            }
        }
        Law::Identity(e) | Law::Zero(e) => {
            let e = constant(e);
            for x in &vs {
                let out = if matches!(a.law, Law::Identity(_)) {
                    x
                } else {
                    &e
                };
                eq(
                    format!("{e} left of {x}"),
                    call(op, vec![v(&e), v(x)]),
                    v(out),
                )?;
                eq(
                    format!("{e} right of {x}"),
                    call(op, vec![v(x), v(&e)]),
                    v(out),
                )?;
            }
        }
        Law::Inverse(g) => {
            for x in &vs {
                eq(
                    format!("{g} after, {x}"),
                    call(g, vec![call(op, vec![v(x)])]),
                    v(x),
                )?;
                eq(
                    format!("{g} before, {x}"),
                    call(op, vec![call(g, vec![v(x)])]),
                    v(x),
                )?;
            }
        }
        Law::LeftDistributesOver(add) | Law::RightDistributesOver(add) => {
            let left = matches!(a.law, Law::LeftDistributesOver(_));
            let mul = |p: Term, q: Term| {
                if left {
                    call(op, vec![p, q])
                } else {
                    call(op, vec![q, p])
                }
            };
            for (x, y, z) in triples() {
                let l = mul(v(x), call(add, vec![v(y), v(z)]));
                let r = call(add, vec![mul(v(x), v(y)), mul(v(x), v(z))]);
                eq(format!("{x}, {y}, {z}"), l, r)?;
            }
        }
        Law::Monotone(signs) => {
            let arity = signs.len();
            let all: Vec<Vec<Value>> = (0..arity).fold(vec![vec![]], |acc, _| {
                acc.iter()
                    .flat_map(|p| {
                        vs.iter()
                            .map(move |x| [p.clone(), vec![x.clone()]].concat())
                    })
                    .collect()
            });
            for (i, sign) in signs.iter().enumerate() {
                for args in &all {
                    for b in vs.iter().filter(|b| le(&args[i], b)) {
                        n += 1;
                        let mut moved = args.clone();
                        moved[i] = b.clone();
                        let (fa, fb) = (
                            run(op, &args.iter().collect::<Vec<_>>()),
                            run(op, &moved.iter().collect::<Vec<_>>()),
                        );
                        let ok = match sign {
                            Tonicity::Up => le(&fa, &fb),
                            Tonicity::Down => le(&fb, &fa),
                        };
                        if !ok {
                            return Err(format!(
                                "argument {i} from {} to {b}: {fa} then {fb}",
                                args[i]
                            ));
                        }
                    }
                }
            }
        }
        Law::Injective => {
            for (x, y) in pairs() {
                n += 1;
                if x != y && run(op, &[x]) == run(op, &[y]) {
                    return Err(format!("{x} and {y} meet"));
                }
            }
        }
        Law::Reflexive | Law::Irreflexive => {
            for x in &vs {
                n += 1;
                if holds(op, &[x, x]) != matches!(a.law, Law::Reflexive) {
                    return Err(format!("{x}"));
                }
            }
        }
        Law::Symmetric | Law::Antisymmetric | Law::Total => {
            for (x, y) in pairs() {
                n += 1;
                let (xy, yx) = (holds(op, &[x, y]), holds(op, &[y, x]));
                let ok = match a.law {
                    Law::Symmetric => !xy || yx,
                    Law::Antisymmetric => !(xy && yx) || x == y,
                    _ => xy || yx,
                };
                if !ok {
                    return Err(format!("{x}, {y}"));
                }
            }
        }
        Law::Transitive => {
            for (x, y, z) in triples() {
                n += 1;
                if holds(op, &[x, y]) && holds(op, &[y, z]) && !holds(op, &[x, z]) {
                    return Err(format!("{x}, {y}, {z}"));
                }
            }
        }
    }
    Ok(n)
}

#[test]
fn every_axiom_holds_on_the_harness_instances() {
    let mut total = 0;
    for a in AXIOMS {
        match check(a) {
            Ok(n) => total += n,
            Err(why) => panic!("{} at {:?}: {:?} fails on {why}", a.op, a.carrier, a.law),
        }
    }
    assert_eq!(AXIOMS.len(), 86);
    assert!(total > 50_000, "{total} instances");
}

#[test]
fn a_false_claim_of_each_kind_is_refuted() {
    use Carrier::*;
    use Tonicity::*;
    let claim = |op, carrier, law| Axiom { op, carrier, law };
    let controls = [
        claim("+", F64, Law::Associative), // 0.1 + 0.2 + 0.3
        claim("++", String, Law::Commutative),
        claim("+", Int, Law::Idempotent),
        claim("+", F64, Law::Identity(Const::F64(0.0))), // -0.0 + 0.0 is 0.0
        claim("*", F64, Law::Zero(Const::F64(0.0))),     // 0.0 * inf is NaN
        claim("square", Int, Law::Inverse("neg")),
        claim("+", Int, Law::LeftDistributesOver("*")),
        claim("-", Int, Law::RightDistributesOver("*")),
        claim("-", Int, Law::Monotone(&[Up, Up])),
        claim("square", Int, Law::Injective),
        claim("<", Int, Law::Reflexive),
        claim("<=", Int, Law::Irreflexive),
        claim("<", Int, Law::Symmetric),
        claim("!=", Int, Law::Antisymmetric),
        claim("!=", Int, Law::Transitive),
        claim("<", Int, Law::Total),
    ];
    for c in &controls {
        assert!(
            check(c).is_err(),
            "{} at {:?}: {:?} was not refuted",
            c.op,
            c.carrier,
            c.law
        );
    }
    // Every kind of law has a control.
    for a in AXIOMS {
        assert!(
            controls
                .iter()
                .any(|c| discriminant(&c.law) == discriminant(&a.law))
        );
    }
}

/// An axiom as the prelude writes it.
fn zed_line(a: &Axiom) -> String {
    let c = |k: Const| match k {
        Const::Int(n) => n.to_string(),
        Const::F64(x) => format!("{x:?}"),
        Const::Bool(b) => b.to_string(),
        Const::Str(s) => format!("{s:?}"),
    };
    let law = match a.law {
        Law::Identity(k) => format!("#identity({})", c(k)),
        Law::Zero(k) => format!("#zero({})", c(k)),
        Law::Inverse(g) => format!("#inverse({g:?})"),
        Law::LeftDistributesOver(g) => format!("#leftDistributesOver({g:?})"),
        Law::RightDistributesOver(g) => format!("#rightDistributesOver({g:?})"),
        Law::Monotone(signs) => {
            let s: Vec<&str> = signs
                .iter()
                .map(|t| if *t == Tonicity::Up { "#up" } else { "#down" })
                .collect();
            format!("#monotone([{}])", s.join(", "))
        }
        other => {
            let name = format!("{other:?}");
            format!("#{}{}", name[..1].to_lowercase(), &name[1..])
        }
    };
    let carrier = format!("{:?}", a.carrier).to_lowercase();
    format!("Axiom(op: {:?}, carrier: #{carrier}, law: {law}),", a.op)
}

#[test]
fn the_prelude_copy_is_the_rust_table() {
    let prelude: Vec<&str> = PRELUDE
        .lines()
        .map(str::trim)
        .filter(|l| l.starts_with("Axiom("))
        .collect();
    let rust: Vec<String> = AXIOMS.iter().map(zed_line).collect();
    assert_eq!(prelude, rust);
}
