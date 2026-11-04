//! Every axiom holds on the finite-model harness's instances of its carrier (step M0.10), run
//! on the reference evaluator; each kind of law has a false claim the same check refutes; and
//! the prelude's copy of the table is the Rust one.

use std::mem::discriminant;

use num_bigint::BigInt;
use zed_kernel::term::build::{if_, lit, prim};
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

/// The kernel term of `op` applied to `args`. `square`, `quot` and `mulI64` are not operators:
/// they are here so the controls can claim laws of functions that do not have them.
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
        "bitAnd" => Prim::BitAnd,
        "bitOr" => Prim::BitOr,
        "bitXor" => Prim::BitXor,
        "shl" => Prim::Shl,
        "shr" => Prim::Shr,
        "div" => Prim::IntDiv,
        "**" => Prim::Pow,
        "square" => return prim(Prim::Mul, vec![args[0].clone(), args[0].clone()]),
        // `quot(a, b)`, for `b > 0`, is the quotient rounded toward zero, which `div` is not at
        // a negative `a`.
        "quot" => {
            let [a, b]: [Term; 2] = args.try_into().expect("`quot` takes two arguments");
            let below = prim(Prim::Lt, vec![a.clone(), lit(Value::Int(0))]);
            let up = prim(
                Prim::IntDiv,
                vec![prim(Prim::Neg, vec![a.clone()]), b.clone()],
            );
            return if_(
                below,
                prim(Prim::Neg, vec![up]),
                prim(Prim::IntDiv, vec![a, b]),
            );
        }
        // `mulI64(a, b)` is the product wrapped to a signed 64-bit word, as machine arithmetic
        // gives it: `(a * b + 2^63) mod 2^64 - 2^63`.
        "mulI64" => {
            let half = lit(near_two_pow(63, 0));
            let shifted = prim(Prim::Add, vec![prim(Prim::Mul, args), half.clone()]);
            let word = prim(Prim::Mod, vec![shifted, lit(near_two_pow(64, 0))]);
            return prim(Prim::Sub, vec![word, half]);
        }
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
    match a.op {
        "bitAnd" | "bitOr" | "bitXor" => {
            let small = (1..=8).try_fold(0, |n, w| Ok::<_, String>(n + check_word(a, w)?))?;
            Ok(small + check_on(a, &word_corners())?)
        }
        "shl" | "shr" => {
            let counts: Vec<Value> = (0..256).map(Value::Int).collect();
            check_shift(a, &shift_values(), &counts)
        }
        _ => check_on(a, &values(a.carrier)),
    }
}

/// `2^e + d`.
fn near_two_pow(e: u32, d: i64) -> Value {
    Value::int((BigInt::from(1) << e) + d)
}

/// Values of the bit words at the machine word and past it, where the evaluator leaves `i64`
/// for exact digits: below, at and above `2^63` and `2^64`, and two wider ones.
fn word_corners() -> Vec<Value> {
    let mut vs: Vec<Value> = [0, 1, 2, 3].map(Value::Int).to_vec();
    for e in [62, 63, 64] {
        vs.extend([-1, 0, 1].map(|d| near_two_pow(e, d)));
    }
    vs.extend([near_two_pow(65, 5), near_two_pow(128, -1)]);
    vs
}

/// The `x` of the shifts: every int of at most 8 binary digits, of either sign, and both signs
/// of the values about `2^63` and `2^64`.
fn shift_values() -> Vec<Value> {
    let mut vs: Vec<Value> = (-256..256).map(Value::Int).collect();
    for e in [63, 64] {
        for d in [-1, 0, 1] {
            let c = (BigInt::from(1) << e) + d;
            vs.extend([Value::int(-&c), Value::int(c)]);
        }
    }
    vs
}

/// Checks a law of the bit word `a.op` on the finite model of the `w`-digit values `0 ..< 2^w`,
/// which the word maps into itself: the evaluator gives the word's table on every pair, every
/// entry must again be a `w`-digit value, and the law is checked on the table, one lookup per
/// instance, so the work is the `4^w` evaluations of the table and one step per tuple checked.
pub(super) fn check_word(a: &Axiom, w: u32) -> Result<usize, String> {
    let size = 1usize << w;
    let mut table = Vec::with_capacity(size * size);
    for x in 0..size {
        for y in 0..size {
            let (vx, vy) = (Value::Int(x as i64), Value::Int(y as i64));
            match run(a.op, &[&vx, &vy]) {
                Value::Int(v) if (0..size as i64).contains(&v) => table.push(v as usize),
                other => return Err(format!("{x}, {y}: {other} has more than {w} digits")),
            }
        }
    }
    let t = |x: usize, y: usize| table[x * size + y];
    let member = |c: Const| match c {
        Const::Int(e) if (0..size as i64).contains(&e) => e as usize,
        other => panic!("{other:?} is no {w}-digit value"),
    };
    let mut n = 0;
    let mut holds = |what: &dyn Fn() -> String, ok: bool| {
        n += 1;
        if ok { Ok(()) } else { Err(what()) }
    };
    match a.law {
        Law::Associative => {
            for x in 0..size {
                for y in 0..size {
                    let xy = t(x, y);
                    for z in 0..size {
                        holds(&|| format!("{x}, {y}, {z}"), t(xy, z) == t(x, t(y, z)))?;
                    }
                }
            }
        }
        Law::Commutative => {
            for x in 0..size {
                for y in 0..size {
                    holds(&|| format!("{x}, {y}"), t(x, y) == t(y, x))?;
                }
            }
        }
        Law::Idempotent => {
            for x in 0..size {
                holds(&|| format!("{x}"), t(x, x) == x)?;
            }
        }
        Law::Identity(e) => {
            let e = member(e);
            for x in 0..size {
                holds(&|| format!("{e} and {x}"), t(e, x) == x && t(x, e) == x)?;
            }
        }
        Law::SelfInverse(e) => {
            let e = member(e);
            for x in 0..size {
                holds(&|| format!("{x}"), t(x, x) == e)?;
            }
        }
        other => panic!("{other:?} is not checked on the bit-word models"),
    }
    Ok(n)
}

/// Checks `op(x, k) == g(x, 2 ** k)`, a [`Law::PowerOfTwo`] of a shift, for every `x` of `xs`
/// and `k` of `ks`. Both sides must give a value: an error on both is no agreement here.
fn check_shift(a: &Axiom, xs: &[Value], ks: &[Value]) -> Result<usize, String> {
    let Law::PowerOfTwo(g) = a.law else {
        panic!("{:?} is not a law of a shift", a.law)
    };
    let v = |x: &Value| lit(x.clone());
    let mut n = 0;
    for x in xs {
        for k in ks {
            n += 1;
            let l = eval(&call(a.op, vec![v(x), v(k)]));
            let pow = call("**", vec![lit(Value::Int(2)), v(k)]);
            let r = eval(&call(g, vec![v(x), pow]));
            match (&l, &r) {
                (Ok(p), Ok(q)) if p == q => {}
                _ => return Err(format!("{x}, {k}: {l:?} against {r:?}")),
            }
        }
    }
    Ok(n)
}

/// Checks `a` on the values `vs` of its carrier.
fn check_on(a: &Axiom, vs: &[Value]) -> Result<usize, String> {
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
            for x in vs {
                eq(format!("{x}"), call(op, vec![v(x), v(x)]), v(x))?;
            }
        }
        Law::Identity(e) | Law::Zero(e) => {
            let e = constant(e);
            for x in vs {
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
            for x in vs {
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
            for x in vs {
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
        Law::Implies(other) => {
            for (x, y) in pairs() {
                n += 1;
                if holds(op, &[x, y]) && !holds(other, &[x, y]) {
                    return Err(format!("{x}, {y}"));
                }
            }
        }
        Law::Composes(next, result) => {
            for (x, y, z) in triples() {
                n += 1;
                if holds(op, &[x, y]) && holds(next, &[y, z]) && !holds(result, &[x, z]) {
                    return Err(format!("{x}, {y}, {z}"));
                }
            }
        }
        Law::SelfInverse(e) => {
            let e = constant(e);
            for x in vs {
                eq(format!("{x}"), call(op, vec![v(x), v(x)]), v(&e))?;
            }
        }
        Law::PowerOfTwo(_) => panic!("a shift is checked by `check_shift`"),
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
    assert_eq!(AXIOMS.len(), 129);
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
        claim("<=", Int, Law::Implies("<")), // 1 <= 1 but not 1 < 1
        claim("<=", Int, Law::Composes("<=", "<")), // 1 <= 1 <= 1 but not 1 < 1
        claim(">=", F64, Law::Composes(">=", ">")), // likewise at a float
        claim("<", F64, Law::Composes(">", "<")), // 0.0 < 1.0 > 0.0 but not 0.0 < 0.0
        claim("<=", F64, Law::Implies("==")), // 0.0 <= 1.0
        claim("<=", F64, Law::Composes(">=", "<=")), // 0.0 <= 2.0 >= 1.0 but not 2.0 <= 1.0
        claim("!=", F64, Law::Irreflexive),  // NaN != NaN
        claim("!=", F64, Law::Transitive),   // 0.0 != 1.0 != 0.0 but not 0.0 != 0.0
        claim("!=", Bool, Law::Transitive),  // true != false != true but not true != true
        claim("==", Bool, Law::Irreflexive), // true == true
        claim(">=", String, Law::Implies(">")), // "a" >= "a" but not "a" > "a"
        claim(">", String, Law::Total),      // neither "a" > "a"
        claim("<=", String, Law::Composes("<=", "<")), // "a" <= "a" <= "a" but not "a" < "a"
        claim("<", String, Law::Composes(">", "<")), // "a" < "b" > "a" but not "a" < "a"
        claim("bitOr", Int, Law::SelfInverse(Const::Int(0))), // bitOr(1, 1) is 1
        claim("bitAnd", Int, Law::Identity(Const::Int(0))), // bitAnd(0, 1) is 0
        claim("shr", Int, Law::PowerOfTwo("quot")), // shr(-1, 1) is -1, and -1 quot 2 is 0
        claim("shl", Int, Law::PowerOfTwo("mulI64")), // shl(1, 63) is 2^63, not -2^63
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
        Law::Implies(g) => format!("#implies({g:?})"),
        Law::Composes(g, r) => format!("#composes({g:?}, {r:?})"),
        Law::SelfInverse(k) => format!("#selfInverse({})", c(k)),
        Law::PowerOfTwo(g) => format!("#powerOfTwo({g:?})"),
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
    format!(
        "Axiom(op: {:?}, carrier: #{carrier}, property: {law}),",
        a.op
    )
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

/// The compositions sec:verification gives an order chain are axioms at `int`, `f64` and
/// `String` (DESIGN M0.11): in `a <= b < c <= d` each pair of links composes, and the chain ends
/// at `a < d`, which proves a `<=` law through `<` implying `<=`. The `>=`, `>` family is the
/// same, so `name <= "m" < other` on strings reaches `name < other` as it does on numbers.
#[test]
fn the_compositions_an_order_chain_needs_are_axioms() {
    use zedc::axioms::of;
    let has = |op: &str, c: Carrier, law: Law| of(op, c).any(|l| *l == law);
    for c in [Carrier::Int, Carrier::F64, Carrier::String] {
        for (strict, weak) in [("<", "<="), (">", ">=")] {
            let missing: Vec<String> = [
                (weak, Law::Transitive),
                (strict, Law::Transitive),
                (weak, Law::Composes(strict, strict)),
                (strict, Law::Composes(weak, strict)),
                (strict, Law::Implies(weak)),
            ]
            .into_iter()
            .filter(|&(op, law)| !has(op, c, law))
            .map(|(op, law)| format!("{op} {law:?}"))
            .collect();
            assert!(missing.is_empty(), "at {c:?}: {missing:?}");
        }
    }
    // No `<=` link turns into `<`, nor `>=` into `>`: a chain of weak links never proves a strict
    // law.
    for c in [Carrier::Int, Carrier::F64, Carrier::String] {
        assert!(!has("<=", c, Law::Implies("<")));
        assert!(!has("<=", c, Law::Composes("<=", "<")));
        assert!(!has(">=", c, Law::Implies(">")));
        assert!(!has(">=", c, Law::Composes(">=", ">")));
    }
    // At `String` a chain of one comparison composes by transitivity, `<` and `>` alike. No
    // carrier makes `!=` transitive: `a != b` and `b != a` do not give `a != a`.
    for op in ["<", "<=", ">", ">="] {
        assert!(has(op, Carrier::String, Law::Transitive), "{op}");
    }
    for c in [Carrier::Int, Carrier::F64, Carrier::Bool, Carrier::String] {
        assert!(!has("!=", c, Law::Transitive), "{c:?}");
    }
}

/// The float instances the order axioms are checked on hold a NaN, both zeros and both
/// infinities, so the f64 entries are checked where IEEE comparison departs from an order.
#[test]
fn the_float_instances_hold_the_ieee_corner_values() {
    let vs = values(Carrier::F64);
    let has = |x: f64| vs.iter().any(|v| *v == Value::float(x));
    assert!(
        vs.iter()
            .any(|v| matches!(v, Value::Float(x) if x.get().is_nan()))
    );
    for x in [0.0, -0.0, f64::INFINITY, f64::NEG_INFINITY] {
        assert!(has(x), "{x}");
    }
    // At a NaN neither premise of a composition holds: NaN <= NaN and NaN < 1.0 are false.
    let nan = Value::float(f64::NAN);
    assert!(!holds("<=", &[&nan, &nan]));
    assert!(!holds("<", &[&nan, &Value::float(1.0)]));
    // And `!=` is not irreflexive at `f64`, which is why the table gives it only `#symmetric`
    // there: `NaN != NaN`, and both ways round with any other float.
    assert!(holds("!=", &[&nan, &nan]));
    let one = Value::float(1.0);
    assert!(holds("!=", &[&nan, &one]) && holds("!=", &[&one, &nan]));
    let (inf, ninf) = (Value::float(f64::INFINITY), Value::float(f64::NEG_INFINITY));
    assert!(holds("!=", &[&inf, &ninf]) && holds("!=", &[&ninf, &inf]));
    assert!(!holds("!=", &[&inf, &inf]));
    // At the zeros, `-0.0 <= 0.0` and `0.0 <= -0.0` but neither `<` the other.
    let (z, nz) = (Value::float(0.0), Value::float(-0.0));
    assert!(le(&nz, &z) && le(&z, &nz));
    assert!(!holds("<", &[&nz, &z]) && !holds("<", &[&z, &nz]));
    // and `-0.0 != 0.0` is false both ways, as `==` holds between them.
    assert!(!holds("!=", &[&nz, &z]) && !holds("!=", &[&z, &nz]));
    assert!(holds(">=", &[&nz, &z]) && !holds(">", &[&z, &nz]));
}

/// Strings compare by code point, which is the byte order of their UTF-8 (sec:order): a proper
/// prefix first, `"é"` (U+00E9) after `"z"`, and U+E000 before U+10000, which UTF-16 code units
/// would put the other way. The evaluator's comparisons agree with that order on strings the
/// harness's `a`, `b` instances lack, and every `String` axiom of `!=` and the comparisons,
/// the compositions of an order chain among them, holds on them.
#[test]
fn strings_compare_by_code_point() {
    let words = [
        "",
        "a",
        "ab",
        "abc",
        "b",
        "z",
        "Z",
        "é",
        "e\u{301}",
        "\u{E000}",
        "\u{10000}",
        "a\u{0}",
    ];
    let vs: Vec<Value> = words.iter().map(|s| Value::str(s)).collect();
    for (x, sx) in vs.iter().zip(words) {
        for (y, sy) in vs.iter().zip(words) {
            let by_char = sx.chars().cmp(sy.chars());
            assert_eq!(sx.as_bytes().cmp(sy.as_bytes()), by_char, "{sx:?}, {sy:?}");
            for (op, want) in [
                ("<", by_char.is_lt()),
                ("<=", by_char.is_le()),
                (">", by_char.is_gt()),
                (">=", by_char.is_ge()),
                ("!=", by_char.is_ne()),
            ] {
                assert_eq!(holds(op, &[x, y]), want, "{sx:?} {op} {sy:?}");
            }
        }
    }
    let mut n = 0;
    for a in AXIOMS
        .iter()
        .filter(|a| a.carrier == Carrier::String && a.op != "++")
    {
        match check_on(a, &vs) {
            Ok(k) => n += k,
            Err(why) => panic!("{} at String: {:?} fails on {why}", a.op, a.law),
        }
    }
    assert!(n > 9_000, "{n} instances");
}

/// `==` is an equivalence and `!=` irreflexive and symmetric at every carrier but `f64`, where a
/// NaN makes both only symmetric (DESIGN M0.11): the table has exactly those laws of the two at
/// each carrier. At `bool` the evaluator's `==` and `!=` are the truth tables of equality and
/// exclusive or, on all four pairs.
#[test]
fn equality_has_its_laws_at_every_carrier() {
    use zedc::axioms::of;
    let laws = |op: &str, c: Carrier| of(op, c).copied().collect::<Vec<Law>>();
    for c in [Carrier::Int, Carrier::Bool, Carrier::String] {
        assert_eq!(
            laws("==", c),
            [Law::Reflexive, Law::Symmetric, Law::Transitive],
            "== at {c:?}"
        );
        assert_eq!(
            laws("!=", c),
            [Law::Irreflexive, Law::Symmetric],
            "!= at {c:?}"
        );
    }
    assert_eq!(laws("==", Carrier::F64), [Law::Symmetric, Law::Transitive]);
    assert_eq!(laws("!=", Carrier::F64), [Law::Symmetric]);
    for x in [false, true] {
        for y in [false, true] {
            let (a, b) = (Value::Bool(x), Value::Bool(y));
            assert_eq!(holds("==", &[&a, &b]), x == y, "{x} == {y}");
            assert_eq!(holds("!=", &[&a, &b]), x ^ y, "{x} != {y}");
        }
    }
}

/// The bit words' axioms hold on every value of 1 to 8 binary digits and on the values about
/// `2^63` and `2^64`, where the evaluator leaves machine integers; each width is checked, and the
/// number of instances is the count the models give.
#[test]
fn the_bit_word_axioms_hold_at_every_width_to_8() {
    let of = |op: &str| -> Vec<&Axiom> { AXIOMS.iter().filter(|a| a.op == op).collect() };
    for op in ["bitAnd", "bitOr", "bitXor"] {
        for a in of(op) {
            for w in 1..=8 {
                let n = check_word(a, w).unwrap_or_else(|why| panic!("{op} {:?}: {why}", a.law));
                let tuples = match a.law {
                    Law::Associative => 1 << (3 * w),
                    Law::Commutative => 1 << (2 * w),
                    _ => 1 << w,
                };
                assert_eq!(n, tuples, "{op} {:?} at width {w}", a.law);
            }
            check_on(a, &word_corners()).unwrap_or_else(|why| panic!("{op} {:?}: {why}", a.law));
        }
    }
    // The shifts: every `x` of at most 8 digits of either sign and the corners, every count
    // below 256, so `shl(1, 64)` and `shr(-1, 100)` are among them.
    for a in of("shl").into_iter().chain(of("shr")) {
        assert_eq!(check(a), Ok(524 * 256), "{} {:?}", a.op, a.law);
    }
    let v = |n: i64| Value::Int(n);
    assert_eq!(run("shl", &[&v(1), &v(64)]), near_two_pow(64, 0));
    assert_eq!(run("shr", &[&v(-1), &v(100)]), v(-1));
    assert_eq!(run("shr", &[&v(-7), &v(1)]), v(-4));
}

/// The harness rejects a false law of a shift, at the instance where it first fails: `shr` is
/// not division rounding toward zero, which differs on a negative `x` once the quotient is
/// inexact, and `shl` does not wrap at the signed 64-bit word, which it would only past
/// `2^63`, so the harness reaches values past the machine word.
#[test]
fn false_shift_axioms_are_refuted_where_they_fail() {
    let claim = |op, g| Axiom {
        op,
        carrier: Carrier::Int,
        law: Law::PowerOfTwo(g),
    };
    let first = |a: Axiom| check(&a).expect_err("refuted");
    // -256 div 2^k is exact up to k = 8; at k = 9 it is -1, and toward zero 0.
    assert!(first(claim("shr", "quot")).starts_with("-256, 9: "));
    // -256 * 2^k is at least -2^63 up to k = 55.
    assert!(first(claim("shl", "mulI64")).starts_with("-256, 56: "));
    // `shr` is not `shl`'s law, nor `shl` `shr`'s.
    assert!(first(claim("shr", "*")).starts_with("-256, 1: "));
    assert!(first(claim("shl", "div")).starts_with("-256, 1: "));
}
