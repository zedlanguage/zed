//! Soundness on random programs (DESIGN.md rule 4: a program the checker accepts never meets a
//! kernel type error at run time). For each arrow the checker gives a random function of
//! scalars, each value the evaluator computes at arguments of the arrow's parameter types lies
//! in its result; and no random program the checker accepts, of functions of no declared
//! parameter types that destructure tuples, compute on the components of a pair, call their
//! parameters, take lambdas and use `^` and the bit words, raises a kernel type error when it
//! runs or gives a value outside the static type of its result. Each run takes a new seed and
//! prints it; `ZED_TEST_SEED=<seed>` makes the same programs again ([`zed_tests::seed::seed`]).

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::{Evaluator, F64, KernelError, Term, Value, World};
use zed_tests::instances::Rng;
use zedc::check::ty::{Carrier, Piece, Ty};
use zedc::elab::Cones;
use zedc::rejection::Row;

use super::info;
use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};

/// A random body over `x` and `y`, of depth at most `d`.
fn body(rng: &mut Rng, d: u32) -> String {
    if d == 0 || rng.below(3) == 0 {
        return match rng.below(7) {
            0 | 1 => "x".into(),
            2 | 3 => "y".into(),
            // A literal takes the carrier it meets.
            4 => rng.int(-3, 3).to_string(),
            5 => format!("{}.5", rng.int(-2, 2)),
            _ => "\"s\"".into(),
        };
    }
    let a = body(rng, d - 1);
    let b = body(rng, d - 1);
    match rng.below(9) {
        0 => format!("({a} + {b})"),
        1 => format!("({a} - {b})"),
        2 => format!("({a} * {b})"),
        3 => format!("({a} / {b})"),
        4 => format!("({a} ++ {b})"),
        5 => format!("(-{a})"),
        6 => format!("if {a} < {b} {{ {a} }} else {{ {b} }}"),
        7 => format!("if {a} == {b} {{ {b} }} else {{ {a} }}"),
        _ => format!("(if {a} is String {{ len({a}) }} else {{ {b} }})"),
    }
}

/// Argument texts of carrier `c`.
fn args(c: Carrier) -> &'static [&'static str] {
    match c {
        Carrier::Int => &["0", "2", "-3"],
        Carrier::F64 => &["0.0f64", "1.5f64", "-2.25f64"],
        Carrier::F32 => &["0.0f32", "1.5f32", "-2.25f32", "1e-45f32"],
        Carrier::Rat => &["0r", "3r/2r", "(0r - 2r)"],
        Carrier::Str => &["\"\"", "\"ab\""],
        Carrier::Bool => &["true", "false"],
    }
}

/// What the random functions of `x` and `y` of one seed gave ([`computed_values`]).
#[derive(Default)]
struct Computed {
    /// Functions the checker accepted.
    fns: usize,
    /// Values run, each of which lies in the result of its arrow.
    checked: usize,
    /// Runs that stopped with another error than a type error.
    failed: usize,
    /// Arrows not called, since a decimal literal of the body reaches the call's value with
    /// nothing to give it a carrier, as `2.5` of `if x == 2.5 { 2.5 } else { x }` at an `int`
    /// `x`, which the checker rejects at the call (DESIGN.md L1.26b).
    unfixed: usize,
}

/// The `bodies` random functions of `x` and `y` from the seed `seed`, each checked and run at
/// arguments of each arrow of its signature ([`compute`]).
fn computed_values(seed: u64, bodies: usize) -> Computed {
    let mut rng = Rng::new(seed);
    let mut c = Computed::default();
    for _ in 0..bodies {
        let f = format!("f(positional x, positional y) = {};\n", body(&mut rng, 3));
        compute(seed, &f, &mut c);
    }
    c
}

/// Checks the function `f` of `x` and `y`, of seed `seed` (0 for a built function), and if the
/// checker accepts it, runs it at arguments of each arrow of its signature, adding to `c`.
fn compute(seed: u64, f: &str, c: &mut Computed) {
    let (i, _) = info(f);
    if !i.errors.is_empty() {
        return;
    }
    let s = i.sigs.values().next().unwrap().clone();
    c.fns += 1;
    // One call for each arrow with carrier parameters and each pair of arguments.
    let arrows = s.expand();
    let mut by_arrow = Vec::new();
    for a in &arrows {
        let cs: Option<Vec<Carrier>> = a
            .params
            .iter()
            .map(|p| match p.pieces().as_slice() {
                [pc] => pc.carrier(),
                _ => None,
            })
            .collect();
        let Some(cs) = cs else { continue };
        let calls: Vec<String> = (args(cs[0]).iter())
            .flat_map(|x| args(cs[1]).iter().map(move |y| format!("f({x}, {y})")))
            .collect();
        by_arrow.push((calls, &a.result));
    }
    // The program of `f` and the calls `calls`, the `k`th bound to `rk`.
    let program = |calls: &mut dyn Iterator<Item = &String>| {
        let mut p = f.to_string();
        for (k, call) in calls.enumerate() {
            p += &format!("r{k} = {call};\n");
        }
        p
    };
    let u = match elab(&program(&mut by_arrow.iter().flat_map(|(cs, _)| cs))) {
        Ok(u) => u,
        Err(_) => {
            // An arrow whose calls the checker rejects as holding a decimal literal that
            // nothing gives a carrier is left out; any other rejection is a fault.
            by_arrow.retain(|(calls, _)| {
                let (i, _) = info(&program(&mut calls.iter()));
                let unfixed = i.errors.iter().all(|e| e.row == Some(Row::UnfixedDecimal));
                assert!(unfixed, "seed {seed}: {f}{calls:?}: {:?}", i.errors);
                c.unfixed += usize::from(!i.errors.is_empty());
                i.errors.is_empty()
            });
            let p = program(&mut by_arrow.iter().flat_map(|(cs, _)| cs));
            elab(&p).unwrap_or_else(|e| panic!("seed {seed}: {p}: {e:?}"))
        }
    };
    // One index of the unit for all its calls, where `Unit::get` makes one for each.
    let cones = Cones::new(&u);
    let kernels: HashMap<&str, &Arc<str>> = u
        .defs
        .iter()
        .map(|d| (d.name.as_str(), &d.kernel))
        .collect();
    let calls = by_arrow
        .iter()
        .flat_map(|(cs, r)| cs.iter().map(move |c| (c, *r)));
    for (k, (call, result)) in calls.enumerate() {
        let t = cones.close(Term::Var(kernels[format!("r{k}").as_str()].clone()));
        match Evaluator::new(World::new()).run(&with_prelude(t)) {
            Ok(v) => {
                assert!(
                    result.contains(&v),
                    "seed {seed}: {f}{call}: {v} is not in {result}"
                );
                c.checked += 1;
            }
            // An accepted program never meets a type error (DESIGN.md rule 4).
            Err(KernelError::Type(m)) => panic!("seed {seed}: {f}{call}: type error: {m}"),
            // Another run-time error; a division by zero is the atom, a value.
            Err(_) => c.failed += 1,
        }
    }
}

/// The random functions the test of computed values makes. Drawn until 40 were accepted and
/// 100 values checked, 24 seeds (101 to 124) took 71 to 112 functions, 81 on average.
const BODIES: usize = 81;

/// A function the checker accepts whose arrows have carrier parameters, so its values are
/// run and checked: the case the test of computed values meets if no random function does.
const BUILT_COMPUTED: &str = "f(positional x, positional y) = x + y;\n";

#[test]
fn each_computed_value_is_in_its_arrows_result() {
    let seed = zed_tests::seed::seed("each_computed_value_is_in_its_arrows_result");
    let c = computed_values(seed, BODIES);
    println!(
        "{} functions, {} values, {} failed, {} arrows not called",
        c.fns, c.checked, c.failed, c.unfixed
    );
    // The values checked: by the random functions, or else by the function built for it.
    if c.checked == 0 {
        println!("values checked only by the function built for it");
        let mut b = Computed::default();
        compute(0, BUILT_COMPUTED, &mut b);
        assert!(b.checked > 0, "{BUILT_COMPUTED}: no value checked");
    }
}

#[test]
fn the_function_built_to_be_computed_has_its_values_checked() {
    let mut c = Computed::default();
    compute(0, BUILT_COMPUTED, &mut c);
    assert_eq!(c.fns, 1, "{BUILT_COMPUTED}: rejected");
    assert!(c.checked > 0, "{BUILT_COMPUTED}: no value checked");
    assert_eq!(c.failed, 0, "{BUILT_COMPUTED}: a run failed");
}

#[test]
fn a_wrong_claim_is_caught() {
    // The check above would reject a result type that missed the value.
    let (i, _) = info("f(positional x, positional y) = x + y;\n");
    let a = &i.sigs.values().next().unwrap().expand()[0];
    assert!(a.result.contains(&Value::Int(3)));
    assert!(!a.result.contains(&Value::Float(F64::new(3.0))));
    assert!(!a.result.contains(&Value::Str("3".into())));
}

/// A random program: one to three functions `h0`, `h1`, `h2` of no declared parameter types,
/// each of which may call those before it, and a top-level definition `r` that calls them.
///
/// The value a name holds is small: an argument is a literal, a name, a tuple, a lambda or an
/// `if` of these, never the result of arithmetic, and an exponent or a shift amount is a
/// literal or a name, so no run builds a number of more than a few thousand bits.
struct Gen {
    rng: Rng,
    /// For each function so far, `h0` first, its number of parameters and what it does with
    /// its first.
    arity: Vec<(usize, First)>,
    /// The number of lambdas so far, which names the next one's parameter.
    lambdas: usize,
}

/// What a function does with its first parameter, which the arguments of its calls follow.
#[derive(Clone, Copy)]
enum First {
    /// Anything else.
    Value,
    /// It calls it: a call passes a lambda most often.
    Called,
    /// It computes on two components of it, as `p[0] + p[1]`: a call passes a pair most
    /// often, whose literals the body computes on (item SOUND-top-literals).
    Pair,
}

/// The bit words of two int operands, the shifts, the words of one operand and a width, and
/// the rotations.
const WORDS2: [&str; 3] = ["bitAnd", "bitOr", "bitXor"];
const SHIFTS: [&str; 2] = ["shl", "shr"];
const WIDTH1: [&str; 3] = ["bitNot", "leadingZeros", "trailingZeros"];
const ROTATES: [&str; 2] = ["rotl", "rotr"];

impl Gen {
    fn new(seed: u64) -> Self {
        Gen {
            rng: Rng::new(seed),
            arity: Vec::new(),
            lambdas: 0,
        }
    }

    /// A literal of one of the five carriers, or a name of `scope`.
    fn leaf(&mut self, scope: &[&str]) -> String {
        if !scope.is_empty() && self.rng.below(2) == 0 {
            return self.rng.pick(scope).to_string();
        }
        match self.rng.below(8) {
            0..=3 => self.rng.int(-3, 3).to_string(),
            4 => format!("{}.5", self.rng.int(-2, 2)),
            5 => self.rng.pick(&["\"s\"", "\"ab\""]).to_string(),
            6 => self.rng.pick(&["true", "false"]).to_string(),
            _ => self.rng.int(0, 3).to_string(),
        }
    }

    /// An exponent or a shift amount: a name of `scope`, or an int from -2 to 3.
    fn amount(&mut self, scope: &[&str]) -> String {
        if !scope.is_empty() && self.rng.below(2) == 0 {
            self.rng.pick(scope).to_string()
        } else {
            self.rng.int(-2, 3).to_string()
        }
    }

    /// An argument of depth at most `d`: a literal, a name, a tuple, a lambda when `fns`, or an
    /// `if` of these. A tuple holds no lambda, which the checker rejects.
    fn arg(&mut self, scope: &[&str], d: u32, fns: bool) -> String {
        if d == 0 || self.rng.below(3) == 0 {
            return self.leaf(scope);
        }
        match self.rng.below(5) {
            0 => format!(
                "({}, {})",
                self.arg(scope, d - 1, false),
                self.arg(scope, d - 1, false)
            ),
            1 => format!(
                "({}, {}, {})",
                self.arg(scope, d - 1, false),
                self.arg(scope, d - 1, false),
                self.arg(scope, d - 1, false)
            ),
            2 | 3 if fns => self.lambda(scope, d),
            _ => {
                let (a, b) = (self.leaf(scope), self.leaf(scope));
                let (t, e) = (self.arg(scope, d - 1, fns), self.arg(scope, d - 1, fns));
                format!("if {a} < {b} {{ {t} }} else {{ {e} }}")
            }
        }
    }

    /// A lambda of one parameter, its body of depth below `d`. The body calls no name, so no
    /// lambda applies itself.
    fn lambda(&mut self, scope: &[&str], d: u32) -> String {
        let v = format!("v{}", self.lambdas);
        self.lambdas += 1;
        let mut inner = scope.to_vec();
        inner.push(&v);
        let body = self.expr(&inner, d - 1, false);
        format!("({v} -> {body})")
    }

    /// The arguments of a call of `n` parameters, the first most often a lambda or a pair as
    /// `first` says the function called uses it.
    fn args(&mut self, scope: &[&str], n: usize, first: First) -> String {
        let a: Vec<String> = (0..n)
            .map(
                |k| match (k == 0 && self.rng.below(4) > 0).then_some(first) {
                    Some(First::Called) => self.lambda(scope, 2),
                    Some(First::Pair) => format!(
                        "({}, {})",
                        self.arg(scope, 1, false),
                        self.arg(scope, 1, false)
                    ),
                    Some(First::Value) | None => self.arg(scope, 2, true),
                },
            )
            .collect();
        a.join(", ")
    }

    /// An expression of depth at most `d` over the names of `scope`, which may call the
    /// functions so far, and the names of `scope` when `calls`.
    fn expr(&mut self, scope: &[&str], d: u32, calls: bool) -> String {
        if d == 0 || self.rng.below(4) == 0 {
            return self.leaf(scope);
        }
        let e = |g: &mut Self| g.expr(scope, d - 1, calls);
        match self.rng.below(24) {
            0 => format!("({} + {})", e(self), e(self)),
            1 => format!("({} - {})", e(self), e(self)),
            2 => format!("({} * {})", e(self), e(self)),
            3 => format!("({} / {})", e(self), e(self)),
            4 => format!("({} ++ {})", e(self), e(self)),
            5 => format!("(-{})", e(self)),
            6 | 7 => format!("({})^{}", e(self), self.amount(scope)),
            8 => {
                let (a, b) = (e(self), e(self));
                format!("if {a} < {b} {{ {a} }} else {{ {b} }}")
            }
            9 => {
                // Most often a comparison; else a condition that may not be a bool.
                let c = match self.rng.below(3) {
                    0 => e(self),
                    _ => format!("{} == {}", e(self), e(self)),
                };
                format!("if {c} {{ {} }} else {{ {} }}", e(self), e(self))
            }
            10 => {
                let (a, b) = (e(self), e(self));
                format!("if {a} is int {{ {a} }} else {{ {b} }}")
            }
            11 => {
                let (a, b) = (e(self), e(self));
                format!("(if {a} is String {{ len({a}) }} else {{ {b} }})")
            }
            12 => format!("({}, {})", e(self), e(self)),
            13 => format!("({})[{}]", e(self), self.rng.below(3)),
            14..=16 if !self.arity.is_empty() => {
                let h = self.rng.below(self.arity.len());
                let (n, first) = self.arity[h];
                format!("h{h}({})", self.args(scope, n, first))
            }
            17 if calls && !scope.is_empty() => {
                let f = self.rng.pick(scope);
                format!("{f}({})", self.args(scope, 1, First::Value))
            }
            18 => format!(
                "{}({})",
                self.lambda(scope, d),
                self.args(scope, 1, First::Value)
            ),
            19 => {
                let w = self.rng.pick(&WORDS2);
                format!("{w}({}, {})", e(self), e(self))
            }
            20 => {
                let w = self.rng.pick(&SHIFTS);
                format!("{w}({}, {})", e(self), self.amount(scope))
            }
            21 => match self.rng.below(3) {
                0 => format!("popCount({})", e(self)),
                1 => format!("{}({}, width: 8)", self.rng.pick(&WIDTH1), e(self)),
                _ => {
                    let w = self.rng.pick(&ROTATES);
                    format!("{w}({}, {}, width: 8)", e(self), self.amount(scope))
                }
            },
            22 => format!("sum({})", e(self)),
            _ => format!("{}({})", self.rng.pick(&["int", "String", "f64"]), e(self)),
        }
    }

    /// The next function `h{i}`: a body that destructures its first parameter, a call of a
    /// function before it that passes its parameters on, a body that calls its first parameter,
    /// a body that gives its first parameter to `^`, a shift or a bit word, a body that
    /// computes on two components of its first parameter, or a body of one expression.
    fn helper(&mut self) -> String {
        let i = self.arity.len();
        let n = 1 + self.rng.below(2);
        let mut scope: Vec<&str> = ["p", "q"][..n].to_vec();
        let head: Vec<String> = scope.iter().map(|p| format!("positional {p}")).collect();
        let head = head.join(", ");
        let mut first = First::Value;
        let text = match self.rng.below(6) {
            4 => {
                // Each operand a component of `p`, or a literal or `q`.
                first = First::Pair;
                let operand = |g: &mut Self| match g.rng.below(3) {
                    0 => "p[0]".to_string(),
                    1 => "p[1]".to_string(),
                    _ => g.leaf(&scope[1..]),
                };
                let (a, b) = (operand(self), operand(self));
                let body = match self.rng.below(4) {
                    0 => format!("({a} + {b})"),
                    1 => format!("({a} - {b})"),
                    2 => format!("({a} * {b})"),
                    _ => format!("(-{a})"),
                };
                format!("h{i}({head}) = {body};\n")
            }
            0 => {
                let k = 2 + self.rng.below(2);
                let names = &["a", "b", "c"][..k];
                scope.extend(names);
                let body = self.expr(&scope, 3, true);
                format!(
                    "h{i}({head}) {{\n  {} = p;\n  return {body};\n}}\n",
                    names.join(", ")
                )
            }
            1 if i > 0 => {
                let h = self.rng.below(i);
                first = self.arity[h].1;
                let a: Vec<&str> = (0..self.arity[h].0)
                    .map(|_| self.rng.pick(&scope))
                    .collect();
                format!("h{i}({head}) = h{h}({});\n", a.join(", "))
            }
            2 => {
                first = First::Called;
                let a = self.expr(&scope[1..], 2, false);
                let body = match self.rng.below(2) {
                    0 => format!("p({a})"),
                    _ => format!("({} + p({a}))", self.expr(&scope, 1, false)),
                };
                format!("h{i}({head}) = {body};\n")
            }
            3 => {
                // The domain of the operation falls on `p`: `^` and a shift take an amount
                // of at least 0, and a bit word an operand of at least 0.
                let x = self.leaf(&scope);
                let body = match self.rng.below(5) {
                    0 => format!("({x})^p"),
                    1 => format!("{}({x}, p)", self.rng.pick(&SHIFTS)),
                    2 => format!("{}(p, {x})", self.rng.pick(&WORDS2)),
                    3 => "popCount(p)".to_string(),
                    _ => format!("{}(p, {x}, width: 8)", self.rng.pick(&ROTATES)),
                };
                format!("h{i}({head}) = {body};\n")
            }
            _ => format!("h{i}({head}) = {};\n", self.expr(&scope, 3, true)),
        };
        self.arity.push((n, first));
        text
    }
}

/// The forms counted among the programs run, each with what shows it in a program's text.
const FORMS: [(&str, &[&str]); 8] = [
    ("destructuring", &[" = p;"]),
    ("lambda", &[" -> "]),
    ("power", &[")^"]),
    (
        "bit word",
        &[
            "bit",
            "shl(",
            "shr(",
            "popCount(",
            "Zeros(",
            "rotl(",
            "rotr(",
        ],
    ),
    ("tuple", &["(("]),
    ("call of a parameter", &[" p(", " q(", "(p(", "(q("]),
    ("call passed on", &[") = h"]),
    ("components of a pair", &["p[0]", "p[1]"]),
];

/// What the random programs of some seeds gave.
#[derive(Default)]
struct Runs {
    /// Programs the checker accepted that ran to a value.
    ran: usize,
    /// Programs the checker rejected.
    rejected: usize,
    /// Accepted programs whose `r` may be a function, which a run does not give.
    functions: usize,
    /// Runs that stopped for another reason than a type error: out of fuel, or a number too
    /// large to build.
    stopped: usize,
    /// For each form of [`FORMS`], the programs run that use it.
    forms: [usize; FORMS.len()],
    /// Each accepted program whose run raised a kernel type error, with the error.
    type_errors: Vec<String>,
    /// Each accepted program whose run gave a value that its static type does not hold
    /// (item SOUND-top-literals), with the value and the type.
    outside: Vec<String>,
    /// Programs run whose type of `r` has no kernel type to test the value against.
    untyped: usize,
}

/// Whether a value of `ty` may be or hold a function, which a run cannot give as its result:
/// the evaluator refuses a result that is a function or holds one at any depth, in a tuple
/// component or an atom's payload ("the program's result holds a function"). The checker is
/// right to accept such a program, since a tuple may hold a function (DESIGN.md step L1.17).
/// A family is data, but the test has always skipped one at the top as a function, and still
/// does. A kind-wide part, `(..)`, may hold a function too ([`Ty::first_order`]). It reads the
/// outer level of `ty` only: each row and payload shape keeps what it holds at any depth.
///
/// Assumption, not proved: a value the evaluator refuses as holding a function always has a
/// static type that [`Ty::first_order`] reports as holding one, so a type variable or the
/// unknown at a component never stands for a function in a value that runs. Evidence: the six
/// programs of [`RESULTS_HOLDING_FUNCTIONS`] and 64 further seeds (3000 to 3063) raised no such
/// refusal with this test (2026-11-14). A program it misses fails this test with the refusal,
/// which then shows the case.
fn may_give_function(ty: &Ty) -> bool {
    !ty.first_order() || ty.pieces().iter().any(|pc| matches!(pc, Piece::Fn(_)))
}

/// The runs of the programs of the seed `seed`: `sets` sets of functions with four definitions
/// of `r` over each ([`run_program`]).
fn run_programs(seed: u64, sets: usize) -> Runs {
    let mut runs = Runs::default();
    let mut g = Gen::new(seed);
    for _ in 0..sets {
        g.arity.clear();
        let count = 1 + g.rng.below(3);
        let helpers: String = (0..count).map(|_| g.helper()).collect();
        for _ in 0..4 {
            let p = format!("{helpers}r = {};\n", g.expr(&[], 3, false));
            run_program(seed, &p, &mut runs);
        }
    }
    runs
}

/// Checks the program `p` of seed `seed` (0 for a built program), and if the checker accepts it
/// and its `r` holds no function, runs it, adding to `runs`.
fn run_program(seed: u64, p: &str, runs: &mut Runs) {
    let (i, _) = info(p);
    if !i.errors.is_empty() {
        runs.rejected += 1;
        return;
    }
    if may_give_function(&i.tops["r"]) {
        runs.functions += 1;
        return;
    }
    let u = elab(p).unwrap_or_else(|e| panic!("seed {seed}: {p}: {e:?}"));
    let t = u
        .get("r")
        .unwrap_or_else(|| panic!("seed {seed}: {p}: no `r`"));
    // Every run here takes far fewer steps; the fuel only stops a lambda that a checker fault let
    // apply itself.
    let mut ev = Evaluator::new(World::new()).with_fuel(1_000_000);
    match ev.run(&with_prelude(t)) {
        Ok(v) => {
            runs.ran += 1;
            // The value lies in the static type of `r` (DESIGN.md rule 4).
            let ty = &i.tops["r"];
            match ty.kernel() {
                Some(k) if !k.contains(&v) => runs
                    .outside
                    .push(format!("{p}value {v} is not in its type {ty}")),
                Some(_) => {}
                None => runs.untyped += 1,
            }
            for (k, (_, marks)) in FORMS.iter().enumerate() {
                runs.forms[k] += usize::from(marks.iter().any(|m| p.contains(m)));
            }
        }
        Err(KernelError::Type(m)) => {
            runs.type_errors.push(format!("{p}type error: {m}"));
        }
        Err(_) => runs.stopped += 1,
    }
}

/// The sets of functions the test of random programs makes. Drawn until 20 programs ran and
/// each form of [`FORMS`] occurred among them, 24 seeds (101 to 124) took 27 to 79 sets, 46 on
/// average.
const SETS: usize = 46;

/// For each form of [`FORMS`], a program the checker accepts whose `r` holds no function and
/// has a kernel type, which runs to a value and uses the form: the case the test of random
/// programs meets if no random program does.
const BUILT_FORMS: [&str; FORMS.len()] = [
    "h0(positional p) {\n  a, b = p;\n  return a + b;\n}\nr = h0((1, 2));\n",
    "r = (v0 -> v0 + 1)(2);\n",
    "r = (2)^3;\n",
    "r = bitAnd(6, 3);\n",
    "r = ((1, 2), 3);\n",
    "h0(positional p) = p(3);\nr = h0((v0 -> v0));\n",
    "h0(positional p) = p + 1;\nh1(positional p) = h0(p);\nr = h1(2);\n",
    "h0(positional p) = (p[0] + p[1]);\nr = h0((1, 2));\n",
];

/// The runs of the program built for form `k` of [`FORMS`].
fn built_form(k: usize) -> Runs {
    let mut runs = Runs::default();
    run_program(0, BUILT_FORMS[k], &mut runs);
    runs
}

/// Fails on any program of `r` that raised a kernel type error or gave a value outside the
/// static type of `r`.
fn assert_sound(seed: u64, r: &Runs) {
    assert!(
        r.type_errors.is_empty(),
        "seed {seed}: {} accepted programs raised a kernel type error:\n{}",
        r.type_errors.len(),
        r.type_errors.join("----\n")
    );
    assert!(
        r.outside.is_empty(),
        "seed {seed}: {} accepted programs gave a value outside the type of `r`:\n{}",
        r.outside.len(),
        r.outside.join("----\n")
    );
}

/// Runs random programs and fails on any accepted program whose run raises a kernel type error
/// or gives a value its static type does not hold. Each form of [`FORMS`] that no random
/// program run uses is met by the program built for it, and a value tested against a kernel
/// type likewise, so a change that stopped the checker accepting a form, or running it, fails
/// here rather than testing less without notice.
#[test]
fn accepted_random_programs_raise_no_type_error() {
    let seed = zed_tests::seed::seed("accepted_random_programs_raise_no_type_error");
    let r = run_programs(seed, SETS);
    println!(
        "{} ran, {} rejected, {} may give a function, {} stopped, {} untyped, forms {:?}",
        r.ran, r.rejected, r.functions, r.stopped, r.untyped, r.forms
    );
    assert_sound(seed, &r);
    for (k, (name, _)) in FORMS.iter().enumerate() {
        if r.forms[k] == 0 {
            println!("{name} met only by the program built for it");
            let b = built_form(k);
            assert_sound(0, &b);
            assert_eq!(b.forms[k], 1, "{}: does not run {name}", BUILT_FORMS[k]);
        }
    }
    if r.ran == r.untyped {
        println!("a value tested against its type only by a program built for it");
        let b = built_form(0);
        assert_eq!((b.ran, b.untyped), (1, 0), "{}: not tested", BUILT_FORMS[0]);
    }
}

/// The test of random programs with the specific fixes off (TEST-random-sweep-off,
/// `obligation_test_modes`): the end-of-walk check of uses no step discharged
/// (CHK-obligation-sweep) refuses alone what those fixes refuse, so no accepted program raises
/// a kernel type error. A seed this fails on and the test above passes is a fault the end-of-walk
/// check misses; a seed both fail on is a fault neither catches.
#[test]
fn accepted_random_programs_raise_no_type_error_with_the_fixes_off() {
    let seed = zed_tests::seed::seed("accepted_random_programs_raise_no_type_error_with_the_fixes_off");
    zedc::check::obligation_test_modes::set(true, false);
    let r = run_programs(seed, SETS);
    zedc::check::obligation_test_modes::set(false, false);
    println!(
        "{} ran, {} rejected, {} may give a function, {} stopped, {} untyped",
        r.ran, r.rejected, r.functions, r.stopped, r.untyped
    );
    assert_sound(seed, &r);
}

#[test]
fn each_program_built_for_a_form_runs_and_uses_it() {
    for (k, (name, _)) in FORMS.iter().enumerate() {
        let b = built_form(k);
        assert_sound(0, &b);
        assert_eq!(
            (b.ran, b.untyped, b.forms[k]),
            (1, 0, 1),
            "{}: does not run {name} to a value of a kernel type",
            BUILT_FORMS[k]
        );
    }
}

/// The programs of seeds 1006, 1067, 1184, 2040, 2237 and 15863670430612687588 whose `r` holds
/// a function inside a tuple (row FAIL-random-result-holds-function): the checker accepts each,
/// the evaluator refuses each result as holding a function, and the test of random programs
/// skips each as one that may give a function, as it skips a function at the top.
const RESULTS_HOLDING_FUNCTIONS: [&str; 6] = [
    "h0(positional p, positional q) = popCount(p);\n\
     r = (v9 -> (v10 -> (if v9 is String { len(v9) } else { v10 }))(((v9, v9), v9, v9)))((v11 -> \"s\"));\n",
    "h0(positional p, positional q) = bitAnd(p, p);\n\
     h1(positional p, positional q) = popCount(p);\n\
     h2(positional p) = p;\n\
     r = ((-0), h2((v50 -> (v50 - 0))));\n",
    "h0(positional p, positional q) = (-2, p);\n\
     h1(positional p) = h0(p, p);\n\
     r = h1((v15 -> v15));\n",
    // A function in a union inside a tuple.
    "h0(positional p, positional q) = (q, q);\n\
     r = h0(\"s\", if -1 < -3 { false } else { (v69 -> v69) });\n",
    "h0(positional p) = rotr(p, 3, width: 8);\n\
     r = (v114 -> (String(-2), v114))((v115 -> -3));\n",
    "h0(positional p) = (p, p(p));\n\
     h1(positional p) = p;\n\
     h2(positional p) = h1(p);\n\
     r = (h0((v124 -> (v125 -> v125)((v126 -> 3)))), h2((v127 -> f64(v127))));\n",
];

#[test]
fn a_result_holding_a_function_in_a_tuple_is_skipped() {
    for p in RESULTS_HOLDING_FUNCTIONS {
        let (i, _) = info(p);
        assert!(i.errors.is_empty(), "{p}rejected: {:?}", i.errors);
        let ty = &i.tops["r"];
        assert!(
            may_give_function(ty),
            "{p}`r : {ty}` holds a function and is not skipped"
        );
        let u = elab(p).unwrap_or_else(|e| panic!("{p}{e:?}"));
        let t = u.get("r").unwrap_or_else(|| panic!("{p}no `r`"));
        let mut ev = Evaluator::new(World::new()).with_fuel(1_000_000);
        match ev.run(&with_prelude(t)) {
            Err(KernelError::Type(m)) => assert_eq!(m, "the program's result holds a function"),
            other => panic!("{p}the run gave {other:?}, not the refusal of a held function"),
        }
    }
}

#[test]
fn a_result_of_data_alone_is_not_skipped() {
    // A tuple, a payload and a scalar with no function: the test runs these.
    for p in [
        "r = (1, (2, \"s\"));\n",
        "h0(positional p) = #a(p, (p, 1));\nr = h0(3);\n",
        "r = 2 + 3;\n",
    ] {
        let (i, _) = info(p);
        assert!(i.errors.is_empty(), "{p}rejected: {:?}", i.errors);
        let ty = &i.tops["r"];
        assert!(!may_give_function(ty), "{p}`r : {ty}` is skipped");
    }
}

/// The seeds that found row FAIL-random-result-holds-function, each with the sets of functions
/// the test of random programs made for it when it stopped once 20 programs ran and each form
/// occurred, so each seed runs the same programs as when it found the row.
const RESULT_HOLDING_SEEDS: [(u64, usize); 6] = [
    (1006, 52),
    (1067, 113),
    (1184, 73),
    (2040, 48),
    (2237, 99),
    (15_863_670_430_612_687_588, 90),
];

/// The seeds that found row FAIL-random-result-holds-function, run as the test of random
/// programs ran them.
#[test]
fn the_seeds_of_results_holding_functions_raise_no_type_error() {
    for (seed, sets) in RESULT_HOLDING_SEEDS {
        let r = run_programs(seed, sets);
        assert_sound(seed, &r);
        assert!(r.functions > 0, "seed {seed}: no program skipped");
    }
}
