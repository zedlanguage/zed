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
use zedc::check::ty::{Carrier, Piece};
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

/// The random functions of `x` and `y` from the seed `seed`, each checked and run at arguments
/// of each arrow of its signature, until `enough` holds of what they gave, or at most `cap`
/// functions.
fn computed_values(seed: u64, enough: impl Fn(&Computed) -> bool, cap: usize) -> Computed {
    let mut rng = Rng::new(seed);
    let mut c = Computed::default();
    for _ in 0..cap {
        if enough(&c) {
            break;
        }
        let f = format!("f(positional x, positional y) = {};\n", body(&mut rng, 3));
        let (i, _) = info(&f);
        if !i.errors.is_empty() {
            continue;
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
            let mut p = f.clone();
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
    c
}

/// The functions and values the test of computed values needs before it stops, and the most
/// functions it makes. Over 48 seeds it made 40 to 80 functions and ran 100 to 335 values, in
/// 0.15 to 0.4 s, eight runs at once at load 36; the cap is met only if the generator or the
/// checker stops giving functions.
const ENOUGH_FNS: usize = 40;
const ENOUGH_CHECKED: usize = 100;
const CAP: usize = 2_000;

#[test]
fn each_computed_value_is_in_its_arrows_result() {
    let seed = zed_tests::seed::seed("each_computed_value_is_in_its_arrows_result");
    let enough = |c: &Computed| c.fns >= ENOUGH_FNS && c.checked >= ENOUGH_CHECKED;
    let c = computed_values(seed, enough, CAP);
    println!(
        "{} functions, {} values, {} failed, {} arrows not called",
        c.fns, c.checked, c.failed, c.unfixed
    );
    assert!(
        enough(&c),
        "seed {seed}: {} functions, {} values",
        c.fns,
        c.checked
    );
    assert!(
        c.failed < c.checked / 4,
        "seed {seed}: {} failed of {}",
        c.failed,
        c.checked
    );
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

/// The runs of the programs of the seed `seed`, sets of functions with four definitions of `r`
/// over each, until `enough` holds of what they gave, or at most `cap` sets.
fn run_programs(seed: u64, enough: impl Fn(&Runs) -> bool, cap: usize) -> Runs {
    let mut runs = Runs::default();
    let mut g = Gen::new(seed);
    for _ in 0..cap {
        if enough(&runs) {
            break;
        }
        g.arity.clear();
        let count = 1 + g.rng.below(3);
        let helpers: String = (0..count).map(|_| g.helper()).collect();
        for _ in 0..4 {
            let p = format!("{helpers}r = {};\n", g.expr(&[], 3, false));
            let (i, _) = info(&p);
            if !i.errors.is_empty() {
                runs.rejected += 1;
                continue;
            }
            if i.tops["r"]
                .pieces()
                .iter()
                .any(|pc| matches!(pc, Piece::Fn(_)))
            {
                runs.functions += 1;
                continue;
            }
            let u = elab(&p).unwrap_or_else(|e| panic!("seed {seed}: {p}: {e:?}"));
            let t = u
                .get("r")
                .unwrap_or_else(|| panic!("seed {seed}: {p}: no `r`"));
            // Every run here takes far fewer steps; the fuel only stops a lambda that a
            // checker fault let apply itself.
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
    }
    runs
}

/// The programs run and the programs of each form of [`FORMS`] that the test of random
/// programs needs before it stops, and the most sets of functions it makes. Over 48 seeds it
/// ran 20 to 49 of 150 to 430 programs made, in 0.33 to 1.7 s, eight runs at once at load 40.
const ENOUGH_RAN: usize = 20;
const ENOUGH_OF_EACH_FORM: usize = 1;
const SETS_CAP: usize = 2_000;

/// Runs random programs and fails on any accepted program whose run raises a kernel type error
/// or gives a value its static type does not hold. The programs are made until enough of them
/// ran and each form of [`FORMS`] occurs among them, so a change that stopped the generator
/// making one, or the checker accepting it, fails here at the cap rather than testing less
/// without notice.
#[test]
fn accepted_random_programs_raise_no_type_error() {
    let seed = zed_tests::seed::seed("accepted_random_programs_raise_no_type_error");
    let enough =
        |r: &Runs| r.ran >= ENOUGH_RAN && r.forms.iter().all(|&f| f >= ENOUGH_OF_EACH_FORM);
    let r = run_programs(seed, enough, SETS_CAP);
    println!(
        "{} ran, {} rejected, {} may give a function, {} stopped, forms {:?}",
        r.ran, r.rejected, r.functions, r.stopped, r.forms
    );
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
    // Nearly every type of `r` has a kernel type, so the test above sees nearly every value.
    assert!(
        r.untyped * 10 < r.ran,
        "seed {seed}: {} of {} values run have no kernel type to test",
        r.untyped,
        r.ran
    );
    assert!(
        r.ran >= ENOUGH_RAN,
        "seed {seed}: only {} programs ran in {SETS_CAP} sets; {} were rejected, {} may give a \
         function and {} stopped",
        r.ran,
        r.rejected,
        r.functions,
        r.stopped
    );
    for (k, (name, _)) in FORMS.iter().enumerate() {
        assert!(
            r.forms[k] >= ENOUGH_OF_EACH_FORM,
            "seed {seed}: only {} programs run in {SETS_CAP} sets use {name}",
            r.forms[k]
        );
    }
}
