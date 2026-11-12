//! Soundness on random programs (DESIGN.md rule 4: a program the checker accepts never meets a
//! kernel type error at run time). For each arrow the checker gives a random function of
//! scalars, each value the evaluator computes at arguments of the arrow's parameter types lies
//! in its result; and no random program the checker accepts, of functions of no declared
//! parameter types that destructure tuples, call their parameters, take lambdas and use `^`
//! and the bit words, raises a kernel type error when it runs. The seeds are fixed, so each
//! run makes the same programs.

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::{Evaluator, F64, KernelError, Term, Value, World};
use zed_tests::instances::Rng;
use zedc::check::ty::{Carrier, Piece};
use zedc::elab::Cones;

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
        Carrier::Rat => &["0r", "3r/2r", "(0r - 2r)"],
        Carrier::Str => &["\"\"", "\"ab\""],
        Carrier::Bool => &["true", "false"],
    }
}

#[test]
fn each_computed_value_is_in_its_arrows_result() {
    let mut rng = Rng::new(26);
    let (mut fns, mut checked, mut failed) = (0, 0, 0);
    for _ in 0..700 {
        let f = format!("f(positional x, positional y) = {};\n", body(&mut rng, 3));
        let (i, _) = info(&f);
        if !i.errors.is_empty() {
            continue;
        }
        let s = i.sigs.values().next().unwrap().clone();
        fns += 1;
        // One call for each arrow with carrier parameters and each pair of arguments.
        let mut p = f.clone();
        let mut calls = Vec::new();
        let arrows = s.expand();
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
            for x in args(cs[0]) {
                for y in args(cs[1]) {
                    p += &format!("r{} = f({x}, {y});\n", calls.len());
                    calls.push((format!("f({x}, {y})"), &a.result));
                }
            }
        }
        let u = elab(&p).unwrap_or_else(|e| panic!("{p}: {e:?}"));
        // One index of the unit for all its calls, where `Unit::get` makes one for each.
        let cones = Cones::new(&u);
        let kernels: HashMap<&str, &Arc<str>> = u
            .defs
            .iter()
            .map(|d| (d.name.as_str(), &d.kernel))
            .collect();
        for (k, (call, result)) in calls.iter().enumerate() {
            let t = cones.close(Term::Var(kernels[format!("r{k}").as_str()].clone()));
            match Evaluator::new(World::new()).run(&with_prelude(t)) {
                Ok(v) => {
                    assert!(result.contains(&v), "{f}{call}: {v} is not in {result}");
                    checked += 1;
                }
                // An accepted program never meets a type error (DESIGN.md rule 4).
                Err(KernelError::Type(m)) => panic!("{f}{call}: type error: {m}"),
                // Another run-time error; a division by zero is the atom, a value.
                Err(_) => failed += 1,
            }
        }
    }
    println!("{fns} functions, {checked} values, {failed} failed");
    assert!(
        fns >= 300 && checked >= 650,
        "{fns} functions, {checked} values"
    );
    assert!(failed < checked / 4, "{failed} failed of {checked}");
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
    /// For each function so far, `h0` first, its number of parameters and whether it calls
    /// its first.
    arity: Vec<(usize, bool)>,
    /// The number of lambdas so far, which names the next one's parameter.
    lambdas: usize,
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

    /// The arguments of a call of `n` parameters, the first most often a lambda when `applies`,
    /// as the function called calls its first parameter.
    fn args(&mut self, scope: &[&str], n: usize, applies: bool) -> String {
        let a: Vec<String> = (0..n)
            .map(|k| match k == 0 && applies && self.rng.below(4) > 0 {
                true => self.lambda(scope, 2),
                false => self.arg(scope, 2, true),
            })
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
                let (n, applies) = self.arity[h];
                format!("h{h}({})", self.args(scope, n, applies))
            }
            17 if calls && !scope.is_empty() => {
                let f = self.rng.pick(scope);
                format!("{f}({})", self.args(scope, 1, false))
            }
            18 => format!("{}({})", self.lambda(scope, d), self.args(scope, 1, false)),
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
    /// a body that gives its first parameter to `^`, a shift or a bit word, or a body of one
    /// expression.
    fn helper(&mut self) -> String {
        let i = self.arity.len();
        let n = 1 + self.rng.below(2);
        let mut scope: Vec<&str> = ["p", "q"][..n].to_vec();
        let head: Vec<String> = scope.iter().map(|p| format!("positional {p}")).collect();
        let head = head.join(", ");
        let mut applies = false;
        let text = match self.rng.below(5) {
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
                applies = self.arity[h].1;
                let a: Vec<&str> = (0..self.arity[h].0)
                    .map(|_| self.rng.pick(&scope))
                    .collect();
                format!("h{i}({head}) = h{h}({});\n", a.join(", "))
            }
            2 => {
                applies = true;
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
        self.arity.push((n, applies));
        text
    }
}

/// The forms counted among the programs run, each with what shows it in a program's text.
const FORMS: [(&str, &[&str]); 7] = [
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
}

/// The runs of the programs of the seeds `seeds`: for each seed, `n` sets of functions and
/// four definitions of `r` over each.
fn run_programs(seeds: std::ops::Range<u64>, n: usize) -> Runs {
    let mut runs = Runs::default();
    for seed in seeds {
        let mut g = Gen::new(seed);
        for _ in 0..n {
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
                let u = elab(&p).unwrap_or_else(|e| panic!("{p}: {e:?}"));
                let t = u.get("r").unwrap_or_else(|| panic!("{p}: no `r`"));
                // Every run here takes far fewer steps; the fuel only stops a lambda that a
                // checker fault let apply itself.
                let mut ev = Evaluator::new(World::new()).with_fuel(1_000_000);
                match ev.run(&with_prelude(t)) {
                    Ok(_) => {
                        runs.ran += 1;
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
    }
    runs
}

/// Runs the programs of the seeds `seeds`, a hundred sets of functions each, and fails on any
/// accepted program whose run raises a kernel type error. Each form of [`FORMS`] must occur
/// among the programs run, so a change that stopped the generator making one, or the checker
/// accepting it, fails here rather than testing less without notice.
fn no_type_error(seeds: std::ops::Range<u64>) {
    let r = run_programs(seeds.clone(), 100);
    assert!(
        r.type_errors.is_empty(),
        "seeds {seeds:?}: {} accepted programs raised a kernel type error:\n{}",
        r.type_errors.len(),
        r.type_errors.join("----\n")
    );
    assert!(
        r.ran >= 200,
        "seeds {seeds:?}: only {} programs ran; {} were rejected, {} may give a function and {} \
         stopped",
        r.ran,
        r.rejected,
        r.functions,
        r.stopped
    );
    for (k, (name, _)) in FORMS.iter().enumerate() {
        assert!(
            r.forms[k] >= 10,
            "seeds {seeds:?}: only {} programs run use {name}",
            r.forms[k]
        );
    }
}

#[test]
fn accepted_random_programs_raise_no_type_error_seeds_0_to_7() {
    no_type_error(0..8);
}

#[test]
fn accepted_random_programs_raise_no_type_error_seeds_8_to_15() {
    no_type_error(8..16);
}

#[test]
fn accepted_random_programs_raise_no_type_error_seeds_16_to_23() {
    no_type_error(16..24);
}

#[test]
fn accepted_random_programs_raise_no_type_error_seeds_24_to_31() {
    no_type_error(24..32);
}
