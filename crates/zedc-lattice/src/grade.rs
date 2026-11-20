//! The tonicity grade of a term in one binder: ↑s, ↑, `const`, ↓ or ↓s, or none (DESIGN.md
//! sec:property_tracking, "strict tonicity"; plan row TONIC-strict).
//!
//! A grade of a term `f` in its binder `x` holds at every pair of values `x < x'` of `x`'s
//! domain, the other inputs fixed, at which both `f(x)` and `f(x')` evaluate: ↑ is
//! `f(x) <= f(x')`, ↑s is `f(x) < f(x')`, `const` is `f(x) == f(x')`, and ↓, ↓s the reverse.
//! A strict grade given here says more: the term evaluates at every point of the domains. DESIGN
//! states totality as a condition beside the grade ("↑s or ↓s on its domain ... and total
//! there, is `injective`"); every reader of a strict grade needs both (the injectivity witness,
//! the inverse by bisection, the selection rule's total keys), so a term that may fail
//! anywhere, in a part that depends on `x` or not (`x + 5 mod y` at `y = 0`), has its strict
//! grade weakened, which keeps the non-strict claim true.
//!
//! The rules are DESIGN's, at `int` and `rat`, read with the binders' intervals:
//!
//! - `x + y` is ↑s in each argument, `x - y` ↑s in `x` and ↓s in `y`, `-x` ↓s
//!   ([`Tonicity::plus`]).
//! - `x * y`, `y` constant in `x`: `x`'s grade where `y > 0`, flipped where `y < 0`, weakened
//!   where `y` touches 0 from one side, none where `y` has both signs. Two factors that both
//!   depend on `x`: each must keep one sign; the product is strict when both are, or when one
//!   is and the other lies above 0 (the function `mul`).
//! - `x ^ n`, `n >= 1` a literal: `x`'s grade for odd `n`; for even `n`, `x`'s grade where `x`
//!   lies at or above 0, flipped where it lies at or below 0. `x ^ 0` is `const`. A negative
//!   `n` has no grade.
//! - `x div c`, `c` constant in `x`: `x`'s grade weakened, flipped as well where `c < 0`.
//! - `min` and `max`: ↑ in each argument, ↑s when both arguments are ↑s.
//! - `mod`, the rat `/` and every other operation: `const` when every argument is, else none.
//! - Composition: signs multiply, and a composite is strict only when every stage is, since
//!   each rule reads only its arguments' grades and ranges.
//!
//! At a float carrier nothing is strict (`x + 1.0 == x` at `x = 1.0e16`), and at a `@checked`
//! integer type nothing is strict either, since an operation there can give `#overflow`: the
//! integer rules are read and the result weakened, which is sound because a checked operation
//! that does not fail gives the unbounded value, and no rule's direction depends on strictness.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc_base::axioms::Tonicity;

use super::interval::{End, IntervalSet, Num};

/// The arithmetic a term's binder and operations are read in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arith {
    /// `int`, unbounded: no operation overflows.
    Int,
    /// A `@checked` integer type: the operations of `int`, each of which may give
    /// `#overflow`.
    Checked,
    /// `rat`, exact.
    Rat,
    /// `f64` or `f32`, IEEE 754, in IEEE order: a pair with a NaN is in no order (IEEE Std
    /// 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 5.11; the full comment is in
    /// zed-kernel `value.rs`, `Value::surface_cmp`).
    Float,
}

/// The sign set of a value: a bit for each of negative, zero and positive.
type Signs = u8;
const NEG: Signs = 1;
const ZERO: Signs = 2;
const POS: Signs = 4;
const ALL: Signs = NEG | ZERO | POS;

/// The values a node may take.
#[derive(Clone)]
enum Range {
    /// At `int`: one interval holding every value ([`Bounds`]), or `None` for no value.
    Ints(Option<Bounds>),
    /// At `rat`: the signs of the values.
    Signs(Signs),
    /// At a float: the value of a finite literal, else `None`.
    Float(Option<f64>),
}

/// A subterm's grade, its range, and whether it may fail where it depends on `x`.
#[derive(Clone)]
struct Node {
    grade: Option<Tonicity>,
    range: Range,
    fails: bool,
}

/// What a name or a subterm stands for: a value, a primitive as a function (the prelude binds
/// `min` to `PrimFn(Min)`), or anything else.
#[derive(Clone)]
enum Item {
    Val(Node),
    Fn(Prim),
    Opaque,
}

/// One step of the walk.
enum Task<'t> {
    /// Push the item of a subterm, or the tasks that make it.
    Visit(&'t Term),
    /// Pop the items of a `Prim` or `App`'s parts and push its own.
    Combine(&'t Term),
    /// Pop a `let`'s bound item and bind it.
    Bind(&'t str),
    /// Drop the binding, the body's item made.
    Unbind(&'t str),
}

/// The grade of `body` in the binder `x` over the other inputs' domains `inputs` (and `x`'s,
/// when `inputs` names it; else `x` ranges over every value), read in `arith`. `None` when no
/// rule gives one. At [`Arith::Rat`] each domain's pieces are read as the rationals between
/// their ends; at [`Arith::Float`] the domains are not read.
///
/// The term is the kernel's: a call of a prelude name that is bound to a primitive
/// (`interp::prelude`) is read as the primitive.
// Complexity tradeoff: naive version, a recursive walk carrying each subterm's interval set
// (`revision::forward`): a deep term (a chain of n additions) overflows the Rust stack;
// `forward` over sets of p and q pieces costs O(p q), the pieces of a product chain growing
// with its depth; and even one interval's exact ends grow by a factor's bits at each product,
// so a chain of n products costs O(n^2) (measured: 20.3 times the bytes at 8n over x >= 0).
// Used: an explicit stack of tasks and items, O(n) steps over n subterms with one hash lookup
// per name, each range one interval with `f64` ends rounded outward ([`Bounds`]), so each step
// is O(1) floating-point operations. Given up: the holes of a range, and exact ends past 2^53,
// where a rounded end may cover 0 and a rule then gives no grade (never a wrong one). Tests:
// `l01_25_preimage_catalog::bench::strict` (`grading_scales_linearly` and the chain over
// x >= 0, `grading_with_growing_ends_scales_linearly`).
pub fn grade(
    body: &Term,
    x: &str,
    inputs: &BTreeMap<Arc<str>, IntervalSet>,
    arith: Arith,
) -> Option<Tonicity> {
    let mut g = Grader {
        x,
        inputs,
        arith,
        scope: HashMap::new(),
    };
    let mut tasks = vec![Task::Visit(body)];
    let mut items: Vec<Item> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(t) => g.visit(t, &mut tasks, &mut items),
            Task::Combine(t) => {
                let n = match t {
                    Term::Prim(_, args) => args.len(),
                    Term::App(_, args) => args.len() + 1,
                    _ => unreachable!("only a Prim or an App is combined"),
                };
                let parts = items.split_off(items.len() - n);
                items.push(g.combine(t, parts));
            }
            Task::Bind(name) => {
                let v = items
                    .pop()
                    .expect("a let's bound item was made before its Bind");
                g.scope.entry(name).or_default().push(v);
            }
            Task::Unbind(name) => {
                let bound = g.scope.get_mut(name).and_then(Vec::pop);
                // A bound value that may fail makes the `let` fail where it does even when
                // the body does not read it: an evaluation error (`x ^ -1` at `int`) stops
                // the whole run.
                if let (Some(Item::Val(b)), Some(Item::Val(r))) = (bound, items.last_mut()) {
                    r.fails |= b.fails;
                }
            }
        }
    }
    let Some(Item::Val(root)) = items.pop() else {
        return None;
    };
    let grade = root.grade?;
    let weak = root.fails || matches!(arith, Arith::Checked | Arith::Float);
    Some(if weak { grade.weak() } else { grade })
}

/// The walk's state: the binder, the inputs, the arithmetic, and each `let` name's bindings,
/// innermost last.
struct Grader<'a, 't> {
    x: &'a str,
    inputs: &'a BTreeMap<Arc<str>, IntervalSet>,
    arith: Arith,
    scope: HashMap<&'t str, Vec<Item>>,
}

impl<'t> Grader<'_, 't> {
    fn visit(&mut self, t: &'t Term, tasks: &mut Vec<Task<'t>>, items: &mut Vec<Item>) {
        match t {
            Term::Lit(v) => items.push(Item::Val(self.lit(v))),
            Term::Var(n) => items.push(self.var(n)),
            Term::PrimFn(p) => items.push(Item::Fn(*p)),
            Term::Lam(..) => items.push(Item::Opaque),
            Term::Prim(_, args) => {
                tasks.push(Task::Combine(t));
                tasks.extend(args.iter().rev().map(Task::Visit));
            }
            Term::App(f, args) => {
                tasks.push(Task::Combine(t));
                tasks.extend(args.iter().rev().map(Task::Visit));
                tasks.push(Task::Visit(f));
            }
            Term::Let(n, e, b) => {
                tasks.push(Task::Unbind(n));
                tasks.push(Task::Visit(b));
                tasks.push(Task::Bind(n));
                tasks.push(Task::Visit(e));
            }
            _ => items.push(Item::Val(self.opaque())),
        }
    }

    /// A value no rule reads: no grade, any value, and it may fail.
    fn opaque(&self) -> Node {
        Node {
            grade: None,
            range: self.any(),
            fails: true,
        }
    }

    /// Any value of the arithmetic.
    fn any(&self) -> Range {
        match self.arith {
            Arith::Int | Arith::Checked => Range::Ints(Some(Bounds::ALL)),
            Arith::Rat => Range::Signs(ALL),
            Arith::Float => Range::Float(None),
        }
    }

    /// A literal: `const` when it is a number of the arithmetic, a finite one at a float
    /// (`x + inf` is NaN at `x = -inf`), else no grade and a value that may fail (an
    /// operation on it fails at the kernel, so a rule that read it as a constant would call a
    /// term total that is not).
    fn lit(&self, v: &Value) -> Node {
        let range = match (self.arith, v) {
            (Arith::Int | Arith::Checked, Value::Int(n)) => {
                Some(Range::Ints(Some(Bounds::point(&Num::from(*n)))))
            }
            (Arith::Int | Arith::Checked, Value::Big(n)) => {
                Some(Range::Ints(Some(Bounds::point(&Num::from(&**n)))))
            }
            (Arith::Rat, Value::Rat(r)) => Some(Range::Signs(if r.is_zero() {
                ZERO
            } else if r.is_negative() {
                NEG
            } else {
                POS
            })),
            (Arith::Float, Value::Float(f)) if f.get().is_finite() => {
                Some(Range::Float(Some(f.get())))
            }
            (Arith::Float, Value::Float32(f)) if f.get().is_finite() => {
                Some(Range::Float(Some(f64::from(f.get()))))
            }
            _ => None,
        };
        match range {
            Some(range) => Node {
                grade: Some(Tonicity::Const),
                range,
                fails: false,
            },
            None => self.opaque(),
        }
    }

    /// A name: its innermost `let` binding, else the binder (↑s), else another input
    /// (`const`; at a float none, since a fixed NaN is in no order), else unknown: a value of
    /// no grade that may fail (a name the run does not bind fails there).
    fn var(&self, n: &str) -> Item {
        if let Some(v) = self.scope.get(n).and_then(|v| v.last()) {
            return v.clone();
        }
        let input = |grade| {
            let range = match (self.arith, self.inputs.get(n)) {
                (Arith::Float, _) | (_, None) => self.any(),
                (Arith::Int | Arith::Checked, Some(d)) => Range::Ints(Bounds::of(d)),
                (Arith::Rat, Some(d)) => Range::Signs(real_signs(d)),
            };
            Item::Val(Node {
                grade,
                range,
                fails: false,
            })
        };
        if n == self.x {
            input(Some(Tonicity::StrictUp))
        } else if self.arith != Arith::Float && self.inputs.contains_key(n) {
            input(Some(Tonicity::Const))
        } else {
            Item::Val(self.opaque())
        }
    }

    /// The item of a `Prim` or `App` from its parts' items.
    fn combine(&self, t: &Term, mut parts: Vec<Item>) -> Item {
        let (p, args) = match t {
            Term::Prim(p, args) => (Some(*p), args),
            Term::App(_, args) => match parts.remove(0) {
                Item::Fn(p) => (Some(p), args),
                _ => (None, args),
            },
            _ => unreachable!("only a Prim or an App is combined"),
        };
        let Some(p) = p else {
            return Item::Val(self.opaque());
        };
        let ns: Vec<Node> = parts
            .into_iter()
            .map(|i| match i {
                Item::Val(n) => n,
                Item::Fn(_) | Item::Opaque => self.opaque(),
            })
            .collect();
        // The exponent of `^` is read by [`Self::pow`], not as a value: an `int` literal is
        // the exponent at `rat` too, and any other exponent gives a value that may fail.
        let read = if p == Prim::Pow {
            &ns[..ns.len().min(1)]
        } else {
            &ns[..]
        };
        let child_fails = read.iter().any(|n| n.fails);
        let mut out = match self.arith {
            Arith::Float => self.float(p, &ns),
            _ => self.exact(p, args, &ns),
        };
        out.fails |= child_fails;
        Item::Val(out)
    }

    /// The rules at `int`, `@checked` and `rat`.
    fn exact(&self, p: Prim, args: &[Term], ns: &[Node]) -> Node {
        use Tonicity::Const;
        let ints = self.arith != Arith::Rat;
        let node = |grade, range| Node {
            grade,
            range,
            fails: false,
        };
        match (p, ns) {
            (Prim::Add, [a, b]) => node(
                plus(a.grade, b.grade),
                self.range2(a, b, |x, y| Some(x.add(y)), add_signs),
            ),
            (Prim::Sub, [a, b]) => node(
                plus(a.grade, b.grade.map(Tonicity::flip)),
                self.range2(
                    a,
                    b,
                    |x, y| Some(x.add(y.neg())),
                    |x, y| add_signs(x, neg_signs(y)),
                ),
            ),
            (Prim::Neg, [a]) => node(
                a.grade.map(Tonicity::flip),
                self.range2(a, a, |x, _| Some(x.neg()), |x, _| neg_signs(x)),
            ),
            (Prim::Mul, [a, b]) => node(
                mul(a.grade, self.signs(a), b.grade, self.signs(b)),
                self.range2(a, b, |x, y| Some(x.mul(y)), mul_signs),
            ),
            (Prim::Min | Prim::Max, [a, b]) => {
                let min = p == Prim::Min;
                let f = |u: f64, v: f64| if min { u.min(v) } else { u.max(v) };
                let s = |u: i8, v: i8| if min { u.min(v) } else { u.max(v) };
                node(
                    min_max(a.grade, b.grade),
                    self.range2(
                        a,
                        b,
                        |x, y| {
                            Some(Bounds {
                                lo: f(x.lo, y.lo),
                                hi: f(x.hi, y.hi),
                            })
                        },
                        |x, y| pairwise(x, y, s),
                    ),
                )
            }
            (Prim::Pow, [a, _]) => self.pow(a, &args[1]),
            (Prim::IntDiv, [a, b]) if ints => {
                let s = self.signs(b);
                let grade = match (a.grade, b.grade) {
                    (Some(ga), Some(Const)) if s & !(ZERO | POS) == 0 => Some(ga.weak()),
                    (Some(ga), Some(Const)) if s & !(ZERO | NEG) == 0 => Some(ga.flip().weak()),
                    _ => None,
                };
                Node {
                    fails: s & ZERO != 0,
                    ..node(grade, self.range2(a, b, Bounds::div, |_, _| ALL))
                }
            }
            // `mod`, and the rat `/`: no grade (`x mod 3` cycles; `1 / x` is DESIGN's to
            // grade, not this row's); `const` of two constants.
            (Prim::Mod, [a, b]) if ints => {
                self.constant_or_none(a, b, self.range2(a, b, Bounds::rem, |_, _| ALL))
            }
            (Prim::Div, [a, b]) if !ints => {
                let range = self.range2(a, b, |_, _| None, |x, y| mul_signs(x, y & !ZERO));
                self.constant_or_none(a, b, range)
            }
            // No rule says where these fail (`abs` does not, `int(x)` may), so each may.
            _ => Node {
                grade: ns.iter().all(|n| n.grade == Some(Const)).then_some(Const),
                range: self.any(),
                fails: true,
            },
        }
    }

    /// `a mod b` at `int` or `a / b` at `rat`: `const` when both are, else none; it fails
    /// where `b` may be 0.
    fn constant_or_none(&self, a: &Node, b: &Node, range: Range) -> Node {
        let constant = a.grade == Some(Tonicity::Const) && b.grade == Some(Tonicity::Const);
        Node {
            grade: constant.then_some(Tonicity::Const),
            range,
            fails: self.signs(b) & ZERO != 0,
        }
    }

    /// `a ^ n`, `n` the literal `e` (an exponent that is not a literal has no rule).
    fn pow(&self, a: &Node, e: &Term) -> Node {
        let Some(n) = (match e {
            Term::Lit(v) => Num::of_integer(v),
            _ => None,
        }) else {
            return self.opaque();
        };
        let s = self.signs(a);
        let constant = a.grade == Some(Tonicity::Const);
        if n.is_zero() {
            // `x ^ 0` is 1 at every `x`, `0 ^ 0` included, at `int` and `rat`.
            let range = match self.arith {
                Arith::Rat => Range::Signs(POS),
                _ => Range::Ints(Some(Bounds { lo: 1.0, hi: 1.0 })),
            };
            return Node {
                grade: Some(Tonicity::Const),
                range,
                fails: false,
            };
        }
        if n.signum() < 0 {
            // At `int` no negative power is defined; at `rat` `0r ^ n` fails.
            return Node {
                grade: constant.then_some(Tonicity::Const),
                range: match self.arith {
                    Arith::Rat => Range::Signs(pow_signs(s, &n) & !ZERO),
                    _ => Range::Ints(None),
                },
                fails: self.arith != Arith::Rat || s & ZERO != 0,
            };
        }
        let grade = match a.grade {
            g if n.is_odd() || constant => g,
            Some(g) if s & !(ZERO | POS) == 0 => Some(g),
            Some(g) if s & !(ZERO | NEG) == 0 => Some(g.flip()),
            _ => None,
        };
        let range = match &a.range {
            Range::Ints(d) => Range::Ints(d.map(|d| d.pow(&n))),
            _ => Range::Signs(pow_signs(s, &n)),
        };
        Node {
            grade,
            range,
            fails: false,
        }
    }

    /// The rules at a float: only a chain of `+`, `-`, `*`, `-x`, `min` and `max` in which
    /// each binary operation has one operand a finite literal, nonzero for `*`, and the
    /// result weak. Proof: each such stage maps a non-NaN operand to a non-NaN result
    /// (`inf + c` and `inf * c` are infinities, `c` finite and for `*` nonzero), its exact
    /// value is monotone in the operand, and IEEE rounding is monotone, so `t <= t'` gives
    /// `t op c <= t' op c` in IEEE order; two zeros compare equal, so a pair `-0.0`, `0.0`
    /// is never `t < t'`. A constant that is not a literal may be NaN (`inf - inf`), so only
    /// a literal is `const`. The proof rests on two rules of IEEE Std 754-2019,
    /// doi:10.1109/IEEESTD.2019.8766229: an operation is the exact result rounded (section
    /// 5.4.1; the full comment is in zed-kernel `eval.rs`, fn `prim_on`, at `Prim::Sqrt`), and
    /// every rounding direction is monotone (section 4.3; full comment in zed-kernel `num.rs`,
    /// enum `Rounding`), with the comparisons of section 5.11 (zed-kernel `value.rs`,
    /// `Value::surface_cmp`). The monotonicity of rounding is from memory, not read in the
    /// standard, which is paywalled.
    fn float(&self, p: Prim, ns: &[Node]) -> Node {
        let lit = |n: &Node| match n.range {
            Range::Float(Some(v)) if n.grade == Some(Tonicity::Const) => Some(v),
            _ => None,
        };
        let grade = match (p, ns) {
            (Prim::Neg, [a]) => a.grade.map(Tonicity::flip),
            (Prim::Add | Prim::Sub | Prim::Mul | Prim::Min | Prim::Max, [a, b]) => {
                match (lit(a), lit(b)) {
                    (None, Some(c)) => float_stage(p, a.grade, c, false),
                    (Some(c), None) => float_stage(p, b.grade, c, true),
                    _ => None,
                }
            }
            _ => None,
        };
        let range = match (p, ns) {
            (Prim::Neg, [a]) => Range::Float(lit(a).map(|v| -v)),
            _ => Range::Float(None),
        };
        Node {
            grade: grade.map(Tonicity::weak),
            range,
            fails: false,
        }
    }

    /// The signs of a node's values.
    fn signs(&self, n: &Node) -> Signs {
        match &n.range {
            Range::Ints(d) => d.map_or(0, Bounds::signs),
            Range::Signs(s) => *s,
            Range::Float(Some(v)) if *v > 0.0 => POS,
            Range::Float(Some(v)) if *v < 0.0 => NEG,
            Range::Float(Some(_)) => ZERO,
            Range::Float(None) => ALL,
        }
    }

    /// The range of an operation over `a` and `b`: `ints` on their bounds at `int` (no value
    /// when either has none), the sign table `f` at `rat`.
    fn range2(
        &self,
        a: &Node,
        b: &Node,
        ints: impl Fn(Bounds, Bounds) -> Option<Bounds>,
        f: impl Fn(Signs, Signs) -> Signs,
    ) -> Range {
        match (&a.range, &b.range) {
            (Range::Ints(x), Range::Ints(y)) => Range::Ints(match (x, y) {
                (Some(x), Some(y)) => ints(*x, *y),
                _ => None,
            }),
            _ if self.arith == Arith::Rat => Range::Signs(f(self.signs(a), self.signs(b))),
            _ => self.any(),
        }
    }
}

/// The grade of a float stage `t op c` (`c op t` when `left`), `t` of grade `g`.
fn float_stage(p: Prim, g: Option<Tonicity>, c: f64, left: bool) -> Option<Tonicity> {
    let g = g?;
    match p {
        Prim::Add | Prim::Min | Prim::Max => Some(g),
        Prim::Sub if left => Some(g.flip()),
        Prim::Sub => Some(g),
        Prim::Mul if c > 0.0 => Some(g),
        Prim::Mul if c < 0.0 => Some(g.flip()),
        _ => None,
    }
}

/// The grade of a sum from its terms' grades.
fn plus(a: Option<Tonicity>, b: Option<Tonicity>) -> Option<Tonicity> {
    a?.plus(b?)
}

/// The grade of `a * b` from the factors' grades and signs.
///
/// One factor constant in `x`: the other's grade scaled by its signs ([`scale`]). Both
/// depending on `x`: each factor is read as `±f` with `f >= 0` (a factor with both signs has
/// no grade), `-f` flipping its grade, and the two `f`s must move one way. Then for `f`, `g`
/// both ↑ and at least 0, `x < x'`: `f(x) g(x) <= f(x) g(x') <= f(x') g(x')`; the second step
/// is strict when `f` is ↑s and `g(x') > 0`, which holds when `g` lies above 0 or `g` is ↑s
/// (`g(x') > g(x) >= 0`); the first is strict when `g` is ↑s and `f(x) > 0`, by the same
/// argument with the roles swapped. Both ↓ is the same with the pair read from `x'`. So the
/// product is strict when both are strict, or when one is strict and the other lies above 0.
fn mul(ga: Option<Tonicity>, sa: Signs, gb: Option<Tonicity>, sb: Signs) -> Option<Tonicity> {
    let (ga, gb) = (ga?, gb?);
    if gb == Tonicity::Const {
        return scale(ga, sb);
    }
    if ga == Tonicity::Const {
        return scale(gb, sa);
    }
    let (fa, na, pa) = nonneg(ga, sa)?;
    let (fb, nb, pb) = nonneg(gb, sb)?;
    if fa.sign() != fb.sign() {
        return None;
    }
    let strict = (fa.is_strict() && (fb.is_strict() || pb)) || (fb.is_strict() && pa);
    let g = if strict { fa.strict() } else { fa.weak() };
    Some(if na != nb { g.flip() } else { g })
}

/// A factor read as `±f`, `f >= 0`: `f`'s grade, whether it was negated, and whether `f`
/// lies above 0. `None` for a factor with both signs.
fn nonneg(g: Tonicity, s: Signs) -> Option<(Tonicity, bool, bool)> {
    if s & !(ZERO | POS) == 0 {
        Some((g, false, s & !POS == 0))
    } else if s & !(ZERO | NEG) == 0 {
        Some((g.flip(), true, s & !NEG == 0))
    } else {
        None
    }
}

/// The grade of `t * c`, `t` of grade `g` and `c` constant in `x` with signs `s`; a product
/// of two constants is constant, whatever their signs.
fn scale(g: Tonicity, s: Signs) -> Option<Tonicity> {
    if g == Tonicity::Const {
        Some(Tonicity::Const)
    } else if s & !POS == 0 {
        Some(g)
    } else if s & !NEG == 0 {
        Some(g.flip())
    } else if s == ZERO {
        Some(Tonicity::Const)
    } else if s & !(ZERO | POS) == 0 {
        Some(g.weak())
    } else if s & !(ZERO | NEG) == 0 {
        Some(g.flip().weak())
    } else {
        None
    }
}

/// The grade of `min(a, b)` or `max(a, b)`: proof for ↑s, `x < x'`: `f(x) < f(x')` and
/// `g(x) < g(x')`, so the smaller (larger) of the first pair is below the smaller (larger)
/// of the second.
fn min_max(a: Option<Tonicity>, b: Option<Tonicity>) -> Option<Tonicity> {
    let (a, b) = (a?, b?);
    if a == Tonicity::Const {
        return Some(b.weak());
    }
    if b == Tonicity::Const {
        return Some(a.weak());
    }
    if a.sign() != b.sign() {
        return None;
    }
    Some(if a.is_strict() && b.is_strict() {
        a
    } else {
        a.weak()
    })
}

/// The integers from `lo` to `hi`, both whole `f64`s or infinities, `lo <= hi`, `lo` never
/// `+inf` and `hi` never `-inf`, so no sum of two ends is `inf - inf`. Each operation rounds
/// outward: its `lo` is at or below the least value it holds, its `hi` at or above the
/// greatest. Below 2^53 in size every integer is an `f64` and each operation is exact.
///
/// Proof of the rounding: an `f64` operation rounds to nearest, within half a unit in the last
/// place, so the exact result `t` of a correctly rounded `r` lies within `[r.next_down(),
/// r.next_up()]`; the result is an integer, so `ceil` of the first and `floor` of the second
/// still bound it ([`lower`], [`upper`]). An overflow to `inf` keeps `t` beyond `f64::MAX`,
/// which `lower` gives.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Bounds {
    lo: f64,
    hi: f64,
}

/// `2^53`: every integer of at most this size is an `f64`.
const TWO_53: f64 = 9_007_199_254_740_992.0;

/// A lower bound of the integer `t` whose rounded value is `r`: `r` itself when `|r| < 2^53`,
/// since then `r == t` (if `|t| <= 2^53`, `t` is an `f64` and rounds to itself; if `|t| > 2^53`,
/// `|r| >= 2^53`, as rounding is monotone and `2^53` is an `f64`), else one place below.
fn lower(r: f64) -> f64 {
    if r.abs() < TWO_53 {
        r
    } else {
        r.next_down().ceil()
    }
}

/// An upper bound of the integer whose rounded value is `r`; as [`lower`].
fn upper(r: f64) -> f64 {
    if r.abs() < TWO_53 {
        r
    } else {
        r.next_up().floor()
    }
}

/// `2^63`, the least integer above `i64::MAX`: a lower bound of every larger one.
const TWO_63: f64 = 9_223_372_036_854_775_808.0;

impl Bounds {
    const ALL: Bounds = Bounds {
        lo: f64::NEG_INFINITY,
        hi: f64::INFINITY,
    };

    /// An end as a lower bound (`up` false) or an upper bound: itself when it is an `f64`,
    /// else rounded outward; past `i64`, `2^63` or an infinity on the side that holds it.
    fn end(e: &End, up: bool) -> f64 {
        match e {
            End::NegInf => f64::NEG_INFINITY,
            End::PosInf => f64::INFINITY,
            End::Fin(n) => match n.to_i64() {
                // `as` rounds to nearest; a whole `f64` of size at most 2^63 converts to
                // `i128` exactly, so equal integers mean the end is that `f64`.
                Some(v) if (v as f64) as i128 == i128::from(v) => v as f64,
                Some(v) if up => upper(v as f64),
                Some(v) => lower(v as f64),
                None if n.signum() > 0 => {
                    if up {
                        f64::INFINITY
                    } else {
                        TWO_63
                    }
                }
                None if up => -TWO_63,
                None => f64::NEG_INFINITY,
            },
        }
    }

    /// The bounds of `d`, `None` when it is empty.
    fn of(d: &IntervalSet) -> Option<Bounds> {
        let (lo, hi) = d.bounds()?;
        Some(Bounds {
            lo: Bounds::end(lo, false),
            hi: Bounds::end(hi, true),
        })
    }

    /// The one integer `n`.
    fn point(n: &Num) -> Bounds {
        let e = End::Fin(n.clone());
        Bounds {
            lo: Bounds::end(&e, false),
            hi: Bounds::end(&e, true),
        }
    }

    fn signs(self) -> Signs {
        (if self.lo < 0.0 { NEG } else { 0 })
            | (if self.lo <= 0.0 && self.hi >= 0.0 {
                ZERO
            } else {
                0
            })
            | (if self.hi > 0.0 { POS } else { 0 })
    }

    fn add(self, b: Bounds) -> Bounds {
        Bounds {
            lo: lower(self.lo + b.lo),
            hi: upper(self.hi + b.hi),
        }
    }

    fn neg(self) -> Bounds {
        Bounds {
            lo: -self.hi,
            hi: -self.lo,
        }
    }

    /// The least and greatest of the four products of ends, `0 * inf` read as 0 (an infinite
    /// end stands for unbounded finite values, and 0 times any of them is 0).
    fn mul(self, b: Bounds) -> Bounds {
        let m = |u: f64, v: f64| if u == 0.0 || v == 0.0 { 0.0 } else { u * v };
        let c = [
            m(self.lo, b.lo),
            m(self.lo, b.hi),
            m(self.hi, b.lo),
            m(self.hi, b.hi),
        ];
        Bounds {
            lo: lower(c.into_iter().fold(f64::INFINITY, f64::min)),
            hi: upper(c.into_iter().fold(f64::NEG_INFINITY, f64::max)),
        }
    }

    /// `x ^ n`, `n >= 1`: an odd power is increasing, so its ends are the ends' powers; an
    /// even one is `|x| ^ n`, the least and greatest `|x|` giving its ends.
    fn pow(self, n: &Num) -> Bounds {
        if n.is_odd() {
            let at = |v: f64, up: bool| {
                if v < 0.0 {
                    -pow_magnitude(-v, n, !up)
                } else {
                    pow_magnitude(v, n, up)
                }
            };
            Bounds {
                lo: at(self.lo, false).ceil(),
                hi: at(self.hi, true).floor(),
            }
        } else {
            let (small, large) = if self.lo >= 0.0 {
                (self.lo, self.hi)
            } else if self.hi <= 0.0 {
                (-self.hi, -self.lo)
            } else {
                (0.0, self.hi.max(-self.lo))
            };
            Bounds {
                lo: pow_magnitude(small, n, false).ceil(),
                hi: pow_magnitude(large, n, true).floor(),
            }
        }
    }

    /// The Euclidean `a div b`, over the divisors other than 0 (where it fails): by `b > 0`
    /// it is `floor(a / b)`, and by `b < 0` it is `-(a div -b)` (from `a = b q + r` with
    /// `0 <= r < |b|`). `None` when 0 is the only divisor.
    fn div(self, b: Bounds) -> Option<Bounds> {
        let pos = (b.hi >= 1.0).then(|| self.floor_div(b.lo.max(1.0), b.hi));
        let neg = (b.lo <= -1.0).then(|| self.floor_div(-b.hi.min(-1.0), -b.lo).neg());
        match (pos, neg) {
            (Some(p), Some(q)) => Some(Bounds {
                lo: p.lo.min(q.lo),
                hi: p.hi.max(q.hi),
            }),
            (p, q) => p.or(q),
        }
    }

    /// `floor(a / b)` over `a` in `self` and `b` in `p..=q`, `1 <= p <= q` (`q` may be
    /// infinite). For `a >= 0` it falls as `b` grows and for `a < 0` it rises, so its least
    /// value is at `lo` and `q` (`lo >= 0`) or `p` (`lo < 0`), and its greatest at `hi` and
    /// `p` (`hi >= 0`) or `q` (`hi < 0`); as `b` grows without bound it tends to 0 for
    /// `a >= 0` and is -1 for `a < 0`.
    fn floor_div(self, p: f64, q: f64) -> Bounds {
        let lo = if self.lo < 0.0 {
            floor_quotient(self.lo, p, false)
        } else if q.is_infinite() {
            0.0
        } else {
            floor_quotient(self.lo, q, false)
        };
        let hi = if self.hi >= 0.0 {
            floor_quotient(self.hi, p, true)
        } else if q.is_infinite() {
            -1.0
        } else {
            floor_quotient(self.hi, q, true)
        };
        Bounds { lo, hi }
    }

    /// The Euclidean `a mod b`: `0 <= r < |b|` for `b != 0`, `None` when 0 is the only
    /// divisor.
    fn rem(self, b: Bounds) -> Option<Bounds> {
        let m = b.hi.max(-b.lo);
        (m >= 1.0).then(|| Bounds {
            lo: 0.0,
            hi: upper(m - 1.0),
        })
    }
}

/// `floor(a / b)` rounded down (`up` false) or up, `a` a whole `f64` or an infinity and `b`
/// a finite whole `f64` at least 1. When both are in `i64` (each whole `f64` there converts
/// exactly) the quotient is the exact `i64` one, `div_euclid` being `floor` for `b > 0`, and
/// no larger than `|a|`, so it is exact below 2^53 in size and rounded outward by [`lower`]
/// or [`upper`] above. Past `i64`: when `b` divides `a` the quotient is a whole number no
/// larger than `|a|` whose odd part divides `a`'s, so it is an `f64` and the division exact
/// (`%` on `f64`s is exact too). Otherwise `t = a / b` is not whole, and its rounding `r`:
/// - not whole: `floor(t) = floor(r)`, as a whole number strictly between `t` and `r` would
///   be an `f64` (`|r| < 2^52` here) nearer `t` than `r`;
/// - whole and below 2^53 in size: `floor(t)` is `r` when `t > r` and `r - 1` when `t < r`,
///   `t - r` having the sign of `a - b r` (`b > 0`), which `mul_add` rounds once and so
///   keeps (it is not 0, as `t` is not whole);
/// - else moved one place outward before `floor`.
///
/// (The `f64` path alone was not exact below 2^53: `(2^53 - 1) / (2^52 - 1)` rounds to 2,
/// which it moved to 1, and `(2^64 - 2^11) / 2^52`, the `f64` `4096 - 2^-41`, it moved to
/// 4096; found by TONIC-big-ends.)
fn floor_quotient(a: f64, b: f64, up: bool) -> f64 {
    if a.is_infinite() {
        a
    } else if (-TWO_63..TWO_63).contains(&a) && b < TWO_63 {
        // `a >= -2^63` and `b >= 1`, so the quotient cannot overflow `i64`.
        let q = ((a as i64).div_euclid(b as i64)) as f64;
        if up { upper(q) } else { lower(q) }
    } else if a % b == 0.0 {
        a / b
    } else if (a / b).fract() != 0.0 {
        (a / b).floor()
    } else if (a / b).abs() < TWO_53 {
        let r = a / b;
        if (-b).mul_add(r, a) > 0.0 { r } else { r - 1.0 }
    } else if up {
        (a / b).next_up().floor()
    } else {
        (a / b).next_down().floor()
    }
}

/// `m ^ n` rounded up (`up`) or down, `m >= 0` a whole `f64` or `inf`, `n >= 1`: 0 and 1 are
/// their own powers; else square and multiply over `n`'s bits, each product moved one place
/// outward, or kept when below `2^53`, where the product of two whole `f64`s is exact (as in
/// [`lower`]) (multiplication of numbers at least 1 is increasing in each, so bounds of the
/// factors bound the product). An `n` past `i64` with `m >= 2` gives a power past `f64::MAX`.
fn pow_magnitude(m: f64, n: &Num, up: bool) -> f64 {
    if m <= 1.0 {
        return m;
    }
    let step = |v: f64| {
        if v < TWO_53 {
            v
        } else if up {
            v.next_up()
        } else {
            v.next_down()
        }
    };
    let Some(mut k) = n.to_i64() else {
        return if up { f64::INFINITY } else { f64::MAX };
    };
    let (mut acc, mut base) = (1.0, m);
    loop {
        if k & 1 == 1 {
            // `1 * base` is exact.
            acc = if acc == 1.0 { base } else { step(acc * base) };
        }
        k >>= 1;
        if k == 0 {
            return acc;
        }
        base = step(base * base);
    }
}

/// The signs of the numbers between the ends of each piece of `d`, read as integers or as
/// rationals (the same signs: a piece holds 0 exactly when its ends do not share a sign).
fn real_signs(d: &IntervalSet) -> Signs {
    d.pieces().fold(0, |s, (lo, hi)| {
        let (l, h) = (lo.signum(), hi.signum());
        s | if l < 0 { NEG } else { 0 }
            | if l <= 0 && h >= 0 { ZERO } else { 0 }
            | if h > 0 { POS } else { 0 }
    })
}

/// The signs of `f(u, v)` over the signs `u` of `a` and `v` of `b`, `f` on one sign each
/// (-1, 0, 1).
fn pairwise(a: Signs, b: Signs, f: impl Fn(i8, i8) -> i8) -> Signs {
    let mut out = 0;
    for (sa, u) in [(NEG, -1), (ZERO, 0), (POS, 1)] {
        for (sb, v) in [(NEG, -1), (ZERO, 0), (POS, 1)] {
            if a & sa != 0 && b & sb != 0 {
                out |= match f(u, v) {
                    -1 => NEG,
                    0 => ZERO,
                    1 => POS,
                    _ => ALL,
                };
            }
        }
    }
    out
}

/// The signs of a sum: two signs that differ and are not 0 give any sign (`2` is read as
/// "any" by [`pairwise`]).
fn add_signs(a: Signs, b: Signs) -> Signs {
    pairwise(a, b, |u, v| if u * v < 0 { 2 } else { (u + v).signum() })
}

/// The signs of `-a`.
fn neg_signs(a: Signs) -> Signs {
    (a & ZERO) | if a & NEG != 0 { POS } else { 0 } | if a & POS != 0 { NEG } else { 0 }
}

/// The signs of a product.
fn mul_signs(a: Signs, b: Signs) -> Signs {
    pairwise(a, b, |u, v| u * v)
}

/// The signs of `a ^ n`, `n != 0` (0 keeps its sign; a negative `n` fails there).
fn pow_signs(a: Signs, n: &Num) -> Signs {
    if n.is_odd() {
        a
    } else {
        (a & ZERO) | if a & (NEG | POS) != 0 { POS } else { 0 }
    }
}

/// The outward rounding of [`Bounds`] (plan row TONIC-big-ends): each operation's bounds hold
/// the exact range, computed in [`Num`] at the ends of its operands, for ends near ±2^52,
/// ±2^53, ±2^63 and past `i64`; and where every end and result is below 2^53 in size the
/// bounds are that range. The grades these ranges give are checked by running the terms in
/// `tests/steps/l01_25_preimage_catalog/big_ends.rs`.
#[cfg(test)]
mod tests {
    use super::*;

    /// The integer a whole finite `f64` is; `None` at an infinity.
    fn num_of(v: f64) -> Option<Num> {
        if !v.is_finite() {
            return None;
        }
        // Below 2^127 the cast is exact; above, the value is its 53-bit significand times a
        // power of 2.
        if v.abs() < 1e38 {
            return Some(Num::from(v as i128));
        }
        let bits = v.to_bits();
        let e = ((bits >> 52) & 0x7ff) as i64 - 1075;
        let m = ((bits & ((1 << 52) - 1)) | (1 << 52)) as i128;
        let m = Num::from(if v < 0.0 { -m } else { m });
        Some(&m * &Num::pow2(&Num::from(e)))
    }

    /// Whether `b` holds every integer from `lo` to `hi`.
    fn holds(b: Bounds, lo: &Num, hi: &Num) -> bool {
        let below = b.lo == f64::NEG_INFINITY || num_of(b.lo).is_some_and(|l| &l <= lo);
        let above = b.hi == f64::INFINITY || num_of(b.hi).is_some_and(|h| &h >= hi);
        below && above
    }

    /// Whether `b` is exactly `lo..=hi`.
    fn is(b: Bounds, lo: &Num, hi: &Num) -> bool {
        num_of(b.lo).as_ref() == Some(lo) && num_of(b.hi).as_ref() == Some(hi)
    }

    fn small(n: &Num) -> bool {
        n.abs() < Num::from(1i64 << 53)
    }

    /// Ends near 0 and near ±2^k for each `k` of 52, 53, 54, 62, 63, 64, 70 and 100.
    fn ends() -> Vec<Num> {
        let mut out: Vec<Num> = [0i64, 1, 2, 3, 7, 1000].map(Num::from).to_vec();
        for k in [52i64, 53, 54, 62, 63, 64, 70, 100] {
            let p = Num::pow2(&Num::from(k));
            for d in [-3i64, -1, 0, 1, 3] {
                out.push(&p + &Num::from(d));
            }
        }
        let negated: Vec<Num> = out.iter().map(|n| -n).collect();
        out.extend(negated);
        zed_collections::sorted::sort_dedup(&mut out);
        out
    }

    /// Ranges of one end and of each end to the next three in [`ends`].
    fn ranges() -> Vec<(Num, Num)> {
        let e = ends();
        (0..e.len())
            .flat_map(|i| (i..(i + 4).min(e.len())).map(move |j| (i, j)))
            .map(|(i, j)| (e[i].clone(), e[j].clone()))
            .collect()
    }

    fn bounds((lo, hi): &(Num, Num)) -> Bounds {
        Bounds::of(&IntervalSet::range(
            End::Fin(lo.clone()),
            End::Fin(hi.clone()),
        ))
        .expect("a range of at least one integer")
    }

    /// The least and greatest of `vs`.
    fn span(vs: impl IntoIterator<Item = Num>) -> (Num, Num) {
        let mut vs: Vec<Num> = vs.into_iter().collect();
        vs.sort();
        (vs[0].clone(), vs[vs.len() - 1].clone())
    }

    /// Asserts that `got` holds `want`, and is `want` when every end of the operands and of
    /// `want` is below 2^53 in size.
    fn check(what: &str, got: Bounds, want: &(Num, Num), operands: &[&(Num, Num)]) {
        assert!(
            holds(got, &want.0, &want.1),
            "{what}: {got:?} misses {want:?}"
        );
        let exact = operands
            .iter()
            .flat_map(|(l, h)| [l, h])
            .chain([&want.0, &want.1])
            .all(small);
        assert!(
            !exact || is(got, &want.0, &want.1),
            "{what}: {got:?} is not {want:?}"
        );
    }

    #[test]
    fn an_end_holds_its_integer_and_is_it_below_two_to_the_53() {
        for n in ends() {
            let b = Bounds::point(&n);
            check(&format!("{n}"), b, &(n.clone(), n.clone()), &[]);
        }
        // An end that is an `f64` is kept, past 2^53 too; one that is not is widened.
        for v in [1i64 << 53, 1 << 62, -(1 << 62) - 1024, i64::MIN] {
            let n = Num::from(v);
            assert!(is(Bounds::point(&n), &n, &n), "{v}");
        }
        for v in [(1i64 << 53) + 1, i64::MAX, (1 << 62) + 1] {
            let b = Bounds::point(&Num::from(v));
            assert!(b.lo < b.hi, "{v}: {b:?}");
        }
        // An end past `i64` is 2^63 or an infinity, toward the side that holds it.
        let big = Num::pow2(&Num::from(70i64));
        assert_eq!(
            Bounds::point(&big),
            Bounds {
                lo: TWO_63,
                hi: f64::INFINITY
            }
        );
        assert_eq!(
            Bounds::point(&-&big),
            Bounds {
                lo: f64::NEG_INFINITY,
                hi: -TWO_63
            }
        );
    }

    #[test]
    fn sums_and_differences_hold_the_exact_range() {
        let rs = ranges();
        for a in &rs {
            for b in &rs {
                let sum = (&a.0 + &b.0, &a.1 + &b.1);
                check("+", bounds(a).add(bounds(b)), &sum, &[a, b]);
                let diff = (&a.0 - &b.1, &a.1 - &b.0);
                check("-", bounds(a).add(bounds(b).neg()), &diff, &[a, b]);
            }
        }
    }

    #[test]
    fn products_hold_the_exact_range() {
        let rs = ranges();
        for a in &rs {
            for b in &rs {
                let p = span([&a.0 * &b.0, &a.0 * &b.1, &a.1 * &b.0, &a.1 * &b.1]);
                check("*", bounds(a).mul(bounds(b)), &p, &[a, b]);
            }
        }
    }

    #[test]
    fn euclidean_quotients_hold_the_exact_range() {
        // `floor(a / b)` is monotone in `a` and, on each side of 0, in `b`, so its least and
        // greatest values are at the corners of each side.
        let rs = ranges();
        let one = Num::from(1i64);
        for a in &rs {
            for b in &rs {
                let mut divisors = Vec::new();
                if b.1 >= one {
                    divisors.extend([b.0.clone().max(one.clone()), b.1.clone()]);
                }
                if b.0 <= -&one {
                    divisors.extend([b.0.clone(), b.1.clone().min(-&one)]);
                }
                let got = bounds(a).div(bounds(b));
                if divisors.is_empty() {
                    assert_eq!(got, None, "0 is the only divisor");
                    continue;
                }
                let q = span(
                    divisors
                        .iter()
                        .flat_map(|d| [a.0.div_euclid(d), a.1.div_euclid(d)]),
                );
                check("div", got.expect("a divisor other than 0"), &q, &[a, b]);
                let m = divisors.iter().map(Num::abs).max().expect("a divisor");
                let r = bounds(a).rem(bounds(b)).expect("a divisor other than 0");
                assert!(holds(r, &Num::from(0i64), &(&m - &one)), "mod: {r:?}");
            }
        }
    }

    /// Whole `f64`s near 0 and within a few places of ±2^k for each `k` of 52, 53, 54, 62,
    /// 63, 64, 70 and 100. Unlike [`ends`], each is an `f64`, so the operations below see
    /// them unwidened and their own rounding is all that the checks measure (a `Bounds` end
    /// past 2^53 is already a place wide, which can hide a missing step in an operation).
    fn whole_f64s() -> Vec<f64> {
        let mut out = vec![0.0, 1.0, 2.0, 3.0, 7.0, 1000.0];
        for k in [52, 53, 54, 62, 63, 64, 70, 100] {
            let p = 2f64.powi(k);
            let (mut up, mut down) = (p, p);
            out.push(p);
            for _ in 0..3 {
                up = up.next_up();
                down = down.next_down();
                out.extend([up, down]);
            }
        }
        // Below 2^52 the places are fractions.
        out.retain(|v| v.fract() == 0.0);
        let negated: Vec<f64> = out.iter().map(|v| -v).collect();
        out.extend(negated);
        out
    }

    #[test]
    fn floor_quotients_of_whole_f64s_bound_the_exact_quotient() {
        let divisors = whole_f64s().into_iter().filter(|b| *b >= 1.0);
        for b in divisors {
            for a in whole_f64s() {
                let exact = num_of(a).unwrap().div_euclid(&num_of(b).unwrap());
                let (lo, hi) = (floor_quotient(a, b, false), floor_quotient(a, b, true));
                let what = format!("floor({a} / {b})");
                assert!(
                    holds(Bounds { lo, hi }, &exact, &exact),
                    "{what}: {lo} {hi}"
                );
                if small(&exact) {
                    assert!(is(Bounds { lo, hi }, &exact, &exact), "{what}: {lo} {hi}");
                }
            }
        }
    }

    #[test]
    fn floor_quotients_past_i64_that_round_to_a_whole_number_are_exact() {
        // `a` past `i64` and `b` near `a / n`, so that `a / b` is within a place of the whole
        // `n`, on either side, without `b` dividing `a`: the case decided by the sign of
        // `a - b r`.
        let mut seen = 0;
        for k in [63, 64, 70, 100] {
            let mut a = 2f64.powi(k);
            for _ in 0..4 {
                for m in [10, 20, 30, 40, 50] {
                    for j in [0.0, 1.0, 3.0] {
                        let n = 2f64.powi(m) + j;
                        for b in [
                            (a / n).floor() - 1.0,
                            (a / n).floor(),
                            (a / n).ceil(),
                            (a / n).ceil() + 1.0,
                        ] {
                            let r = a / b;
                            if r.fract() == 0.0 && a % b != 0.0 {
                                seen += 1;
                            }
                            let exact = num_of(a).unwrap().div_euclid(&num_of(b).unwrap());
                            let q = Bounds {
                                lo: floor_quotient(a, b, false),
                                hi: floor_quotient(a, b, true),
                            };
                            assert!(is(q, &exact, &exact), "floor({a} / {b}): {q:?}");
                        }
                    }
                }
                a = a.next_down();
            }
        }
        assert!(seen > 0, "no quotient rounded to a whole number");
    }

    #[test]
    fn powers_of_whole_f64s_bound_the_exact_power() {
        for m in whole_f64s().into_iter().filter(|m| *m >= 0.0) {
            for n in [1u32, 2, 3, 4, 5, 7, 8, 13, 64] {
                let exact = num_of(m).unwrap().pow(n);
                let k = Num::from(i64::from(n));
                let b = Bounds {
                    lo: pow_magnitude(m, &k, false),
                    hi: pow_magnitude(m, &k, true),
                };
                assert!(holds(b, &exact, &exact), "{m} ^ {n}: {b:?}");
                if small(&exact) {
                    assert!(is(b, &exact, &exact), "{m} ^ {n}: {b:?}");
                }
            }
        }
    }

    #[test]
    fn powers_hold_the_exact_range() {
        for a in &ranges() {
            for n in [1u32, 2, 3, 4, 5, 7, 8, 13, 64] {
                let (l, h) = (a.0.pow(n), a.1.pow(n));
                let want = if n % 2 == 1 {
                    (l, h)
                } else if a.0.signum() < 0 && a.1.signum() > 0 {
                    (Num::from(0i64), l.max(h))
                } else {
                    span([l, h])
                };
                let got = bounds(a).pow(&Num::from(i64::from(n)));
                check(&format!("^ {n}"), got, &want, &[a]);
            }
        }
    }
}
