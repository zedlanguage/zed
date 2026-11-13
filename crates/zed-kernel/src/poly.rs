//! The sparse polynomial normal form over a commutative ring (step POLY-nf; DESIGN.md
//! sec:verification, rung 2 at `int` and `rat`, and sec:optimizer, rung 3 at every ring with
//! that evidence).
//!
//! An identity `lhs == rhs` is read as two polynomials: `+`, `-`, `*`, unary `-` and `^` with
//! a literal exponent are ring operations, a number literal is a coefficient (a rational one
//! only at `rat`, where `/` by a nonzero literal is a product with its inverse too), each
//! binder is a variable, and every other subterm is an atom, a variable of its own named by its
//! text. A `let` is read through, its value shared.
//!
//! [`decide`] first compares the two sides at two points derived from the identity's content,
//! the same on every run and in batch and single-file checking (sec:optimizer,
//! \[SchwartzZippel\]). The sides are evaluated modulo the prime `2^61 - 1`; a difference there is
//! a difference over the integers, so at `int` and `rat` with no atom it refutes the identity,
//! and a witness of small integers is then found one binder at a time among `deg + 1` values
//! (sec:verification, rung 2). Agreement is no grade: it only lets the expansion run. Then
//! products of sums are expanded and like monomials merged; equal normal forms prove the
//! identity in every commutative ring, since the expansion uses only the ring laws.
//!
//! The expansion counts its work as it goes, each operation charged before it runs by the
//! sizes of its operands, and stops with a [`Refusal`] once the work would pass [`LIMIT`]: the
//! work that took 250 ms on the machine and at the load it was measured at (QUESTIONS A99).

use std::borrow::Cow;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::digest::{Digest, step};
use crate::num::{is_prime, mul_cost, mul_int, mul_uint, pow_uint};
use crate::term::{Prim, Term};
use crate::value::Value;

/// The ring the identity is read in.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Carrier {
    /// `int`: integer coefficients; a difference at a point refutes.
    Int,
    /// `rat`: rational coefficients, and `/` by a nonzero literal; a difference at a point
    /// refutes.
    Rat,
    /// A commutative ring known only by its evidence (rung 3): integer coefficients, read as
    /// sums of the ring's one. A difference proves nothing, since the identity may hold in a
    /// ring of finite characteristic (`(x + y) * (x + y) == x * x + y * y` holds mod 2).
    Ring,
}

/// The most work the expansion of an identity may spend: 250 ms of the expansion on the
/// machine and at the load it was measured at (QUESTIONS A99), in work units, so that every
/// machine refuses the same identities. Measured on 2026-11-13 on an AMD Ryzen 9 5950X (16
/// cores, 32 threads, up to 5.1 GHz) at a load average of 36 to 41 from other builds and tests,
/// with the test profile (`opt-level = 2`): the largest identity of each of nine families of
/// products, powers and sums (a probe of plan row POLY-work-250ms, not kept; `l03_09_egraph::calibration` times three laws again) took 10 to 22 ns a unit, 14.3 ns as
/// the geometric mean, 70 000 units a millisecond.
///
/// The work is counted by `Budget`, each operation charged before it runs, by the operands'
/// sizes: its number of terms `t`, and the words `w` of its widest coefficient, 64 bits each.
/// A unit is one of the dense product's `L log2 L`, about 14 ns, in the `L` 32-bit words of the
/// packed integers (`Poly::plan`), so the dense product's charge grows with the exponents'
/// span times the coefficients' bits. The other charges are that unit times their measured
/// times: a sum or a negation `SUM_TERM` or `SPARSE_TERM` a term and `SUM_WORD` a word of
/// its operands, the sparse product `PAIR` plus `w1 w2` for each of its `t1 t2` pairs, the
/// support product `SUPPORT` for each unit it counts, and a power of one term the words of
/// its result.
///
/// Complexity tradeoff: the naive limit, a bound on the written size of the identity
/// (QUESTIONS A98: the work of the costliest product of three sums written at that size),
/// refused a power by the value of its exponent, `(x + y) ^ 72 - x == (x + y) ^ 36 * (y + x) ^
/// 36 - x` at 0.3 ms, while it allowed a sum of 4096 names that takes 4 s; its units tracked
/// the time within a factor of 40. This limit refuses by the predicted time itself, at the cost
/// of one constant measured on one machine, which a faster or idle machine spends in less than
/// 250 ms; the counted work predicts the time within a factor of 2 on every family but one,
/// a sparse product whose pairs merge into few terms (`((x + y) ^ 64 + x) ^ 2`, 52 ns a unit).
/// Not counted: the reading of the identity, its points and its factors, linear in its size
/// (about 0.2 ms for a size of 6000), so no identity is refused for its length alone. A refusal
/// costs at most the limit, since each operation is charged before it runs. A complete
/// solution would decide identity of arithmetic formulas deterministically in polynomial time,
/// which no known algorithm does (polynomial identity testing), so some identities must be
/// refused.
pub const LIMIT: f64 = 17_500_000.0;

/// The time [`LIMIT`] stands for, in milliseconds.
pub const LIMIT_MS: f64 = 250.0;

/// The charge for each term a sum or a negation reads, with packed keys: about 30 ns, its
/// coefficient's copy and later free.
const SUM_TERM: f64 = 2.0;

/// The charge for each term a sum or a negation reads, with keys that are not packed: about 90
/// ns, its key's copy too.
const SPARSE_TERM: f64 = 6.0;

/// The charge for each 64-bit word of a coefficient a sum or a negation reads: about 3 ns.
const SUM_WORD: f64 = 0.2;

/// The charge for each pair of the sparse product besides its `w1 w2` words: about 130 ns, the
/// product's allocation, its sorting and its merge.
const PAIR: f64 = 8.0;

/// The charge for each unit the support product counts: about 30 ns.
const SUPPORT: f64 = 2.0;

/// The cost of a pair of the sparse product besides its coefficients' product, in `Poly::mul`'s
/// choice of method, in the units of `num::mul_cost` (one word product, about 16 instructions).
/// Measured in instructions by `crossover poly-dense|poly-gaps|poly-wide <shape> pair` on
/// 2026-11-13 (load about 60 on 32 cores; instruction counts do not depend on it), with
/// [`SLOT_COST`] and [`DENSE_COST`] as set. Each shape alone fits: `poly-dense 1` 48 to 67,
/// `poly-dense 4` 67 to 84, `poly-gaps 16` 72 to 96, `poly-gaps 64` 59 to 69, `poly-wide 2`
/// up to 210, `poly-wide 8` from 48. No value fits all, so the choice is off somewhere by at
/// most 1.09 times the cheaper method's instructions, at any value from 60 to 66; `poly-wide 8`
/// is off by 1.30 at every value of all three constants, since `num::mul_cost` overcounts its
/// packed product.
const PAIR_COST: f64 = 60.0;

/// The cost of a slot of the dense product's output besides the product of the packed
/// integers, in `Poly::mul`'s choice of method, in the units of `num::mul_cost`. Measured as
/// [`PAIR_COST`], `... slot`: `poly-dense 1` fits 25 to 73, `poly-dense 4` up to 18,
/// `poly-gaps 16` up to 19, `poly-gaps 64` 7 to 46, `poly-wide 8` up to 91; set within 1.09.
const SLOT_COST: f64 = 40.0;

/// The cost of the dense product besides its slots and its packed product (packing, the
/// transform's setup, unpacking), over the sparse product's besides its pairs, in
/// `Poly::mul`'s choice of method, in the units of `num::mul_cost`. Measured as
/// [`PAIR_COST`], `... fixed`: `poly-dense 1` fits 596 to 996, `poly-dense 4` 106 to 455,
/// `poly-wide 2` from 99, the rest up to 1158 or more; set within 1.09. Without this term
/// (0) the best that `PAIR_COST` and `SLOT_COST` reach is 1.41.
const DENSE_COST: f64 = 700.0;

/// The units of [`LIMIT`] in one unit of `num::mul_cost`, as [`PAIR`] and [`PAIR_COST`] measure
/// the same cost of a pair in each: about 2 ns, a word product's 16 instructions.
const CHOICE_UNIT: f64 = PAIR / PAIR_COST;

/// The work an expansion has spent, the most it may spend, and the work it would have reached
/// at the charge it refused, in the units of [`LIMIT`].
struct Budget {
    spent: f64,
    most: f64,
    wanted: f64,
}

impl Budget {
    fn new(most: f64) -> Budget {
        Budget {
            spent: 0.0,
            most,
            wanted: 0.0,
        }
    }

    /// What is left to spend.
    fn left(&self) -> f64 {
        self.most - self.spent
    }

    /// Spends `w`; `None`, and nothing spent, when that would pass the most, the work it would
    /// have reached kept as the prediction.
    fn spend(&mut self, w: f64) -> Option<()> {
        if self.spent + w > self.most {
            self.wanted = self.spent + w;
            return None;
        }
        self.spent += w;
        Some(())
    }
}

/// The charge for a sum or a negation reading `p`: [`SUM_TERM`], or [`SPARSE_TERM`] with keys
/// that are not packed, for each term, and [`SUM_WORD`] for each word of its coefficients.
fn sum_charge<K: Key>(p: &Poly<K>) -> f64 {
    let words: u64 = p.terms.iter().map(|(_, c)| c.bits().div_ceil(64)).sum();
    p.terms.len() as f64 * K::TERM + words as f64 * SUM_WORD
}

/// The prime the points are taken modulo, `2^61 - 1`.
const P: u64 = (1 << 61) - 1;

/// What [`decide`] found.
#[derive(Clone, Debug, PartialEq)]
pub enum Verdict {
    /// The two normal forms are equal: the identity holds in every commutative ring.
    Proved,
    /// The two sides differ at the point, a value for each binder in the order given.
    Refuted(Point),
    /// The normal forms differ, but no point refutes: a side holds an atom, which may depend on
    /// the binders, or the carrier is a ring that may have finite characteristic.
    Differs,
    /// The expansion would cost more than [`LIMIT`] allows, or an exponent is too wide.
    Refused(Refusal),
}

/// The decision on an identity, and the measures of its normal forms.
#[derive(Clone, Debug)]
pub struct Decision {
    /// The verdict.
    pub verdict: Verdict,
    /// The most sums any product multiplies, a power `a ^ n` counting the fewer of `n` times the
    /// sums of `a` and the bound on its monomials less one: a measure of the written shape, which
    /// no longer refuses anything (see [`LIMIT`]).
    pub sums: u64,
    /// The total degree of the two sides, at most; `None` past `u64::MAX`.
    pub degree: Option<u64>,
    /// The number of terms of each side's normal form, when they were expanded.
    pub terms: Option<[usize; 2]>,
    /// Whether the sides were found equal as products of powers of the same factors, each
    /// factor expanded once and the sides not at all: `(1 + x) ^ 1000 == (1 + x) ^ 500 * (x +
    /// 1) ^ 500`.
    pub factored: bool,
    /// The identity's size as a term: one for each operation, name, atom, `let` and read of a
    /// `let`'s name, and one for each number plus the bits of its numerator, of its denominator
    /// when that is not 1, and of an exponent.
    pub size: u64,
    /// The work the expansion counted, in the units of [`LIMIT`]: of the reading of the factors
    /// when [`Decision::factored`], of the sides' expansion when they were expanded, up to the
    /// refused operation when refused, and 0 when a point decided.
    pub work: f64,
}

/// Values for the binders, in the order given, at which the two sides differ.
#[derive(Clone, Debug, PartialEq)]
pub struct Point(pub Vec<(Arc<str>, BigInt)>);

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, (name, v)) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{name} = {v}")?;
        }
        Ok(())
    }
}

/// Why a product is not expanded.
#[derive(Clone, Debug, PartialEq)]
pub enum Refused {
    /// The expansion's work would pass [`LIMIT`]: the work it would have reached at the refused
    /// operation, a lower bound on the whole expansion's.
    Work(f64),
    /// A power's exponent, or a monomial's degree, is past `u64::MAX`, the widest exponent a
    /// monomial holds.
    Exponent,
}

/// A product the normal form does not expand: an error naming it, with a written proof in its
/// menu and the points that agreed.
#[derive(Clone, Debug, PartialEq)]
pub struct Refusal {
    /// The product, as the kernel term prints it.
    pub product: String,
    /// Why.
    pub why: Refused,
    /// The points at which the two sides agreed; empty when no point could be read (a
    /// rational constant whose denominator the prime divides).
    pub agreed: Vec<Point>,
}

impl Refusal {
    /// The message, in the form of sec:diagnostics: a short headline naming the product, the
    /// notes, and the repair, a written proof of `law`, the law's text without its `;`. For
    /// [`Refused::Work`] it is the row "Expansion too costly" of the rejection table: the law (in
    /// the repair), the product, the predicted time against 250 ms, the predicted work against
    /// [`LIMIT`], that the limit was measured once so that every machine refuses the same laws,
    /// and the points at which the two sides agreed.
    pub fn message(&self, law: &str) -> String {
        let mut out = match &self.why {
            Refused::Work(work) => format!(
                "Cannot expand `{}`: expanding the law takes at least {:.0} ms, more than {LIMIT_MS} ms.",
                self.product,
                (work / LIMIT * LIMIT_MS).ceil()
            ),
            Refused::Exponent => format!(
                "Cannot expand `{}`: an exponent is above {}.",
                self.product,
                u64::MAX
            ),
        };
        match &self.why {
            Refused::Work(work) => out.push_str(&format!(
                "\n  note: the time is predicted from the sizes of the sums and products: at least {work:.0} units of work, against a limit of {LIMIT:.0} units measured as {LIMIT_MS} ms on one machine, so that every machine refuses the same laws.",
            )),
            Refused::Exponent => {}
        }
        if !self.agreed.is_empty() {
            let points: Vec<String> = self.agreed.iter().map(|p| format!("`{p}`")).collect();
            out.push_str(&format!(
                "\n  note: the two sides agree at every point tried: {}.",
                points.join(" and ")
            ));
        }
        out.push_str(&format!("\n  Try `{law} proof {{ … }}` instead."));
        out
    }
}

/// The verdict on `lhs == rhs`, with `binders` the names of the identity's binders, in the
/// order a witness lists them. The cost is linear in the two terms for the points, and the
/// expansion's cost after: `O(N log N)` in the number `N` of products its multiplications
/// form, the least of a sparse and a dense product at each step (see `Poly::mul`).
pub fn decide(lhs: &Term, rhs: &Term, binders: &[&str], carrier: Carrier) -> Decision {
    Identity::new(lhs, rhs, binders, carrier).decide()
}

/// The normal form of `t`, printed with the highest total degree first (`x ^ 2 + 2 * x * y`),
/// or the refusal of one of its products.
pub fn normal_form(t: &Term, binders: &[&str], carrier: Carrier) -> Result<String, Refusal> {
    let zero = Term::Lit(Value::Int(0));
    let id = Identity::new(t, &zero, binders, carrier);
    let shapes = id.shapes();
    let reach = id.reachable(&id.sides);
    if let Some(i) = id.too_wide(&shapes, &reach) {
        return Err(id.refused(i, Refused::Exponent, Vec::new()));
    }
    let mut budget = Budget::new(LIMIT);
    Ok(match id.keys(&shapes, &reach) {
        Keys::Packed(ctx) => {
            let forms = id.expand::<u128>(&ctx, &reach, &id.sides[..1], &mut budget);
            id.show(
                &forms.map_err(|i| id.refused(i, Refused::Work(budget.wanted), Vec::new()))?[0],
                &ctx,
            )
        }
        Keys::Sparse => {
            let ctx = Packing::none();
            let forms = id.expand::<Sparse>(&ctx, &reach, &id.sides[..1], &mut budget);
            id.show(
                &forms.map_err(|i| id.refused(i, Refused::Work(budget.wanted), Vec::new()))?[0],
                &ctx,
            )
        }
    })
}

/// A node of an identity's two sides, a DAG whose children come before their parents.
#[derive(Debug)]
enum Node {
    /// `num / den`, reduced, `den` positive.
    Const(BigInt, BigInt),
    /// A binder or an atom: the index of its name.
    Leaf(u32),
    Add(usize, usize),
    Sub(usize, usize),
    Neg(usize),
    Mul(usize, usize),
    Pow(usize, BigUint),
}

/// The written shape of a node: its total degree at most (`None` past `u64::MAX`), the sums
/// it multiplies ([`Decision::sums`]), and its number of monomials at most (`u64::MAX` past
/// it).
#[derive(Clone, Copy, Debug)]
struct Shape {
    degree: Option<u64>,
    sums: u64,
    terms: u64,
}

/// The two sides of an identity, lowered.
struct Identity<'t> {
    nodes: Vec<Node>,
    /// The term each operation's node was lowered from, to name a refused one.
    origin: Vec<Option<&'t Term>>,
    /// The names of the leaves: the binders first, then the atoms' texts.
    names: Vec<Arc<str>>,
    binders: usize,
    sides: [usize; 2],
    carrier: Carrier,
    /// The size as a term ([`Decision::size`]).
    size: u64,
}

/// The work of the lowering's loop, which keeps its own stack so that a term of any depth is
/// lowered on a small call stack.
enum Work<'t> {
    Visit(&'t Term),
    Build(Op, &'t Term),
    Bind(&'t str),
    Unbind(&'t str),
}

/// The operation a [`Work::Build`] applies to the lowered operands on the stack.
enum Op {
    Add,
    Sub,
    Mul,
    Neg,
    Pow(BigUint),
    /// A product with the constant `num / den`, the inverse of a divisor.
    Scale(BigInt, BigInt),
}

impl<'t> Identity<'t> {
    /// `lhs` and `rhs` lowered: one pass over each term with a stack, a lookup per name.
    fn new(lhs: &'t Term, rhs: &'t Term, binders: &[&str], carrier: Carrier) -> Identity<'t> {
        let mut id = Identity {
            nodes: Vec::new(),
            origin: Vec::new(),
            names: binders.iter().map(|b| Arc::from(*b)).collect(),
            binders: binders.len(),
            sides: [0, 0],
            carrier,
            size: 0,
        };
        let binder: HashMap<&str, u32> = binders
            .iter()
            .enumerate()
            .map(|(i, b)| (*b, u32::try_from(i).expect("fewer than 2^32 binders")))
            .collect();
        let mut atoms: HashMap<String, u32> = HashMap::new();
        let mut lets: HashMap<&'t str, Vec<usize>> = HashMap::new();
        for (side, t) in [lhs, rhs].into_iter().enumerate() {
            let mut work = vec![Work::Visit(t)];
            let mut done: Vec<usize> = Vec::new();
            while let Some(w) = work.pop() {
                match w {
                    Work::Visit(t) => match id.visit(t, carrier) {
                        Visit::Leaf(l) => done.push(l),
                        Visit::Name(n) => {
                            let at = match lets.get(n).and_then(|s| s.last()) {
                                Some(&i) => {
                                    id.size += 1;
                                    i
                                }
                                None => match binder.get(n) {
                                    Some(&b) => id.push(Node::Leaf(b), None),
                                    None => id.atom(&mut atoms, n.to_string()),
                                },
                            };
                            done.push(at);
                        }
                        Visit::Atom => {
                            let at = id.atom(&mut atoms, t.to_string());
                            done.push(at);
                        }
                        Visit::Op(op, args) => {
                            work.push(Work::Build(op, t));
                            work.extend(args.iter().rev().map(Work::Visit));
                        }
                        Visit::Let(name, e, body) => {
                            id.size += 1;
                            work.push(Work::Unbind(name));
                            work.push(Work::Visit(body));
                            work.push(Work::Bind(name));
                            work.push(Work::Visit(e));
                        }
                    },
                    Work::Build(op, t) => {
                        let b = done.pop().expect("an operand lowered");
                        let at = match op {
                            Op::Neg => id.push(Node::Neg(b), Some(t)),
                            Op::Pow(n) => id.push(Node::Pow(b, n), Some(t)),
                            Op::Scale(n, d) => {
                                let c = id.push(Node::Const(n, d), None);
                                id.push(Node::Mul(b, c), Some(t))
                            }
                            Op::Add | Op::Sub | Op::Mul => {
                                let a = done.pop().expect("two operands lowered");
                                match op {
                                    Op::Add => id.push(Node::Add(a, b), Some(t)),
                                    Op::Sub => id.push(Node::Sub(a, b), Some(t)),
                                    _ => id.push(Node::Mul(a, b), Some(t)),
                                }
                            }
                        };
                        done.push(at);
                    }
                    Work::Bind(name) => {
                        let v = done.pop().expect("a let's value lowered");
                        lets.entry(name).or_default().push(v);
                    }
                    Work::Unbind(name) => {
                        lets.get_mut(name).and_then(Vec::pop);
                    }
                }
            }
            id.sides[side] = done.pop().expect("a side lowered");
        }
        id
    }

    /// Adds node `n`, lowered from `origin`, and its size: one, and the bits of a number or an
    /// exponent.
    fn push(&mut self, n: Node, origin: Option<&'t Term>) -> usize {
        self.size += 1 + match &n {
            Node::Const(a, b) => a.bits() + if b.is_one() { 0 } else { b.bits() },
            Node::Pow(_, e) => e.bits(),
            _ => 0,
        };
        self.nodes.push(n);
        self.origin.push(origin);
        self.nodes.len() - 1
    }

    /// The leaf of the atom whose text is `text`, one per text.
    fn atom(&mut self, atoms: &mut HashMap<String, u32>, text: String) -> usize {
        let next = u32::try_from(self.names.len()).expect("fewer than 2^32 names");
        let l = match atoms.get(&text) {
            Some(&l) => l,
            None => {
                self.names.push(Arc::from(text.as_str()));
                atoms.insert(text, next);
                next
            }
        };
        self.push(Node::Leaf(l), None)
    }

    /// How `t` is lowered.
    fn visit(&mut self, t: &'t Term, carrier: Carrier) -> Visit<'t> {
        match t {
            Term::Lit(v) => match constant(v, carrier) {
                Some((n, d)) => Visit::Leaf(self.push(Node::Const(n, d), None)),
                None => Visit::Atom,
            },
            Term::Var(n) => Visit::Name(n),
            Term::Let(n, e, body) => Visit::Let(n, e, body),
            Term::Prim(p, args) => match (p, &args[..]) {
                (Prim::Add, [_, _]) => Visit::Op(Op::Add, &args[..]),
                (Prim::Sub, [_, _]) => Visit::Op(Op::Sub, &args[..]),
                (Prim::Mul, [_, _]) => Visit::Op(Op::Mul, &args[..]),
                (Prim::Neg, [_]) => Visit::Op(Op::Neg, &args[..]),
                (Prim::Pow, [_, Term::Lit(e)]) => match exponent(e) {
                    Some(e) => Visit::Op(Op::Pow(e), &args[..1]),
                    None => Visit::Atom,
                },
                (Prim::Div, [_, Term::Lit(d)]) if carrier == Carrier::Rat => {
                    match constant(d, carrier) {
                        Some((n, d)) if !n.is_zero() => {
                            let (n, d) = if n.is_negative() { (-d, -n) } else { (d, n) };
                            Visit::Op(Op::Scale(n, d), &args[..1])
                        }
                        _ => Visit::Atom,
                    }
                }
                _ => Visit::Atom,
            },
            _ => Visit::Atom,
        }
    }

    /// The nodes `roots` reach, the roots included; from the sides, a `let` whose value the body
    /// never reads is not reached.
    fn reachable(&self, roots: &[usize]) -> Vec<bool> {
        let mut r = vec![false; self.nodes.len()];
        for &s in roots {
            r[s] = true;
        }
        for i in (0..self.nodes.len()).rev() {
            if !r[i] {
                continue;
            }
            match &self.nodes[i] {
                Node::Const(..) | Node::Leaf(_) => {}
                Node::Neg(a) | Node::Pow(a, _) => r[*a] = true,
                Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
                    r[*a] = true;
                    r[*b] = true;
                }
            }
        }
        r
    }

    /// The written shape of each node, in one pass.
    fn shapes(&self) -> Vec<Shape> {
        let mut s: Vec<Shape> = Vec::with_capacity(self.nodes.len());
        for n in &self.nodes {
            let shape = match n {
                Node::Const(..) => Shape {
                    degree: Some(0),
                    sums: 0,
                    terms: 1,
                },
                Node::Leaf(_) => Shape {
                    degree: Some(1),
                    sums: 0,
                    terms: 1,
                },
                Node::Neg(a) => s[*a],
                Node::Add(a, b) | Node::Sub(a, b) => {
                    let (a, b) = (s[*a], s[*b]);
                    Shape {
                        degree: a.degree.zip(b.degree).map(|(x, y)| x.max(y)),
                        sums: a.sums.max(b.sums).max(1),
                        terms: a.terms.saturating_add(b.terms),
                    }
                }
                Node::Mul(a, b) => {
                    let (a, b) = (s[*a], s[*b]);
                    Shape {
                        degree: a.degree.zip(b.degree).and_then(|(x, y)| x.checked_add(y)),
                        sums: a.sums.saturating_add(b.sums),
                        terms: a.terms.saturating_mul(b.terms),
                    }
                }
                Node::Pow(a, e) => {
                    let a = s[*a];
                    let e64 = e.to_u64();
                    // An exponent past `u64::MAX` is refused unless the base is 0, 1 or -1,
                    // so reading it as `u64::MAX` only keeps the bounds below upper bounds.
                    let n = e64.unwrap_or(u64::MAX);
                    Shape {
                        degree: match (a.degree, e64) {
                            (Some(0), _) => Some(0),
                            (Some(d), Some(e)) => d.checked_mul(e),
                            _ => None,
                        },
                        // `a ^ n` is a product of `a.sums * n` sums, and also, expanded, a
                        // sum of at most C(T + n - 1, T - 1) <= (n + 1) ^ (T - 1) monomials
                        // for `T = a.terms`: as many as a product of `T - 1` sums of `n + 1`
                        // terms. The smaller count bounds it.
                        sums: a.sums.saturating_mul(n).min(a.terms - 1),
                        terms: power_terms(a.terms, n),
                    }
                }
            };
            s.push(shape);
        }
        s
    }

    /// The first product or power among the nodes `reach` marks whose exponent or degree is past
    /// `u64::MAX`, in the order the nodes were built, so the smallest.
    fn too_wide(&self, shapes: &[Shape], reach: &[bool]) -> Option<usize> {
        for (i, n) in self.nodes.iter().enumerate() {
            if !reach[i] {
                continue;
            }
            // Complexity tradeoff: an exponent or a degree past `u64::MAX` (`x ^ 2 ^ 64` written
            // out) is refused, though true or false is still found at the points first: a
            // monomial holds its exponents as `u64` words, packed into `u128` keys or listed,
            // and an exponent of any width would cost a big integer per exponent in every
            // monomial for a shape no obligation of the corpus writes (COMPLEXITY.md
            // POLY-nf-exponent). A base of 0, 1 or -1 is not refused: its power is a constant.
            // Tested by `poly::tests::refused_shapes`.
            let wide = match n {
                Node::Pow(a, e) => e.to_u64().is_none() && !self.trivial_base(*a),
                _ => false,
            };
            if wide || matches!(n, Node::Mul(..) | Node::Pow(..)) && shapes[i].degree.is_none() {
                return Some(i);
            }
        }
        None
    }

    /// The refusal of node `i`'s operation, with `agreed` the points that agreed.
    fn refused(&self, i: usize, why: Refused, agreed: Vec<Point>) -> Refusal {
        Refusal {
            product: self.origin[i].map_or_else(String::new, |t| t.to_string()),
            why,
            agreed,
        }
    }

    /// Whether node `a` is the constant 0, 1 or -1, whose powers need no exponent's width.
    fn trivial_base(&self, mut a: usize) -> bool {
        while let Node::Neg(b) = &self.nodes[a] {
            a = *b;
        }
        matches!(&self.nodes[a], Node::Const(n, d) if d.is_one() && n.magnitude() <= &BigUint::one())
    }

    /// Whether a difference at a point refutes: the carrier is `int` or `rat` and every leaf
    /// the sides reach is a binder.
    fn refutable(&self, reach: &[bool]) -> bool {
        self.carrier != Carrier::Ring
            && self.nodes.iter().zip(reach).all(|(n, r)| match n {
                Node::Leaf(l) if *r => (*l as usize) < self.binders,
                _ => true,
            })
    }

    /// The identity's content digest: each node's digest from its children's, so equal
    /// identities, in any run and any unit, get equal points.
    fn seed(&self) -> u64 {
        let mut d: Vec<u64> = Vec::with_capacity(self.nodes.len());
        for n in &self.nodes {
            let h = match n {
                Node::Const(a, b) => {
                    let mut h = Digest::default();
                    0u8.hash(&mut h);
                    a.to_signed_bytes_le().hash(&mut h);
                    b.to_signed_bytes_le().hash(&mut h);
                    h.finish()
                }
                Node::Leaf(l) => {
                    let mut h = Digest::default();
                    1u8.hash(&mut h);
                    h.write(self.names[*l as usize].as_bytes());
                    u8::from((*l as usize) < self.binders).hash(&mut h);
                    h.finish()
                }
                Node::Add(a, b) => step(step(2, d[*a]), d[*b]),
                Node::Sub(a, b) => step(step(3, d[*a]), d[*b]),
                Node::Mul(a, b) => step(step(4, d[*a]), d[*b]),
                Node::Neg(a) => step(5, d[*a]),
                Node::Pow(a, e) => {
                    let mut h = Digest::default();
                    6u8.hash(&mut h);
                    d[*a].hash(&mut h);
                    e.to_bytes_le().hash(&mut h);
                    h.finish()
                }
            };
            d.push(h);
        }
        let carrier = match self.carrier {
            Carrier::Int => 0,
            Carrier::Rat => 1,
            Carrier::Ring => 2,
        };
        step(step(carrier, d[self.sides[0]]), d[self.sides[1]])
    }

    /// Point `k` of the identity whose digest is `seed`: each name's coordinate from the seed,
    /// the name and `k`.
    fn point(&self, seed: u64, k: u64) -> Vec<u64> {
        self.names
            .iter()
            .map(|n| {
                let mut h = Digest::default();
                h.write_u64(seed);
                h.write(n.as_bytes());
                h.write_u64(k);
                h.finish() % P
            })
            .collect()
    }

    /// The two sides modulo `P` at `at`, a value per name, in one pass over the nodes, into
    /// `vals`; `None` when a constant's denominator is a multiple of `P`.
    fn eval(&self, at: &[u64], vals: &mut Vec<u64>) -> Option<[u64; 2]> {
        vals.clear();
        for n in &self.nodes {
            let v = match n {
                Node::Const(a, b) => {
                    let d = residue(b);
                    if d == 0 {
                        return None;
                    }
                    mulmod(residue(a), powmod(d, &BigUint::from(P - 2)))
                }
                Node::Leaf(l) => at[*l as usize],
                Node::Add(a, b) => addmod(vals[*a], vals[*b]),
                Node::Sub(a, b) => addmod(vals[*a], P - vals[*b]),
                Node::Neg(a) => (P - vals[*a]) % P,
                Node::Mul(a, b) => mulmod(vals[*a], vals[*b]),
                Node::Pow(a, e) => powmod(vals[*a], e),
            };
            vals.push(v);
        }
        Some([vals[self.sides[0]], vals[self.sides[1]]])
    }

    /// The decision: the points, then the sides as products of powers of the same factors,
    /// then the refusal, then the expansion.
    fn decide(&self) -> Decision {
        let shapes = self.shapes();
        let reach = self.reachable(&self.sides);
        let sums = shapes
            .iter()
            .zip(&reach)
            .filter(|(_, r)| **r)
            .map(|(s, _)| s.sums)
            .max()
            .unwrap_or(0);
        let degree = shapes[self.sides[0]]
            .degree
            .zip(shapes[self.sides[1]].degree)
            .map(|(a, b)| a.max(b));
        let decision = |verdict, terms, work| Decision {
            verdict,
            sums,
            degree,
            terms,
            factored: false,
            size: self.size,
            work,
        };
        let refutable = self.refutable(&reach);
        let seed = self.seed();
        let mut vals = Vec::with_capacity(self.nodes.len());
        let mut agreed = Vec::new();
        for k in 0..2 {
            let at = self.point(seed, k);
            match self.eval(&at, &mut vals) {
                None => break,
                Some([a, b]) if a == b => agreed.push(self.binder_point(&at)),
                Some(_) if refutable => {
                    let w = self.witness(at, degree, &mut vals);
                    return decision(Verdict::Refuted(w), None, 0.0);
                }
                Some(_) => return decision(Verdict::Differs, None, 0.0),
            }
        }
        if let Some(work) = self.factored(&shapes) {
            return Decision {
                factored: true,
                ..decision(Verdict::Proved, None, work)
            };
        }
        if let Some(i) = self.too_wide(&shapes, &reach) {
            let r = self.refused(i, Refused::Exponent, agreed);
            return decision(Verdict::Refused(r), None, 0.0);
        }
        let mut budget = Budget::new(LIMIT);
        let forms = match self.keys(&shapes, &reach) {
            Keys::Packed(ctx) => self
                .expand::<u128>(&ctx, &reach, &self.sides, &mut budget)
                .map(|f| self.compare(f, &ctx, refutable)),
            Keys::Sparse => {
                let ctx = Packing::none();
                self.expand::<Sparse>(&ctx, &reach, &self.sides, &mut budget)
                    .map(|f| self.compare(f, &ctx, refutable))
            }
        };
        match forms {
            Ok((verdict, terms)) => decision(verdict, Some(terms), budget.spent),
            Err(i) => {
                let r = self.refused(i, Refused::Work(budget.wanted), agreed);
                decision(Verdict::Refused(r), None, budget.spent)
            }
        }
    }

    /// Whether the two sides are equal as products of powers of the same factors, found
    /// without expanding either side. Each side is read as `c * f1 ^ e1 * … * fk ^ ek` through
    /// its products, powers and negations, the exponents multiplied down (`((x + y) ^ 3 * z) ^
    /// 2` is `(x + y) ^ 6 * z ^ 2`). Each factor, a sum, a name or a constant, is expanded once
    /// and divided by its content and the sign of its first term, so `2 * y - 2 * x` is `-2`
    /// times `x - y`. Equal factors merge by adding their exponents, and the sides are equal
    /// when every factor has the same exponent on both and their constants agree. `false` when
    /// the sides are not found equal so, and then the expansion decides. A side that is a sum or a
    /// name is one factor at exponent 1, which the other side matches only as that factor times a
    /// constant, a product the expansion forms as cheaply; so such an identity (`x * x - y * y ==
    /// (x - y) * (x + y)`) is left to the expansion at once, not expanded twice.
    ///
    /// Complexity tradeoff: the naive way, expanding both sides, costs the size of the expanded
    /// powers, `(1 + x) ^ k` `k + 1` terms of up to `k` bits, `O(k^2)` bits for an exponent of
    /// `log k` written digits. This pass costs one step for each node and side, in `u128`
    /// exponents, the expansion of each factor once, which the expansion of the sides would
    /// pay too, and one hash of each factor's form, so `(1 + x) ^ 1000000 == (1 + x) ^ 500000 *
    /// (1 + x) ^ 500000` costs as much as `1 + x`. Given up: an identity whose factors differ
    /// (`(1 + x) ^ k * (1 - x) ^ k == (1 - x ^ 2) ^ k`) is left to the expansion, which forms the
    /// factors again, so such an identity costs up to twice the expansion; and so is one
    /// whose exponents multiply past `2^128`: as big integers, the exponents down a chain of `m`
    /// powers of 64 bits would cost `O(m^2)` words, and the expansion refuses an exponent past
    /// `u64::MAX` anyway. A factor whose expansion passes the limit leaves the identity to the
    /// expansion, which refuses it. A constant below 1 is kept as its reciprocal on the other
    /// side, so `2` and `1 / 2` cancel; the constants that still do not cancel are multiplied out
    /// by a product tree, no larger than the coefficients the expansion would form, and charged.
    /// Constants with a common factor that is not the whole of either (`4 ^ k` against `2 ^ (2 *
    /// k)`) are raised, not cancelled: a coprime base of the constants would cancel them.
    /// Tested by `poly::tests::products_of_powers` and `l03_09_egraph::factored` (COMPLEXITY.md
    /// POLY-nf-power-value).
    ///
    /// The work is counted against [`LIMIT`] as the expansion's is, the constants' powers
    /// charged the words of their results, and past it the identity is left to the expansion,
    /// which counts afresh: the factors' keys may differ from the sides', so their forms are not
    /// reused, and a refused identity costs at most twice the limit. `Some` of the work when the
    /// sides are found equal.
    fn factored(&self, shapes: &[Shape]) -> Option<f64> {
        let is_factor = |i: usize| {
            matches!(
                self.nodes[i],
                Node::Add(..) | Node::Sub(..) | Node::Leaf(_) | Node::Const(..)
            )
        };
        if self.sides.iter().any(|&root| {
            matches!(
                self.nodes[root],
                Node::Add(..) | Node::Sub(..) | Node::Leaf(_)
            )
        }) {
            return None;
        }
        let (exp, minus) = self.exponents()?;
        let factors: Vec<usize> = (0..self.nodes.len())
            .filter(|&i| exp[i] != [0, 0] && is_factor(i))
            .collect();
        let reach = self.reachable(&factors);
        if self.too_wide(shapes, &reach).is_some() {
            return None;
        }
        let mut budget = Budget::new(LIMIT);
        let b = &mut budget;
        let same = match self.keys(shapes, &reach) {
            Keys::Packed(ctx) => self.same_factors::<u128>(&ctx, &reach, &factors, &exp, minus, b),
            Keys::Sparse => {
                self.same_factors::<Sparse>(&Packing::none(), &reach, &factors, &exp, minus, b)
            }
        };
        same.then_some(budget.spent)
    }

    /// The exponent of every node in each side's product of powers, and whether each side's
    /// negations are odd in number: a product passes its exponent to both children, a power
    /// its exponent times its own, a negation its exponent; `None` past `u128::MAX`. Nodes are
    /// built children first, so one pass from the last node visits every parent first.
    fn exponents(&self) -> Option<(Vec<[u128; 2]>, [bool; 2])> {
        let mut exp = vec![[0u128; 2]; self.nodes.len()];
        let mut minus = [false; 2];
        for (s, &root) in self.sides.iter().enumerate() {
            exp[root][s] = 1;
        }
        for i in (0..self.nodes.len()).rev() {
            for s in 0..2 {
                let e = exp[i][s];
                if e == 0 {
                    continue;
                }
                let mut pass = |c: usize, by: u128| -> Option<()> {
                    exp[c][s] = exp[c][s].checked_add(by)?;
                    Some(())
                };
                match &self.nodes[i] {
                    Node::Mul(a, b) => {
                        pass(*a, e)?;
                        pass(*b, e)?;
                    }
                    // `a ^ 0` is 1, as `Poly::pow` has it, even for `a` zero.
                    Node::Pow(a, k) if !k.is_zero() => pass(*a, e.checked_mul(k.to_u128()?)?)?,
                    Node::Neg(a) => {
                        pass(*a, e)?;
                        minus[s] ^= e % 2 == 1;
                    }
                    _ => {}
                }
            }
        }
        Some((exp, minus))
    }

    /// Whether the sides' products of `factors`, at the exponents `exp` and with the signs
    /// `minus`, are equal, each factor expanded once with keys `K` ([`Identity::factored`]),
    /// the work charged to `budget`: `false` past it.
    fn same_factors<K: Key>(
        &self,
        ctx: &Packing,
        reach: &[bool],
        factors: &[usize],
        exp: &[[u128; 2]],
        mut minus: [bool; 2],
        budget: &mut Budget,
    ) -> bool {
        let Ok(forms) = self.expand::<K>(ctx, reach, factors, budget) else {
            return false;
        };
        let mut zero = [false; 2];
        // Each factor's form without its content and sign, and the content `num / den`, each
        // with its exponents on the two sides.
        let mut forms_at: HashMap<Vec<(K, BigInt)>, [u128; 2]> = HashMap::new();
        let mut constants: HashMap<(BigUint, BigUint), [u128; 2]> = HashMap::new();
        let add = |to: &mut [u128; 2], e: [u128; 2]| -> Option<()> {
            for s in 0..2 {
                to[s] = to[s].checked_add(e[s])?;
            }
            Some(())
        };
        for (form, &i) in forms.into_iter().zip(factors) {
            let e = exp[i];
            let Some((first, c)) = form.terms.first() else {
                for s in 0..2 {
                    zero[s] |= e[s] > 0;
                }
                continue;
            };
            let negative = c.is_negative();
            let constant = form.terms.len() == 1 && *first == K::unit();
            let content = form.terms.iter().fold(BigInt::zero(), |g, (_, c)| g.gcd(c));
            for s in 0..2 {
                minus[s] ^= negative && e[s] % 2 == 1;
            }
            let g = content.gcd(&form.den);
            let (num, den) = (
                (&content / &g).into_parts().1,
                (&form.den / &g).into_parts().1,
            );
            // A constant below 1 is kept as its reciprocal on the other side (`c ^ l * A == c ^ r
            // * B` is `A * (1 / c) ^ r == B * (1 / c) ^ l`), so the 2 of `2 * x + 2` cancels the
            // 1/2 of `/ 2` instead of both being raised to their exponents.
            let (num, den, at) = if num < den {
                (den, num, [e[1], e[0]])
            } else {
                (num, den, e)
            };
            if !(num.is_one() && den.is_one())
                && add(constants.entry((num, den)).or_default(), at).is_none()
            {
                return false;
            }
            if !constant {
                let unit = if negative { -content } else { content };
                let primitive = form
                    .terms
                    .into_iter()
                    .map(|(k, c)| (k, c / &unit))
                    .collect();
                if add(forms_at.entry(primitive).or_default(), e).is_none() {
                    return false;
                }
            }
        }
        if zero[0] || zero[1] {
            return zero[0] && zero[1];
        }
        if forms_at.values().any(|[l, r]| l != r) || minus[0] != minus[1] {
            return false;
        }
        // The constants that do not cancel: `l` over `r` on each side, compared crosswise.
        let mut parts: [[Vec<BigUint>; 2]; 2] = Default::default();
        for ((num, den), [l, r]) in constants {
            let (s, d) = if l > r { (0, l - r) } else { (1, r - l) };
            if d == 0 {
                continue;
            }
            let Ok(d) = u64::try_from(d) else {
                return false;
            };
            // The words of the two powers, as `Poly::pow` charges a monomial's.
            let gain = |x: &BigUint| ((x.bits() - 1) as f64 * d as f64 / 64.0).ceil().max(1.0);
            if budget.spend(gain(&num) + gain(&den)).is_none() {
                return false;
            }
            parts[s][0].push(pow_uint(&num, d));
            parts[s][1].push(pow_uint(&den, d));
        }
        let [[ln, ld], [rn, rd]] = parts.map(|p| p.map(product));
        mul_uint(&ln, &rd) == mul_uint(&rn, &ld)
    }

    /// The verdict from the two sides' normal forms with keys `K`, and their numbers of terms.
    /// Their difference is not charged: one merge of two lists the expansion paid to form.
    fn compare<K: Key>(
        &self,
        forms: Vec<Poly<K>>,
        ctx: &Packing,
        refutable: bool,
    ) -> (Verdict, [usize; 2]) {
        let mut forms = forms.into_iter();
        let (l, r) = (
            forms.next().expect("the left side expanded"),
            forms.next().expect("the right side expanded"),
        );
        let terms = [l.terms.len(), r.terms.len()];
        let diff = l
            .add(&r, true, &mut Budget::new(f64::INFINITY))
            .expect("an unbounded budget");
        let verdict = if diff.terms.is_empty() {
            Verdict::Proved
        } else if !refutable {
            Verdict::Differs
        } else {
            self.expanded_witness(&diff, ctx)
                .map_or(Verdict::Differs, Verdict::Refuted)
        };
        (verdict, terms)
    }

    /// The binders' coordinates of `at`.
    fn binder_point(&self, at: &[u64]) -> Point {
        Point(
            self.names[..self.binders]
                .iter()
                .zip(at)
                .map(|(n, v)| (n.clone(), BigInt::from(*v)))
                .collect(),
        )
    }

    /// A witness of small integers from `at`, a point where the sides differ: each binder in
    /// turn takes the first of `0, 1, -1, 2, -2, …` at which the sides still differ, the
    /// binders after it kept at `at`.
    ///
    /// Complexity tradeoff: nothing is given up; the cost is a pass over the nodes per value
    /// tried. Holding the earlier binders at their values and the later ones at `at`, the
    /// difference is a polynomial in this binder of degree at most `degree`, not zero since it
    /// is not zero at `at`'s coordinate, so one of any `degree + 1` distinct values, or that
    /// coordinate itself, keeps it nonzero: at most `degree + 2` passes for a binder, and
    /// usually one or two, a binder needing more only where the difference has that many
    /// small integer roots in it. Tested by `l03_09_egraph::witness` (COMPLEXITY.md K107).
    fn witness(&self, mut at: Vec<u64>, degree: Option<u64>, vals: &mut Vec<u64>) -> Point {
        let tries = degree.map_or(u64::MAX, |d| d.saturating_add(1)).min(P - 1);
        let mut found = Vec::with_capacity(self.binders);
        for b in 0..self.binders {
            let keep = at[b];
            let mut chosen = BigInt::from(keep);
            for i in 0..tries {
                let v = small(i);
                at[b] = small_mod(v);
                if let Some([x, y]) = self.eval(&at, vals)
                    && x != y
                {
                    chosen = BigInt::from(v);
                    break;
                }
                at[b] = keep;
            }
            found.push((self.names[b].clone(), chosen));
        }
        Point(found)
    }

    /// The keys the expansion uses: a monomial packed into a `u128` by Kronecker substitution,
    /// each name a digit of radix `degree + 1`, when every monomial fits; a list of names and
    /// exponents otherwise.
    fn keys(&self, shapes: &[Shape], reach: &[bool]) -> Keys {
        // Every node expanded, not only the sides: `(x ^ 9) ^ 0` is of degree 0, and `x ^ 9`
        // is expanded on the way.
        let mut d = 0;
        for (s, r) in shapes.iter().zip(reach) {
            if *r {
                match s.degree {
                    Some(x) => d = d.max(x),
                    None => return Keys::Sparse,
                }
            }
        }
        let radix = u128::from(d) + 1;
        let mut strides = Vec::with_capacity(self.names.len());
        let mut s: u128 = 1;
        for _ in 0..self.names.len() {
            strides.push(s);
            match s.checked_mul(radix) {
                Some(n) => s = n,
                None => return Keys::Sparse,
            }
        }
        Keys::Packed(Packing { radix, strides })
    }

    /// The normal forms of `roots`, with `reach` the nodes they reach. Each node is expanded
    /// once, from its children's forms, and a form is dropped after its last use. Each
    /// operation is charged to `budget` before it runs; `Err` of the node whose operation would
    /// pass it.
    fn expand<K: Key>(
        &self,
        ctx: &Packing,
        reach: &[bool],
        roots: &[usize],
        budget: &mut Budget,
    ) -> Result<Vec<Poly<K>>, usize> {
        let mut uses = vec![0usize; self.nodes.len()];
        for (i, n) in self.nodes.iter().enumerate() {
            if !reach[i] {
                continue;
            }
            match n {
                Node::Const(..) | Node::Leaf(_) => {}
                Node::Neg(a) | Node::Pow(a, _) => uses[*a] += 1,
                Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
                    uses[*a] += 1;
                    uses[*b] += 1;
                }
            }
        }
        for &s in roots {
            uses[s] += 1;
        }
        // A sum or difference read only by one other sum or difference is inside a chain: it
        // is not formed, and the chain's top node adds up the chain's summands at once
        // ([`Poly::sum`]). A root is read by the caller too, so it is never inside a chain.
        //
        // Complexity tradeoff: the naive expansion forms every node, so a sum written
        // `x0 + x1 + … + xn`, a left-deep chain, forms the partial sums of 2, 3, …, n terms,
        // O(n^2) term copies: `(x0 + … + x4095) * (y + z)` took 3.6 s and was refused by
        // [`LIMIT`]. Read as one sum of its k summands of T terms in all, the chain costs
        // O(T log k) term reads (O(T + k log k) when one summand dominates), whatever the
        // shape it was written in. Nothing is given up: the sum is the same polynomial, and a
        // partial sum that is also read elsewhere (a `let`) is formed as before. Tested by
        // `l03_09_egraph::scaling::a_written_chain_of_n_names_times_a_sum` (COMPLEXITY.md
        // POLY-sum-chain-fold).
        let mut inner = vec![false; self.nodes.len()];
        for (i, n) in self.nodes.iter().enumerate() {
            if let (true, Node::Add(a, b) | Node::Sub(a, b)) = (reach[i], n) {
                for c in [*a, *b] {
                    if uses[c] == 1 && matches!(self.nodes[c], Node::Add(..) | Node::Sub(..)) {
                        inner[c] = true;
                    }
                }
            }
        }
        let mut forms: Vec<Option<Poly<K>>> = (0..self.nodes.len()).map(|_| None).collect();
        // The forms each node reads, with whether each is subtracted: a chain's summands, or
        // an operation's operands.
        let mut read: Vec<(usize, bool)> = Vec::new();
        let mut stack: Vec<(usize, bool)> = Vec::new();
        for (i, n) in self.nodes.iter().enumerate() {
            if !reach[i] || inner[i] {
                continue;
            }
            read.clear();
            match n {
                Node::Const(..) | Node::Leaf(_) => {}
                Node::Neg(a) | Node::Pow(a, _) => read.push((*a, false)),
                Node::Mul(a, b) => read.extend([(*a, false), (*b, false)]),
                Node::Add(..) | Node::Sub(..) => {
                    // The summands left to right, by an explicit stack: a chain is as deep as
                    // it is long.
                    stack.push((i, false));
                    while let Some((j, minus)) = stack.pop() {
                        match &self.nodes[j] {
                            Node::Add(a, b) if j == i || inner[j] => {
                                stack.extend([(*b, minus), (*a, minus)]);
                            }
                            Node::Sub(a, b) if j == i || inner[j] => {
                                stack.extend([(*b, !minus), (*a, minus)]);
                            }
                            _ => read.push((j, minus)),
                        }
                    }
                }
            }
            let f = {
                let form = |j: usize| forms[j].as_ref().expect("a child expanded first");
                match n {
                    Node::Const(a, b) => Some(Poly::constant(a.clone(), b.clone())),
                    Node::Leaf(l) => Some(Poly::monomial(K::leaf(ctx, *l))),
                    Node::Add(..) | Node::Sub(..) => {
                        let parts: Vec<(&Poly<K>, bool)> =
                            read.iter().map(|&(j, minus)| (form(j), minus)).collect();
                        Poly::sum(&parts, budget)
                    }
                    Node::Neg(a) => form(*a).neg(budget),
                    Node::Mul(a, b) => form(*a).mul(form(*b), budget),
                    Node::Pow(a, e) => form(*a).pow(e, budget),
                }
                .ok_or(i)?
            };
            for &(c, _) in &read {
                uses[c] -= 1;
                if uses[c] == 0 {
                    forms[c] = None;
                }
            }
            forms[i] = Some(f);
        }
        // A root named twice (both sides one node) is copied for all but its last naming.
        Ok(roots
            .iter()
            .map(|&s| {
                uses[s] -= 1;
                let f = &mut forms[s];
                if uses[s] == 0 {
                    f.take().expect("a root expanded")
                } else {
                    f.clone().expect("a root expanded")
                }
            })
            .collect())
    }

    /// A witness of small integers from `diff`, the difference of the normal forms, not zero:
    /// each binder in turn takes the first of `0, 1, -1, …` that leaves the difference, with
    /// the earlier binders at their values, a nonzero polynomial modulo `P` in the later ones.
    /// `None` only when every value leaves it zero, which needs an exponent of `P` or more
    /// (`x ^ (2^61 - 1) - x` is zero at every point modulo `P`).
    ///
    /// Each exponent `e >= P` of the binder is read as `1 + (e - 1) mod (P - 1)`, which has the
    /// same value at every point modulo `P` (Fermat), so the difference has degree below `P` in
    /// the binder: when it is then zero, `None` is returned at once, and otherwise one of its
    /// first `d + 1` values leaves it nonzero, `d` that reduced degree.
    ///
    /// Complexity tradeoff: a difference that is zero at every point modulo `P` has no witness
    /// found here, and is then [`Verdict::Differs`]; finding one would need arithmetic with
    /// numbers of `P` bits or a second prime. The cost is a pass over the terms per value
    /// tried, at most `d + 1` values a binder; without the reduction, `x ^ (2^61 - 1) - x`
    /// tried all `2^61 - 1` values. Reached only when both points agreed and the normal forms
    /// differ, a chance of at most `degree / P` for each point. Tested by
    /// `l03_09_egraph::witness` and `poly::tests::a_difference_zero_modulo_p_has_no_witness`
    /// (COMPLEXITY.md POLY-nf-wide-root).
    fn expanded_witness<K: Key>(&self, diff: &Poly<K>, ctx: &Packing) -> Option<Point> {
        // The numerators modulo P, after dividing out their content, so not all zero.
        let content = diff.terms.iter().fold(BigInt::zero(), |g, (_, c)| g.gcd(c));
        let mut cur: Vec<(K, u64)> = diff
            .terms
            .iter()
            .map(|(k, c)| (k.clone(), residue(&(c / &content))))
            .filter(|(_, c)| *c != 0)
            .collect();
        if cur.is_empty() {
            return None;
        }
        let mut found = Vec::with_capacity(self.binders);
        for b in 0..self.binders {
            let v = u32::try_from(b).expect("fewer than 2^32 binders");
            let mut reduced: HashMap<(K, u64), u64> = HashMap::new();
            for (k, c) in &cur {
                let (e, rest) = k.without(ctx, v);
                let e = if e < P { e } else { 1 + (e - 1) % (P - 1) };
                let s = reduced.entry((rest, e)).or_insert(0);
                *s = addmod(*s, *c);
            }
            let split: Vec<(K, u64, u64)> = reduced
                .into_iter()
                .filter(|(_, c)| *c != 0)
                .map(|((rest, e), c)| (rest, e, c))
                .collect();
            let tries = split.iter().map(|(_, e, _)| e + 1).max()?;
            let mut next = None;
            for i in 0..tries {
                let x = small(i);
                let xm = small_mod(x);
                let mut acc: HashMap<K, u64> = HashMap::new();
                for (rest, e, c) in &split {
                    let t = mulmod(*c, powmod(xm, &BigUint::from(*e)));
                    let s = acc.entry(rest.clone()).or_insert(0);
                    *s = addmod(*s, t);
                }
                let mut left: Vec<(K, u64)> = acc.into_iter().filter(|(_, c)| *c != 0).collect();
                if !left.is_empty() {
                    left.sort_by(|a, b| a.0.cmp(&b.0));
                    next = Some((x, left));
                    break;
                }
            }
            let (x, left) = next?;
            cur = left;
            found.push((self.names[b].clone(), BigInt::from(x)));
        }
        Some(Point(found))
    }

    /// `p` printed, the highest total degree first and then by the names' order.
    fn show<K: Key>(&self, p: &Poly<K>, ctx: &Packing) -> String {
        let mut terms: Vec<(Vec<(u32, u64)>, &BigInt)> = p
            .terms
            .iter()
            .map(|(k, c)| {
                let mut e = Vec::new();
                k.exponents(ctx, &mut e);
                (e, c)
            })
            .collect();
        let degree = |e: &[(u32, u64)]| e.iter().map(|(_, x)| u128::from(*x)).sum::<u128>();
        terms.sort_by(|(a, _), (b, _)| {
            degree(b).cmp(&degree(a)).then_with(|| {
                // Graded lexicographic: the larger exponent of the first name first.
                let dense = |e: &[(u32, u64)], v: u32| {
                    e.iter().find(|(w, _)| *w == v).map_or(0, |(_, x)| *x)
                };
                let mut names: Vec<u32> = a.iter().chain(b.iter()).map(|(v, _)| *v).collect();
                names.sort_unstable();
                names.dedup();
                names
                    .iter()
                    .map(|v| dense(b, *v).cmp(&dense(a, *v)))
                    .find(|o| o.is_ne())
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
        });
        if terms.is_empty() {
            return "0".to_string();
        }
        let mut out = String::new();
        for (i, (e, c)) in terms.iter().enumerate() {
            let neg = c.is_negative();
            match (i, neg) {
                (0, true) => out.push('-'),
                (0, false) => {}
                (_, true) => out.push_str(" - "),
                (_, false) => out.push_str(" + "),
            }
            let mag = BigInt::from_biguint(Sign::Plus, c.magnitude().clone());
            let g = mag.gcd(&p.den);
            let (n, d) = (&mag / &g, &p.den / &g);
            let mut parts: Vec<String> = Vec::new();
            if !(n.is_one() && d.is_one()) || e.is_empty() {
                parts.push(if d.is_one() {
                    n.to_string()
                } else {
                    format!("{n}/{d}")
                });
            }
            for (v, x) in e {
                let name = &self.names[*v as usize];
                parts.push(if *x == 1 {
                    name.to_string()
                } else {
                    format!("{name} ^ {x}")
                });
            }
            out.push_str(&parts.join(" * "));
        }
        out
    }
}

/// How the lowering reads a term.
enum Visit<'t> {
    /// A constant, lowered.
    Leaf(usize),
    /// A variable.
    Name(&'t str),
    /// Any other term: an atom named by its text.
    Atom,
    /// A ring operation on these operands.
    Op(Op, &'t [Term]),
    /// `name = e; body`.
    Let(&'t str, &'t Term, &'t Term),
}

/// The number `v` as a coefficient `num / den`: an integer at every carrier, a rational only at
/// `rat`; `None` for any other value, or a number whose digits the system will not build.
fn constant(v: &Value, carrier: Carrier) -> Option<(BigInt, BigInt)> {
    match v {
        Value::Int(n) => Some((BigInt::from(*n), BigInt::one())),
        Value::Big(r) => Some((r.to_integer().ok()?, BigInt::one())),
        Value::Rat(r) if carrier == Carrier::Rat => {
            let (n, d) = r.built_parts().ok()?;
            let sign = if r.is_negative() {
                Sign::Minus
            } else {
                Sign::Plus
            };
            Some((
                BigInt::from_biguint(sign, n.into_owned()),
                BigInt::from_biguint(Sign::Plus, d.into_owned()),
            ))
        }
        _ => None,
    }
}

/// A literal exponent: a nonnegative integer.
fn exponent(v: &Value) -> Option<BigUint> {
    match v {
        Value::Int(n) => u64::try_from(*n).ok().map(BigUint::from),
        Value::Big(r) => r.to_integer().ok()?.to_biguint(),
        _ => None,
    }
}

/// The most monomials `a ^ n` expands to when `a` has at most `t` monomials (`t >= 1`): the
/// number of ways to write `n` as a sum of `t` exponents, C(t + n - 1, k) for
/// `k = min(t - 1, n)`, or `u64::MAX` past it. Each step `i` multiplies by
/// `(t + n - 1 - k + i) / i`, at least 2, since `t + n - 1 - k = max(t - 1, n) >= k >= i`: so
/// at most 64 steps reach `u64::MAX`.
fn power_terms(t: u64, n: u64) -> u64 {
    let m = u128::from(t) + u128::from(n) - 1;
    let k = (t - 1).min(n);
    let mut r: u128 = 1;
    for i in 1..=u128::from(k) {
        // C(m - k + i, i) = C(m - k + i - 1, i - 1) * (m - k + i) / i, exact.
        r = match r.checked_mul(m - u128::from(k) + i) {
            Some(x) => x / i,
            None => return u64::MAX,
        };
        if r > u128::from(u64::MAX) {
            return u64::MAX;
        }
    }
    u64::try_from(r).expect("checked against u64::MAX")
}

/// The `i`-th of `0, 1, -1, 2, -2, …`.
fn small(i: u64) -> i128 {
    let h = i128::from(i.div_ceil(2));
    if i % 2 == 1 { h } else { -h }
}

/// `v` modulo `P`.
fn small_mod(v: i128) -> u64 {
    let p = i128::from(P);
    u64::try_from(v.rem_euclid(p)).expect("a residue is below P")
}

/// `a` modulo `P`, in `0..P`.
fn residue(a: &BigInt) -> u64 {
    a.mod_floor(&BigInt::from(P))
        .to_u64()
        .expect("a residue is below P")
}

fn addmod(a: u64, b: u64) -> u64 {
    let s = a + b;
    if s >= P { s - P } else { s }
}

/// `a * b` modulo `P = 2^61 - 1`: the 122-bit product folded once, since `2^61 = 1` modulo `P`.
fn mulmod(a: u64, b: u64) -> u64 {
    let x = u128::from(a) * u128::from(b);
    let lo = u64::try_from(x & u128::from(P)).expect("61 bits");
    let hi = u64::try_from(x >> 61).expect("61 bits");
    addmod(lo, hi)
}

/// `b ^ e` modulo `P`, with the exponent reduced modulo `P - 1` (Fermat) when `b` is not 0:
/// `O(log e)` for the reduction and 61 squarings.
fn powmod(b: u64, e: &BigUint) -> u64 {
    if e.is_zero() {
        return 1;
    }
    if b == 0 {
        return 0;
    }
    let mut e = (e % (P - 1)).to_u64().expect("below P - 1");
    let (mut b, mut r) = (b, 1);
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(r, b);
        }
        b = mulmod(b, b);
        e >>= 1;
    }
    r
}

/// Which keys an expansion uses.
enum Keys {
    Packed(Packing),
    Sparse,
}

/// The digits of a packed key: name `v` is the digit of weight `strides[v]`, of radix `radix`.
struct Packing {
    radix: u128,
    strides: Vec<u128>,
}

impl Packing {
    fn none() -> Packing {
        Packing {
            radix: 0,
            strides: Vec::new(),
        }
    }
}

/// A monomial: a product of names with their exponents.
trait Key: Clone + Ord + Hash + Eq {
    /// The charge for each term a sum or a negation reads: [`SUM_TERM`] for packed keys,
    /// [`SPARSE_TERM`] for keys that must be copied.
    const TERM: f64;
    /// The monomial 1.
    fn unit() -> Self;
    /// The name `v`.
    fn leaf(ctx: &Packing, v: u32) -> Self;
    /// The product of two monomials.
    fn times(&self, o: &Self) -> Self;
    /// The monomial to the power `n`.
    fn power(&self, n: u64) -> Self;
    /// The index of a packed key, which a product adds: Kronecker substitution.
    fn index(&self) -> Option<u128>;
    /// The packed key of index `i`.
    fn at(i: u128) -> Self;
    /// The names with nonzero exponents, in the names' order.
    fn exponents(&self, ctx: &Packing, out: &mut Vec<(u32, u64)>);
    /// The exponent of `v`, and the monomial without `v`.
    fn without(&self, ctx: &Packing, v: u32) -> (u64, Self);
}

impl Key for u128 {
    const TERM: f64 = SUM_TERM;

    fn unit() -> Self {
        0
    }
    fn leaf(ctx: &Packing, v: u32) -> Self {
        ctx.strides[v as usize]
    }
    fn times(&self, o: &Self) -> Self {
        self + o
    }
    fn power(&self, n: u64) -> Self {
        self * u128::from(n)
    }
    fn index(&self) -> Option<u128> {
        Some(*self)
    }
    fn at(i: u128) -> Self {
        i
    }
    fn exponents(&self, ctx: &Packing, out: &mut Vec<(u32, u64)>) {
        let mut k = *self;
        let mut v = 0u32;
        while k > 0 {
            let e = k % ctx.radix;
            if e > 0 {
                out.push((
                    v,
                    u64::try_from(e).expect("an exponent is at most the degree"),
                ));
            }
            k /= ctx.radix;
            v += 1;
        }
    }
    fn without(&self, ctx: &Packing, v: u32) -> (u64, Self) {
        let s = ctx.strides[v as usize];
        let e = (self / s) % ctx.radix;
        (
            u64::try_from(e).expect("an exponent is at most the degree"),
            self - e * s,
        )
    }
}

/// A monomial as its names and exponents, in the names' order, each exponent nonzero.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Sparse(Box<[(u32, u64)]>);

impl Key for Sparse {
    const TERM: f64 = SPARSE_TERM;

    fn unit() -> Self {
        Sparse(Box::default())
    }
    fn leaf(_: &Packing, v: u32) -> Self {
        Sparse(Box::new([(v, 1)]))
    }
    fn times(&self, o: &Self) -> Self {
        let (a, b) = (&self.0, &o.0);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() && j < b.len() {
            match a[i].0.cmp(&b[j].0) {
                std::cmp::Ordering::Less => {
                    out.push(a[i]);
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    out.push(b[j]);
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    // The shape check bounded every degree by `u64::MAX`.
                    out.push((a[i].0, a[i].1 + b[j].1));
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&a[i..]);
        out.extend_from_slice(&b[j..]);
        Sparse(out.into_boxed_slice())
    }
    fn power(&self, n: u64) -> Self {
        Sparse(self.0.iter().map(|(v, e)| (*v, e * n)).collect())
    }
    fn index(&self) -> Option<u128> {
        None
    }
    fn at(_: u128) -> Self {
        unreachable!("a sparse key has no index, so no dense product makes one")
    }
    fn exponents(&self, _: &Packing, out: &mut Vec<(u32, u64)>) {
        out.extend_from_slice(&self.0);
    }
    fn without(&self, _: &Packing, v: u32) -> (u64, Self) {
        match self.0.iter().position(|(w, _)| *w == v) {
            Some(i) => {
                let mut rest = self.0.to_vec();
                let (_, e) = rest.remove(i);
                (e, Sparse(rest.into_boxed_slice()))
            }
            None => (0, self.clone()),
        }
    }
}

/// A polynomial `sum c * m / den`: the terms in increasing order of their monomials, each `c`
/// nonzero, `den` positive and, past a product or sum, sharing no factor with every `c`.
#[derive(Clone, Debug)]
struct Poly<K> {
    den: BigInt,
    terms: Vec<(K, BigInt)>,
}

impl<K: Key> Poly<K> {
    fn constant(n: BigInt, d: BigInt) -> Poly<K> {
        let terms = if n.is_zero() {
            Vec::new()
        } else {
            vec![(K::unit(), n)]
        };
        Poly { den: d, terms }
    }

    fn monomial(k: K) -> Poly<K> {
        Poly {
            den: BigInt::one(),
            terms: vec![(k, BigInt::one())],
        }
    }

    /// `-self`, charged [`sum_charge`] to `budget`; `None` when that would pass it.
    fn neg(&self, budget: &mut Budget) -> Option<Poly<K>> {
        budget.spend(sum_charge(self))?;
        Some(Poly {
            den: self.den.clone(),
            terms: self.terms.iter().map(|(k, c)| (k.clone(), -c)).collect(),
        })
    }

    /// `self + o`, or `self - o` when `sub`: one merge of the two sorted lists, `O(t1 + t2)`
    /// coefficient operations, over a common denominator. Charged the operands' [`sum_charge`] to
    /// `budget`; `None` when that would pass it.
    fn add(&self, o: &Poly<K>, sub: bool, budget: &mut Budget) -> Option<Poly<K>> {
        budget.spend(sum_charge(self) + sum_charge(o))?;
        let same = self.den == o.den;
        let (den, fa, fb) = if same {
            (self.den.clone(), None, None)
        } else {
            let l = self.den.lcm(&o.den);
            let fa = &l / &self.den;
            let fb = &l / &o.den;
            (l, Some(fa), Some(fb))
        };
        let scale = |c: &BigInt, f: &Option<BigInt>| -> BigInt {
            match f {
                Some(f) => c * f,
                None => c.clone(),
            }
        };
        let flip = |c: BigInt| if sub { -c } else { c };
        let (a, b) = (&self.terms, &o.terms);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() || j < b.len() {
            let ord = match (a.get(i), b.get(j)) {
                (Some(x), Some(y)) => x.0.cmp(&y.0),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, _) => std::cmp::Ordering::Greater,
            };
            match ord {
                std::cmp::Ordering::Less => {
                    out.push((a[i].0.clone(), scale(&a[i].1, &fa)));
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    out.push((b[j].0.clone(), flip(scale(&b[j].1, &fb))));
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    let c = scale(&a[i].1, &fa) + flip(scale(&b[j].1, &fb));
                    if !c.is_zero() {
                        out.push((a[i].0.clone(), c));
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        Some(Poly { den, terms: out }.reduced())
    }

    /// The sum of `parts`, each subtracted when its flag is set, by merging the two with the
    /// fewest terms until one is left ([`Poly::add`], which charges `budget`); `None` when a
    /// charge would pass it. `parts` is not empty.
    ///
    /// Complexity tradeoff: the naive sum adds the parts one after another, O(T k) term reads
    /// for k parts of T terms in all, O(k^2) for a chain of k names. Merging balanced halves
    /// (the plan row's other option) reads O(T log k) terms, but reads a part of most of the
    /// terms at each of the log k levels. Merging the two smallest first is the optimal merge
    /// pattern of sorted lists (D. A. Huffman, "A method for the construction of
    /// minimum-redundancy codes", Proc. IRE 40(9), 1952; D. E. Knuth, The Art of Computer
    /// Programming vol. 3, section 5.4.9): it reads each term once per level of the merge tree
    /// it sits at, O(T log k) at most and O(T + k log k) for one large part and k small ones,
    /// plus O(k log k) for the heap. Sizes are counted in terms, not words, so a part of few
    /// wide coefficients may be merged later than its words would place it. The plan row's
    /// first option, one map of all the terms, would still sort its T terms at the end,
    /// O(T log T), and would need its own handling of the parts' denominators, which
    /// [`Poly::add`] already brings to their lcm. Measured on a chain of n names times
    /// `(y + z)`: 9.1 times the instructions and 8.6 times the bytes from n = 500 to 4000
    /// (n log n predicts 10.7), the same as a balanced sum of the same names.
    fn sum(parts: &[(&Poly<K>, bool)], budget: &mut Budget) -> Option<Poly<K>> {
        let mut slots: Vec<Option<(Cow<'_, Poly<K>>, bool)>> = parts
            .iter()
            .map(|&(p, minus)| Some((Cow::Borrowed(p), minus)))
            .collect();
        // Ties go to the earlier part, so the merge order, and so the charges, depend only on
        // the parts.
        let mut heap: BinaryHeap<Reverse<(usize, usize)>> = parts
            .iter()
            .enumerate()
            .map(|(i, (p, _))| Reverse((p.terms.len(), i)))
            .collect();
        loop {
            let Reverse((_, a)) = heap.pop().expect("a part to sum");
            let (pa, ma) = slots[a].take().expect("each slot is popped once");
            let Some(Reverse((_, b))) = heap.pop() else {
                return if ma {
                    pa.neg(budget)
                } else {
                    Some(pa.into_owned())
                };
            };
            let (pb, mb) = slots[b].take().expect("each slot is popped once");
            // `pa + pb` is `pa - pb` when their signs differ, and keeps `pa`'s sign.
            let s = pa.add(&pb, ma != mb, budget)?;
            heap.push(Reverse((s.terms.len(), a)));
            slots[a] = Some((Cow::Owned(s), ma));
        }
    }

    /// `self * o`, by the cheapest of three methods with the same result.
    ///
    /// Complexity tradeoff: nothing is given up; a crossing of methods with identical
    /// results, chosen from their cost formulas, not from timings. The sparse product forms
    /// all `t1 * t2` products and sorts them, `O(t1 t2 log(t1 t2))` coefficient products of
    /// `w1 * w2` words. The dense product packs each side into one integer, a slot of `b` bits
    /// a monomial index (Kronecker substitution: a packed key's index is linear in its
    /// exponents, and the degree bound leaves no carry between digits), and multiplies the two
    /// integers with `num::mul_int`, `O(L log L)` in their `L` words by the number-theoretic
    /// transform (BIGINT-fast-mul). The dense product is taken when its estimate,
    /// [`DENSE_COST`] + [`SLOT_COST`] per output slot + `num::mul_cost` of the packed integers, is
    /// at most the sparse product's, `t1 t2` times [`PAIR_COST`] + `num::mul_cost` of the
    /// coefficients ([`Choice`]); the three constants are fitted by `crossover poly-*` (QUESTIONS
    /// A96). The naive choice, `L log2 L` against `t1 t2 w1 w2` with unit constants, took the
    /// slower method by up to 9.6 times its instructions (univariate sums of one-word
    /// coefficients went sparse up to 45 terms each; the crossover is at 5); the fitted one by at most
    /// 1.09, and 1.30 on 8 terms of 8 to 1024 words. So a product whose monomials
    /// merge densely, as of two univariate sums, costs `O(n log n)` in its output, and one of
    /// sums in different names, whose `t1 * t2` products are all distinct, costs
    /// `O(t1 t2 log(t1 t2))`, near-linear in its output too. Between them, a product whose
    /// pairs fall on few indices spread over a long span, as `((x + y)^k + x)^2`, pays neither
    /// `t1 t2` nor its span with the support product ([`Poly::support_mul`]), `O(n log n)` in
    /// its output; it is tried first when its estimated cost is below both. Tested by
    /// `l03_09_egraph::scaling` (COMPLEXITY.md K107, Crossovers, POLY-nf-sparse-product).
    ///
    /// Charged to `budget`, in the units of [`LIMIT`]: [`SUPPORT`] times what the support
    /// product counted, which it bounds by the cheaper of the dense and the sparse cost and by
    /// what is left; and when it gives up, the chosen method's charge, before it runs: the dense
    /// cost, or [`Poly::sparse_charge`]. `None` when a charge would pass the budget.
    fn mul(&self, o: &Poly<K>, budget: &mut Budget) -> Option<Poly<K>> {
        let den = &self.den * &o.den;
        if self.terms.is_empty() || o.terms.is_empty() {
            return Some(Poly {
                den: BigInt::one(),
                terms: Vec::new(),
            });
        }
        let terms = match self.plan(o) {
            None => {
                budget.spend(self.sparse_charge(o))?;
                self.sparse_mul(o)
            }
            Some(plan) => {
                let cheaper = plan.dense.min(plan.sparse);
                let mut tried = 0.0;
                let bound = cheaper.min(budget.left() / SUPPORT);
                let support = self.support_mul(o, &plan, bound, &mut tried);
                budget.spend(tried * SUPPORT)?;
                match support {
                    Some(terms) => terms,
                    None => {
                        budget.spend(if plan.takes_dense {
                            plan.dense
                        } else {
                            self.sparse_charge(o)
                        })?;
                        if plan.takes_dense {
                            self.dense_mul(o, plan.slot, plan.step)
                        } else {
                            self.sparse_mul(o)
                        }
                    }
                }
            }
        };
        Some(Poly { den, terms }.reduced())
    }

    /// The cost of the sparse product with `o`: `t1 * t2` products of `w1 * w2` words, `w` the
    /// widest coefficient's words.
    fn sparse_cost(&self, o: &Poly<K>) -> f64 {
        let w = |p: &Poly<K>| {
            let bits = p.terms.iter().map(|(_, c)| c.bits()).max().unwrap_or(0);
            bits.div_ceil(64).max(1) as f64
        };
        self.terms.len() as f64 * o.terms.len() as f64 * w(self) * w(o)
    }

    /// The charge for the sparse product with `o`: [`PAIR`] plus `w1 * w2` for each of the
    /// `t1 * t2` pairs, in units of the dense product's ([`LIMIT`]): a pair's allocation, sorting
    /// and merge take about 8 of the dense product's units.
    fn sparse_charge(&self, o: &Poly<K>) -> f64 {
        let pairs = self.terms.len() as f64 * o.terms.len() as f64;
        pairs * PAIR + self.sparse_cost(o)
    }

    /// The costs of the dense and the sparse product with `o`, the dense product's slot width in
    /// 32-bit words, and the step between the indices that may hold a term: the greatest common
    /// divisor of every index's distance from its side's lowest. `None` for keys that are not
    /// packed, which only the sparse product takes. The costs are charges, in the units of
    /// [`LIMIT`]; which method to take is chosen apart from them, by [`Choice`], in the units of
    /// `num::mul_cost`.
    ///
    /// Complexity tradeoff: the naive dense product gives every index between the lowest and
    /// the highest a slot, but a homogeneous polynomial of degree `d` in `x` and `y` uses only
    /// every `radix - 1`-th index (`x^i y^(d-i)` is at `d radix - i (radix - 1)`), so its packed
    /// integer is `radix` times longer than its terms and the product of two such sums costs
    /// `O(radix t log(radix t))` for an output of `t` terms: superlinear in the output, since the
    /// radix grows with the degree. Dividing every distance by its greatest common divisor `g`
    /// removes those empty slots exactly, as the product's distances are sums of the sides'
    /// and so multiples of `g` too: one `O(t1 + t2)` pass of word-sized gcds per product, which
    /// the packing's own `O(t1 + t2)` pass already costs. Kept: a sum with empty indices that no
    /// common step removes (`x^5 y^2 + x y + 1`) still pays its span, unless the support product
    /// is cheaper.
    fn plan(&self, o: &Poly<K>) -> Option<Plan> {
        let (lo_a, hi_a) = (self.terms[0].0.index()?, self.terms.last()?.0.index()?);
        let (lo_b, hi_b) = (o.terms[0].0.index()?, o.terms.last()?.0.index()?);
        let mut step = 0u128;
        for (p, lo) in [(self, lo_a), (o, lo_b)] {
            for (k, _) in &p.terms {
                if step == 1 {
                    break;
                }
                step = step.gcd(&(k.index()? - lo));
            }
        }
        let step = step.max(1);
        let span = ((hi_a - lo_a) / step)
            .checked_add((hi_b - lo_b) / step)?
            .checked_add(1)?;
        let bits = |p: &Poly<K>| p.terms.iter().map(|(_, c)| c.bits()).max().unwrap_or(0);
        let (ta, tb) = (self.terms.len() as u64, o.terms.len() as u64);
        // |c| < 2^(ba + bb + bits(min(ta, tb))), and one bit more for the sign.
        let slot_bits = bits(self) + bits(o) + u64::from(64 - ta.min(tb).leading_zeros()) + 1;
        let slot_words = slot_bits.div_ceil(32);
        // The packed product's transforms, and the packing, setup and unpacking the choice
        // below counts, which a product of few terms spends mostly in (`(x + y) ^ 72 - x`
        // took 2.4 times its prediction without them).
        let dense = span
            .checked_mul(u128::from(slot_words))
            .map_or(f64::INFINITY, |w| ntt_cost(w as f64))
            + CHOICE_UNIT * (DENSE_COST + SLOT_COST * span as f64);
        let sparse = self.sparse_cost(o);
        let words =
            |p: &Poly<K>| usize::try_from(bits(p).div_ceil(64).max(1)).unwrap_or(usize::MAX);
        let packed = |hi: u128, lo: u128| {
            ((hi - lo) / step)
                .checked_add(1)
                .and_then(|n| n.checked_mul(u128::from(slot_words)))
                .and_then(|w| usize::try_from(w.div_ceil(2)).ok())
                .unwrap_or(usize::MAX)
        };
        // Complexity tradeoff: the choice was `dense <= sparse` on the charges above, both with
        // unit constants; the dense product's fixed cost and its packed product's method
        // (schoolbook, Toom or transform, as `num::mul` takes it) were not counted, so it took
        // the slower method by up to 9.6 times. This estimate costs two `num::mul_cost` calls,
        // `O(log L)` each, beside the `O(t1 + t2)` pass above; measured by `crossover poly-*`.
        let choice = Choice {
            pairs: ta as f64 * tb as f64,
            pair: mul_cost(words(self), words(o)),
            slots: span as f64,
            packed: mul_cost(packed(hi_a, lo_a), packed(hi_b, lo_b)),
        };
        Some(Plan {
            slot: slot_words,
            step,
            dense,
            sparse,
            takes_dense: choice.takes_dense(),
            choice,
        })
    }

    /// The sparse product: every pair's product, sorted by monomial and merged.
    fn sparse_mul(&self, o: &Poly<K>) -> Vec<(K, BigInt)> {
        let mut all: Vec<(K, BigInt)> = Vec::with_capacity(self.terms.len() * o.terms.len());
        for (ka, ca) in &self.terms {
            for (kb, cb) in &o.terms {
                all.push((ka.times(kb), mul_int(ca, cb)));
            }
        }
        all.sort_by(|a, b| a.0.cmp(&b.0));
        let mut out: Vec<(K, BigInt)> = Vec::with_capacity(all.len());
        for (k, c) in all {
            match out.last_mut() {
                Some((lk, lc)) if *lk == k => *lc += c,
                _ => out.push((k, c)),
            }
        }
        out.retain(|(_, c)| !c.is_zero());
        out
    }

    /// The dense product, `slot` 32-bit words for every `step`-th monomial index.
    fn dense_mul(&self, o: &Poly<K>, slot: u64, step: u128) -> Vec<(K, BigInt)> {
        let slot = usize::try_from(slot).expect("a slot fits in memory");
        let base_a = self.terms[0].0.index().expect("a packed key");
        let base_b = o.terms[0].0.index().expect("a packed key");
        let packed = |terms: &[(K, BigInt)], base: u128| {
            let at = |k: &K| usize::try_from((k.index().expect("packed") - base) / step);
            let len = at(&terms.last().expect("not empty").0).expect("fits in memory") + 1;
            pack(
                len,
                slot,
                terms
                    .iter()
                    .map(|(k, c)| (at(k).expect("fits in memory"), c)),
            )
        };
        let product = mul_int(&packed(&self.terms, base_a), &packed(&o.terms, base_b));
        let hi_a = self
            .terms
            .last()
            .expect("not empty")
            .0
            .index()
            .expect("packed");
        let hi_b = o
            .terms
            .last()
            .expect("not empty")
            .0
            .index()
            .expect("packed");
        let span = usize::try_from((hi_a - base_a) / step + (hi_b - base_b) / step + 1)
            .expect("fits in memory");
        let mut out = Vec::new();
        unpack(&product, slot, span, |j, c| {
            out.push((K::at(base_a + base_b + j as u128 * step), c));
        });
        out
    }

    /// The product with `o` from its support: the indices that some pair of terms reaches
    /// ([`sumset`]), then their coefficients ([`coefficients`]); `None` when its estimated cost
    /// is not below `budget`, the cheaper of the dense and the sparse product or less, or when
    /// the work runs past it. `spent` is its work, in the units of the other two's costs.
    ///
    /// Complexity tradeoff: the dense product pays the span between the lowest and the highest
    /// index, `O(L log L)` in `L` words, and the sparse one all `t1 t2` pairs, so a product
    /// whose pairs fall on `s` indices spread over a span much longer than `s`, far fewer than
    /// `t1 t2`, pays more than its output by either: `((x + y)^k + x)^2` has `3k + 3` terms of
    /// about `2k` bits, about `6 k^2` bits, against `k^3` words for the dense and `k^4 / 4096`
    /// word products for the sparse product. The support product (after Arnold and Roche,
    /// "Output-sensitive algorithms for sumset and sparse polynomial multiplication", ISSAC 2015)
    /// folds both sides modulo `z^p - 1` for a prime `p` near `s`, which maps index `i` to
    /// slot `i mod p`, and multiplies the folds densely: `O(s log s)` in `s` slots per round, with
    /// rounds of falling size, so `O(n log n)` in the output when the coefficients are not much
    /// wider than the output's. Its primes are drawn from the sides' content digest, so the work
    /// is the same on every run, and each step checks its results exactly: an index or a
    /// coefficient is taken only from a slot that provably holds that index alone, so a bad draw
    /// costs time, never a wrong term, and the budget bounds the time (at most twice the cheaper
    /// method's cost when the estimate is wrong).
    fn support_mul(
        &self,
        o: &Poly<K>,
        plan: &Plan,
        budget: f64,
        spent: &mut f64,
    ) -> Option<Vec<(K, BigInt)>> {
        let (a, b) = (&self.terms, &o.terms);
        let (ta, tb) = (a.len(), b.len());
        let lo = |t: &[(K, BigInt)]| t[0].0.index().expect("a packed key");
        let (lo_a, lo_b) = (lo(a), lo(b));
        let reduce = |t: &[(K, BigInt)], lo: u128| -> Vec<u128> {
            t.iter()
                .map(|(k, _)| (k.index().expect("packed") - lo) / plan.step)
                .collect()
        };
        let (ra, rb) = (reduce(a, lo_a), reduce(b, lo_b));
        let bits = |x: u128| u64::from(128 - x.leading_zeros());
        let pairs = ta as u128 * tb as u128;
        // Each of the nine moments `sum a^i b^j` (i, j < 3) of a slot is at most
        // `pairs * ha^2 * hb^2`.
        let sub = usize::try_from(
            (bits(pairs) + 2 * bits(*ra.last()?) + 2 * bits(*rb.last()?)).div_ceil(32),
        )
        .ok()?;
        // A slot of the coefficients' product is at most `sum |a_i| * sum |b_j|`, and one bit
        // more for the sign.
        let sum_bits = |t: &[(K, BigInt)]| {
            t.iter()
                .fold(BigUint::zero(), |s, (_, c)| s + c.magnitude())
                .bits()
        };
        let slot = usize::try_from((sum_bits(a) + sum_bits(b) + 1).div_ceil(32)).ok()?;
        let words = |t: &[(K, BigInt)]| -> f64 {
            t.iter()
                .map(|(_, c)| c.bits().div_ceil(64).max(1) as f64)
                .sum()
        };
        let folds = words(a) + words(b);
        let cost = |s: f64| {
            let p = 1.5 * s;
            2.0 * (sumset_round(p, sub, ta + tb) + coefficient_round(p, slot, folds))
        };
        let sampling = SAMPLES as f64 * (ta + tb) as f64;
        if sampling + cost((ta + tb - 1) as f64) >= budget {
            return None;
        }
        let mut rng = {
            let mut h = Digest::default();
            ra.hash(&mut h);
            rb.hash(&mut h);
            h.finish()
        };
        // Complexity tradeoff: the support's size `s` is not known before the sumset is found, and
        // the sumset of sides whose pairs are all distinct costs more than the sparse product of
        // the same sides. A mean of `1 / count` over `SAMPLES` pairs drawn at random, `count` the
        // number of pairs on the drawn pair's index, estimates `s / (t1 t2)` in
        // `O(SAMPLES (t1 + t2))`, so such a product goes to the sparse one at once.
        let mut inverse = 0.0;
        for _ in 0..SAMPLES {
            rng = step(rng, 1);
            let i = (rng % ta as u64) as usize;
            rng = step(rng, 2);
            let j = (rng % tb as u64) as usize;
            inverse += 1.0 / pairs_at(&ra, &rb, ra[i] + rb[j]) as f64;
        }
        let estimate = (pairs as f64 * inverse / SAMPLES as f64).max((ta + tb - 1) as f64);
        *spent = sampling;
        if *spent + cost(estimate) >= budget {
            return None;
        }
        let support = sumset(&ra, &rb, sub, estimate as u64, &mut rng, spent, budget)?;
        let coefficients = coefficients(
            [(&a[..], &ra[..]), (&b[..], &rb[..])],
            &support,
            slot,
            folds,
            &mut rng,
            spent,
            budget,
        )?;
        let base = lo_a + lo_b;
        Some(
            support
                .iter()
                .zip(coefficients)
                .filter(|(_, c)| !c.is_zero())
                .map(|(s, c)| (K::at(base + s * plan.step), c))
                .collect(),
        )
    }

    /// `self ^ e`: a monomial's power directly, otherwise by squaring with [`Poly::mul`], each
    /// product charged to `budget`; `None` when that would pass it. A monomial's power is
    /// charged the words its coefficient and denominator gain, `(bits - 1) n / 64` each and at
    /// least one: no more than the result's words, so a power of 1 costs 2 at any exponent.
    fn pow(&self, e: &BigUint, budget: &mut Budget) -> Option<Poly<K>> {
        if e.is_zero() {
            return Some(Poly::constant(BigInt::one(), BigInt::one()));
        }
        if self.terms.is_empty() {
            return Some(self.clone());
        }
        let Some(n) = e.to_u64() else {
            // The shape check refuses a wide exponent of anything but 0, 1 and -1.
            let (k, c) = &self.terms[0];
            let odd = e.bit(0);
            let c = if c.is_negative() && odd {
                -BigInt::one()
            } else {
                BigInt::one()
            };
            budget.spend(2.0)?;
            return Some(Poly {
                den: BigInt::one(),
                terms: vec![(k.clone(), c)],
            });
        };
        if let [(k, c)] = &self.terms[..] {
            let gain = |x: &BigInt| ((x.bits() - 1) as f64 * n as f64 / 64.0).ceil().max(1.0);
            budget.spend(gain(c) + gain(&self.den))?;
            let mag = pow_uint(c.magnitude(), n);
            let sign = if c.is_negative() && n % 2 == 1 {
                Sign::Minus
            } else {
                Sign::Plus
            };
            return Some(Poly {
                den: BigInt::from_biguint(Sign::Plus, pow_uint(self.den.magnitude(), n)),
                terms: vec![(k.power(n), BigInt::from_biguint(sign, mag))],
            });
        }
        let mut base = Cow::Borrowed(self);
        let mut acc: Option<Poly<K>> = None;
        let mut n = n;
        while n > 0 {
            if n & 1 == 1 {
                acc = Some(match acc {
                    None => base.as_ref().clone(),
                    Some(a) => a.mul(&base, budget)?,
                });
            }
            n >>= 1;
            if n > 0 {
                base = Cow::Owned(base.mul(&base, budget)?);
            }
        }
        Some(acc.expect("the exponent is not zero"))
    }

    /// The polynomial with `den` and the coefficients divided by their common factor.
    fn reduced(mut self) -> Poly<K> {
        if self.den.is_one() {
            return self;
        }
        if self.terms.is_empty() {
            self.den = BigInt::one();
            return self;
        }
        let mut g = self.den.clone();
        for (_, c) in &self.terms {
            if g.is_one() {
                return self;
            }
            g = g.gcd(c);
        }
        if g.is_one() {
            return self;
        }
        self.den /= &g;
        for (_, c) in &mut self.terms {
            *c /= &g;
        }
        self
    }
}

/// The costs of the dense and the sparse product of two sums of packed keys ([`Poly::plan`]).
struct Plan {
    /// The dense product's slot, in 32-bit words.
    slot: u64,
    /// The step between the indices that may hold a term.
    step: u128,
    /// The dense product's cost, infinite when its integer's length does not fit in a `u128`.
    dense: f64,
    /// The sparse product's cost.
    sparse: f64,
    /// Whether [`Poly::mul`] takes the dense product when the support product gives way.
    takes_dense: bool,
    /// The sizes that choice is made from.
    choice: Choice,
}

/// The sizes of a product that [`Poly::mul`] chooses the dense or the sparse product by, in
/// the units of `num::mul_cost` (one word product).
#[derive(Clone, Copy, Debug)]
struct Choice {
    /// The sparse product's pairs, `t1 t2`.
    pairs: f64,
    /// The cost of one pair's coefficient product, at the widest coefficients' words.
    pair: f64,
    /// The dense product's output slots, its span.
    slots: f64,
    /// The cost of the product of the two packed integers.
    packed: f64,
}

impl Choice {
    /// The dense product's estimated cost.
    fn dense(&self) -> f64 {
        DENSE_COST + SLOT_COST * self.slots + self.packed
    }

    /// The sparse product's estimated cost.
    fn sparse(&self) -> f64 {
        self.pairs * (PAIR_COST + self.pair)
    }

    /// Whether the dense product is estimated to cost no more than the sparse one.
    fn takes_dense(&self) -> bool {
        self.dense() <= self.sparse()
    }
}

/// The pairs drawn to estimate the size of a product's support ([`Poly::support_mul`]): the
/// estimate only chooses a method, so its error costs time, never a wrong term.
const SAMPLES: u32 = 32;

/// The primes tried for each round of [`coefficients`], the one that leaves the most indices alone
/// for its size taken.
const CANDIDATES: u32 = 4;

/// The product of `v`, 1 when it is empty.
///
/// Complexity tradeoff: multiplying in turn costs `O(m B)` word products for `m` numbers of
/// `B` words in all, the running product being up to `B` words long at each step; multiplying
/// pairs, then pairs of those, costs `O(M(B) log m)`, `M` the cost of one product of `B` words.
fn product(mut v: Vec<BigUint>) -> BigUint {
    while v.len() > 1 {
        let mut next = Vec::with_capacity(v.len().div_ceil(2));
        let mut it = v.into_iter();
        while let Some(a) = it.next() {
            next.push(match it.next() {
                Some(b) => mul_uint(&a, &b),
                None => a,
            });
        }
        v = next;
    }
    v.pop().unwrap_or_else(BigUint::one)
}

/// The cost of a product of `words` 32-bit words by the number-theoretic transform, in the
/// sparse product's unit of one word product: `w log2 w` in its `w` 64-bit words.
fn ntt_cost(words: f64) -> f64 {
    let w = words / 2.0;
    w * w.log2().max(1.0)
}

/// The cost of a round of [`sumset`] at a prime `p`, with `sub` words a moment and `terms`
/// terms in both sides.
fn sumset_round(p: f64, sub: usize, terms: usize) -> f64 {
    ntt_cost(2.0 * p * (9 * sub) as f64) + terms as f64
}

/// The cost of a round of [`coefficients`] at a prime `p`, with `slot` words a slot and `folds`
/// words in both sides' coefficients.
fn coefficient_round(p: f64, slot: usize, folds: f64) -> f64 {
    ntt_cost(2.0 * p * slot as f64) + folds
}

/// The number of pairs of `a` in `ra` and `b` in `rb`, both increasing, with `a + b == s`: one
/// merge of the two lists, `O(t1 + t2)`.
fn pairs_at(ra: &[u128], rb: &[u128], s: u128) -> u64 {
    let (mut i, mut j, mut n) = (0, rb.len(), 0);
    while i < ra.len() && j > 0 {
        match (ra[i] + rb[j - 1]).cmp(&s) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j -= 1,
            std::cmp::Ordering::Equal => {
                n += 1;
                i += 1;
                j -= 1;
            }
        }
    }
    n
}

/// The first prime at or past a point of `[lambda, 2 lambda)` drawn from `rng`, which advances.
fn draw_prime(lambda: u64, rng: &mut u64) -> u64 {
    let lo = lambda.max(2);
    *rng = step(*rng, 3);
    let mut p = lo + *rng % lo;
    while !is_prime(p) {
        p += 1;
    }
    p
}

/// Every `a + b`, `a` in `ra` and `b` in `rb`, in increasing order, each once, by rounds at a
/// prime `p` drawn from `lambda` on: each side folded modulo `z^p - 1` (index `i` to slot
/// `i mod p`) and the folds multiplied densely, `sub` words a moment; `None` once `spent` passes
/// `budget`.
///
/// One side is packed with sub-digits `1`, `a` and `a^2` at 0, 1 and 2 of its slot, the other
/// with `1`, `b` and `b^2` at 0, 3 and 6, so one product gives each slot's nine moments
/// `sum a^i b^j` over its pairs, at sub-digit `i + 3 j`, and from them its pairs' count `C`,
/// `W = sum (a + b)` and `Q = sum (a + b)^2`. Over the slot's distinct sums `s`, of `c_s` pairs
/// each, `C Q - W^2 = sum_(s < s') c_s c_s' (s - s')^2` (Lagrange's identity), zero exactly when
/// the slot holds one sum, `W / C`: so a sum is taken only when it is certain. A later round
/// subtracts the sums found from its slots, so it sees only the rest. The first prime is drawn
/// near `lambda`, the caller's estimate of the sums; the next near twice the slots left open,
/// at least twice the sums left, or near twice the last when a round found none, so the rounds
/// end however the primes fall.
fn sumset(
    ra: &[u128],
    rb: &[u128],
    sub: usize,
    mut lambda: u64,
    rng: &mut u64,
    spent: &mut f64,
    budget: f64,
) -> Option<Vec<u128>> {
    let mut found: Vec<(u128, u64)> = Vec::new();
    loop {
        let p = draw_prime(lambda, rng);
        *spent += sumset_round(p as f64, sub, ra.len() + rb.len());
        if *spent > budget {
            return None;
        }
        let n = usize::try_from(p).ok()?;
        let at = |i: u128| (i % u128::from(p)) as usize;
        let fold = |r: &[u128], sub_at: [usize; 3]| {
            let mut w = vec![0u32; n * 9 * sub];
            for &a in r {
                let slot = at(a) * 9 * sub;
                add_into(&mut w[slot + sub_at[0] * sub..], &[1]);
                add_into(&mut w[slot + sub_at[1] * sub..], &words(a));
                add_into(&mut w[slot + sub_at[2] * sub..], &square(a));
            }
            BigUint::new(w)
        };
        let product = mul_uint(&fold(ra, [0, 1, 2]), &fold(rb, [0, 3, 6])).to_u32_digits();
        let digit = |j: usize, k: usize| {
            let from = ((j * 9 + k) * sub).min(product.len());
            nat(&product[from..(from + sub).min(product.len())])
        };
        // Modulo `z^p - 1`, the product's slots `r` and `r + p` are one.
        let moment = |r: usize, k: usize| digit(r, k) + digit(r + n, k);
        let mut moments = vec![[BigUint::zero(), BigUint::zero(), BigUint::zero()]; n];
        for (r, m) in moments.iter_mut().enumerate() {
            let c = moment(r, 0);
            if !c.is_zero() {
                let w = moment(r, 1) + moment(r, 3);
                let q = moment(r, 2) + (moment(r, 4) << 1u32) + moment(r, 6);
                *m = [c, w, q];
            }
        }
        for &(s, c) in &found {
            let [mc, mw, mq] = &mut moments[at(s)];
            let (c, s) = (BigUint::from(c), BigUint::from(s));
            let cs = &c * &s;
            *mq -= &cs * &s;
            *mw -= cs;
            *mc -= c;
        }
        let (mut open, mut new) = (0u64, 0usize);
        for [c, w, q] in &moments {
            if c.is_zero() {
                continue;
            }
            if c * q == w * w {
                found.push(((w / c).to_u128()?, c.to_u64()?));
                new += 1;
            } else {
                open += 1;
            }
        }
        if open == 0 {
            break;
        }
        lambda = if new == 0 { 2 * lambda } else { 2 * open };
    }
    found.sort_unstable();
    Some(found.into_iter().map(|(s, _)| s).collect())
}

/// A side of a product: its terms and their indices, reduced.
type Side<'a, K> = (&'a [(K, BigInt)], &'a [u128]);

/// The coefficient of each index of `support` in the product of the two sides, each its terms
/// and their indices reduced as `support`'s, by rounds at a prime `p` near the number `u` of
/// indices left, the best of `CANDIDATES` drawn from `2u / 3` on: both sides'
/// coefficients folded modulo `z^p - 1`, `slot` words a slot, and the folds multiplied densely;
/// `folds` is the sides' coefficients' words, and `None` comes once `spent` passes `budget`.
///
/// A slot is the sum of the coefficients of the indices of `support` on it, as the product has no
/// other index. The coefficients found are subtracted from it, and a slot with one index left
/// gives that index's coefficient exactly. When no candidate leaves an index alone, the next
/// candidates are drawn from twice as far on, so the rounds end however the primes fall.
fn coefficients<K>(
    sides: [Side<K>; 2],
    support: &[u128],
    slot: usize,
    folds: f64,
    rng: &mut u64,
    spent: &mut f64,
    budget: f64,
) -> Option<Vec<BigInt>> {
    let mut found = vec![BigInt::zero(); support.len()];
    let mut open: Vec<usize> = (0..support.len()).collect();
    let mut done: Vec<usize> = Vec::with_capacity(support.len());
    let mut lambda = (2 * open.len() as u64).div_ceil(3);
    let mut count = Vec::new();
    while !open.is_empty() {
        // Complexity tradeoff: a prime drawn at random leaves about `e^(-u/p)` of the `u`
        // indices left alone in their slots, so a prime near `u` is cheapest over all rounds
        // (`p e^(u/p)`, least at `p = u`), but a support of a few arithmetic progressions with one
        // difference, as `((x + y)^k + x)^2`'s, either misses itself modulo `p` or overlaps
        // nearly whole, and a round that overlaps leaves half. The support is known here, so each
        // of `CANDIDATES` primes is tried by counting its lone indices, `O(u + p)`, far below the
        // `O(p slot log(p slot))` product, and the one with the most for its size is taken.
        let mut best = (0.0, 0);
        for _ in 0..CANDIDATES {
            let p = draw_prime(lambda, rng);
            let score = lone(&open, support, p, &mut count) as f64 / p as f64;
            if score > best.0 {
                best = (score, p);
            }
        }
        *spent += (CANDIDATES as usize * open.len()) as f64;
        let p = best.1;
        if p == 0 {
            lambda *= 2;
            continue;
        }
        *spent += coefficient_round(p as f64, slot, folds);
        if *spent > budget {
            return None;
        }
        lone(&open, support, p, &mut count);
        let n = usize::try_from(p).ok()?;
        let at = |i: u128| (i % u128::from(p)) as usize;
        let [fa, fb] = sides.map(|(terms, r)| {
            let mut fold = vec![BigInt::zero(); n];
            for ((_, c), &i) in terms.iter().zip(r) {
                fold[at(i)] += c;
            }
            pack(n, slot, fold.iter().enumerate())
        });
        let mut slots = vec![BigInt::zero(); n];
        unpack(&mul_int(&fa, &fb), slot, 2 * n - 1, |j, c| {
            slots[j % n] += c
        });
        for &u in &done {
            let r = at(support[u]);
            if count[r] == 1 {
                slots[r] -= &found[u];
            }
        }
        open.retain(|&u| {
            let r = at(support[u]);
            if count[r] != 1 {
                return true;
            }
            found[u] = std::mem::take(&mut slots[r]);
            done.push(u);
            false
        });
        lambda = (2 * open.len() as u64).div_ceil(3);
    }
    Some(found)
}

/// The number of indices of `open`, positions in `support`, alone in their slot modulo `p`, with
/// `count` left holding each slot's number of them.
fn lone(open: &[usize], support: &[u128], p: u64, count: &mut Vec<u32>) -> usize {
    let at = |u: usize| (support[u] % u128::from(p)) as usize;
    count.clear();
    count.resize(usize::try_from(p).expect("a prime that fits in memory"), 0);
    for &u in open {
        count[at(u)] += 1;
    }
    open.iter().filter(|&&u| count[at(u)] == 1).count()
}

/// The values as one integer, `sum c * 2^(32 slot i)` over the pairs `(i, c)`, `i < len` and
/// `|c| < 2^(32 slot)`: the positive and the negative values written into two digit vectors and
/// subtracted, linear in the words.
fn pack<'a>(
    len: usize,
    slot: usize,
    values: impl IntoIterator<Item = (usize, &'a BigInt)>,
) -> BigInt {
    let len = len * slot;
    let (mut pos, mut neg) = (vec![0u32; len], Vec::new());
    for (i, c) in values {
        let into = if c.is_negative() {
            if neg.is_empty() {
                neg = vec![0u32; len];
            }
            &mut neg
        } else {
            &mut pos
        };
        for (w, d) in into[i * slot..]
            .iter_mut()
            .zip(c.magnitude().iter_u32_digits())
        {
            *w = d;
        }
    }
    let p = BigInt::from_biguint(Sign::Plus, BigUint::new(pos));
    if neg.is_empty() {
        p
    } else {
        p - BigInt::from_biguint(Sign::Plus, BigUint::new(neg))
    }
}

/// `f(j, c)` for each slot `j < len` of `product`, `slot` 32-bit words each, whose value `c` is
/// not zero, every value below `2^(32 slot - 1)` in magnitude: a negative value is its two's
/// complement in its slot, with a borrow from the next.
fn unpack(product: &BigInt, slot: usize, len: usize, mut f: impl FnMut(usize, BigInt)) {
    let negative = product.is_negative();
    let words = product.magnitude().to_u32_digits();
    let half = BigUint::one() << (slot * 32 - 1);
    let full = BigUint::one() << (slot * 32);
    let mut carry = false;
    for j in 0..len {
        let from = (j * slot).min(words.len());
        let to = ((j + 1) * slot).min(words.len());
        let digits = &words[from..to];
        if !carry && digits.iter().all(|w| *w == 0) {
            continue;
        }
        let mut v = BigUint::from_slice(digits);
        if carry {
            v += 1u32;
        }
        let c = if v >= half {
            carry = true;
            BigInt::from_biguint(Sign::Minus, &full - v)
        } else {
            carry = false;
            BigInt::from_biguint(Sign::Plus, v)
        };
        if !c.is_zero() {
            f(j, if negative { -c } else { c });
        }
    }
}

/// The natural number of the 32-bit `digits`, least first, with no allocation when it is zero.
fn nat(digits: &[u32]) -> BigUint {
    if digits.iter().all(|d| *d == 0) {
        BigUint::zero()
    } else {
        BigUint::from_slice(digits)
    }
}

/// `w += v`, both 32-bit digits, least first; the caller leaves room for the carry.
fn add_into(w: &mut [u32], v: &[u32]) {
    let len = v.iter().rposition(|d| *d != 0).map_or(0, |i| i + 1);
    let mut carry = 0u64;
    for (x, d) in w.iter_mut().zip(&v[..len]) {
        let s = u64::from(*x) + u64::from(*d) + carry;
        *x = s as u32;
        carry = s >> 32;
    }
    let mut i = len;
    while carry != 0 {
        let s = u64::from(w[i]) + carry;
        w[i] = s as u32;
        carry = s >> 32;
        i += 1;
    }
}

/// The 32-bit digits of `a`, least first.
fn words(a: u128) -> [u32; 4] {
    std::array::from_fn(|i| (a >> (32 * i)) as u32)
}

/// The 32-bit digits of `a^2`, least first: `a = h 2^64 + l` gives
/// `a^2 = h^2 2^128 + 2 h l 2^64 + l^2`, with no allocation.
fn square(a: u128) -> [u32; 8] {
    let m = u128::from(u64::MAX);
    let (h, l) = (a >> 64, a & m);
    let (ll, hl, hh) = (l * l, h * l, h * h);
    let t1 = (ll >> 64) + 2 * (hl & m);
    let t2 = (t1 >> 64) + 2 * (hl >> 64) + (hh & m);
    let t3 = (t2 >> 64) + (hh >> 64);
    let limbs = [ll & m, t1 & m, t2 & m, t3];
    std::array::from_fn(|i| (limbs[i / 2] >> (32 * (i % 2))) as u32)
}

/// The dense and the sparse product of `Poly::mul`, one by one, for the crossover benchmarks
/// (crate zed-benches, binary `crossover`; DESIGN.md sec:plan, QUESTIONS A96), which time both
/// on both sides of the change of method and check that they give the same output. Not for
/// other use: each function forces one method whatever the sizes.
#[doc(hidden)]
pub mod crossover {
    use num_bigint::BigInt;
    use num_traits::{One, Zero};

    use super::Poly;

    /// `super::PAIR_COST` as built.
    pub const PAIR_COST: f64 = super::PAIR_COST;

    /// `super::SLOT_COST` as built.
    pub const SLOT_COST: f64 = super::SLOT_COST;

    /// `super::DENSE_COST` as built.
    pub const DENSE_COST: f64 = super::DENSE_COST;

    /// A polynomial of packed monomials with denominator 1, as `Poly::mul` multiplies them.
    #[derive(Clone, Debug)]
    pub struct Sum(Poly<u128>);

    impl Sum {
        /// The sum of `terms`, each a monomial's packed index and its coefficient, in any order;
        /// like indices are merged and zero coefficients dropped.
        pub fn new(mut terms: Vec<(u128, BigInt)>) -> Sum {
            terms.sort_by_key(|(k, _)| *k);
            let mut merged: Vec<(u128, BigInt)> = Vec::with_capacity(terms.len());
            for (k, c) in terms {
                match merged.last_mut() {
                    Some((lk, lc)) if *lk == k => *lc += c,
                    _ => merged.push((k, c)),
                }
            }
            merged.retain(|(_, c)| !c.is_zero());
            Sum(Poly {
                den: BigInt::one(),
                terms: merged,
            })
        }

        /// Its number of terms.
        pub fn len(&self) -> usize {
            self.0.terms.len()
        }

        /// Whether it has no terms.
        pub fn is_empty(&self) -> bool {
            self.0.terms.is_empty()
        }
    }

    /// `a * b` by the dense product, at the slot and step `Poly::plan` gives.
    pub fn dense(a: &Sum, b: &Sum) -> Vec<(u128, BigInt)> {
        let plan = a.0.plan(&b.0).expect("packed keys");
        a.0.dense_mul(&b.0, plan.slot, plan.step)
    }

    /// `a * b` by the sparse product.
    pub fn sparse(a: &Sum, b: &Sum) -> Vec<(u128, BigInt)> {
        a.0.sparse_mul(&b.0)
    }

    /// Whether `Poly::mul` takes the dense product for `a * b` when the support product gives
    /// way.
    pub fn takes_dense(a: &Sum, b: &Sum) -> bool {
        let plan = a.0.plan(&b.0).expect("packed keys");
        plan.takes_dense
    }

    /// The value of `super::PAIR_COST` at which `Poly::mul` changes method for `a * b`: the
    /// dense product at or above it, the sparse one below.
    pub fn pair_flip(a: &Sum, b: &Sum) -> Option<f64> {
        let c = a.0.plan(&b.0).expect("packed keys").choice;
        Some(c.dense() / c.pairs - c.pair)
    }

    /// The value of `super::SLOT_COST` at which `Poly::mul` changes method for `a * b`: the
    /// dense product at or below it, the sparse one above.
    pub fn slot_flip(a: &Sum, b: &Sum) -> Option<f64> {
        let c = a.0.plan(&b.0).expect("packed keys").choice;
        Some((c.sparse() - c.dense()) / c.slots + super::SLOT_COST)
    }

    /// The value of `super::DENSE_COST` at which `Poly::mul` changes method for `a * b`: the
    /// dense product at or below it, the sparse one above.
    pub fn fixed_flip(a: &Sum, b: &Sum) -> Option<f64> {
        let c = a.0.plan(&b.0).expect("packed keys").choice;
        Some(c.sparse() - c.dense() + super::DENSE_COST)
    }
}

#[cfg(test)]
mod tests;

pub mod roots;
