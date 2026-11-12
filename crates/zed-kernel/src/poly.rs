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
//! A product of four or more sums over two or more names is refused ([`Refusal`]), counting
//! `s ^ n` as `n` sums and a sum inside a factor as one more sum of the product: the expansion
//! of `s` sums of `t` terms has up to `t^s` monomials. The refusal is the written shape of the
//! product, never the number of terms (see `REFUSED_SUMS`).

use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::digest::{Digest, step};
use crate::num::{mul_int, pow_uint};
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

/// The fewest sums, counted with the exponents of their powers, of a product over two or more
/// names that is refused.
///
/// Complexity tradeoff: what is given up is every identity with a product of four or more sums
/// over two or more names (`(a + b) * (c + d) * (e + f) * (g + h)`, `(x + y) ^ 4`), refused
/// with [`Refusal`]: an error naming the product, with a written proof (rung 8) in its menu and
/// the note that every point agreed; a false one is still refuted at a point first. Why: the
/// expansion of a product of `s` sums of `t` terms has up to `t^s` monomials, exponential in
/// the written `s`, and deciding polynomial identities of formulas in deterministic polynomial
/// time is an open problem (polynomial identity testing), so some written shape must be
/// refused. The count is a property of the written product, never of the number of terms; a
/// product whose sums are all in one name is never refused, since its expansion has at most
/// its degree plus one terms. Four is one above the most the corpus's obligations need: the
/// measurement (`l00_poly_nf::measure`, COMPLEXITY.md POLY-nf-sums) found at most three, in
/// `(a + b) ^ 3`, over the spec's laws and the associativity and commutativity obligations of
/// the studies' reducers, and the plan's row needs `(a + b) * (c + d) * (e + f)`. Tested by
/// `l00_poly_nf::refusal`. A complete solution would decide identity of arithmetic formulas
/// deterministically in polynomial time, which no known algorithm does.
pub const REFUSED_SUMS: u64 = 4;

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
    /// A product of a refused written shape.
    Refused(Refusal),
}

/// The decision on an identity, and the measures of its normal forms.
#[derive(Clone, Debug)]
pub struct Decision {
    /// The verdict.
    pub verdict: Verdict,
    /// The most sums any product multiplies, counted as [`REFUSED_SUMS`] counts them.
    pub sums: u64,
    /// The total degree of the two sides, at most; `None` past `u64::MAX`.
    pub degree: Option<u64>,
    /// The number of terms of each side's normal form, when they were expanded.
    pub terms: Option<[usize; 2]>,
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
    /// It multiplies this many sums over two or more names, at least [`REFUSED_SUMS`].
    Sums(u64),
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
    /// notes, and the repair, a written proof of `law`, the law's text without its `;`.
    pub fn message(&self, law: &str) -> String {
        let mut out = match &self.why {
            Refused::Sums(n) => format!(
                "Cannot expand `{}`: it multiplies {n} sums of more than one name.",
                self.product
            ),
            Refused::Exponent => format!(
                "Cannot expand `{}`: an exponent is above {}.",
                self.product,
                u64::MAX
            ),
        };
        match &self.why {
            Refused::Sums(_) => out.push_str(&format!(
                "\n  note: a product of {REFUSED_SUMS} or more sums is expanded only when its sums are all in one name, as `(1 + x) ^ 2 * (1 + x ^ 2) ^ 2`."
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
    if let Some(r) = id.refusal(Vec::new()) {
        return Err(r);
    }
    let reach = id.reachable();
    Ok(match id.keys(&reach) {
        Keys::Packed(ctx) => id.show(&id.expand::<u128>(&ctx, &reach)[0], &ctx),
        Keys::Sparse => id.show(
            &id.expand::<Sparse>(&Packing::none(), &reach)[0],
            &Packing::none(),
        ),
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

/// Which names a subterm holds: none, one, or more than one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Names {
    None,
    One(u32),
    Many,
}

impl Names {
    fn join(self, o: Names) -> Names {
        match (self, o) {
            (Names::None, x) | (x, Names::None) => x,
            (Names::One(a), Names::One(b)) if a == b => Names::One(a),
            _ => Names::Many,
        }
    }
}

/// The written shape of a node: its total degree at most (`None` past `u64::MAX`), the sums
/// it multiplies, and the names of the whole node and of the sums it multiplies.
#[derive(Clone, Copy, Debug)]
struct Shape {
    degree: Option<u64>,
    sums: u64,
    names: Names,
    sum_names: Names,
}

/// The two sides of an identity, lowered.
struct Identity<'t> {
    nodes: Vec<Node>,
    /// The term each `Mul` and `Pow` node was lowered from, to name a refused product.
    origin: Vec<Option<&'t Term>>,
    /// The names of the leaves: the binders first, then the atoms' texts.
    names: Vec<Arc<str>>,
    binders: usize,
    sides: [usize; 2],
    carrier: Carrier,
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
                                Some(&i) => i,
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
                            work.push(Work::Unbind(name));
                            work.push(Work::Visit(body));
                            work.push(Work::Bind(name));
                            work.push(Work::Visit(e));
                        }
                    },
                    Work::Build(op, t) => {
                        let b = done.pop().expect("an operand lowered");
                        let at = match op {
                            Op::Neg => id.push(Node::Neg(b), None),
                            Op::Pow(n) => id.push(Node::Pow(b, n), Some(t)),
                            Op::Scale(n, d) => {
                                let c = id.push(Node::Const(n, d), None);
                                id.push(Node::Mul(b, c), Some(t))
                            }
                            Op::Add | Op::Sub | Op::Mul => {
                                let a = done.pop().expect("two operands lowered");
                                match op {
                                    Op::Add => id.push(Node::Add(a, b), None),
                                    Op::Sub => id.push(Node::Sub(a, b), None),
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

    fn push(&mut self, n: Node, origin: Option<&'t Term>) -> usize {
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

    /// The nodes the two sides reach; a `let` whose value the body never reads is not.
    fn reachable(&self) -> Vec<bool> {
        let mut r = vec![false; self.nodes.len()];
        for s in self.sides {
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
                    names: Names::None,
                    sum_names: Names::None,
                },
                Node::Leaf(l) => Shape {
                    degree: Some(1),
                    sums: 0,
                    names: Names::One(*l),
                    sum_names: Names::None,
                },
                Node::Neg(a) => s[*a],
                Node::Add(a, b) | Node::Sub(a, b) => {
                    let (a, b) = (s[*a], s[*b]);
                    let names = a.names.join(b.names);
                    Shape {
                        degree: a.degree.zip(b.degree).map(|(x, y)| x.max(y)),
                        sums: a.sums.max(b.sums).max(1),
                        names,
                        sum_names: names,
                    }
                }
                Node::Mul(a, b) => {
                    let (a, b) = (s[*a], s[*b]);
                    Shape {
                        degree: a.degree.zip(b.degree).and_then(|(x, y)| x.checked_add(y)),
                        sums: a.sums.saturating_add(b.sums),
                        names: a.names.join(b.names),
                        sum_names: a.sum_names.join(b.sum_names),
                    }
                }
                Node::Pow(a, e) => {
                    let a = s[*a];
                    let e64 = e.to_u64();
                    Shape {
                        degree: match (a.degree, e64) {
                            (Some(0), _) => Some(0),
                            (Some(d), Some(e)) => d.checked_mul(e),
                            _ => None,
                        },
                        sums: match (a.sums, e64) {
                            (0, _) => 0,
                            (x, Some(e)) => x.saturating_mul(e),
                            (_, None) => u64::MAX,
                        },
                        names: a.names,
                        sum_names: a.sum_names,
                    }
                }
            };
            s.push(shape);
        }
        s
    }

    /// The first refused product the sides reach, in the order the nodes were built, so the
    /// smallest: with `agreed` the points that agreed.
    fn refusal(&self, agreed: Vec<Point>) -> Option<Refusal> {
        let shapes = self.shapes();
        let reach = self.reachable();
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
            let why = match n {
                Node::Pow(a, e) if e.to_u64().is_none() && !self.trivial_base(*a) => {
                    Some(Refused::Exponent)
                }
                Node::Mul(..) | Node::Pow(..) if shapes[i].degree.is_none() => {
                    Some(Refused::Exponent)
                }
                Node::Mul(..) | Node::Pow(..)
                    if shapes[i].sums >= REFUSED_SUMS && shapes[i].sum_names == Names::Many =>
                {
                    Some(Refused::Sums(shapes[i].sums))
                }
                _ => None,
            };
            if let Some(why) = why {
                let product = self.origin[i].map_or_else(String::new, |t| t.to_string());
                return Some(Refusal {
                    product,
                    why,
                    agreed,
                });
            }
        }
        None
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

    /// The decision: the points, then the refusal, then the expansion.
    fn decide(&self) -> Decision {
        let shapes = self.shapes();
        let reach = self.reachable();
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
        let decision = |verdict, terms| Decision {
            verdict,
            sums,
            degree,
            terms,
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
                    return decision(Verdict::Refuted(w), None);
                }
                Some(_) => return decision(Verdict::Differs, None),
            }
        }
        if let Some(r) = self.refusal(agreed) {
            return decision(Verdict::Refused(r), None);
        }
        match self.keys(&reach) {
            Keys::Packed(ctx) => self.compare::<u128>(&ctx, &reach, refutable, degree, decision),
            Keys::Sparse => {
                self.compare::<Sparse>(&Packing::none(), &reach, refutable, degree, decision)
            }
        }
    }

    /// The decision from the two normal forms with keys `K`.
    fn compare<K: Key>(
        &self,
        ctx: &Packing,
        reach: &[bool],
        refutable: bool,
        degree: Option<u64>,
        decision: impl Fn(Verdict, Option<[usize; 2]>) -> Decision,
    ) -> Decision {
        let [l, r] = self.expand::<K>(ctx, reach);
        let terms = Some([l.terms.len(), r.terms.len()]);
        let diff = l.add(&r, true);
        if diff.terms.is_empty() {
            return decision(Verdict::Proved, terms);
        }
        if !refutable {
            return decision(Verdict::Differs, terms);
        }
        match self.expanded_witness(&diff, ctx, degree) {
            Some(w) => decision(Verdict::Refuted(w), terms),
            None => decision(Verdict::Differs, terms),
        }
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
    /// small integer roots in it. Tested by `l00_poly_nf::witness` (COMPLEXITY.md K107).
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
    fn keys(&self, reach: &[bool]) -> Keys {
        // Every node the sides reach, not only the sides: `(x ^ 9) ^ 0` is of degree 0, and
        // `x ^ 9` is expanded on the way.
        let mut d = 0;
        for (s, r) in self.shapes().iter().zip(reach) {
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

    /// The normal forms of the two sides. Each node is expanded once, from its children's
    /// forms, and a form is dropped after its last use.
    fn expand<K: Key>(&self, ctx: &Packing, reach: &[bool]) -> [Poly<K>; 2] {
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
        for s in self.sides {
            uses[s] += 1;
        }
        let mut forms: Vec<Option<Poly<K>>> = (0..self.nodes.len()).map(|_| None).collect();
        for (i, n) in self.nodes.iter().enumerate() {
            if !reach[i] {
                continue;
            }
            let f = {
                let form = |j: usize| forms[j].as_ref().expect("a child expanded first");
                match n {
                    Node::Const(a, b) => Poly::constant(a.clone(), b.clone()),
                    Node::Leaf(l) => Poly::monomial(K::leaf(ctx, *l)),
                    Node::Add(a, b) => form(*a).add(form(*b), false),
                    Node::Sub(a, b) => form(*a).add(form(*b), true),
                    Node::Neg(a) => form(*a).neg(),
                    Node::Mul(a, b) => form(*a).mul(form(*b)),
                    Node::Pow(a, e) => form(*a).pow(e),
                }
            };
            let children: [Option<usize>; 2] = match n {
                Node::Const(..) | Node::Leaf(_) => [None, None],
                Node::Neg(a) | Node::Pow(a, _) => [Some(*a), None],
                Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => [Some(*a), Some(*b)],
            };
            for c in children.into_iter().flatten() {
                uses[c] -= 1;
                if uses[c] == 0 {
                    forms[c] = None;
                }
            }
            forms[i] = Some(f);
        }
        let [l, r] = self.sides;
        let lf = forms[l].take().expect("the left side expanded");
        let rf = if l == r {
            lf.clone()
        } else {
            forms[r].take().expect("the right side expanded")
        };
        [lf, rf]
    }

    /// A witness of small integers from `diff`, the difference of the normal forms, not zero:
    /// each binder in turn takes the first of `0, 1, -1, …` that leaves the difference, with
    /// the earlier binders at their values, a nonzero polynomial modulo `P` in the later ones.
    /// `None` only when every value leaves it zero, which needs an exponent of `P` or more
    /// (`x ^ (2^61 - 1) - x` is zero at every point modulo `P`).
    ///
    /// Complexity tradeoff: a difference of degree `P` or more in a binder may have no witness
    /// found here, and is then [`Verdict::Differs`]; finding one would need arithmetic with
    /// numbers of `P` bits or a second prime. The cost is a pass over the terms per value
    /// tried, at most `degree + 1` values a binder. Reached only when both points agreed and
    /// the normal forms differ, a chance of at most `degree / P` for each point. Tested by
    /// `l00_poly_nf::witness` (COMPLEXITY.md POLY-nf-wide-root).
    fn expanded_witness<K: Key>(
        &self,
        diff: &Poly<K>,
        ctx: &Packing,
        degree: Option<u64>,
    ) -> Option<Point> {
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
        let tries = degree.map_or(u64::MAX, |d| d.saturating_add(1)).min(P - 1);
        let mut found = Vec::with_capacity(self.binders);
        for b in 0..self.binders {
            let v = u32::try_from(b).expect("fewer than 2^32 binders");
            let mut next = None;
            for i in 0..tries {
                let x = small(i);
                let xm = small_mod(x);
                let mut acc: HashMap<K, u64> = HashMap::new();
                for (k, c) in &cur {
                    let (e, rest) = k.without(ctx, v);
                    let t = mulmod(*c, powmod(xm, &BigUint::from(e)));
                    let s = acc.entry(rest).or_insert(0);
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

    fn neg(&self) -> Poly<K> {
        Poly {
            den: self.den.clone(),
            terms: self.terms.iter().map(|(k, c)| (k.clone(), -c)).collect(),
        }
    }

    /// `self + o`, or `self - o` when `sub`: one merge of the two sorted lists, `O(t1 + t2)`
    /// coefficient operations, over a common denominator.
    fn add(&self, o: &Poly<K>, sub: bool) -> Poly<K> {
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
        Poly { den, terms: out }.reduced()
    }

    /// `self * o`, by the cheaper of two methods with the same result.
    ///
    /// Complexity tradeoff: nothing is given up; a crossing of two methods with identical
    /// results, chosen from their cost formulas, not from timings. The sparse product forms
    /// all `t1 * t2` products and sorts them, `O(t1 t2 log(t1 t2))` coefficient products of
    /// `w1 * w2` words. The dense product packs each side into one integer, a slot of `b` bits
    /// a monomial index (Kronecker substitution: a packed key's index is linear in its
    /// exponents, and the degree bound leaves no carry between digits), and multiplies the two
    /// integers with `num::mul_int`, `O(L log L)` in their `L` words by the number-theoretic
    /// transform (BIGINT-fast-mul). The dense product is taken when `L log2 L` is at most
    /// `t1 * t2 * w1 * w2`, both formulas with unit constants: so a product whose monomials
    /// merge densely, as of two univariate sums, costs `O(n log n)` in its output, and one of
    /// sums in different names, whose `t1 * t2` products are all distinct, costs
    /// `O(t1 t2 log(t1 t2))`, near-linear in its output too. Tested by
    /// `l00_poly_nf::scaling` (COMPLEXITY.md K107, Crossovers).
    fn mul(&self, o: &Poly<K>) -> Poly<K> {
        let den = &self.den * &o.den;
        if self.terms.is_empty() || o.terms.is_empty() {
            return Poly {
                den: BigInt::one(),
                terms: Vec::new(),
            };
        }
        let terms = match self.dense_cost(o) {
            Some(plan) => self.dense_mul(o, plan),
            None => self.sparse_mul(o),
        };
        Poly { den, terms }.reduced()
    }

    /// The slot width in 32-bit words of the dense product with `o`, when it is cheaper than
    /// the sparse one.
    fn dense_cost(&self, o: &Poly<K>) -> Option<u64> {
        let (lo_a, hi_a) = (self.terms[0].0.index()?, self.terms.last()?.0.index()?);
        let (lo_b, hi_b) = (o.terms[0].0.index()?, o.terms.last()?.0.index()?);
        let span = (hi_a - lo_a).checked_add(hi_b - lo_b)?.checked_add(1)?;
        let bits = |p: &Poly<K>| p.terms.iter().map(|(_, c)| c.bits()).max().unwrap_or(0);
        let (ta, tb) = (self.terms.len() as u64, o.terms.len() as u64);
        // |c| < 2^(ba + bb + bits(min(ta, tb))), and one bit more for the sign.
        let slot_bits = bits(self) + bits(o) + u64::from(64 - ta.min(tb).leading_zeros()) + 1;
        let slot_words = slot_bits.div_ceil(32);
        let words = span.checked_mul(u128::from(slot_words))? as f64 / 2.0;
        let dense = words * words.log2().max(1.0);
        let wa = bits(self).div_ceil(64).max(1) as f64;
        let wb = bits(o).div_ceil(64).max(1) as f64;
        let sparse = ta as f64 * tb as f64 * wa * wb;
        (dense <= sparse).then_some(slot_words)
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

    /// The dense product, `slot` 32-bit words a monomial index.
    fn dense_mul(&self, o: &Poly<K>, slot: u64) -> Vec<(K, BigInt)> {
        let slot = usize::try_from(slot).expect("a slot fits in memory");
        let base_a = self.terms[0].0.index().expect("a packed key");
        let base_b = o.terms[0].0.index().expect("a packed key");
        let product = mul_int(
            &pack(&self.terms, base_a, slot),
            &pack(&o.terms, base_b, slot),
        );
        let negative = product.is_negative();
        let words = product.magnitude().to_u32_digits();
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
        let span = usize::try_from(hi_a - base_a + hi_b - base_b + 1).expect("fits in memory");
        let half = BigUint::one() << (slot * 32 - 1);
        let full = BigUint::one() << (slot * 32);
        let mut out = Vec::new();
        let mut carry = false;
        for j in 0..span {
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
                let c = if negative { -c } else { c };
                out.push((K::at(base_a + base_b + j as u128), c));
            }
        }
        out
    }

    /// `self ^ e`: a monomial's power directly, otherwise by squaring with [`Poly::mul`].
    fn pow(&self, e: &BigUint) -> Poly<K> {
        if e.is_zero() {
            return Poly::constant(BigInt::one(), BigInt::one());
        }
        if self.terms.is_empty() {
            return self.clone();
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
            return Poly {
                den: BigInt::one(),
                terms: vec![(k.clone(), c)],
            };
        };
        if let [(k, c)] = &self.terms[..] {
            let mag = pow_uint(c.magnitude(), n);
            let sign = if c.is_negative() && n % 2 == 1 {
                Sign::Minus
            } else {
                Sign::Plus
            };
            return Poly {
                den: BigInt::from_biguint(Sign::Plus, pow_uint(self.den.magnitude(), n)),
                terms: vec![(k.power(n), BigInt::from_biguint(sign, mag))],
            };
        }
        let mut base = Cow::Borrowed(self);
        let mut acc: Option<Poly<K>> = None;
        let mut n = n;
        while n > 0 {
            if n & 1 == 1 {
                acc = Some(match acc {
                    None => base.as_ref().clone(),
                    Some(a) => a.mul(&base),
                });
            }
            n >>= 1;
            if n > 0 {
                base = Cow::Owned(base.mul(&base));
            }
        }
        acc.expect("the exponent is not zero")
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

/// The terms as one integer, `sum c * 2^(32 slot (index - base))`: the positive and the
/// negative coefficients written into two digit vectors and subtracted, linear in the words.
fn pack<K: Key>(terms: &[(K, BigInt)], base: u128, slot: usize) -> BigInt {
    let hi = terms.last().expect("not empty").0.index().expect("packed");
    let len = usize::try_from(hi - base + 1).expect("fits in memory") * slot;
    let (mut pos, mut neg) = (vec![0u32; len], Vec::new());
    for (k, c) in terms {
        let at = usize::try_from(k.index().expect("packed") - base).expect("fits") * slot;
        let digits = c.magnitude().to_u32_digits();
        let into = if c.is_negative() {
            if neg.is_empty() {
                neg = vec![0u32; len];
            }
            &mut neg
        } else {
            &mut pos
        };
        into[at..at + digits.len()].copy_from_slice(&digits);
    }
    let p = BigInt::from_biguint(Sign::Plus, BigUint::new(pos));
    if neg.is_empty() {
        p
    } else {
        p - BigInt::from_biguint(Sign::Plus, BigUint::new(neg))
    }
}

#[cfg(test)]
mod tests;
