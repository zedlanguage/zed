//! The one normal form of range bounds, sizes and costs (DESIGN.md step L1.17d, sec:domains
//! "One form for bounds, sizes and costs"; plan row KEPT-ast-normal-form): a sum
//! `c0 + c1 * m1 + ... + ck * mk` of distinct monomials with constant coefficients, read from a
//! Zed expression, ordered by Hardy's order per symbol, read exactly (ranges, sizes) or up to
//! dominance (costs, `O`), printed by one printer and lowered to one kernel term, so that equal
//! normal forms get one content address (step M0.7, through `zedc-zir`).
//!
//! It lives in the bootstrap checker until row KEPT-prelude-normal-form moves it into the
//! prelude as `boundNormalForm`. The constants are the kernel's kept values ([`Rat`], step
//! L1.17b): products, quotients and powers of them build nothing, and a sum of two of them is
//! added only by the sum rule ([`Rat::sum_folds`]), so normalizing never builds a wide sum.
//!
//! The pieces:
//! - [`Form`]: the map from each monomial to its coefficient, a sum of kept constants
//!   ([`Coef`]); the empty monomial holds `c0`. The map is keyed by the derived structural
//!   order, so equal normal forms are equal maps; [`Form::terms`] gives the printing order.
//! - [`Atom`]: a symbol (`n`, `xs::len`), an opaque call, `log(a)` (costs only), an exponential
//!   `q^m` over the joint coprime base, a held sum (a power of a sum not yet expanded), an
//!   irrational algebraic base `realRoot([c0, c1, ...], k)`, or an opaque power.
//! - The order: [`order`] (the total order that extends dominance) and [`dominated`].
//! - The readings: [`Form::big_o`] (costs: coefficients and dominated monomials dropped),
//!   [`work`] (a loop's trip count times its body, negative monomials dropped).
//! - Sizes: [`bits`] and [`digits`] of a kept constant, exact, with nothing built.
//! - [`read`] from Zed text, [`Form`]'s `Display` back to it, and [`Form::to_term`].

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};
use zed_kernel::num::TooLarge;
use zed_kernel::{Rat, Term, Value};
use zedc_syntax::ast::{BinaryOp, Expr, ExprKind, UnaryOp};

/// Which reading an expression has (DESIGN.md L1.17d, "Two readings"). A range bound and a
/// size are exact and have no `log`; a cost is an upper bound, where `log` is base 2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reading {
    /// A range bound or a size: one value at each value of its symbols.
    Exact,
    /// A cost: a quantity at most its value, with `log` in base 2.
    Cost,
}

/// The base of an exponential atom.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Base {
    /// An element of the joint coprime base of the expression's constants: a prime of one
    /// word, or a wide integer that is no perfect power, coprime to every other base.
    Int(BigUint),
    /// The real root of `c0 + c1 x + ...` numbered `k` from the least, counted from 0, which
    /// prints as `realRoot([c0, c1, ...], k)` (answer of 2026-11-24 in row KEPT-ast-normal-form).
    Root(Vec<BigInt>, u32),
}

/// An atom of a monomial (DESIGN.md L1.17d, "The normal form").
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Atom {
    /// A symbol: a parameter, a name a block binds, `xs::len`, `s::card`.
    Sym(Arc<str>),
    /// A call with its arguments in normal form, which the form does not look into.
    Call(Arc<str>, Vec<Form>),
    /// `log(a)` in a cost, base 2: of a symbol, a call, a held sum, or a constant atom such as
    /// `log(3)`, which is a constant.
    Log(Box<Form>),
    /// `q^m`, `m` a monomial with coefficient 1. Its power `c` in a monomial is `(q^m)^c`.
    Exp(Base, Mono),
    /// A sum held whole: its power in the monomial is a power of the sum not expanded until a
    /// question needs its monomials ([`Form::expanded`]), as `(n + 1)^(2^40)` is.
    Sum(Box<Form>),
    /// `a ^ b` that no rewrite reaches, such as `n ^ m` or `2 ^ (n / 2)`: opaque.
    Pow(Box<Form>, Box<Form>),
}

/// A monomial: atoms with nonzero integer exponents, by the structural order of atoms.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Mono(Vec<(Atom, BigInt)>);

/// A coefficient: nonzero kept constants that the sum rule does not add, by value. One summand
/// is the common case; `3^(2^40) + 1` keeps two.
pub type Coef = Vec<Rat>;

/// An expression in normal form: each monomial with its coefficient; the empty monomial holds
/// the constant `c0`. Zero is the empty map.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Form(BTreeMap<Mono, Coef>);

fn rint(n: impl Into<BigInt>) -> Rat {
    Rat::int(n.into())
}

/// `b ^ e` for an integer `e` of either sign, `b` not 0 when `e < 0`.
fn rpow(b: &Rat, e: &BigInt) -> Result<Option<Rat>, TooLarge> {
    b.pow_int(&Rat::int(e.clone()))
}

impl Mono {
    /// The monomial 1.
    pub fn one() -> Mono {
        Mono(Vec::new())
    }

    /// `a ^ e`.
    pub fn atom(a: Atom, e: BigInt) -> Mono {
        match e.is_zero() {
            true => Mono::one(),
            false => Mono(vec![(a, e)]),
        }
    }

    /// Whether it is 1.
    pub fn is_one(&self) -> bool {
        self.0.is_empty()
    }

    /// Its atoms and exponents.
    pub fn atoms(&self) -> &[(Atom, BigInt)] {
        &self.0
    }

    /// The product, by a merge of the two sorted lists: O(atoms).
    pub fn mul(&self, o: &Mono) -> Mono {
        let (mut out, mut i, mut j) = (Vec::with_capacity(self.0.len() + o.0.len()), 0, 0);
        while i < self.0.len() || j < o.0.len() {
            let pick = match (self.0.get(i), o.0.get(j)) {
                (Some(a), Some(b)) => a.0.cmp(&b.0),
                (Some(_), None) => Ordering::Less,
                _ => Ordering::Greater,
            };
            match pick {
                Ordering::Less => {
                    out.push(self.0[i].clone());
                    i += 1;
                }
                Ordering::Greater => {
                    out.push(o.0[j].clone());
                    j += 1;
                }
                Ordering::Equal => {
                    let e = &self.0[i].1 + &o.0[j].1;
                    if !e.is_zero() {
                        out.push((self.0[i].0.clone(), e));
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        Mono(out)
    }

    /// `m ^ e`, `e` not 0.
    fn pow(&self, e: &BigInt) -> Mono {
        Mono(self.0.iter().map(|(a, f)| (a.clone(), f * e)).collect())
    }

    fn symbols(&self, out: &mut BTreeSet<Arc<str>>) {
        for (a, _) in &self.0 {
            a.symbols(out);
        }
    }

    fn has_symbol(&self) -> bool {
        self.0.iter().any(|(a, _)| a.has_symbol())
    }
}

impl Atom {
    fn symbols(&self, out: &mut BTreeSet<Arc<str>>) {
        match self {
            Atom::Sym(x) => {
                out.insert(x.clone());
            }
            Atom::Call(_, args) => args.iter().for_each(|f| f.symbols(out)),
            Atom::Log(f) | Atom::Sum(f) => f.symbols(out),
            Atom::Exp(_, m) => m.symbols(out),
            Atom::Pow(a, b) => {
                a.symbols(out);
                b.symbols(out);
            }
        }
    }

    fn has_symbol(&self) -> bool {
        let mut s = BTreeSet::new();
        self.symbols(&mut s);
        !s.is_empty()
    }
}

/// `a + b` added into one constant when the sum builds no more than its operands hold, as the
/// checker's constant folding decides ([`Rat::sum_folds`], with its proof); otherwise `None`.
fn add_if_small(a: &Rat, b: &Rat) -> Result<Option<Rat>, TooLarge> {
    match a.sum_folds(b)? {
        true => a.add(b).map(Some),
        false => Ok(None),
    }
}

/// Adds `x` into the summands `c`: into the first one the sum rule adds it to, again with the
/// result, else as a summand of its own. Zeros are dropped. O(summands) sum rules for each.
fn coef_push(c: &mut Coef, mut x: Rat) -> Result<(), TooLarge> {
    'again: loop {
        if x.is_zero() {
            return Ok(());
        }
        for i in 0..c.len() {
            if let Some(s) = add_if_small(&c[i], &x)? {
                c.remove(i);
                x = s;
                continue 'again;
            }
        }
        let at = c.partition_point(|y| y < &x);
        c.insert(at, x);
        return Ok(());
    }
}

fn coef_add(a: &Coef, b: &Coef) -> Result<Coef, TooLarge> {
    let mut c = a.clone();
    for x in b {
        coef_push(&mut c, x.clone())?;
    }
    Ok(c)
}

fn coef_mul(a: &Coef, b: &Coef) -> Result<Coef, TooLarge> {
    let mut c = Coef::new();
    for x in a {
        for y in b {
            coef_push(&mut c, x.mul(y)?)?;
        }
    }
    Ok(c)
}

/// The sign of a sum of kept constants. One summand, or all of one sign, is read off; else
/// the largest in magnitude decides when it exceeds the others' count times the next, and
/// otherwise the sum is built ([`TooLarge`] when that is refused).
fn coef_sign(c: &Coef) -> Result<Ordering, TooLarge> {
    let sign = |x: &Rat| match (x.is_zero(), x.is_negative()) {
        (true, _) => Ordering::Equal,
        (_, true) => Ordering::Less,
        _ => Ordering::Greater,
    };
    if c.iter().all(|x| sign(x) == sign(&c[0])) {
        return Ok(c.first().map_or(Ordering::Equal, sign));
    }
    let mut abs: Vec<(Rat, usize)> = c.iter().enumerate().map(|(i, x)| (x.abs(), i)).collect();
    abs.sort();
    let (big, i) = &abs[abs.len() - 1];
    let next = &abs[abs.len() - 2].0;
    if big.try_cmp(&next.mul(&rint(abs.len() as u64 - 1))?)? == Ordering::Greater {
        return Ok(sign(&c[*i]));
    }
    let mut s = rint(0);
    for x in c {
        s = s.add(x)?;
    }
    Ok(sign(&s))
}

impl Form {
    /// 0.
    pub fn zero() -> Form {
        Form::default()
    }

    /// The constant `c`.
    pub fn constant(c: Rat) -> Form {
        let mut f = Form::zero();
        if !c.is_zero() {
            f.0.insert(Mono::one(), vec![c]);
        }
        f
    }

    /// `a ^ e`, coefficient 1.
    pub fn atom(a: Atom, e: BigInt) -> Form {
        let mut f = Form::zero();
        f.0.insert(Mono::atom(a, e), vec![rint(1)]);
        f
    }

    /// The symbol `x`.
    pub fn sym(x: &str) -> Form {
        Form::atom(Atom::Sym(x.into()), BigInt::one())
    }

    /// Whether it is 0.
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    /// Its monomials and coefficients, largest first by [`order`], constants last: the order
    /// of the printer. O(t log t) comparisons for `t` monomials.
    pub fn terms(&self) -> Vec<(&Mono, &Coef)> {
        let mut t: Vec<(&Mono, &Coef)> = self.0.iter().collect();
        t.sort_by(|a, b| order(b.0, a.0));
        t
    }

    /// The count of monomials.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether it has no monomials (is 0).
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The constant it is, when it is one kept constant.
    pub fn as_constant(&self) -> Option<&Rat> {
        match self.0.len() {
            0 => None,
            1 => match self.0.iter().next() {
                Some((m, c)) if m.is_one() && c.len() == 1 => Some(&c[0]),
                _ => None,
            },
            _ => None,
        }
    }

    fn symbols(&self, out: &mut BTreeSet<Arc<str>>) {
        self.0.keys().for_each(|m| m.symbols(out));
    }

    /// The single monomial and its one-summand coefficient, when it is `c * m`.
    fn as_term(&self) -> Option<(&Mono, &Rat)> {
        match (self.0.len(), self.0.iter().next()) {
            (1, Some((m, c))) if c.len() == 1 => Some((m, &c[0])),
            _ => None,
        }
    }

    fn insert(&mut self, m: Mono, c: &Coef) -> Result<(), TooLarge> {
        let sum = match self.0.get(&m) {
            Some(d) => coef_add(d, c)?,
            None => c.clone(),
        };
        match sum.is_empty() {
            true => self.0.remove(&m),
            false => self.0.insert(m, sum),
        };
        Ok(())
    }

    /// Whether a monomial holds a sum to a positive power.
    fn holds_sum(&self) -> bool {
        self.0.keys().any(|m| {
            m.0.iter()
                .any(|(a, e)| matches!(a, Atom::Sum(_)) && e.is_positive())
        })
    }

    /// A held sum stays held only as the whole expression's one monomial: in a sum or product
    /// with other monomials its monomials are needed, so it is expanded ([`Form::expanded`]).
    fn settle(self) -> Result<Form, TooLarge> {
        match self.0.len() > 1 && self.holds_sum() {
            true => self.expanded(),
            false => Ok(self),
        }
    }

    /// `a + b`, into `a`: O(t_b log(t_a + t_b)) map operations, so a chain of `k` sums costs
    /// O(t log t) in all. Only an operand of one monomial can hold a sum (`settle`), so only
    /// such an operand is looked at for one.
    pub fn plus(self, o: &Form) -> Result<Form, TooLarge> {
        let held = |f: &Form| f.0.len() == 1 && f.holds_sum();
        let check = held(&self) || held(o);
        let mut f = self;
        for (m, c) in &o.0 {
            f.insert(m.clone(), c)?;
        }
        match check && f.0.len() > 1 {
            true => f.expanded(),
            false => Ok(f),
        }
    }

    /// `-a`.
    pub fn neg(&self) -> Form {
        Form(
            (self.0.iter())
                .map(|(m, c)| (m.clone(), c.iter().map(Rat::neg).rev().collect()))
                .collect(),
        )
    }

    /// `a - b`.
    pub fn minus(self, o: &Form) -> Result<Form, TooLarge> {
        self.plus(&o.neg())
    }

    /// `a * b`, distributed: O(t_a t_b) products of monomials.
    pub fn mul(&self, o: &Form) -> Result<Form, TooLarge> {
        let mut f = Form::zero();
        for (m1, c1) in &self.0 {
            for (m2, c2) in &o.0 {
                f.insert(m1.mul(m2), &coef_mul(c1, c2)?)?;
            }
        }
        f.settle()
    }

    /// `a ^ e` at an integer `e`: a monomial `c * m` is raised term by term (`Rat` powers
    /// build nothing), any other sum is held whole; `None` for `0 ^ e`, `e < 0`.
    pub fn pow_int(&self, e: &BigInt) -> Result<Option<Form>, TooLarge> {
        if e.is_zero() {
            return Ok(Some(Form::constant(rint(1))));
        }
        if e.is_one() {
            return Ok(Some(self.clone()));
        }
        if self.is_zero() {
            return Ok(e.is_positive().then(Form::zero));
        }
        if let Some((m, c)) = self.as_term() {
            let Some(c) = rpow(c, e)? else {
                return Ok(None);
            };
            let mut f = Form::zero();
            f.0.insert(m.pow(e), vec![c]);
            return Ok(Some(f));
        }
        // A held sum to a power is a monomial above, whose powers multiply.
        Ok(Some(Form::atom(
            Atom::Sum(Box::new(self.clone())),
            e.clone(),
        )))
    }

    /// Every held sum with a positive power replaced by its monomials, sized before it is made:
    /// `(t1 + ... + tk)^e` has at most `C(e + k - 1, k - 1)` monomials, and the system is asked
    /// for their memory ([`zed_kernel::num::room`]) before any is built, so
    /// `(n + 1)^(2^40)` is refused here and stays held elsewhere. Then by squaring: O(log e)
    /// products, each O(t^2) in its operands' monomials.
    pub fn expanded(&self) -> Result<Form, TooLarge> {
        let mut out = Form::zero();
        for (m, c) in &self.0 {
            let mut term = Form(BTreeMap::from([(Mono::one(), c.clone())]));
            let mut rest = Mono::one();
            for (a, e) in &m.0 {
                match (a, e.is_positive()) {
                    (Atom::Sum(s), true) => {
                        let s = s.expanded()?;
                        let k = s.0.values().map(Vec::len).sum::<usize>().max(1);
                        let count = choose(&(e.magnitude() + BigUint::from(k - 1)), k as u64 - 1);
                        // One monomial is held in about 64 bytes of map node and coefficient
                        // (a measured round figure is not needed: the ask only refuses a size
                        // the machine cannot give, and 512 bits is within a factor of two of
                        // a node of the map of one atom).
                        let size = count * BigUint::from(512u32);
                        zed_kernel::num::room(size.clone(), size)?;
                        let mut p = Form::constant(rint(1));
                        let mut base = s;
                        let mut n = e.magnitude().clone();
                        while !n.is_zero() {
                            if n.bit(0) {
                                p = p.mul_plain(&base)?;
                            }
                            n >>= 1u32;
                            if !n.is_zero() {
                                base = base.mul_plain(&base)?;
                            }
                        }
                        term = term.mul_plain(&p)?;
                    }
                    _ => rest = rest.mul(&Mono::atom(a.clone(), e.clone())),
                }
            }
            let rest = Form(BTreeMap::from([(rest, vec![rint(1)])]));
            for (m, c) in term.mul_plain(&rest)?.0 {
                out.insert(m, &c)?;
            }
        }
        Ok(out)
    }

    fn mul_plain(&self, o: &Form) -> Result<Form, TooLarge> {
        let mut f = Form::zero();
        for (m1, c1) in &self.0 {
            for (m2, c2) in &o.0 {
                f.insert(m1.mul(m2), &coef_mul(c1, c2)?)?;
            }
        }
        Ok(f)
    }

    /// Whether `a` and `b` are equal at every value of their symbols, when neither has an
    /// opaque atom (DESIGN.md L1.17d, "What is decided"): their difference, expanded, is 0.
    pub fn equals(&self, o: &Form) -> Result<bool, TooLarge> {
        Ok(self.expanded()?.minus(&o.expanded()?)?.is_zero())
    }

    /// The cost reading `O(e)` (DESIGN.md L1.17d, "Two readings"): held sums read by their own
    /// `O`, monomials of negative coefficient dropped (a cost is at least 0), coefficients
    /// dropped, and every monomial another one dominates dropped ([`maxima`]).
    pub fn big_o(&self) -> Result<Form, TooLarge> {
        let mut kept = Vec::new();
        for (m, c) in &self.0 {
            if coef_sign(c)? != Ordering::Greater {
                continue;
            }
            let mut out = Mono::one();
            for (a, e) in &m.0 {
                let one = match (a, e.is_positive()) {
                    (Atom::Sum(s), true) => {
                        let o = s.big_o()?;
                        match o.as_term() {
                            Some((m, _)) => m.pow(e),
                            None => Mono::atom(Atom::Sum(Box::new(o)), e.clone()),
                        }
                    }
                    _ => Mono::atom(a.clone(), e.clone()),
                };
                out = out.mul(&one);
            }
            kept.push(out);
        }
        let mut f = Form::zero();
        for m in maxima(kept) {
            f.0.insert(m, vec![rint(1)]);
        }
        Ok(f)
    }

    /// The kernel term it is, for the content address of step M0.7 (`zedc-zir` `lower` then
    /// `canon::address`): a lambda over its symbols in name order, its body the sum of its
    /// terms in structural order, so equal normal forms give one term. A symbol becomes a
    /// parameter, a call `f(..)` and `log(..)` an application of a free name, a kept constant
    /// a literal `rat`. A held sum is lowered as written, so the address of two equal forms
    /// is one when both are taken of their [`Form::expanded`] forms.
    /// The functions it calls (`log`, `realRoot` and opaque calls) are parameters too, after
    /// the symbols, so the term is closed.
    pub fn to_term(&self) -> Term {
        let mut syms = BTreeSet::new();
        self.symbols(&mut syms);
        let mut calls = BTreeSet::new();
        self.callees(&mut calls);
        let params = syms
            .iter()
            .chain(calls.difference(&syms))
            .cloned()
            .collect();
        Term::Lam(params, self.body_term().into())
    }

    fn callees(&self, out: &mut BTreeSet<Arc<str>>) {
        for (a, _) in self.0.keys().flat_map(|m| m.0.iter()) {
            match a {
                Atom::Sym(_) => {}
                Atom::Call(f, args) => {
                    out.insert(f.clone());
                    args.iter().for_each(|g| g.callees(out));
                }
                Atom::Log(g) => {
                    out.insert("log".into());
                    g.callees(out);
                }
                Atom::Exp(b, m) => {
                    if let Base::Root(..) = b {
                        out.insert("realRoot".into());
                    }
                    Form(BTreeMap::from([(m.clone(), vec![rint(1)])])).callees(out);
                }
                Atom::Sum(g) => g.callees(out),
                Atom::Pow(g, h) => {
                    g.callees(out);
                    h.callees(out);
                }
            }
        }
    }

    fn body_term(&self) -> Term {
        let lit = |c: &Rat| Term::Lit(Value::Rat(Arc::new(word_form(c))));
        let bin = |p, a: Term, b: Term| Term::Prim(p, vec![a, b]);
        let sum = |ts: Vec<Term>| {
            let mut ts = ts.into_iter();
            match ts.next() {
                None => lit(&rint(0)),
                Some(first) => ts.fold(first, |a, b| bin(zed_kernel::term::Prim::Add, a, b)),
            }
        };
        let terms = (self.0.iter())
            .map(|(m, c)| {
                let c = sum(c.iter().map(lit).collect());
                m.0.iter().fold(c, |acc, (a, e)| {
                    let p = bin(
                        zed_kernel::term::Prim::Pow,
                        a.term(),
                        lit(&Rat::int(e.clone())),
                    );
                    bin(zed_kernel::term::Prim::Mul, acc, p)
                })
            })
            .collect();
        sum(terms)
    }
}

/// A constant in the one form its value has when its numerator and denominator each fit in a
/// word: built, with no kept primes. The ZIR writes a number as it is kept (`W::kept` in
/// crates/zedc-zir/src/zir/binary.rs: "equal numbers kept in different forms ... are written
/// differently"), so `(-2)^2`, kept as `2^2`, and `(-2)*(-2)`, built as `4`, would get two
/// content addresses for one form, against DESIGN.md L1.17d ("equal forms get one content
/// address"). Found by `random_polynomials_have_equal_forms_exactly_when_they_agree_at_random_
/// points` (l01_17), seed 9013687090289476703, pair 180.
///
/// Why a word: the test is on the value alone (`bits`, exact, of the numerator and of the
/// denominator, each read from the kept form without building it), so two forms of one value
/// both pass or both fail it, and those that pass are built to the same `num/den` in lowest
/// terms, one serialization. The word is the bound the sum rule already uses
/// ([`Rat::sum_folds`], "the larger of 64 bits and ..."), so the build is at most two words.
/// A wider value keeps its form: making it canonical needs the factors of a built part (a
/// plain `2^100` written in digits against the kept `2^100`), which is what keeping avoids;
/// that case is left to the address of the value (plan row KEPT-ast-normal-form, its notes).
fn word_form(c: &Rat) -> Rat {
    let (num, den, pows) = c.kept();
    if pows.is_empty() && c.wide().is_empty() {
        return c.clone();
    }
    let side = |sign: i8, plain: &BigInt| {
        let pick = |e: &BigInt| (e.sign() == Sign::Plus) == (sign > 0);
        let ps = (pows.iter())
            .filter(|(_, e)| pick(e))
            .map(|(p, e)| (*p, e.abs()))
            .collect();
        let ws = (c.wide().iter())
            .filter(|(_, e)| pick(e))
            .map(|(q, e)| (q.clone(), e.abs()));
        Rat::from_kept_wide(plain.abs(), BigInt::one(), ps, ws.collect())
    };
    let small = |r: Option<Rat>| {
        r.and_then(|r| {
            bits(&r)
                .ok()
                .flatten()
                .map(|b| (b <= BigUint::from(64u32), r))
        })
    };
    match (small(side(1, num)), small(side(-1, den))) {
        (Some((true, n)), Some((true, d))) => match (n.built_parts(), d.built_parts()) {
            (Ok((n, _)), Ok((d, _))) => {
                let n = BigInt::from_biguint(num.sign(), n.into_owned());
                Rat::new(n, BigInt::from(d.into_owned())).unwrap_or_else(|| c.clone())
            }
            _ => c.clone(),
        },
        _ => c.clone(),
    }
}

impl Atom {
    fn term(&self) -> Term {
        let app = |f: &str, args: Vec<Term>| Term::App(Term::Var(f.into()).into(), args);
        match self {
            Atom::Sym(x) => Term::Var(x.clone()),
            Atom::Call(f, args) => app(f, args.iter().map(Form::body_term).collect()),
            Atom::Log(f) => app("log", vec![f.body_term()]),
            Atom::Exp(b, m) => {
                let base = match b {
                    Base::Int(q) => Term::Lit(Value::Rat(Arc::new(Rat::int(q.clone().into())))),
                    Base::Root(cs, k) => app(
                        "realRoot",
                        cs.iter()
                            .map(|c| Term::Lit(Value::Rat(Arc::new(Rat::int(c.clone())))))
                            .chain([Term::Lit(Value::Rat(Arc::new(rint(*k))))])
                            .collect(),
                    ),
                };
                let mf = Form(BTreeMap::from([(m.clone(), vec![rint(1)])]));
                Term::Prim(zed_kernel::term::Prim::Pow, vec![base, mf.body_term()])
            }
            Atom::Sum(f) => f.body_term(),
            Atom::Pow(a, b) => Term::Prim(
                zed_kernel::term::Prim::Pow,
                vec![a.body_term(), b.body_term()],
            ),
        }
    }
}

/// `C(n, k)`, exact, by `k` products and quotients (each quotient exact: the running value is
/// `C(n - k + i, i)`). O(k) big operations, called with `k` the count of a sum's terms.
fn choose(n: &BigUint, k: u64) -> BigUint {
    let mut c = BigUint::one();
    if *n < BigUint::from(k) {
        return BigUint::zero();
    }
    let base = n - BigUint::from(k);
    for i in 1..=k {
        c = c * (&base + BigUint::from(i)) / BigUint::from(i);
    }
    c
}

// ---------------------------------------------------------------------------------------------
// Exponentials and logarithms.

/// The joint coprime base of one positive constant `q`: `q = prod b^k` over primes of one
/// word and wide atoms that are no perfect power, read from the kernel's own factoring of a
/// power ([`Rat::pow`] factors one-word parts into primes and wide parts into primes below
/// 2^8 and a least root, step L1.17b): `q^2` is taken and its exponents halved, since `q^1` is
/// kept as written. `None` when a plain part is left (the kernel kept it unfactored), or `q`
/// is not above 0.
fn base_of(q: &Rat) -> Result<Option<Vec<(BigUint, BigInt)>>, TooLarge> {
    if q.is_zero() || q.is_negative() {
        return Ok(None);
    }
    let sq = q.pow(&BigUint::from(2u32))?;
    let (num, den, pows) = sq.kept();
    if !num.is_one() || !den.is_one() {
        return Ok(None);
    }
    let half = |e: &BigInt| e / 2;
    let mut out: Vec<(BigUint, BigInt)> = pows
        .iter()
        .map(|(p, e)| (BigUint::from(*p), half(e)))
        .collect();
    out.extend(sq.wide().iter().map(|(w, f)| (w.clone(), half(f))));
    Ok(Some(out))
}

/// `q ^ x` for a positive constant `q` and an exponent in normal form, by `q^(t + u) = q^t *
/// q^u` and `q^(c * m) = (q^m)^c` over the coprime base of `q` (DESIGN.md L1.17d): the
/// constant term of `x` raises `q` itself; each other term `c * m` needs one integer `c`, and
/// gives `(b^m)^(c k)` for each `b^k` of `q`'s base. `None` when a coefficient is not one
/// integer, or `q` has no base (`base_of`): the power is then opaque.
fn exp_of(q: &Rat, x: &Form) -> Result<Option<Form>, TooLarge> {
    let Some(base) = base_of(q)? else {
        return Ok(None);
    };
    let mut out = Form::constant(rint(1));
    for (m, c) in &x.0 {
        let [c] = c.as_slice() else { return Ok(None) };
        if !c.is_integer() {
            return Ok(None);
        }
        let c = c.to_integer()?;
        let f = match m.is_one() {
            true => match rpow(q, &c)? {
                Some(v) => Form::constant(v),
                None => return Ok(None),
            },
            false => {
                let mut mono = Mono::one();
                for (b, k) in &base {
                    mono = mono.mul(&Mono::atom(
                        Atom::Exp(Base::Int(b.clone()), m.clone()),
                        &c * k,
                    ));
                }
                Form(BTreeMap::from([(mono, vec![rint(1)])]))
            }
        };
        out = out.mul(&f)?;
    }
    rebase(out).map(Some)
}

/// The exponential atoms of `f` over the joint coprime base of all their wide bases: when two
/// wide bases share a prime, the natural coprime base of them all is taken
/// (`zed_kernel::num::coprime::coprime_base_exponents`, Bernstein's algorithms, documented
/// there) and each element by its least root ([`zed_kernel::num::least_root`]), so every
/// base is coprime to every other and no perfect power. Primes of one word are coprime to
/// everything already. O(1) when no two wide bases share a prime
/// (`coprime::shares_a_factor`, by product and remainder trees).
fn rebase(f: Form) -> Result<Form, TooLarge> {
    let mut wide = BTreeSet::new();
    for m in f.0.keys() {
        for (a, _) in &m.0 {
            if let Atom::Exp(Base::Int(b), _) = a
                && b.bits() > 64
            {
                wide.insert(b.clone());
            }
        }
    }
    let wide: Vec<BigUint> = wide.into_iter().collect();
    if wide.len() < 2
        || !zed_kernel::num::coprime::shares_a_factor(&wide)
            .iter()
            .any(|s| *s)
    {
        return Ok(f);
    }
    let cb = zed_kernel::num::coprime::coprime_base_exponents(&wide);
    let roots: Vec<(BigUint, BigInt)> = (cb.elements.iter())
        .map(|e| {
            let (r, k) = zed_kernel::num::least_root(e.clone());
            (r, BigInt::from(k))
        })
        .collect();
    let mut out = Form::zero();
    for (m, c) in f.0 {
        let mut mono = Mono::one();
        for (a, e) in m.0 {
            match &a {
                Atom::Exp(Base::Int(b), x) if b.bits() > 64 => {
                    let at = wide.binary_search(b).expect("each wide base was listed");
                    for (el, mult) in &cb.exponents[at] {
                        let (r, k) = &roots[*el as usize];
                        let f = &e * k * BigInt::from(*mult);
                        mono = mono.mul(&Mono::atom(Atom::Exp(Base::Int(r.clone()), x.clone()), f));
                    }
                }
                _ => mono = mono.mul(&Mono::atom(a, e)),
            }
        }
        out.insert(mono, &c)?;
    }
    Ok(out)
}

/// `a ^ x` in normal form: an integer `x` by [`Form::pow_int`]; a positive constant base by
/// `exp_of`; a product of exponentials `(q^m)^c` by `q^(c * m * x)`; a lone algebraic root
/// `r^c` by `(r^m)^(c d)` for each `d * m` of `x`; anything else opaque.
pub fn power(a: &Form, x: &Form) -> Result<Option<Form>, TooLarge> {
    let opaque = || {
        Ok(Some(Form::atom(
            Atom::Pow(Box::new(a.clone()), Box::new(x.clone())),
            BigInt::one(),
        )))
    };
    if let Some(e) = x.as_constant() {
        if e.is_integer() {
            return a.pow_int(&e.to_integer()?);
        }
        return opaque();
    }
    if x.is_zero() {
        return Ok(Some(Form::constant(rint(1))));
    }
    if let Some(q) = a.as_constant() {
        return match exp_of(q, x)? {
            Some(f) => Ok(Some(f)),
            None => opaque(),
        };
    }
    if let Some((m, c)) = a.as_term()
        && c == &rint(1)
        && m.0.iter().all(|(a, _)| matches!(a, Atom::Exp(..)))
    {
        let mut out = Form::constant(rint(1));
        for (at, c) in &m.0 {
            let Atom::Exp(b, em) = at else {
                unreachable!("all exponentials")
            };
            let ex = Form(BTreeMap::from([(em.clone(), vec![Rat::int(c.clone())])])).mul(x)?;
            let f = match b {
                Base::Int(q) => exp_of(&Rat::int(q.clone().into()), &ex)?,
                Base::Root(cs, k) => root_power(cs, *k, &ex)?,
            };
            match f {
                Some(f) => out = out.mul(&f)?,
                None => return opaque(),
            }
        }
        return Ok(Some(out));
    }
    opaque()
}

/// `r ^ x` for the algebraic root `r = realRoot(cs, k)`: `(r^m)^d` for each term `d * m` of
/// `x` with one integer `d`, the constant term as `(r^1)^d`; `None` otherwise.
fn root_power(cs: &[BigInt], k: u32, x: &Form) -> Result<Option<Form>, TooLarge> {
    let mut mono = Mono::one();
    for (m, c) in &x.0 {
        let [c] = c.as_slice() else { return Ok(None) };
        if !c.is_integer() {
            return Ok(None);
        }
        mono = mono.mul(&Mono::atom(
            Atom::Exp(Base::Root(cs.to_vec(), k), m.clone()),
            c.to_integer()?,
        ));
    }
    Ok(Some(Form(BTreeMap::from([(mono, vec![rint(1)])]))))
}

/// `log(a)` in a cost, base 2 (DESIGN.md L1.17d): `log(c * prod a^e) = log(c) + sum e
/// log(a)`, `log(q^m) = m log(q)`, `log(2) = 1`, and the log of another prime or wide base a
/// constant atom `log(q)`; the log of a sum is an atom. `None` for a constant not above 0.
pub fn log_of(a: &Form) -> Result<Option<Form>, TooLarge> {
    let Some((m, c)) = a.as_term() else {
        return Ok(Some(Form::atom(
            Atom::Log(Box::new(a.clone())),
            BigInt::one(),
        )));
    };
    let Some(cb) = base_of(c)? else {
        return Ok(None);
    };
    let log_base = |b: &BigUint| match b == &BigUint::from(2u32) {
        true => Form::constant(rint(1)),
        false => Form::atom(
            Atom::Log(Box::new(Form::constant(Rat::int(b.clone().into())))),
            BigInt::one(),
        ),
    };
    let mut out = Form::zero();
    for (b, k) in &cb {
        out = out.plus(&log_base(b).mul(&Form::constant(Rat::int(k.clone())))?)?;
    }
    for (at, e) in &m.0 {
        let e = Form::constant(Rat::int(e.clone()));
        let one = match at {
            Atom::Exp(Base::Int(q), em) => {
                let em = Form(BTreeMap::from([(em.clone(), vec![rint(1)])]));
                em.mul(&log_base(q))?
            }
            _ => Form::atom(
                Atom::Log(Box::new(Form::atom(at.clone(), BigInt::one()))),
                BigInt::one(),
            ),
        };
        out = out.plus(&one.mul(&e)?)?;
    }
    Ok(Some(out))
}

// ---------------------------------------------------------------------------------------------
// The order (DESIGN.md L1.17d, "One order").

/// The part of a monomial in one symbol `x`: its exponentials in `x` as `(base, exponent
/// monomial, power)`, its power of `x` and its power of `log(x)`.
#[derive(Default)]
struct Part<'a> {
    exps: Vec<(&'a BigUint, &'a Mono, &'a BigInt)>,
    pow: BigInt,
    log: BigInt,
}

/// A monomial split into the coordinates of dominance: its part in each symbol and the power
/// of each opaque atom (a call, a held sum, an opaque power, a log of anything but a symbol,
/// an exponential in more than one symbol or over an algebraic root). Atoms with no symbol are
/// constants and take no coordinate.
#[derive(Default)]
struct Coords<'a> {
    parts: BTreeMap<Arc<str>, Part<'a>>,
    opaque: BTreeMap<&'a Atom, &'a BigInt>,
}

fn coords(m: &Mono) -> Coords<'_> {
    let mut c = Coords::default();
    for (a, e) in &m.0 {
        let mut syms = BTreeSet::new();
        a.symbols(&mut syms);
        let only = match syms.len() {
            0 => continue,
            1 => syms.into_iter().next(),
            _ => None,
        };
        match (a, only) {
            (Atom::Sym(x), _) => c.parts.entry(x.clone()).or_default().pow += e,
            (Atom::Log(f), Some(x)) if **f == Form::sym(&x) => {
                c.parts.entry(x).or_default().log += e
            }
            (Atom::Exp(Base::Int(q), em), Some(x)) if em.0.iter().all(|(a, _)| a.has_symbol()) => {
                c.parts.entry(x).or_default().exps.push((q, em, e))
            }
            _ => {
                c.opaque.insert(a, e);
            }
        }
    }
    c
}

/// The exponent monomials' own order in `x`, the order of their parts.
fn cmp_mono_in(x: &str, a: &Mono, b: &Mono) -> Ordering {
    let (ca, cb) = (coords(a), coords(b));
    let none = Part::default();
    cmp_part(
        ca.parts.get(x).unwrap_or(&none),
        cb.parts.get(x).unwrap_or(&none),
        x,
    )
}

/// Hardy's order of two parts in `x` (Hardy 1912, doi:10.1112/plms/s2-10.1.54, p. 60,
/// Theorem 1; DESIGN.md L1.17d): the exponentials first, the exponent monomials from the
/// largest down (by this order in `x`, recursively), at each the sign of `sum c log q` of the
/// difference, read as the exact order of `prod q^c` of one side against the other's (kept
/// powers, built nothing, step L1.17b); then the power of `x`; then that of `log(x)`.
///
/// Proof sketch that this is Hardy's comparison: the quotient of the two parts is
/// `prod_m exp(D_m * m) * x^dp * log(x)^dl` with `D_m = sum c log q` of the difference at the
/// exponent `m`; the largest `m` with `D_m != 0` makes it tend to infinity (`D_m > 0`) or 0,
/// since `exp(D m)` beats every smaller exponential and every power of `x` and `log x` for an
/// unbounded `m`; with no such `m`, `x^dp` decides, then `log(x)^dl`. A comparison of products
/// refused its memory reads as equal at that exponent and goes on (deterministic, never a
/// wrong strict answer from a value: only a coarser order).
fn cmp_part(a: &Part, b: &Part, x: &str) -> Ordering {
    let mut ms: Vec<&Mono> = a.exps.iter().chain(&b.exps).map(|t| t.1).collect();
    ms.sort_by(|p, q| cmp_mono_in(x, q, p).then_with(|| q.cmp(p)));
    ms.dedup();
    let mut i = 0;
    while i < ms.len() {
        let mut j = i + 1;
        while j < ms.len() && cmp_mono_in(x, ms[i], ms[j]) == Ordering::Equal {
            j += 1;
        }
        let group = &ms[i..j];
        let side = |p: &Part| -> Option<Rat> {
            let mut r = rint(1);
            for (q, m, c) in &p.exps {
                if group.contains(m) {
                    r = r
                        .mul(&rpow(&Rat::int((*q).clone().into()), c).ok()??)
                        .ok()?;
                }
            }
            Some(r)
        };
        if let (Some(l), Some(r)) = (side(a), side(b)) {
            match l.try_cmp(&r) {
                Ok(Ordering::Equal) | Err(_) => {}
                Ok(o) => return o,
            }
        }
        i = j;
    }
    a.pow.cmp(&b.pow).then_with(|| a.log.cmp(&b.log))
}

/// The coordinates of two monomials, in the one order: symbols by name, then opaque atoms in
/// structural order.
fn keys<'a>(a: &Coords<'a>, b: &Coords<'a>) -> (Vec<Arc<str>>, Vec<&'a Atom>) {
    let syms: BTreeSet<Arc<str>> = a.parts.keys().chain(b.parts.keys()).cloned().collect();
    let opq: BTreeSet<&Atom> = a.opaque.keys().chain(b.opaque.keys()).copied().collect();
    (syms.into_iter().collect(), opq.into_iter().collect())
}

fn cmp_coord(a: &Coords, b: &Coords, sym: Option<&str>, atom: Option<&Atom>) -> Ordering {
    let none = Part::default();
    let zero = BigInt::zero();
    match (sym, atom) {
        (Some(x), _) => cmp_part(
            a.parts.get(x).unwrap_or(&none),
            b.parts.get(x).unwrap_or(&none),
            x,
        ),
        (_, Some(t)) => a
            .opaque
            .get(t)
            .copied()
            .unwrap_or(&zero)
            .cmp(b.opaque.get(t).copied().unwrap_or(&zero)),
        _ => Ordering::Equal,
    }
}

/// The total order of monomials, lexicographic over the coordinates (each symbol's part by
/// [`cmp_part`], symbols by name, then each opaque atom's power), then structural. It extends
/// dominance: if `m1` is at most `m2` in every coordinate, the first coordinate where they
/// differ has `m1` below, so `m1 < m2` here. It is transitive as a lexicographic order of total
/// preorders with a total tie-break. DESIGN.md L1.17d names "dominance, then total degree,
/// then content address", which is not transitive once exponentials meet polynomials:
/// `2^n > n^100` by dominance, `n^100 > n^50 * m` by degree, `n^50 * m > 2^n` by degree; row
/// SPEC-bound-form-total-order asks for this order instead.
fn lex(m1: &Mono, m2: &Mono) -> Ordering {
    let (a, b) = (coords(m1), coords(m2));
    let (syms, opq) = keys(&a, &b);
    for x in &syms {
        match cmp_coord(&a, &b, Some(&**x), None) {
            Ordering::Equal => {}
            o => return o,
        }
    }
    for &t in &opq {
        match cmp_coord(&a, &b, None, Some(t)) {
            Ordering::Equal => {}
            o => return o,
        }
    }
    m1.cmp(m2)
}

/// The order of the printer: `lex`, with the constant monomial (no symbol) last.
pub fn order(m1: &Mono, m2: &Mono) -> Ordering {
    match (m1.has_symbol(), m2.has_symbol()) {
        (false, true) => Ordering::Less,
        (true, false) => Ordering::Greater,
        _ => lex(m1, m2),
    }
}

/// Whether `m1` is dominated by `m2`: at most in every symbol's part and every opaque atom's
/// power (DESIGN.md L1.17d).
pub fn dominated(m1: &Mono, m2: &Mono) -> bool {
    let (a, b) = (coords(m1), coords(m2));
    let (syms, opq) = keys(&a, &b);
    syms.iter()
        .all(|x| cmp_coord(&a, &b, Some(&**x), None) != Ordering::Greater)
        && opq
            .iter()
            .all(|&t| cmp_coord(&a, &b, None, Some(t)) != Ordering::Greater)
}

/// The monomials no other one dominates (each once), by `lex` from the largest down.
///
/// Method: sorted by `lex` descending, a monomial is dominated only by one before it (a
/// dominating one is above it in `lex`). With at most two coordinates in the whole set, one
/// before it dominates exactly when its second coordinate is at most the greatest second
/// coordinate seen so far (the first is at least its own, by the sort), so one pass after the
/// sort decides each: O(t log t) comparisons, the maxima-of-a-point-set sweep (Kung, Luccio
/// and Preparata 1975, "On finding the maxima of a set of vectors", J. ACM 22(4):469-476,
/// doi:10.1145/321906.321910, the two-dimensional case). With three or more coordinates each
/// is checked against the maxima kept so far, O(t k) for `k` maxima; their divide and conquer
/// is O(t log^(d-2) t) in `d` coordinates, above O(t log t) from four on, and is row
/// BOUND-maxima-many-symbols.
pub fn maxima(mut ms: Vec<Mono>) -> Vec<Mono> {
    ms.sort_by(|a, b| lex(b, a));
    ms.dedup();
    let mut syms = BTreeSet::new();
    let mut opq = BTreeSet::new();
    let cs: Vec<Coords> = ms.iter().map(coords).collect();
    for c in &cs {
        syms.extend(c.parts.keys().cloned());
        opq.extend(c.opaque.keys().copied());
    }
    let mut out: Vec<usize> = Vec::new();
    if syms.len() + opq.len() <= 2 {
        let (sym2, atom2) = match (syms.iter().nth(1), opq.iter().next(), syms.len()) {
            (Some(x), _, _) => (Some(x.clone()), None),
            (None, Some(t), 1) => (None, Some(*t)),
            (None, Some(_), 0) => (None, opq.iter().nth(1).copied()),
            _ => (None, None),
        };
        let mut best: Option<usize> = None;
        for i in 0..ms.len() {
            let kept = match best {
                None => true,
                Some(b) => {
                    let second = cmp_coord(&cs[i], &cs[b], sym2.as_deref(), atom2);
                    second == Ordering::Greater
                }
            };
            if kept {
                out.push(i);
                best = Some(i);
            }
        }
    } else {
        for i in 0..ms.len() {
            if !out.iter().any(|&j| dominated(&ms[i], &ms[j])) {
                out.push(i);
            }
        }
    }
    out.into_iter().map(|i| ms[i].clone()).collect()
}

/// The work of a loop whose trip count is `trip` (the normal form of `b - a` for `a ..< b`)
/// and whose body has work `body`: their product with the monomials of negative coefficient
/// dropped, which bounds `max(0, b - a)` times the body from above where the symbols are not
/// negative (DESIGN.md L1.17d, "How they combine").
pub fn work(trip: &Form, body: &Form) -> Result<Form, TooLarge> {
    let p = trip.mul(body)?;
    let mut f = Form::zero();
    for (m, c) in p.0 {
        if coef_sign(&c)? == Ordering::Greater {
            f.0.insert(m, c);
        }
    }
    Ok(f)
}

// ---------------------------------------------------------------------------------------------
// Sizes (DESIGN.md L1.17d, "Sizes from the normal form").

/// `floor(log_base |x|)` of a nonzero kept integer `x`, exact, with nothing built.
///
/// An estimate is read from the kept exponents, `sum e log_base q` in fixed point at 2^-52
/// from `f64` logarithms of each part's leading 64 bits, then checked and narrowed by the
/// exact order of kept powers (`base^k <= |x| < base^(k+1)`, step L1.17b): a binary search
/// over the estimate's error interval, widened until it holds the answer, so the result does
/// not rest on the accuracy of `f64::log2`. O(parts) for the estimate, then O(log err)
/// comparisons of kept powers.
fn floor_log(x: &Rat, base: u32) -> Result<BigUint, TooLarge> {
    let x = x.abs();
    let lb = f64::from(base).log2();
    let fixed = |v: &BigUint| -> BigInt {
        let bits = v.bits();
        let shift = bits.saturating_sub(64);
        let top = (v >> shift).to_f64().unwrap_or(f64::MAX);
        let l = (top.log2() + shift as f64) / lb;
        BigInt::from((l * 4503599627370496.0) as i128)
    };
    let (num, _, pows) = x.kept();
    let mut est = fixed(num.magnitude());
    let mut err = BigInt::from(1u64 << 8);
    for (p, e) in pows {
        let l = fixed(&BigUint::from(*p));
        err += e.abs() * ((l.abs() >> 40u32) + 1);
        est += e * l;
    }
    for (w, f) in x.wide() {
        let l = fixed(w);
        err += f.abs() * ((l.abs() >> 40u32) + 1);
        est += f * l;
    }
    let b = rint(base);
    let le = |k: &BigInt| -> Result<bool, TooLarge> {
        match k.sign() {
            Sign::Minus => Ok(true),
            _ => Ok(b.pow(k.magnitude())?.try_cmp(&x)? != Ordering::Greater),
        }
    };
    loop {
        let lo = ((&est - &err) >> 52u32) - 1;
        let hi = ((&est + &err) >> 52u32) + 1;
        if le(&lo)? && !le(&hi)? {
            // base^lo <= x < base^hi: the greatest k with base^k <= x is in [lo, hi).
            let (mut l, mut h) = (lo, hi);
            while &h - &l > BigInt::one() {
                let mid = (&l + &h) >> 1u32;
                match le(&mid)? {
                    true => l = mid,
                    false => h = mid,
                }
            }
            return Ok(l.magnitude().clone());
        }
        err *= 2;
    }
}

/// The bit length `floor(log2 |x|) + 1` of a kept integer `x`, 0 for 0, exact with nothing
/// built; `None` for a value that is no integer.
pub fn bits(x: &Rat) -> Result<Option<BigUint>, TooLarge> {
    if !x.is_integer() {
        return Ok(None);
    }
    if x.is_zero() {
        return Ok(Some(BigUint::zero()));
    }
    Ok(Some(floor_log(x, 2)? + 1u32))
}

/// The count of decimal digits `floor(log10 |x|) + 1` of a kept integer `x` as an `int`
/// prints it, sign apart, 1 for 0, exact with nothing built; `None` for a value that is no
/// integer.
pub fn digits(x: &Rat) -> Result<Option<BigUint>, TooLarge> {
    if !x.is_integer() {
        return Ok(None);
    }
    if x.is_zero() {
        return Ok(Some(BigUint::one()));
    }
    Ok(Some(floor_log(x, 10)? + 1u32))
}

// ---------------------------------------------------------------------------------------------
// Reading and printing.

/// The normal form of the Zed expression `text` under `reading`, or a message saying what it
/// cannot read: `log` outside a cost, an operator outside the ring, a division by 0.
pub fn read(text: &str, reading: Reading) -> Result<Form, String> {
    let tokens = zedc_syntax::lex::lex(text).map_err(|e| format!("{e:?}"))?;
    let tree = zedc_syntax::parse::parse(text, &tokens, "Expr", zedc_syntax::parse::TOP)
        .map_err(|e| format!("{e:?}"))?;
    let e = zedc_syntax::ast::build(text, &tokens, &tree).map_err(|e| format!("{e:?}"))?;
    from_expr(&e, reading)
}

fn too_large(e: TooLarge) -> String {
    format!("the normal form asks for more memory than the system gives: {e:?}")
}

/// The normal form of an expression of the AST.
pub fn from_expr(e: &Expr, reading: Reading) -> Result<Form, String> {
    let go = |e: &Expr| from_expr(e, reading);
    let some = |r: Result<Option<Form>, TooLarge>, what: &str| match r {
        Ok(Some(f)) => Ok(f),
        Ok(None) => Err(format!("{what} is not defined")),
        Err(e) => Err(too_large(e)),
    };
    match &e.kind {
        ExprKind::Int { radix, digits } => match Value::int_text(digits, *radix) {
            Ok(Some(Value::Int(i))) => Ok(Form::constant(rint(i))),
            Ok(Some(Value::Big(r))) => Ok(Form::constant((*r).clone())),
            Ok(_) => Err(format!("`{digits}` is no integer")),
            Err(e) => Err(too_large(e)),
        },
        ExprKind::Rat(d) => match Rat::decimal(d) {
            Ok(Some(r)) => Ok(Form::constant(r)),
            Ok(None) => Err(format!("`{d}` is no rational")),
            Err(e) => Err(too_large(e)),
        },
        ExprKind::Name(x) => Ok(Form::sym(x)),
        ExprKind::Read { of, name } => match &of.kind {
            ExprKind::Name(x) => Ok(Form::sym(&format!("{x}::{name}"))),
            _ => Err("a metadata read of anything but a name".to_string()),
        },
        ExprKind::Unary(UnaryOp::Neg, a) => Ok(go(a)?.neg()),
        ExprKind::Binary(op, a, b) => {
            let (a, b) = (go(a)?, go(b)?);
            match op {
                BinaryOp::Add => a.plus(&b).map_err(too_large),
                BinaryOp::Sub => a.minus(&b).map_err(too_large),
                BinaryOp::Mul => a.mul(&b).map_err(too_large),
                BinaryOp::Div => {
                    let inv = some(b.pow_int(&BigInt::from(-1)), "a division by 0")?;
                    a.mul(&inv).map_err(too_large)
                }
                BinaryOp::Pow => some(power(&a, &b), "`0 ^ e` with `e < 0`"),
                _ => Err(format!("the operator {op:?} in a bound")),
            }
        }
        ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } if named.is_empty() => {
            let ExprKind::Name(f) = &callee.kind else {
                return Err("a call of anything but a name".to_string());
            };
            match (f.as_str(), positional.as_slice()) {
                ("log", [a]) => match reading {
                    Reading::Cost => some(log_of(&go(a)?), "`log` of a constant not above 0"),
                    Reading::Exact => Err(
                        "`log` in a range bound or a size; an integer logarithm is `ilog2(n)`"
                            .to_string(),
                    ),
                },
                ("realRoot", [cs, k]) => {
                    let ExprKind::Array(cs) = &cs.kind else {
                        return Err("`realRoot` takes an array of coefficients".to_string());
                    };
                    let int = |e: &Expr| -> Result<BigInt, String> {
                        let f = go(e)?;
                        match f.as_constant() {
                            Some(c) if c.is_integer() => c.to_integer().map_err(too_large),
                            None if f.is_zero() => Ok(BigInt::zero()),
                            _ => Err("`realRoot` takes integers".to_string()),
                        }
                    };
                    let cs = cs.iter().map(int).collect::<Result<Vec<_>, _>>()?;
                    let k = int(k)?
                        .to_u32()
                        .ok_or("`realRoot`'s index is a small integer")?;
                    Ok(Form::atom(
                        Atom::Exp(Base::Root(cs, k), Mono::one()),
                        BigInt::one(),
                    ))
                }
                _ => {
                    let args = positional.iter().map(go).collect::<Result<Vec<_>, _>>()?;
                    Ok(Form::atom(
                        Atom::Call(f.as_str().into(), args),
                        BigInt::one(),
                    ))
                }
            }
        }
        _ => Err("an expression outside the ring of bounds".to_string()),
    }
}

/// A constant as Zed writes it: an integer by its kept powers (`3*2^63`), a fraction as
/// `n/d` with each side so written, the sign apart. Parses back to the same value.
fn constant_text(c: &Rat) -> String {
    if c.is_integer() {
        return c.abs().integer_text();
    }
    let (num, den, pows) = c.kept();
    let split = |pos: bool| {
        let pows = (pows.iter())
            .filter(|(_, e)| e.is_positive() == pos)
            .map(|(p, e)| (*p, e.abs()))
            .collect();
        let wide = (c.wide().iter())
            .filter(|(_, e)| e.is_positive() == pos)
            .map(|(w, e)| (w.clone(), e.abs()))
            .collect();
        let plain = match pos {
            true => num.abs(),
            false => den.clone(),
        };
        Rat::from_kept_wide(plain, BigInt::one(), pows, wide)
            .map_or_else(|| "?".to_string(), |r| r.integer_text())
    };
    let d = split(false);
    let n = split(true);
    match d.contains(['*', '^']) {
        true => format!("{n}/({d})"),
        false => format!("{n}/{d}"),
    }
}

impl fmt::Display for Form {
    /// The one printer (DESIGN.md L1.17d): terms largest first, constants last, the fewest
    /// parentheses that parse back to the same form.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let terms = self.terms();
        if terms.is_empty() {
            return write!(f, "0");
        }
        for (i, (m, c)) in terms.into_iter().enumerate() {
            let (neg, body) = term_text(m, c);
            match (i, neg) {
                (0, true) => write!(f, "-{body}")?,
                (0, false) => write!(f, "{body}")?,
                (_, true) => write!(f, " - {body}")?,
                (_, false) => write!(f, " + {body}")?,
            }
        }
        Ok(())
    }
}

/// A term's sign and its text without it.
fn term_text(m: &Mono, c: &Coef) -> (bool, String) {
    let mono = mono_text(m);
    let (neg, coef) = match c.as_slice() {
        [x] => (x.is_negative(), constant_text(x)),
        // Summands the sum rule keeps apart, largest first, as one parenthesized sum.
        _ => {
            let mut s = String::new();
            for (i, x) in c.iter().rev().enumerate() {
                let t = constant_text(x);
                match (i, x.is_negative()) {
                    (0, true) => s.push_str(&format!("-{t}")),
                    (0, false) => s.push_str(&t),
                    (_, true) => s.push_str(&format!(" - {t}")),
                    (_, false) => s.push_str(&format!(" + {t}")),
                }
            }
            (false, format!("({s})"))
        }
    };
    let body = match (m.is_one(), coef.as_str()) {
        (true, _) => coef,
        (false, "1") => mono,
        (false, _) if coef.contains('/') && !coef.starts_with('(') => format!("({coef})*{mono}"),
        (false, _) => format!("{coef}*{mono}"),
    };
    (neg, body)
}

fn mono_text(m: &Mono) -> String {
    let mut parts: Vec<(&Atom, &BigInt)> = m.0.iter().map(|(a, e)| (a, e)).collect();
    // Symbols, then logs, then the rest, each by the structural order, so `n*log(n)` reads
    // as written.
    parts.sort_by_key(|(a, _)| match a {
        Atom::Sym(_) => 0,
        Atom::Log(_) => 1,
        Atom::Call(..) => 2,
        Atom::Exp(..) => 3,
        Atom::Sum(_) | Atom::Pow(..) => 4,
    });
    let one = |(a, e): (&Atom, &BigInt)| {
        let t = atom_text(a);
        let e1 = e.is_one();
        let bare = matches!(a, Atom::Sym(_) | Atom::Log(_) | Atom::Call(..));
        match (e1, bare, e.is_negative()) {
            (true, true, _) => t,
            (true, false, _) => match a {
                Atom::Exp(..) | Atom::Pow(..) => t,
                _ => format!("({t})"),
            },
            (false, true, false) => format!("{t}^{e}"),
            (false, true, true) => format!("{t}^({e})"),
            (false, false, false) => format!("({t})^{e}"),
            (false, false, true) => format!("({t})^({e})"),
        }
    };
    parts.into_iter().map(one).collect::<Vec<_>>().join("*")
}

fn atom_text(a: &Atom) -> String {
    match a {
        Atom::Sym(x) => x.to_string(),
        Atom::Call(f, args) => {
            let args: Vec<String> = args.iter().map(Form::to_string).collect();
            format!("{f}({})", args.join(", "))
        }
        Atom::Log(f) => format!("log({f})"),
        Atom::Exp(b, m) => {
            let base = match b {
                Base::Int(q) => q.to_string(),
                Base::Root(cs, k) => {
                    let cs: Vec<String> = cs.iter().map(BigInt::to_string).collect();
                    format!("realRoot([{}], {k})", cs.join(", "))
                }
            };
            if m.is_one() {
                return base;
            }
            let ex = mono_text(m);
            match matches!(m.0.as_slice(), [(Atom::Sym(_), e)] if e.is_one()) {
                true => format!("{base}^{ex}"),
                false => format!("{base}^({ex})"),
            }
        }
        Atom::Sum(f) => f.to_string(),
        Atom::Pow(a, b) => format!("({a})^({b})"),
    }
}
