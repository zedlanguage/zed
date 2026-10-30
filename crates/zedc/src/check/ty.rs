//! The checker's types (step L1.26): a kernel type for the scalars and atoms, structured
//! tuples, function signatures, type variables, and the unknown type `_` of a value no rule
//! has typed yet (a port's lines, a pattern's bound names).
//!
//! A type is a union of pieces: the values of one scalar carrier, the atoms, one tuple shape,
//! one function, one type variable, or the unknown. An operator or a function applies to each
//! combination of its arguments' pieces, so `int | f64` plus `int` is checked as `int + int`
//! and `f64 + int`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use zed_kernel::types::Type as KType;
use zed_kernel::{Universe, Value};

/// A type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ty {
    /// The scalars and atoms, never a tuple or a function.
    pub set: KType,
    /// The tuple shapes, each with its components.
    pub tuples: Vec<Vec<Ty>>,
    /// The functions.
    pub fns: Vec<Arc<Sig>>,
    /// The type variables.
    pub vars: BTreeSet<Arc<str>>,
    /// Whether the type holds the unknown `_`.
    pub dynamic: bool,
}

/// A function's signature: its parameters' names and kinds, shared by its arrows, which
/// together are an intersection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sig {
    /// The parameters.
    pub params: Vec<SParam>,
    /// The arrows.
    pub arrows: Vec<Arrow>,
}

/// A parameter of a signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SParam {
    /// Its name.
    pub name: Arc<str>,
    /// Whether it is passed by position.
    pub positional: bool,
    /// Its default, if it has one: the declaring function's binder, the parameter's index,
    /// and whether the default reads no name of the unit, so a call through a value can
    /// fill it.
    pub default: Option<(usize, usize, bool)>,
}

/// One arrow: a type for each parameter, and the result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arrow {
    /// The parameters' types.
    pub params: Vec<Ty>,
    /// The result.
    pub result: Ty,
}

/// A scalar carrier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Carrier {
    /// `bool`.
    Bool,
    /// `int`.
    Int,
    /// `rat`.
    Rat,
    /// `f64`.
    F64,
    /// `String`.
    Str,
}

impl Carrier {
    /// The five, in the order the signature search tries them.
    pub const ALL: [Carrier; 5] = [
        Carrier::Int,
        Carrier::F64,
        Carrier::Rat,
        Carrier::Str,
        Carrier::Bool,
    ];

    /// Every value of the carrier.
    pub fn ty(self) -> KType {
        match self {
            Carrier::Bool => KType::bool(),
            Carrier::Int => KType::int(),
            Carrier::Rat => KType::rat(),
            Carrier::F64 => KType::f64(),
            Carrier::Str => KType::string(),
        }
    }

    /// Its name.
    pub fn name(self) -> &'static str {
        match self {
            Carrier::Bool => "bool",
            Carrier::Int => "int",
            Carrier::Rat => "rat",
            Carrier::F64 => "f64",
            Carrier::Str => "String",
        }
    }

    /// Whether it is a number.
    pub fn numeric(self) -> bool {
        matches!(self, Carrier::Int | Carrier::Rat | Carrier::F64)
    }
}

/// Every atom.
pub fn atoms() -> KType {
    let carriers = Carrier::ALL.iter().fold(KType::empty(), |a, c| a | c.ty());
    KType::universe(Universe::Scalar) - &carriers
}

/// The atom `#errs` that two distinct failures merge into, with any payload.
pub fn errs() -> KType {
    KType::atom_with("errs", &KType::top())
}

/// A piece of a type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Piece {
    /// Scalars: the values of one carrier, the atoms, or what is neither.
    Set(KType),
    /// A tuple shape.
    Tuple(Vec<Ty>),
    /// A function.
    Fn(Arc<Sig>),
    /// A type variable.
    Var(Arc<str>),
    /// The unknown.
    Dyn,
}

impl Piece {
    /// The carrier of a scalar piece.
    pub fn carrier(&self) -> Option<Carrier> {
        match self {
            Piece::Set(s) => Carrier::ALL.into_iter().find(|c| s.subtype(&c.ty())),
            _ => None,
        }
    }

    /// Whether it is a piece of atoms.
    pub fn is_atoms(&self) -> bool {
        matches!(self, Piece::Set(s) if s.subtype(&atoms()))
    }

    /// The type of this piece alone.
    pub fn ty(&self) -> Ty {
        match self {
            Piece::Set(s) => Ty::set(s.clone()),
            Piece::Tuple(cs) => Ty::tuple(cs.clone()),
            Piece::Fn(s) => Ty::func(s.clone()),
            Piece::Var(v) => Ty::var(v.clone()),
            Piece::Dyn => Ty::dynamic(),
        }
    }
}

/// The binding of type variables made while applying an arrow.
pub type Binds = BTreeMap<Arc<str>, Ty>;

impl Ty {
    /// No value.
    pub fn empty() -> Ty {
        Ty {
            set: KType::empty(),
            tuples: Vec::new(),
            fns: Vec::new(),
            vars: BTreeSet::new(),
            dynamic: false,
        }
    }

    /// The scalars and atoms of `s`.
    pub fn set(s: KType) -> Ty {
        Ty {
            set: s,
            ..Ty::empty()
        }
    }

    /// Every value of `c`.
    pub fn carrier(c: Carrier) -> Ty {
        Ty::set(c.ty())
    }

    /// The type of a scalar literal.
    pub fn lit(v: &Value) -> Ty {
        Ty::set(KType::lit(v).expect("a scalar literal"))
    }

    /// The tuple shape `(cs…)`.
    pub fn tuple(cs: Vec<Ty>) -> Ty {
        Ty {
            tuples: vec![cs],
            ..Ty::empty()
        }
    }

    /// The function `s`.
    pub fn func(s: Arc<Sig>) -> Ty {
        Ty {
            fns: vec![s],
            ..Ty::empty()
        }
    }

    /// The type variable `v`.
    pub fn var(v: Arc<str>) -> Ty {
        let mut t = Ty::empty();
        t.vars.insert(v);
        t
    }

    /// The unknown.
    pub fn dynamic() -> Ty {
        Ty {
            dynamic: true,
            ..Ty::empty()
        }
    }

    /// Whether no value is in it.
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
            && self.tuples.is_empty()
            && self.fns.is_empty()
            && self.vars.is_empty()
            && !self.dynamic
    }

    /// The union.
    pub fn union(&self, other: &Ty) -> Ty {
        let mut out = self.clone();
        out.set = &out.set | &other.set;
        for t in &other.tuples {
            if !out.tuples.contains(t) {
                out.tuples.push(t.clone());
            }
        }
        for f in &other.fns {
            if !out.fns.contains(f) {
                out.fns.push(f.clone());
            }
        }
        out.vars.extend(other.vars.iter().cloned());
        out.dynamic |= other.dynamic;
        out
    }

    /// The union of `ts`.
    pub fn union_all<'t>(ts: impl IntoIterator<Item = &'t Ty>) -> Ty {
        ts.into_iter().fold(Ty::empty(), |a, b| a.union(b))
    }

    /// Its atoms.
    pub fn atoms(&self) -> KType {
        &self.set & &atoms()
    }

    /// It without its atoms.
    pub fn without_atoms(&self) -> Ty {
        Ty {
            set: &self.set - &atoms(),
            ..self.clone()
        }
    }

    /// Its pieces: the scalars split by carrier, then the atoms and the other scalars, the
    /// tuples, the functions, the variables and the unknown.
    pub fn pieces(&self) -> Vec<Piece> {
        let mut out = Vec::new();
        let mut rest = self.set.clone();
        for c in Carrier::ALL {
            let part = &self.set & &c.ty();
            if !part.is_empty() {
                rest = &rest - &c.ty();
                out.push(Piece::Set(part));
            }
        }
        let a = &rest & &atoms();
        if !a.is_empty() {
            out.push(Piece::Set(a.clone()));
            rest = &rest - &a;
        }
        if !rest.is_empty() {
            out.push(Piece::Set(rest));
        }
        out.extend(self.tuples.iter().cloned().map(Piece::Tuple));
        out.extend(self.fns.iter().cloned().map(Piece::Fn));
        out.extend(self.vars.iter().cloned().map(Piece::Var));
        if self.dynamic {
            out.push(Piece::Dyn);
        }
        out
    }

    /// The one numeric carrier its numbers are of, when they are of one and it holds nothing
    /// but those numbers and atoms.
    pub fn numeric_carrier(&self) -> Option<Carrier> {
        if !self.tuples.is_empty() || !self.fns.is_empty() || !self.vars.is_empty() || self.dynamic
        {
            return None;
        }
        let nums = &self.set - &atoms();
        [Carrier::Int, Carrier::Rat, Carrier::F64]
            .into_iter()
            .find(|c| !nums.is_empty() && nums.subtype(&c.ty()))
    }

    /// Whether it holds no variable and no unknown, at any depth.
    pub fn closed(&self) -> bool {
        self.vars.is_empty() && !self.dynamic && self.tuples.iter().flatten().all(Ty::closed)
    }

    /// Whether every value of `self` is in `other`, binding `other`'s variables as needed.
    pub fn sub(&self, other: &Ty, binds: &mut Binds) -> bool {
        self.pieces().iter().all(|p| accepts(other, p, binds))
    }

    /// Whether every value of `self` is in `other`, with no variable bound.
    pub fn subtype(&self, other: &Ty) -> bool {
        let mut b = Binds::new();
        self.sub(other, &mut b) && b.is_empty()
    }

    /// The meet with `t`, as an `is` test narrows: what of `self` is also in `t`.
    pub fn meet(&self, t: &Ty) -> Ty {
        if t.dynamic {
            return self.clone();
        }
        let mut out = Ty::set(&self.set & &t.set);
        for a in &self.tuples {
            for b in &t.tuples {
                if a.len() == b.len() {
                    let cs: Vec<Ty> = a.iter().zip(b).map(|(x, y)| x.meet(y)).collect();
                    if cs.iter().all(|c| !c.is_empty()) && !out.tuples.contains(&cs) {
                        out.tuples.push(cs);
                    }
                }
            }
        }
        if !t.fns.is_empty() {
            out.fns = self.fns.clone();
        }
        if self.dynamic || !self.vars.is_empty() {
            out = out.union(t);
        }
        out
    }

    /// What of `self` is not in `t`, as `is not` narrows: scalars are subtracted, tuples
    /// wholly inside `t` dropped, and the rest kept.
    pub fn diff(&self, t: &Ty) -> Ty {
        let mut out = self.clone();
        out.set = &self.set - &t.set;
        out.tuples.retain(|a| {
            !Ty::tuple(a.clone()).subtype(&Ty {
                set: KType::empty(),
                ..t.clone()
            })
        });
        out
    }

    /// `self` with its variables replaced by their bindings.
    pub fn subst(&self, binds: &Binds) -> Ty {
        if binds.is_empty() {
            return self.clone();
        }
        let mut out = Ty {
            set: self.set.clone(),
            tuples: self
                .tuples
                .iter()
                .map(|cs| cs.iter().map(|c| c.subst(binds)).collect())
                .collect(),
            fns: self.fns.clone(),
            vars: BTreeSet::new(),
            dynamic: self.dynamic,
        };
        for v in &self.vars {
            match binds.get(v) {
                Some(t) => out = out.union(t),
                None => {
                    out.vars.insert(v.clone());
                }
            }
        }
        out
    }

    /// `self` with its variables renamed by `names`.
    pub fn rename(&self, names: &BTreeMap<Arc<str>, Arc<str>>) -> Ty {
        let binds: Binds = names
            .iter()
            .map(|(k, v)| (k.clone(), Ty::var(v.clone())))
            .collect();
        let mut out = self.subst(&binds);
        out.fns = out
            .fns
            .iter()
            .map(|s| {
                Arc::new(Sig {
                    params: s.params.clone(),
                    arrows: s
                        .arrows
                        .iter()
                        .map(|a| Arrow {
                            params: a.params.iter().map(|p| p.rename(names)).collect(),
                            result: a.result.rename(names),
                        })
                        .collect(),
                })
            })
            .collect();
        out
    }

    /// Every variable in it, in order of first appearance.
    pub fn vars_in(&self, out: &mut Vec<Arc<str>>) {
        for v in &self.vars {
            if !out.contains(v) {
                out.push(v.clone());
            }
        }
        for c in self.tuples.iter().flatten() {
            c.vars_in(out);
        }
        for s in &self.fns {
            for a in &s.arrows {
                a.params.iter().for_each(|p| p.vars_in(out));
                a.result.vars_in(out);
            }
        }
    }

    /// Whether the value `v` is in it; a variable or the unknown holds every value.
    pub fn contains(&self, v: &Value) -> bool {
        if self.dynamic || !self.vars.is_empty() {
            return true;
        }
        match v {
            Value::Tuple(items) => self.tuples.iter().any(|cs| {
                cs.len() == items.len() && cs.iter().zip(items).all(|(c, x)| c.contains(x))
            }),
            Value::Family(_) | Value::Path(_) => !self.fns.is_empty(),
            _ => self.set.contains(v),
        }
    }

    /// Whether `self` and `other` may share a value.
    pub fn meets(&self, other: &Ty) -> bool {
        if !self.closed() || !other.closed() {
            return true;
        }
        !(&self.set & &other.set).is_empty()
            || self.tuples.iter().any(|a| {
                other
                    .tuples
                    .iter()
                    .any(|b| a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.meets(y)))
            })
            || (!self.fns.is_empty() && !other.fns.is_empty())
    }
}

/// Whether the piece `p` is in `t`, binding a variable of `t` to it when nothing else of
/// `t` holds it.
fn accepts(t: &Ty, p: &Piece, binds: &mut Binds) -> bool {
    if t.dynamic {
        return true;
    }
    let ok = match p {
        Piece::Dyn => true,
        Piece::Set(s) => s.subtype(&t.set),
        Piece::Tuple(cs) => t.tuples.iter().any(|ds| {
            ds.len() == cs.len() && {
                let mut b = binds.clone();
                let ok = cs.iter().zip(ds).all(|(c, d)| c.sub(d, &mut b));
                if ok {
                    *binds = b;
                }
                ok
            }
        }),
        Piece::Fn(s) => t.fns.iter().any(|q| fits_sig(s, q)),
        Piece::Var(v) => t.vars.contains(v),
    };
    if ok {
        return true;
    }
    match t.vars.iter().next() {
        Some(v) => {
            let b = binds.entry(v.clone()).or_insert_with(Ty::empty);
            *b = b.union(&p.ty());
            true
        }
        None => false,
    }
}

/// Whether a function of signature `s` is a function of signature `q`: the same parameter
/// names and kinds, and on each arrow of `q`, an arrow of `s` that takes its parameters and
/// returns within its result.
pub fn fits_sig(s: &Sig, q: &Sig) -> bool {
    s.params.len() == q.params.len()
        && s.params
            .iter()
            .zip(&q.params)
            .all(|(a, b)| a.positional == b.positional && (a.positional || a.name == b.name))
        && q.arrows.iter().all(|qa| {
            s.arrows.iter().any(|sa| {
                let mut b = Binds::new();
                qa.params
                    .iter()
                    .zip(&sa.params)
                    .all(|(x, y)| x.sub(y, &mut b))
                    && sa.result.subst(&b).subtype(&qa.result)
            })
        })
}

impl Sig {
    /// Whether it has the same parameter names and kinds as `other`.
    pub fn same_kinds(&self, other: &Sig) -> bool {
        self.params.len() == other.params.len()
            && self
                .params
                .iter()
                .zip(&other.params)
                .all(|(a, b)| a.positional == b.positional && a.name == b.name)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut items: Vec<String> = Vec::new();
        if !self.set.is_empty() {
            items.push(surface(&self.set.to_string()));
        }
        for cs in &self.tuples {
            let cs: Vec<String> = cs.iter().map(|c| c.to_string()).collect();
            items.push(match cs.len() {
                1 => format!("({},)", cs[0]),
                _ => format!("({})", cs.join(", ")),
            });
        }
        for s in &self.fns {
            items.push(format!("({s})"));
        }
        items.extend(self.vars.iter().map(|v| v.to_string()));
        if self.dynamic {
            items.push("_".into());
        }
        match items.len() {
            0 => f.write_str("!_"),
            _ => f.write_str(&items.join(" | ")),
        }
    }
}

impl fmt::Display for Sig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let arrows: Vec<String> = self
            .arrows
            .iter()
            .map(|a| {
                let ps: Vec<String> = self
                    .params
                    .iter()
                    .zip(&a.params)
                    .map(|(p, t)| match p.positional {
                        true => t.to_string(),
                        false => format!("{}: {t}", p.name),
                    })
                    .collect();
                format!("({}) -> {}", ps.join(", "), a.result)
            })
            .collect();
        match arrows.len() {
            1 => f.write_str(&arrows[0]),
            _ => {
                let arrows: Vec<String> = arrows.iter().map(|a| format!("({a})")).collect();
                f.write_str(&arrows.join(" & "))
            }
        }
    }
}

/// A kernel type's prefix form, in surface syntax: `(| a b)` is `a | b`, `(\ int 3)` is
/// `int \ 3`, `(#a _)` is `#a(_)`, `(tuple A B)` is `(A, B)`, `(! X)` is `!X`, `(& X Y)` is
/// `X & Y`.
pub fn surface(prefix: &str) -> String {
    let toks = tokens(prefix);
    let mut i = 0;
    let s = sexpr(&toks, &mut i);
    show(&s, 0)
}

enum S {
    Atom(String),
    List(Vec<S>),
}

fn tokens(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let cs: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < cs.len() {
        match cs[i] {
            ' ' => i += 1,
            '(' | ')' => {
                out.push(cs[i].to_string());
                i += 1;
            }
            '"' => {
                let start = i;
                i += 1;
                while i < cs.len() && cs[i] != '"' {
                    i += if cs[i] == '\\' { 2 } else { 1 };
                }
                i += 1;
                out.push(cs[start..i.min(cs.len())].iter().collect());
            }
            _ => {
                let start = i;
                while i < cs.len() && !matches!(cs[i], ' ' | '(' | ')') {
                    i += 1;
                }
                out.push(cs[start..i].iter().collect());
            }
        }
    }
    out
}

fn sexpr(toks: &[String], i: &mut usize) -> S {
    let t = &toks[*i];
    *i += 1;
    if t != "(" {
        return S::Atom(t.clone());
    }
    let mut items = Vec::new();
    while *i < toks.len() && toks[*i] != ")" {
        items.push(sexpr(toks, i));
    }
    *i += 1;
    S::List(items)
}

/// `s` in surface syntax, parenthesized when its operator binds looser than `prec`: 0 for
/// `|`, 1 for `&`, 2 for `\`, 3 for an operand.
fn show(s: &S, prec: u8) -> String {
    let S::List(items) = s else {
        let S::Atom(a) = s else { unreachable!() };
        return a.clone();
    };
    let (head, rest) = match items.split_first() {
        Some((S::Atom(h), rest)) => (h.as_str(), rest),
        _ => return "!_".into(),
    };
    let wrap = |p: u8, text: String| match prec > p {
        true => format!("({text})"),
        false => text,
    };
    match head {
        "|" if rest.is_empty() => "!_".into(),
        "|" => wrap(
            0,
            rest.iter()
                .map(|r| show(r, 1))
                .collect::<Vec<_>>()
                .join(" | "),
        ),
        "&" => wrap(
            1,
            rest.iter()
                .map(|r| show(r, 2))
                .collect::<Vec<_>>()
                .join(" & "),
        ),
        "\\" => {
            let taken: Vec<String> = rest[1..].iter().map(|r| show(r, 3)).collect();
            let taken = match taken.len() {
                1 => taken[0].clone(),
                _ => format!("({})", taken.join(" | ")),
            };
            wrap(2, format!("{} \\ {taken}", show(&rest[0], 3)))
        }
        "!" => format!("!{}", show(&rest[0], 3)),
        "tuple" => {
            let cs: Vec<String> = rest.iter().map(|r| show(r, 0)).collect();
            match cs.len() {
                1 => format!("({},)", cs[0]),
                _ => format!("({})", cs.join(", ")),
            }
        }
        h if h.starts_with('#') => format!("{h}({})", show(&rest[0], 0)),
        h => format!(
            "({h} {})",
            rest.iter()
                .map(|r| show(r, 3))
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}
