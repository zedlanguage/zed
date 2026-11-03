//! The checker's types (step L1.26): a kernel type for the scalars and atoms, structured
//! tuples, function signatures, type variables, and the unknown type `_` of a value no rule
//! has typed yet (a port's lines, a pattern's bound names).
//!
//! A type is a union of pieces: the values of one scalar carrier, the atoms, one tuple shape,
//! one function, one type variable, or the unknown. An operator or a function applies to each
//! combination of its arguments' pieces, so `int | f64` plus `int` is checked as `int + int`
//! and `f64 + int`.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt;
use std::sync::Arc;

use zed_kernel::types::{Type as KType, Verdict};
use zed_kernel::{Universe, Value};

use crate::lex::Span;

/// A type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    /// The atoms of `set` that are members of a named atom family: data, which `else` keeps
    /// and an operator rejects (sec:failure). The other atoms are loose.
    pub family: KType,
    /// What the payloads of its atoms hold, by atom name: the shapes the atoms were built
    /// with, or `None` where that is not known. The payload of an atom whose name is not
    /// listed is not known.
    pub payloads: BTreeMap<Arc<str>, Option<Vec<Shape>>>,
}

/// The payload an atom was built with: its components by position, and its fields by name.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Shape {
    /// Its components, by position.
    pub items: Vec<Ty>,
    /// Its fields, by name.
    pub fields: BTreeMap<Arc<str>, Ty>,
}

impl Shape {
    /// What it holds at `slot`, if it has that place.
    pub fn at(&self, slot: &Slot) -> Option<&Ty> {
        match slot {
            Slot::Field(n) => self.fields.get(n),
            Slot::Item(i) => self.items.get(*i),
        }
    }

    /// Writes the type of the atom `#name` with this payload to `out`: `#name(int, f: String)`.
    fn write(&self, name: &str, out: &mut String) {
        out.push('#');
        out.push_str(name);
        out.push('(');
        let mut first = true;
        for t in &self.items {
            separate(out, &mut first, ", ");
            t.write(out);
        }
        for (f, t) in &self.fields {
            separate(out, &mut first, ", ");
            out.push_str(f);
            out.push_str(": ");
            t.write(out);
        }
        out.push(')');
    }

    /// It with `f` applied to each component and field.
    fn map(&self, f: impl Fn(&Ty) -> Ty) -> Shape {
        Shape {
            items: self.items.iter().map(&f).collect(),
            fields: self.fields.iter().map(|(n, t)| (n.clone(), f(t))).collect(),
        }
    }
}

/// The payloads of the union of the types `ts`: each name's shapes, once each, and a name some
/// type may hold an unknown payload of is not known. That is found in one union of what of
/// each type's scalars and atoms its payloads do not describe, so the join costs one pass over
/// the types and their shapes.
fn join_payloads(ts: &[&Ty]) -> BTreeMap<Arc<str>, Option<Vec<Shape>>> {
    let mut out: BTreeMap<Arc<str>, Option<Vec<Shape>>> = BTreeMap::new();
    let mut seen: HashSet<(&str, &Shape)> = HashSet::new();
    let mut rest = Vec::new();
    for t in ts {
        let listed = t
            .payloads
            .keys()
            .map(|n| KType::atom_with(n, &KType::top()));
        rest.push(&t.set - &KType::union_all(listed));
        for (n, ss) in &t.payloads {
            let entry = out.entry(n.clone()).or_insert_with(|| Some(Vec::new()));
            match (entry, ss) {
                (entry, None) => *entry = None,
                (Some(have), Some(ss)) => {
                    have.extend(ss.iter().filter(|s| seen.insert((n, s))).cloned());
                }
                (None, Some(_)) => {}
            }
        }
    }
    let rest = KType::union_all(rest);
    for (n, ss) in out.iter_mut() {
        if holds_payload(&rest, n) {
            *ss = None;
        }
    }
    out
}

/// Whether `set` may hold an atom named `n` with a payload.
fn holds_payload(set: &KType, n: &str) -> bool {
    !(set & &KType::atom_with(n, &KType::top())).is_empty()
}

/// A function's signature: its parameters' names and kinds, shared by its arrows, which
/// together are an intersection, and the carriers each bounded type variable ranges over.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sig {
    /// The parameters.
    pub params: Vec<SParam>,
    /// The arrows.
    pub arrows: Vec<Arrow>,
    /// Each bounded type variable, with the mask of the carriers it ranges over: one carrier,
    /// the same at each place the variable stands.
    pub bounds: BTreeMap<Arc<str>, u8>,
    /// Whether it is a family: a morphism held as data (sec:values_morphisms), shown, compared
    /// and put in a tuple as a value, and looked up through its arrows.
    pub data: bool,
    /// What the body needs of the values of its type variables, in the order the body met
    /// the uses: each call checks them again with the variables bound (DESIGN.md rule 4).
    pub needs: Vec<Need>,
    /// Its own type variables, which it binds: a call binds them anew, and a substitution
    /// of the variables of a type that holds it leaves them alone. The others are those of
    /// the functions around it.
    pub own: BTreeSet<Arc<str>>,
}

/// A use the body of a generic function makes of a value whose type is a variable: checked
/// again at each call, on the type the call binds the variable to.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Need {
    /// The type of the value used, a variable of the signature.
    pub on: Ty,
    /// The use.
    pub kind: NeedKind,
    /// What the use gives, a variable of the signature, if it gives a value.
    pub result: Option<Ty>,
    /// The use in the body.
    pub span: Span,
}

/// The uses a [`Need`] records.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NeedKind {
    /// `v[i]` with a literal: a tuple's component, or a family's entry.
    Component {
        /// The component, if the literal is a component number.
        i: Option<usize>,
        /// The literal's type, a family's key.
        key: Ty,
    },
    /// `v[k]` with a key of this type: an application.
    Index(Ty),
    /// A call of `v`, named `what`, with arguments of these types.
    Call {
        /// The value's name in the call.
        what: Arc<str>,
        /// The types of the positional arguments.
        positional: Vec<Ty>,
        /// The names and types of the named arguments.
        named: Vec<(Arc<str>, Ty)>,
        /// Whether the call ends in `...`.
        curry: bool,
    },
    /// A use, `what`, that takes data: the value holds no function.
    Data(Arc<str>),
    /// An argument, of `what`, at a parameter of the closed type `ty`.
    Into {
        /// The function called.
        what: Arc<str>,
        /// The parameter's type.
        ty: Ty,
    },
    /// A name a pattern binds: what the payload of an atom named `atom` holds at `slot`.
    Payload {
        /// The atom's name.
        atom: Arc<str>,
        /// The place in its payload.
        slot: Slot,
    },
}

/// A place in an atom's payload.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Slot {
    /// The field of this name.
    Field(Arc<str>),
    /// The component at this position.
    Item(usize),
}

impl Need {
    /// It with its variables replaced by `binds` at every depth.
    pub fn replace(&self, binds: &Binds) -> Need {
        let all = |ts: &[Ty]| ts.iter().map(|t| t.replace(binds)).collect();
        Need {
            on: self.on.replace(binds),
            kind: match &self.kind {
                NeedKind::Component { i, key } => NeedKind::Component {
                    i: *i,
                    key: key.clone(),
                },
                NeedKind::Index(k) => NeedKind::Index(k.replace(binds)),
                NeedKind::Call {
                    what,
                    positional,
                    named,
                    curry,
                } => NeedKind::Call {
                    what: what.clone(),
                    positional: all(positional),
                    named: named
                        .iter()
                        .map(|(n, t)| (n.clone(), t.replace(binds)))
                        .collect(),
                    curry: *curry,
                },
                NeedKind::Data(what) => NeedKind::Data(what.clone()),
                NeedKind::Into { what, ty } => NeedKind::Into {
                    what: what.clone(),
                    ty: ty.clone(),
                },
                NeedKind::Payload { atom, slot } => NeedKind::Payload {
                    atom: atom.clone(),
                    slot: slot.clone(),
                },
            },
            result: self.result.as_ref().map(|t| t.replace(binds)),
            span: self.span,
        }
    }

    /// Every variable in it, in order of first appearance.
    pub fn vars_in(&self, out: &mut Vars) {
        self.on.vars_in(out);
        match &self.kind {
            NeedKind::Component { .. }
            | NeedKind::Data(_)
            | NeedKind::Into { .. }
            | NeedKind::Payload { .. } => {}
            NeedKind::Index(k) => k.vars_in(out),
            NeedKind::Call {
                positional, named, ..
            } => {
                positional.iter().for_each(|t| t.vars_in(out));
                named.iter().for_each(|(_, t)| t.vars_in(out));
            }
        }
        if let Some(r) = &self.result {
            r.vars_in(out);
        }
    }
}

/// A parameter of a signature.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    /// The five, in the order a class of values holding a literal tries them.
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

    /// Its bit in a mask: its place in [`Carrier::ALL`].
    pub fn bit(self) -> u8 {
        1 << Carrier::ALL
            .iter()
            .position(|&c| c == self)
            .expect("a carrier")
    }

    /// The carriers of the mask `m`, in the order of [`Carrier::ALL`].
    pub fn of_mask(m: u8) -> impl Iterator<Item = Carrier> {
        Carrier::ALL.into_iter().filter(move |c| m & c.bit() != 0)
    }
}

/// The bit of a mask that stands for every value that is not of a carrier: a tuple, a
/// function, an atom.
pub const OTHER: u8 = 1 << 5;

/// The mask of every value.
pub const EVERY: u8 = (1 << 6) - 1;

/// The mask `m` as a type: its carriers joined by `|`, and "other values" for [`OTHER`].
pub fn mask_text(m: u8) -> String {
    let mut out: Vec<&str> = Carrier::of_mask(m).map(Carrier::name).collect();
    if m & OTHER != 0 {
        out.push("other values");
    }
    match out.len() {
        0 => "no type".into(),
        _ => out.join(" | "),
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

/// The bounded variables of the expected function types a comparison is inside, each with the
/// mask of its bound: the caller of such a function picks one carrier of the bound for each,
/// so a variable here stands for every carrier of its mask and is never bound.
type Rigid = BTreeMap<Arc<str>, u8>;

/// Type variables, each once, in order of first appearance.
#[derive(Default)]
pub struct Vars {
    seen: HashSet<Arc<str>>,
    /// The variables, in order.
    pub order: Vec<Arc<str>>,
}

impl Vars {
    /// Whether `v` is one of them.
    pub fn contains(&self, v: &str) -> bool {
        self.seen.contains(v)
    }
}

impl Ty {
    /// No value.
    pub fn empty() -> Ty {
        Ty {
            set: KType::empty(),
            tuples: Vec::new(),
            fns: Vec::new(),
            vars: BTreeSet::new(),
            dynamic: false,
            family: KType::empty(),
            payloads: BTreeMap::new(),
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

    /// The values a variable bounded by the mask `m` may stand for when nothing fixes its
    /// carrier: those of each carrier of `m`, and any value with [`OTHER`].
    pub fn of_mask(m: u8) -> Ty {
        if m & OTHER != 0 {
            return Ty::dynamic();
        }
        Ty::set(Carrier::of_mask(m).fold(KType::empty(), |s, c| &s | &c.ty()))
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

    /// The variable it is, when it is one type variable and nothing else.
    pub fn as_var(&self) -> Option<&Arc<str>> {
        let mut vs = self.vars.iter();
        let v = vs.next()?;
        (vs.next().is_none() && *self == Ty::var(v.clone())).then_some(v)
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
        out.family = &out.family | &other.family;
        if !self.payloads.is_empty() || !other.payloads.is_empty() {
            out.payloads = join_payloads(&[self, other]);
        }
        let have: HashSet<&Vec<Ty>> = self.tuples.iter().collect();
        let new: Vec<&Vec<Ty>> = other.tuples.iter().filter(|t| !have.contains(t)).collect();
        let mut added = HashSet::new();
        out.tuples
            .extend(new.into_iter().filter(|t| added.insert(*t)).cloned());
        let have: HashSet<&Arc<Sig>> = self.fns.iter().collect();
        let new: Vec<&Arc<Sig>> = other.fns.iter().filter(|f| !have.contains(f)).collect();
        let mut added = HashSet::new();
        out.fns
            .extend(new.into_iter().filter(|f| added.insert(*f)).cloned());
        out.vars.extend(other.vars.iter().cloned());
        out.dynamic |= other.dynamic;
        out
    }

    /// The union of `ts`, built once: joining them one at a time copied the union so far each
    /// time, `O(n²)` in the tuple shapes.
    pub fn union_all<'t>(ts: impl IntoIterator<Item = &'t Ty>) -> Ty {
        let ts: Vec<&Ty> = ts.into_iter().collect();
        let mut out = Ty::empty();
        out.set = KType::union_all(ts.iter().map(|t| t.set.clone()));
        out.family = KType::union_all(ts.iter().map(|t| t.family.clone()));
        let mut tuples = HashSet::new();
        let mut fns = HashSet::new();
        if ts.iter().any(|t| !t.payloads.is_empty()) {
            out.payloads = join_payloads(&ts);
        }
        for t in ts {
            out.tuples
                .extend(t.tuples.iter().filter(|c| tuples.insert(*c)).cloned());
            out.fns
                .extend(t.fns.iter().filter(|f| fns.insert(*f)).cloned());
            out.vars.extend(t.vars.iter().cloned());
            out.dynamic |= t.dynamic;
        }
        out
    }

    /// Its atoms.
    pub fn atoms(&self) -> KType {
        &self.set & &atoms()
    }

    /// It without its atoms.
    pub fn without_atoms(&self) -> Ty {
        Ty {
            set: &self.set - &atoms(),
            family: KType::empty(),
            ..self.clone()
        }
    }

    /// It with every atom it holds made a member of a named family, as a `type` declaration
    /// names a union.
    pub fn named(&self) -> Ty {
        Ty {
            family: self.atoms(),
            ..self.clone()
        }
    }

    /// It as a written type reads it: every atom loose, the ascription being the visible act
    /// of re-classifying (sec:failure).
    pub fn written(&self) -> Ty {
        Ty {
            family: KType::empty(),
            ..self.clone()
        }
    }

    /// Its loose atoms: those of no named family.
    pub fn loose(&self) -> KType {
        &self.atoms() - &self.family
    }

    /// What `_` would drop of a value of it (DESIGN.md sec:tour_methods): its loose atoms,
    /// less `named`, the atoms that an `else` in the bound expression writes as its default.
    /// A family's atoms are data, and `_` drops data freely.
    pub fn dropped(&self, named: &KType) -> KType {
        &self.loose() - named
    }

    /// The type of its loose atoms, with their payloads.
    pub fn loose_ty(&self) -> Ty {
        self.of_piece(&Piece::Set(self.loose()))
    }

    /// It without its loose atoms, as `e else d` narrows `e`: what is not an atom, and the
    /// family's atoms. Each step complements only a set that lists no atom names or the
    /// family's, so it costs `O(f log n)` for `f` family atoms of `n`, where `set − loose`
    /// would complement every loose atom.
    pub fn without_loose(&self) -> Ty {
        let mut out = Ty {
            set: &(&self.set - &atoms()) | &(&self.set & &self.family),
            ..self.clone()
        };
        out.prune_payloads();
        out
    }

    /// Drops the payloads of the atoms its set no longer holds (L29-print: a type narrowed to
    /// `String` kept the payload of the `#ioError` it lost, so it differed from `String`).
    fn prune_payloads(&mut self) {
        let set = &self.set;
        self.payloads.retain(|n, _| holds_payload(set, n));
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

    /// Whether it holds no function at any depth (a variable or the unknown may still stand
    /// for one): a type whose values the differential oracle compares (step L1.37).
    pub fn first_order(&self) -> bool {
        self.held_function().is_none()
    }

    /// A function it may hold, at any depth; a family is data, not a function.
    pub fn held_function(&self) -> Option<&Arc<Sig>> {
        self.fns
            .iter()
            .find(|s| !s.data)
            .or_else(|| self.tuples.iter().flatten().find_map(Ty::held_function))
    }

    /// Whether every value of `self` is in `other`, binding `other`'s variables as needed.
    pub fn sub(&self, other: &Ty, binds: &mut Binds) -> bool {
        self.sub_in(other, binds, &mut Rigid::new())
    }

    /// [`Self::sub`] inside the expected function types whose bounded variables `rigid` holds.
    fn sub_in(&self, other: &Ty, binds: &mut Binds, rigid: &mut Rigid) -> bool {
        // `other` as a kernel type, built at most once, when a tuple piece needs it.
        let mut whole: Option<Option<KType>> = None;
        self.pieces().iter().all(|p| {
            // A tuple piece of a type with no variable, function or unknown is decided by the
            // kernel, which sees shapes that hold it only together. Trying each shape in turn
            // costs every shape times the components; the kernel splits the components once.
            // The rule of one shape is sound, so it is tried only when the kernel refused.
            let decided = match p {
                Piece::Tuple(cs) => cs
                    .iter()
                    .map(Ty::kernel)
                    .collect::<Option<Vec<_>>>()
                    .map(KType::tuple)
                    .and_then(|a| {
                        let b = whole.get_or_insert_with(|| other.kernel()).as_ref()?;
                        match a.subtype_verdict(b) {
                            Verdict::Empty => Some(true),
                            Verdict::Inhabited => Some(false),
                            Verdict::Refused(_) => None,
                        }
                    }),
                _ => None,
            };
            decided.unwrap_or_else(|| accepts(other, p, self, binds, rigid))
        })
    }

    /// [`Self::sub_in`] with each tuple piece held by one tuple shape of `other`: the rule for
    /// the components of a tuple, whose joint check is the kernel's on the whole tuple.
    fn sub_by_shape(&self, other: &Ty, binds: &mut Binds, rigid: &mut Rigid) -> bool {
        self.pieces()
            .iter()
            .all(|p| accepts(other, p, self, binds, rigid))
    }

    /// The kernel type of its values, when it holds no function, variable or unknown at any
    /// depth: its scalars and atoms, and its tuple shapes. A tuple piece that no one shape of
    /// a union holds may still be in the union (boxes that cover a box only together); the
    /// kernel decides that, or refuses with its cause.
    pub fn kernel(&self) -> Option<KType> {
        if !self.fns.is_empty() || !self.vars.is_empty() || self.dynamic {
            return None;
        }
        let shapes = self.tuples.iter().map(|cs| {
            let cs = cs.iter().map(Ty::kernel).collect::<Option<Vec<_>>>()?;
            Some(KType::tuple(cs))
        });
        // Joined in pairs: one at a time costs the size of the union so far for each shape.
        let shapes = shapes.collect::<Option<Vec<_>>>()?;
        Some(KType::union_all(
            std::iter::once(self.set.clone()).chain(shapes),
        ))
    }

    /// Whether every value of `self` is in `other`, with no variable bound.
    pub fn subtype(&self, other: &Ty) -> bool {
        let mut b = Binds::new();
        self.sub(other, &mut b) && b.is_empty()
    }

    /// The kernel's verdict on `self <: other`, on what of `self` is outside `other`: `Empty`
    /// when it holds, `Inhabited` when a value outside was built. On kernel types, or on the
    /// scalar sets when either holds a function, variable or unknown; `Empty` when `other` is
    /// the unknown.
    pub fn verdict(&self, other: &Ty) -> Verdict {
        if other.dynamic {
            return Verdict::Empty;
        }
        match (self.kernel(), other.kernel()) {
            (Some(a), Some(b)) => a.subtype_verdict(&b),
            _ => self.set.subtype_verdict(&other.set),
        }
    }

    /// When `self <: other` failed: the clause that says why it was not decided, if the check of
    /// its kernel types (its scalar sets, when either holds a function, variable or unknown)
    /// was refused, and nothing if it was decided. A refusal claims nothing about the types,
    /// so a message that reads as a counterexample would be wrong.
    pub fn refused(&self, other: &Ty) -> String {
        match self.verdict(other) {
            Verdict::Refused(r) => format!(" (not decided: {})", r.message()),
            _ => String::new(),
        }
    }

    /// The meet with `t`, as an `is` test narrows: what of `self` is also in `t`.
    pub fn meet(&self, t: &Ty) -> Ty {
        if t.dynamic {
            return self.clone();
        }
        let mut out = Ty::set(&self.set & &t.set);
        out.family = &self.family & &out.set;
        out.payloads = self.payloads.clone();
        let mut met = Vec::new();
        for a in &self.tuples {
            for b in &t.tuples {
                if a.len() == b.len() {
                    let cs: Vec<Ty> = a.iter().zip(b).map(|(x, y)| x.meet(y)).collect();
                    if cs.iter().all(|c| !c.is_empty()) {
                        met.push(cs);
                    }
                }
            }
        }
        let mut have = HashSet::new();
        let first: Vec<bool> = met.iter().map(|cs| have.insert(cs)).collect();
        out.tuples.extend(
            met.into_iter()
                .zip(first)
                .filter_map(|(cs, f)| f.then_some(cs)),
        );
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
        out.family = &self.family - &t.set;
        out.prune_payloads();
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
            family: self.family.clone(),
            payloads: self.map_payloads(|t| t.subst(binds)),
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

    /// `self` with its variables replaced by `binds` at every depth, inside the functions it
    /// holds too; not inside the types it puts in their place, which may hold the variables
    /// themselves.
    pub fn replace(&self, binds: &Binds) -> Ty {
        if binds.is_empty() {
            return self.clone();
        }
        let mut out = Ty {
            set: self.set.clone(),
            tuples: self
                .tuples
                .iter()
                .map(|cs| cs.iter().map(|c| c.replace(binds)).collect())
                .collect(),
            fns: self
                .fns
                .iter()
                .map(|s| match s.own.iter().any(|v| binds.contains_key(v)) {
                    true => {
                        let free = binds
                            .iter()
                            .filter(|(v, _)| !s.own.contains(*v))
                            .map(|(v, t)| (v.clone(), t.clone()))
                            .collect();
                        Arc::new(s.replace(&free))
                    }
                    false => Arc::new(s.replace(binds)),
                })
                .collect(),
            vars: BTreeSet::new(),
            dynamic: self.dynamic,
            family: self.family.clone(),
            payloads: self.map_payloads(|t| t.replace(binds)),
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

    /// The type of its piece `p` alone, with the payloads of the atoms `p` holds.
    pub fn of_piece(&self, p: &Piece) -> Ty {
        let mut out = p.ty();
        if let Piece::Set(s) = p {
            out.payloads = self
                .payloads
                .iter()
                .filter(|(n, _)| holds_payload(s, n))
                .map(|(n, ss)| (n.clone(), ss.clone()))
                .collect();
        }
        out
    }

    /// Its payloads with `f` applied to each component and field.
    fn map_payloads(&self, f: impl Fn(&Ty) -> Ty) -> BTreeMap<Arc<str>, Option<Vec<Shape>>> {
        self.payloads
            .iter()
            .map(|(n, ss)| {
                let ss = ss.as_ref().map(|ss| ss.iter().map(|s| s.map(&f)).collect());
                (n.clone(), ss)
            })
            .collect()
    }

    /// What the payloads of its atoms named `n` hold: their shapes, or `None` where that is not
    /// known.
    pub fn shapes(&self, n: &str) -> Option<Vec<Shape>> {
        if self.dynamic || !self.vars.is_empty() {
            return None;
        }
        match self.payloads.get(n) {
            Some(s) => s.clone(),
            None if holds_payload(&self.set, n) => None,
            None => Some(Vec::new()),
        }
    }

    /// Every variable in it, in order of first appearance.
    pub fn vars_in(&self, out: &mut Vars) {
        for v in &self.vars {
            if out.seen.insert(v.clone()) {
                out.order.push(v.clone());
            }
        }
        for c in self.tuples.iter().flatten() {
            c.vars_in(out);
        }
        for s in self.payloads.values().flatten().flatten() {
            s.items.iter().for_each(|t| t.vars_in(out));
            s.fields.values().for_each(|t| t.vars_in(out));
        }
        for s in &self.fns {
            for a in &s.arrows {
                a.params.iter().for_each(|p| p.vars_in(out));
                a.result.vars_in(out);
            }
            s.needs.iter().for_each(|n| n.vars_in(out));
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
            Value::Family(_) => self.fns.iter().any(|s| s.data),
            Value::Path(_) => !self.fns.is_empty(),
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

/// Whether the piece `p` of `of` is in `t`, binding a variable of `t` to it when nothing else
/// of `t` holds it. A variable of `rigid` stands for each carrier of its mask in turn: as `p`,
/// `t` must hold each; in `t`, it holds what each carrier, with the rest of `t`, holds.
fn accepts(t: &Ty, p: &Piece, of: &Ty, binds: &mut Binds, rigid: &mut Rigid) -> bool {
    if t.dynamic {
        return true;
    }
    let ok = match p {
        Piece::Dyn => false,
        Piece::Set(s) => {
            s.subtype(&t.set)
                || t.vars.iter().any(|w| {
                    rigid.get(w).is_some_and(|&m| {
                        Carrier::of_mask(m).all(|c| s.subtype(&(&t.set | &c.ty())))
                    })
                })
        }
        Piece::Tuple(cs) => t.tuples.iter().any(|ds| {
            ds.len() == cs.len() && {
                let mut b = binds.clone();
                let ok = cs
                    .iter()
                    .zip(ds)
                    .all(|(c, d)| c.sub_by_shape(d, &mut b, rigid));
                if ok {
                    *binds = b;
                }
                ok
            }
        }),
        Piece::Fn(s) => t.fns.iter().any(|q| fits_in(s, q, rigid)),
        Piece::Var(v) => {
            t.vars.contains(v)
                || rigid
                    .get(v)
                    .is_some_and(|&m| Carrier::of_mask(m).all(|c| c.ty().subtype(&t.set)))
        }
    };
    if ok {
        return true;
    }
    match t.vars.iter().find(|v| !rigid.contains_key(*v)) {
        Some(v) => {
            let b = binds.entry(v.clone()).or_insert_with(Ty::empty);
            *b = b.union(&of.of_piece(p));
            true
        }
        None => false,
    }
}

/// Whether a function of signature `s` is a function of signature `q`: the same parameter
/// names and kinds, and on each arrow of `q`, an arrow of `s` that takes its parameters and
/// returns within its result.
pub fn fits_sig(s: &Sig, q: &Sig) -> bool {
    fits_in(s, q, &mut Rigid::new())
}

/// [`fits_sig`] inside the expected function types whose bounded variables `rigid` holds.
/// `q`'s own bounded variables that a parameter holds join them: the caller of a function of
/// type `q` picks one carrier of each bound, so `s` must take every carrier of it. Each is
/// renamed apart first, since `s` may use the same name for a variable of its own. A bounded
/// variable no parameter holds, of `q` or of `s`, is fixed by no argument, so it stands for
/// any carrier of its bound, as at a call ([`Sig::unheld`]).
fn fits_in(s: &Sig, q: &Sig, rigid: &mut Rigid) -> bool {
    if !s.needs.is_empty() {
        return s == q;
    }
    let same_params = s.params.len() == q.params.len()
        && s.params
            .iter()
            .zip(&q.params)
            .all(|(a, b)| a.positional == b.positional && (a.positional || a.name == b.name));
    if !same_params {
        return false;
    }
    let held = q.held();
    let mut renamed = Binds::new();
    for (v, &m) in q.bounds.iter().filter(|(v, _)| q.own.contains(*v)) {
        let t = match held.contains(v) {
            true => {
                // A quote is in no name a program writes, and the count keeps nested
                // renamings apart.
                let w: Arc<str> = format!("{v}'{}", rigid.len()).into();
                rigid.insert(w.clone(), m);
                Ty::var(w)
            }
            false => Ty::of_mask(m),
        };
        renamed.insert(v.clone(), t);
    }
    let s_unheld = s.unheld();
    let renamed_q;
    let q = match renamed.is_empty() {
        true => q,
        false => {
            renamed_q = q.replace(&renamed);
            &renamed_q
        }
    };
    let fits = q.arrows.iter().all(|qa| {
        s.arrows.iter().any(|sa| {
            let mut b = Binds::new();
            qa.params
                .iter()
                .zip(&sa.params)
                .all(|(x, y)| x.sub_in(y, &mut b, rigid))
                && s.bounds.iter().all(|(v, &m)| {
                    b.get(v)
                        .is_none_or(|t| match t.as_var().and_then(|w| rigid.get(w)) {
                            // Each carrier the caller of `q` may pick is one `s` takes.
                            Some(&mq) => mq & !m == 0,
                            // `v` is one carrier at a call, so it cannot be a rigid variable and
                            // something else at once.
                            None => t.pieces().iter().all(|p| match p.carrier() {
                                Some(c) => m & c.bit() != 0,
                                None => {
                                    m & OTHER != 0
                                        && !matches!(p, Piece::Dyn)
                                        && !matches!(p, Piece::Var(w) if rigid.contains_key(w))
                                }
                            }),
                        })
                })
                && {
                    let mut rb = Binds::new();
                    // `s_unheld` binds to carriers only, so the order of the two is free.
                    sa.result
                        .subst(&s_unheld)
                        .subst(&b)
                        .sub_in(&qa.result, &mut rb, rigid)
                        && rb.is_empty()
                }
        })
    });
    for w in renamed.values().filter_map(Ty::as_var) {
        rigid.remove(w);
    }
    fits
}

impl Sig {
    /// The variables its parameters hold, at any depth, on any arrow.
    pub fn held(&self) -> Vars {
        let mut out = Vars::default();
        for a in &self.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut out));
        }
        out
    }

    /// Its own bounded variables no parameter holds, each bound to [`Ty::of_mask`] of its
    /// bound: no argument fixes its carrier, so a call returns a value of some carrier of it.
    pub fn unheld(&self) -> Binds {
        let held = self.held();
        self.bounds
            .iter()
            .filter(|(v, _)| self.own.contains(*v) && !held.contains(v))
            .map(|(v, &m)| (v.clone(), Ty::of_mask(m)))
            .collect()
    }

    /// One arrow over `params` and `result`, with no bounded variable.
    pub fn one(params: Vec<SParam>, tys: Vec<Ty>, result: Ty) -> Sig {
        Sig {
            params,
            arrows: vec![Arrow {
                params: tys,
                result,
            }],
            bounds: BTreeMap::new(),
            data: false,
            needs: Vec::new(),
            own: BTreeSet::new(),
        }
    }

    /// It with its variables replaced by `binds` at every depth; a bounded variable replaced
    /// by another variable keeps its bound under the new name.
    pub fn replace(&self, binds: &Binds) -> Sig {
        let mut bounds = BTreeMap::new();
        for (v, m) in &self.bounds {
            match binds.get(v) {
                None => {
                    bounds.insert(v.clone(), *m);
                }
                Some(t) => {
                    for w in &t.vars {
                        bounds.insert(w.clone(), *m);
                    }
                }
            }
        }
        Sig {
            params: self.params.clone(),
            arrows: self
                .arrows
                .iter()
                .map(|a| Arrow {
                    params: a.params.iter().map(|p| p.replace(binds)).collect(),
                    result: a.result.replace(binds),
                })
                .collect(),
            bounds,
            data: self.data,
            needs: self.needs.iter().map(|n| n.replace(binds)).collect(),
            own: self
                .own
                .iter()
                .filter(|v| !binds.contains_key(*v))
                .cloned()
                .collect(),
        }
    }

    /// Its arrows with each bounded variable fixed to each carrier of its bound: the product
    /// of the bounds, as long as that product is.
    pub fn expand(&self) -> Vec<Arrow> {
        let mut out = self.arrows.clone();
        for (v, m) in &self.bounds {
            out = out
                .iter()
                .flat_map(|a| {
                    Carrier::of_mask(*m).map(move |c| {
                        let b: Binds = [(v.clone(), Ty::carrier(c))].into();
                        Arrow {
                            params: a.params.iter().map(|p| p.replace(&b)).collect(),
                            result: a.result.replace(&b),
                        }
                    })
                })
                .collect();
        }
        out
    }

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
        let mut text = String::new();
        self.write(&mut text);
        #[cfg(feature = "printed-types")]
        printed::record(self, &text);
        f.write_str(&text)
    }
}

/// Writes `sep` to `out` before every item but the first, which `first` tells.
fn separate(out: &mut String, first: &mut bool, sep: &str) {
    if !*first {
        out.push_str(sep);
    }
    *first = false;
}

impl Ty {
    /// Writes its text, in type syntax, to `out`. Each part is written in place, not built as a
    /// string and copied into the whole: copying cost the depth of each part, so O(n^2) for a
    /// function type n deep.
    fn write(&self, out: &mut String) {
        let mut first = true;
        // An atom whose payloads are known prints each payload's type, `#ioError(op: String,
        // path: String, why: String)` (L29-print); the kernel set holds it with any payload.
        let shaped: Vec<(&Arc<str>, &Vec<Shape>)> = self
            .payloads
            .iter()
            .filter_map(|(n, ss)| Some((n, ss.as_ref()?)))
            .filter(|(n, _)| holds_payload(&self.set, n))
            .collect();
        let rest = (!shaped.is_empty()).then(|| {
            let listed = shaped
                .iter()
                .map(|(n, _)| KType::atom_with(n, &KType::top()));
            &self.set - &KType::union_all(listed)
        });
        let set = rest.as_ref().unwrap_or(&self.set);
        if !set.is_empty() {
            separate(out, &mut first, " | ");
            out.push_str(&set.surface_in_union().to_string());
        }
        for (n, ss) in shaped {
            for s in ss {
                separate(out, &mut first, " | ");
                s.write(n, out);
            }
        }
        for cs in &self.tuples {
            separate(out, &mut first, " | ");
            out.push('(');
            let mut one = true;
            for c in cs {
                separate(out, &mut one, ", ");
                c.write(out);
            }
            if cs.len() == 1 {
                out.push(',');
            }
            out.push(')');
        }
        for s in &self.fns {
            separate(out, &mut first, " | ");
            out.push('(');
            s.write(out);
            out.push(')');
        }
        for v in &self.vars {
            separate(out, &mut first, " | ");
            out.push_str(v);
        }
        if self.dynamic {
            separate(out, &mut first, " | ");
            out.push('_');
        }
        if first {
            out.push_str("!_");
        }
    }
}

impl fmt::Display for Sig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        self.write(&mut text);
        #[cfg(feature = "printed-types")]
        printed::record(&Ty::func(Arc::new(self.clone())), &text);
        f.write_str(&text)
    }
}

impl Sig {
    /// Writes its text, in type syntax, to `out`.
    fn write(&self, out: &mut String) {
        let several = self.arrows.len() != 1;
        let mut first = true;
        for a in &self.arrows {
            separate(out, &mut first, " & ");
            if several {
                out.push('(');
            }
            out.push('(');
            let mut one = true;
            for (p, t) in self.params.iter().zip(&a.params) {
                separate(out, &mut one, ", ");
                if !p.positional {
                    out.push_str(&p.name);
                    out.push_str(": ");
                }
                t.write(out);
            }
            out.push_str(") -> ");
            a.result.write(out);
            if several {
                out.push(')');
            }
        }
        for (i, (v, m)) in self.bounds.iter().enumerate() {
            out.push_str(if i == 0 { " for " } else { ", " });
            out.push_str(v);
            out.push_str(" in ");
            out.push_str(&mask_text(*m));
        }
    }
}

/// The types printed on a thread while recording is on, each with the text printed (feature
/// `printed-types`, OSP-diag): a test parses each text back and compares.
#[cfg(feature = "printed-types")]
pub mod printed {
    use std::cell::RefCell;

    use super::Ty;

    thread_local! {
        static SEEN: RefCell<Option<Vec<(Ty, String)>>> = const { RefCell::new(None) };
    }

    /// Starts recording on this thread, dropping what was recorded.
    pub fn start() {
        SEEN.set(Some(Vec::new()));
    }

    /// What was recorded since `start`, in printed order; recording stops.
    pub fn take() -> Vec<(Ty, String)> {
        SEEN.take().unwrap_or_default()
    }

    /// Records that `t` was printed as `text`, if recording is on.
    pub fn record(t: &Ty, text: &str) {
        SEEN.with_borrow_mut(|seen| {
            if let Some(seen) = seen {
                seen.push((t.clone(), text.into()));
            }
        });
    }
}
