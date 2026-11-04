//! The checker's types (step L1.26): a kernel type for the scalars and atoms, structured
//! tuples, function signatures, type variables, and the unknown type `_` of a value no rule
//! has typed yet (a port's lines, a pattern's bound names).
//!
//! A type is a union of pieces: the values of one scalar carrier, the atoms, one tuple shape,
//! one function, one type variable, or the unknown. An operator or a function applies to each
//! combination of its arguments' pieces, so `int | f64` plus `int` is checked as `int + int`
//! and `f64 + int`.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use zed_kernel::types::{Type as KType, Verdict};
use zed_kernel::{Universe, Value};

use crate::lex::Span;

/// A type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ty {
    /// The scalars and atoms, and the kind-wide part: every tuple or every struct as `(..)`
    /// and `{..}` write them (L1.40d), and what narrowing leaves of those. A tuple shape built
    /// from values is in `tuples`, and a function in `fns`.
    pub set: KType,
    /// The tuple shapes, each with its components.
    pub tuples: Vec<Row>,
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

/// The components of a tuple shape, kept in one shared node with what they hold at any depth,
/// found from the components' rows when the row is made. A row is copied in constant time, so
/// a type is copied in the time of its outer level; and a check that walks into tuples reads
/// a row where it would walk into it, so a tuple nested `n` deep costs `O(n)` in all, not
/// `O(n)` at each level.
#[derive(Clone)]
pub struct Row(Arc<RowData>);

struct RowData {
    cs: Vec<Ty>,
    /// The hash of the components.
    digest: u64,
    /// Whether a component holds a type variable or the unknown, outside functions, at any
    /// depth: whether [`Ty::closed`] fails on one.
    open: bool,
    /// Whether a component holds the unknown, outside functions, at any depth.
    dynamic: bool,
    /// The first function, not a family, that a component holds at any depth.
    held: Option<Arc<Sig>>,
    /// Whether every type variable it holds outside functions, at any depth, was checked as
    /// data when the row was made: set only for the row of a tuple expression, whose
    /// components are each checked as data first.
    data: bool,
}

impl Row {
    /// The row of `cs`.
    pub fn new(cs: Vec<Ty>) -> Row {
        Row::made(cs, false)
    }

    /// The row of `cs`, each checked as data.
    pub(crate) fn of_data(cs: Vec<Ty>) -> Row {
        Row::made(cs, true)
    }

    fn made(cs: Vec<Ty>, data: bool) -> Row {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let digest = BuildHasherDefault::<DefaultHasher>::default().hash_one(&cs);
        let open = cs
            .iter()
            .any(|c| !c.vars.is_empty() || c.dynamic || c.tuples.iter().any(|r| r.0.open));
        let dynamic = cs
            .iter()
            .any(|c| c.dynamic || c.tuples.iter().any(|r| r.0.dynamic));
        let held = cs.iter().find_map(|c| c.held_function().cloned());
        Row(Arc::new(RowData {
            cs,
            digest,
            open,
            dynamic,
            held,
            data,
        }))
    }

    /// Whether a component holds a type variable or the unknown, outside functions, at any
    /// depth.
    pub fn open(&self) -> bool {
        self.0.open
    }

    /// Whether a component holds the unknown, outside functions, at any depth.
    pub fn dynamic(&self) -> bool {
        self.0.dynamic
    }

    /// Whether every type variable it holds outside functions was checked as data when the
    /// row was made.
    pub(crate) fn data(&self) -> bool {
        self.0.data
    }

    /// The components, to change.
    pub fn to_vec(&self) -> Vec<Ty> {
        self.0.cs.clone()
    }
}

impl std::ops::Deref for Row {
    type Target = [Ty];
    fn deref(&self) -> &[Ty] {
        &self.0.cs
    }
}

impl<'a> IntoIterator for &'a Row {
    type Item = &'a Ty;
    type IntoIter = std::slice::Iter<'a, Ty>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.cs.iter()
    }
}

impl FromIterator<Ty> for Row {
    fn from_iter<I: IntoIterator<Item = Ty>>(it: I) -> Row {
        Row::new(it.into_iter().collect())
    }
}

impl PartialEq for Row {
    fn eq(&self, other: &Row) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self.0.digest == other.0.digest && self.0.cs == other.0.cs)
    }
}

impl Eq for Row {}

impl std::hash::Hash for Row {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.0.digest);
    }
}

impl fmt::Debug for Row {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(&self.0.cs).finish()
    }
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
    fn write(&self, name: &str, out: &mut String, scope: &mut Scope) {
        out.push('#');
        out.push_str(name);
        out.push('(');
        let mut first = true;
        for t in &self.items {
            separate(out, &mut first, ", ");
            t.write(out, scope);
        }
        for (f, t) in &self.fields {
            separate(out, &mut first, ", ");
            out.push_str(f);
            out.push_str(": ");
            t.write(out, scope);
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    /// Its own bounded variables a parameter holds, at any depth, on any arrow: an argument
    /// fixes their carriers. Worked out when it is built ([`Sig::note_held`]), so a comparison
    /// does not walk its parameters again at each depth.
    pub held: BTreeSet<Arc<str>>,
    /// How many of the names [`super::var_name`] gives its own type variables and those of the
    /// functions it holds take: a function around it names its own from there on. The checker
    /// writes the own variables of a signature it solved `$k`, for the class `k` each was solved
    /// from, and gives them their names when it finishes, so a function around one does not
    /// rewrite it (CHK-curried).
    pub named: usize,
    /// The variables it holds at any depth, worked out when first asked ([`Sig::facts`]).
    /// Once they are read the signature is not changed in place: a change goes to a clone,
    /// whose facts are worked out again.
    pub facts: Facts,
}

/// The variables a signature holds at any depth, inside the functions it holds too: worked
/// out once for a signature held in a type, so that a substitution, or the naming of the
/// variables of a function around it, does not walk it again at each depth. It is not part
/// of the signature's value, and a clone, which may be changed, works it out again.
///
/// It also keeps the signature [`Sig::settle`] made of it, each solved class variable
/// replaced at every depth: made once, when the checker finishes, so a signature held in many
/// that the checker shows is settled once, not once for each.
///
/// And it keeps the signature's hash ([`Sig::digest`]), made from the hashes of the
/// functions it holds, so a set of functions hashes each at the cost of its outer level.
#[derive(Default)]
pub struct Facts(
    std::sync::OnceLock<VarFacts>,
    std::sync::OnceLock<Arc<Sig>>,
    std::sync::OnceLock<u64>,
);

impl Clone for Facts {
    fn clone(&self) -> Facts {
        Facts::default()
    }
}

impl PartialEq for Facts {
    fn eq(&self, _: &Facts) -> bool {
        true
    }
}

impl Eq for Facts {}

impl std::hash::Hash for Facts {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl fmt::Debug for Facts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("_")
    }
}

/// What [`Facts`] holds. Both sets are persistent and shared with the facts of the functions
/// it holds, so a function around one does not copy them: the larger set is kept and the
/// smaller one added to it.
#[derive(Default)]
pub struct VarFacts {
    /// The class variables.
    pub classes: imbl::OrdSet<Arc<str>>,
    /// The other variables, with its own, bounded and held ones.
    pub names: imbl::OrdSet<Arc<str>>,
    /// The first `n` such that `names` lacks the `n`th variable name ([`super::var_name`]).
    pub free: usize,
}

impl VarFacts {
    /// Whether it holds the variable `v`.
    pub fn holds(&self, v: &str) -> bool {
        self.classes.contains(v) || self.names.contains(v)
    }

    /// The facts of the arrows and needs of `s`, worked out now; for a signature not yet
    /// held in a type, which may still change.
    pub fn of(s: &Sig) -> VarFacts {
        let mut g = VarFacts::default();
        for a in &s.arrows {
            a.params.iter().for_each(|p| g.ty(p));
            g.ty(&a.result);
        }
        for n in &s.needs {
            n.tys().for_each(|t| g.ty(t));
        }
        let extra = s.bounds.keys().chain(&s.own).chain(&s.held);
        extra.for_each(|v| add(&mut g.names, v));
        g.free = g.free.max(s.named);
        while g.names.contains(&*super::var_name(g.free)) {
            g.free += 1;
        }
        g
    }

    /// Adds the variables of `t`.
    fn ty(&mut self, t: &Ty) {
        for v in &t.vars {
            match super::class_id(v) {
                Some(_) => add(&mut self.classes, v),
                None => add(&mut self.names, v),
            }
        }
        for c in t.tuples.iter().flatten() {
            self.ty(c);
        }
        for s in t.payloads.values().flatten().flatten() {
            s.items.iter().for_each(|t| self.ty(t));
            s.fields.values().for_each(|t| self.ty(t));
        }
        for s in &t.fns {
            self.held(s.facts());
        }
    }

    /// Adds the facts of a function it holds: of each set, the larger is kept and the smaller
    /// one added to it, so each variable is copied O(log n) times over a nest of n.
    fn held(&mut self, f: &VarFacts) {
        merge(&mut self.classes, &f.classes);
        merge(&mut self.names, &f.names);
        self.free = self.free.max(f.free);
    }
}

/// Adds `other` to `set`, keeping the larger of the two and adding the smaller to it.
fn merge(set: &mut imbl::OrdSet<Arc<str>>, other: &imbl::OrdSet<Arc<str>>) {
    let small = match other.len() > set.len() {
        true => std::mem::replace(set, other.clone()),
        false => other.clone(),
    };
    for v in &small {
        add(set, v);
    }
}

/// Adds `v` to `set`. A set shared with the facts of another signature is copied along the
/// path to `v` by an insertion, so a variable it already holds is not inserted again.
fn add(set: &mut imbl::OrdSet<Arc<str>>, v: &Arc<str>) {
    if !set.contains(v) {
        set.insert(v.clone());
    }
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
        self.replace_in(binds, Mode::Replace)
    }

    /// [`Need::replace`], or as `mode` says.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Need {
        self.map_tys(|t| t.replace_in(binds, mode))
    }

    /// It with `f` applied to each of the types [`Need::tys`] gives.
    fn map_tys(&self, f: impl Fn(&Ty) -> Ty) -> Need {
        let all = |ts: &[Ty]| ts.iter().map(&f).collect();
        Need {
            on: f(&self.on),
            kind: match &self.kind {
                NeedKind::Component { i, key } => NeedKind::Component {
                    i: *i,
                    key: key.clone(),
                },
                NeedKind::Index(k) => NeedKind::Index(f(k)),
                NeedKind::Call {
                    what,
                    positional,
                    named,
                    curry,
                } => NeedKind::Call {
                    what: what.clone(),
                    positional: all(positional),
                    named: named.iter().map(|(n, t)| (n.clone(), f(t))).collect(),
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
            result: self.result.as_ref().map(&f),
            span: self.span,
        }
    }

    /// Every variable in it, in order of first appearance.
    pub fn vars_in(&self, out: &mut Vars) {
        self.tys().for_each(|t| t.vars_in(out));
    }

    /// The types in it that [`Need::replace`] replaces in, in order.
    pub fn tys(&self) -> impl Iterator<Item = &Ty> {
        let (index, positional, named): (_, &[Ty], &[(Arc<str>, Ty)]) = match &self.kind {
            NeedKind::Component { .. }
            | NeedKind::Data(_)
            | NeedKind::Into { .. }
            | NeedKind::Payload { .. } => (None, &[], &[]),
            NeedKind::Index(k) => (Some(k), &[], &[]),
            NeedKind::Call {
                positional, named, ..
            } => (None, positional, named),
        };
        std::iter::once(&self.on)
            .chain(index)
            .chain(positional)
            .chain(named.iter().map(|(_, t)| t))
            .chain(&self.result)
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

    /// Its place among the bases of [`zed_kernel::types::Split`].
    pub fn base(self) -> usize {
        match self {
            Carrier::Bool => 0,
            Carrier::Int => 1,
            Carrier::Rat => 2,
            Carrier::F64 => 3,
            Carrier::Str => 4,
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
    thread_local! {
        /// Made once, so that every use is one node and compares equal to another by pointer.
        static ATOMS: KType = {
            let carriers = Carrier::ALL.iter().fold(KType::empty(), |a, c| a | c.ty());
            KType::universe(Universe::Scalar) - &carriers
        };
    }
    ATOMS.with(KType::clone)
}

/// Every tuple and every struct, the kinds that `set` holds only as the kind-wide part.
pub fn wide() -> KType {
    &KType::universe(Universe::Tuple) | &KType::universe(Universe::Struct)
}

/// The kernel type of the tuple shape `cs`, when its components have kernel types.
fn shape_kernel(cs: &[Ty]) -> Option<KType> {
    cs.iter()
        .map(Ty::kernel)
        .collect::<Option<Vec<_>>>()
        .map(KType::tuple)
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
    Tuple(Row),
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
            Piece::Tuple(cs) => Ty::of_row(cs.clone()),
            Piece::Fn(s) => Ty::func(s.clone()),
            Piece::Var(v) => Ty::var(v.clone()),
            Piece::Dyn => Ty::dynamic(),
        }
    }
}

/// The binding of type variables made while applying an arrow.
pub type Binds = BTreeMap<Arc<str>, Ty>;

/// How a comparison reads a variable of the types on one side ([`Env`]).
#[derive(Clone, Debug, PartialEq)]
enum Read {
    /// As the rigid variable of this name, in [`Cx::rigid`].
    Rigid(Arc<str>),
    /// As every value of the carriers of the mask, [`Ty::of_mask`].
    Mask(u8),
}

/// The variables of the function types around one side of a comparison that it reads as
/// something else: the own bounded variables of each expected function type around it, and
/// those of each given one that no parameter holds. Persistent, so that each function met
/// keeps the reading of its own side at the cost of a pointer.
type Env = imbl::OrdMap<Arc<str>, Read>;

/// The type a class variable the checker solved stands for, if it was solved to one that
/// holds no variable: a signature solved before the functions around it keeps such a
/// variable in the functions it holds, and is read through this (CHK-carrier).
pub type Solve<'s> = &'s dyn Fn(&str) -> Option<Ty>;

/// How the modes of [`Ty::replace_in`] replace.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// At every depth: [`Ty::replace`].
    Replace,
    /// At every depth, the own variables of functions too: [`Ty::renamed`].
    Rename,
    /// Outside functions: [`Ty::replace_outside`].
    Outside,
}

/// The state of one comparison of function types ([`fits_sig`], [`Ty::sub`]).
#[derive(Default)]
struct Cx<'s> {
    /// The bounded variables of the expected function types the comparison is inside, each
    /// with the mask of its bound: the caller of such a function picks one carrier of the
    /// bound for each, so a variable here stands for every carrier of its mask and is never
    /// bound.
    rigid: BTreeMap<Arc<str>, u8>,
    /// The functions of the types being compared, each put in its type as a variable of its
    /// own and kept here with the reading of its side: a function moved into the other side,
    /// as a binding of a variable there, is read as it was where it came from.
    fns: BTreeMap<Arc<str>, (Arc<Sig>, Env)>,
    /// The names of `rigid` and `fns` made by the comparisons open now, last made last.
    made: Vec<Arc<str>>,
    /// The number of names made: a quote is in no name a program writes, and the count keeps
    /// the names apart.
    count: usize,
    /// The types of the solved class variables, read where a function's arrows are read.
    solve: Option<Solve<'s>>,
    /// When asked for, by [`why_unfit`], why the outermost comparison failed, if one of the
    /// covers rule 6 of sec:type_resolution gives is refused there: `Some(None)` until it is
    /// found. Only the outermost [`fits_in`] reads it, so a comparison inside, tried and
    /// dropped, gives no reason.
    why: Option<Option<String>>,
}

impl Cx<'_> {
    /// A new name, from `v`.
    fn fresh(&mut self, v: &str) -> Arc<str> {
        self.count += 1;
        let w: Arc<str> = format!("{v}'{}", self.count).into();
        self.made.push(w.clone());
        w
    }

    /// `t` as the comparison reads it on a side read by `env`: each variable `env` maps
    /// replaced, and each function, outside other functions, replaced by a new variable that
    /// `fns` maps to it and `env`. The payloads stay as they are, since no comparison reads
    /// them. The cost is that of `t` outside its functions, so each function type is read once
    /// for each comparison of it. A class variable `solve` gives a type is read as that type.
    fn read(&mut self, t: &Ty, env: &Env) -> Ty {
        let mut out = Ty {
            set: t.set.clone(),
            tuples: t
                .tuples
                .iter()
                .map(|cs| cs.iter().map(|c| self.read(c, env)).collect())
                .collect(),
            fns: Vec::new(),
            vars: BTreeSet::new(),
            dynamic: t.dynamic,
            family: t.family.clone(),
            payloads: t.payloads.clone(),
        };
        for s in &t.fns {
            let w = self.fresh("");
            self.fns.insert(w.clone(), (s.clone(), env.clone()));
            out.vars.insert(w);
        }
        let mut solved = Vec::new();
        for v in &t.vars {
            match env.get(v) {
                None => match self.solve.and_then(|f| f(v)) {
                    Some(u) => solved.push(u),
                    None => {
                        out.vars.insert(v.clone());
                    }
                },
                Some(Read::Rigid(w)) => {
                    out.vars.insert(w.clone());
                }
                Some(&Read::Mask(m)) if m & OTHER != 0 => out.dynamic = true,
                Some(&Read::Mask(m)) => {
                    out.set = Carrier::of_mask(m).fold(out.set, |s, c| &s | &c.ty());
                }
            }
        }
        solved.iter().fold(out, |o, u| o.union(u))
    }

    /// Forgets the names made since `mark`.
    fn forget(&mut self, mark: usize) {
        for w in self.made.drain(mark..) {
            self.rigid.remove(&w);
            self.fns.remove(&w);
        }
    }
}

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

    /// The values of `s`: scalars, atoms, and a kind-wide part.
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
        Ty::of_row(Row::new(cs))
    }

    /// The tuple shape of `row`.
    pub fn of_row(row: Row) -> Ty {
        Ty {
            tuples: vec![row],
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
        let have: HashSet<&Row> = self.tuples.iter().collect();
        let new: Vec<&Row> = other.tuples.iter().filter(|t| !have.contains(t)).collect();
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
        // A set that holds no atom loses none.
        let set = match self.set.may_hold_atoms() {
            true => &(&self.set - &atoms()) | &(&self.set & &self.family),
            false => self.set.clone(),
        };
        let mut out = Ty {
            set,
            ..self.clone()
        };
        out.prune_payloads();
        out
    }

    /// It without the atoms `k`, as a call passes them by (rule 6 of sec:type_resolution).
    pub fn without(&self, k: &KType) -> Ty {
        let mut out = Ty {
            set: &self.set - k,
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

    /// Its pieces: the scalars split by carrier, then the atoms, the other scalars, the
    /// kind-wide part, the tuples, the functions, the variables and the unknown.
    pub fn pieces(&self) -> Vec<Piece> {
        let mut out = Vec::new();
        let mut split = self.set.split();
        for c in Carrier::ALL {
            out.extend(split.bases[c.base()].take().map(Piece::Set));
        }
        out.extend(split.atoms.map(Piece::Set));
        // The kind-wide part follows the other scalars, as its own piece.
        if let Some(rest) = split.rest {
            let w = &rest & &wide();
            let rest = &rest - &w;
            if !rest.is_empty() {
                out.push(Piece::Set(rest));
            }
            if !w.is_empty() {
                out.push(Piece::Set(w));
            }
        }
        out.extend(self.tuples.iter().cloned().map(Piece::Tuple));
        out.extend(self.fns.iter().cloned().map(Piece::Fn));
        out.extend(self.vars.iter().cloned().map(Piece::Var));
        if self.dynamic {
            out.push(Piece::Dyn);
        }
        out
    }

    /// The numeric carrier a literal adopts where a value of this type is expected: the one
    /// carrier its numbers are of, when it holds numbers of one carrier and no variable or
    /// unknown, which could stand for numbers of another. Its other members (atoms, strings,
    /// booleans, tuples, functions) do not count, so `1` at `f64 | String` is `1.0`; a type
    /// with numbers of two carriers, as `f64 | rat`, gives none: there a literal keeps its own
    /// carrier when the type holds it and is an error otherwise (`check::carriers_in`; DESIGN.md
    /// L1.26: the carrier "an operator or a parameter expects").
    pub fn numeric_carrier(&self) -> Option<Carrier> {
        if !self.vars.is_empty() || self.dynamic {
            return None;
        }
        // Its numbers are those of one numeric carrier: read off one split, where a meet and
        // a subtype test per carrier would build each part anew.
        let s = self.set.split();
        let mut present = [Carrier::Int, Carrier::Rat, Carrier::F64]
            .into_iter()
            .filter(|c| s.bases[c.base()].is_some());
        match (present.next(), present.next()) {
            (Some(c), None) => Some(c),
            _ => None,
        }
    }

    /// Whether it holds no variable and no unknown, at any depth.
    pub fn closed(&self) -> bool {
        self.vars.is_empty() && !self.dynamic && self.tuples.iter().all(|r| !r.open())
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
            .or_else(|| self.tuples.iter().find_map(|r| r.0.held.as_ref()))
    }

    /// Whether every value of `self` is in `other`, binding `other`'s variables as needed.
    pub fn sub(&self, other: &Ty, binds: &mut Binds) -> bool {
        self.sub_in(other, binds, &mut Cx::default())
    }

    /// [`Self::sub`], each class variable `solve` gives a type read as that type inside the
    /// functions compared.
    pub fn sub_with(&self, other: &Ty, binds: &mut Binds, solve: Solve) -> bool {
        let mut cx = Cx {
            solve: Some(solve),
            ..Cx::default()
        };
        self.sub_in(other, binds, &mut cx)
    }

    /// [`Self::subtype`], read as [`Self::sub_with`] reads.
    pub fn subtype_with(&self, other: &Ty, solve: Solve) -> bool {
        let mut b = Binds::new();
        self.sub_with(other, &mut b, solve) && b.is_empty()
    }

    /// [`Self::sub`] inside the comparisons of function types `cx` holds.
    fn sub_in(&self, other: &Ty, binds: &mut Binds, cx: &mut Cx) -> bool {
        // `other` as a kernel type, built at most once, when a tuple piece needs it.
        let mut whole: Option<Option<KType>> = None;
        self.pieces().iter().all(|p| {
            // A tuple piece of a type with no variable, function or unknown is decided by the
            // kernel, which sees shapes that hold it only together. Trying each shape in turn
            // costs every shape times the components; the kernel splits the components once.
            // The rule of one shape is sound, so it is tried only when the kernel refused.
            // So is a kind-wide part, which tuple shapes of `other` may hold only together.
            let a = match p {
                Piece::Tuple(cs) => shape_kernel(cs),
                Piece::Set(s) if !(s & &wide()).is_empty() => Some(s.clone()),
                _ => None,
            };
            let decided = a.and_then(|a| {
                let b = whole.get_or_insert_with(|| other.kernel()).as_ref()?;
                match a.subtype_verdict(b) {
                    Verdict::Empty => Some(true),
                    Verdict::Inhabited => Some(false),
                    Verdict::Refused(_) => None,
                }
            });
            decided.unwrap_or_else(|| accepts(other, p, self, binds, cx))
        })
    }

    /// [`Self::sub_in`] with each tuple piece held by one tuple shape of `other`: the rule for
    /// the components of a tuple, whose joint check is the kernel's on the whole tuple.
    fn sub_by_shape(&self, other: &Ty, binds: &mut Binds, cx: &mut Cx) -> bool {
        self.pieces()
            .iter()
            .all(|p| accepts(other, p, self, binds, cx))
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
    /// was refused, or, for a function, the clause that names the cover of rule 6 the checker
    /// refuses ([`why_unfit`]), and nothing if it was decided. A refusal claims nothing about
    /// the types, so a message that reads as a counterexample would be wrong.
    pub fn refused(&self, other: &Ty) -> String {
        match self.verdict(other) {
            Verdict::Refused(r) => format!(" (not decided: {})", r.message()),
            // A function that a cover the checker refuses would take ([`why_unfit`]).
            _ => self
                .fns
                .iter()
                .find_map(|s| other.fns.iter().find_map(|q| why_unfit(s, q)))
                .map_or_else(String::new, |why| format!(": {why}")),
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
                        met.push(Row::new(cs));
                    }
                }
            }
        }
        // A kind-wide part of one side keeps the other's shapes it holds whole; of a shape it
        // holds in part, the part goes to the set, where the kernel holds it exactly. A shape
        // with no kernel type is kept, which may be more than the meet.
        for (a, b) in [(self, t), (t, self)] {
            let w = &b.set & &wide();
            if w.is_empty() {
                continue;
            }
            for cs in &a.tuples {
                match shape_kernel(cs) {
                    Some(k) if k.subtype(&w) => met.push(cs.clone()),
                    Some(k) => out.set = &out.set | &(&k & &w),
                    None => met.push(cs.clone()),
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

    /// What of `self` is not in `t`, as `is not` narrows: scalars are subtracted, and so is
    /// all of `t` from the kind-wide part when `t` has a kernel type; tuples wholly inside `t`
    /// are dropped, a tuple that `t`'s kind-wide part holds in part leaves its rest in the set,
    /// and the other tuples are kept.
    pub fn diff(&self, t: &Ty) -> Ty {
        self.diff_in(t, None)
    }

    /// [`Self::diff`], a tuple compared with `t` as [`Self::sub_with`] compares: each class
    /// variable `solve` gives a type read as that type inside the functions it holds.
    pub fn diff_with(&self, t: &Ty, solve: Solve) -> Ty {
        self.diff_in(t, Some(solve))
    }

    /// [`Self::diff`], with the resolver of the comparisons, if any.
    fn diff_in(&self, t: &Ty, solve: Option<Solve>) -> Ty {
        let tk = t.kernel();
        let mut out = self.clone();
        out.set = &self.set - tk.as_ref().unwrap_or(&t.set);
        out.family = &self.family - &t.set;
        out.prune_payloads();
        let w = &t.set & &wide();
        let within = Ty {
            set: w.clone(),
            ..t.clone()
        };
        let mut rest = Vec::new();
        out.tuples.retain(|a| {
            let row = Ty::of_row(a.clone());
            let inside = match solve {
                Some(solve) => row.subtype_with(&within, solve),
                None => row.subtype(&within),
            };
            if inside {
                return false;
            }
            match (&tk, shape_kernel(a)) {
                (Some(tk), Some(k)) if !(&k & &w).is_empty() => {
                    rest.push(&k - tk);
                    false
                }
                _ => true,
            }
        });
        out.set = KType::union_all(std::iter::once(out.set).chain(rest));
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
        self.replace_in(binds, Mode::Replace)
    }

    /// `self` with the variables `names` gives other names, at every depth, inside the
    /// functions it holds too, their own variables among them: each value of `names` is one
    /// variable, and no two keys share one.
    pub fn renamed(&self, names: &Binds) -> Ty {
        self.replace_in(names, Mode::Rename)
    }

    /// `self` with its variables replaced by `binds` outside the functions it holds: the
    /// functions are kept as they are, and so is a tuple that holds no variable outside them.
    pub fn replace_outside(&self, binds: &Binds) -> Ty {
        self.replace_in(binds, Mode::Outside)
    }

    /// [`Ty::replace`], or as `mode` says.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Ty {
        // A type with no tuple, function or payload holds only its own variables; outside
        // functions, one with no tuple or payload does.
        let fns = !self.fns.is_empty() && mode != Mode::Outside;
        let leaf = self.tuples.is_empty() && !fns && self.payloads.is_empty();
        if binds.is_empty() || (leaf && !self.vars.iter().any(|v| binds.contains_key(v))) {
            return self.clone();
        }
        let mut out = Ty {
            set: self.set.clone(),
            tuples: self
                .tuples
                .iter()
                .map(|cs| match mode {
                    Mode::Outside if !cs.open() => cs.clone(),
                    _ => cs.iter().map(|c| c.replace_in(binds, mode)).collect(),
                })
                .collect(),
            fns: self
                .fns
                .iter()
                .map(|s| match s.own.iter().any(|v| binds.contains_key(v)) {
                    _ if mode == Mode::Outside => s.clone(),
                    _ if mode == Mode::Rename => Arc::new(s.replace_in(binds, mode)),
                    // A signature that holds none of the variables replaced is kept whole.
                    _ if !binds
                        .keys()
                        .any(|v| !s.own.contains(v) && s.facts().holds(v)) =>
                    {
                        s.clone()
                    }
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
            payloads: self.map_payloads(|t| t.replace_in(binds, mode)),
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

    /// It with each class variable `solve` gives a type replaced by that type at every depth,
    /// each signature it holds settled once ([`Sig::settle`]). A tuple that holds no variable
    /// and no function is kept whole.
    pub fn settle(&self, solve: Solve) -> Ty {
        let mut out = Ty {
            set: self.set.clone(),
            tuples: (self.tuples.iter())
                .map(|r| match r.open() || r.0.held.is_some() {
                    true => r.iter().map(|c| c.settle(solve)).collect(),
                    false => r.clone(),
                })
                .collect(),
            fns: self.fns.iter().map(|s| s.settle(solve)).collect(),
            vars: BTreeSet::new(),
            dynamic: self.dynamic,
            family: self.family.clone(),
            payloads: self.map_payloads(|t| t.settle(solve)),
        };
        for v in &self.vars {
            match solve(v) {
                Some(t) => out = out.union(&t),
                None => {
                    out.vars.insert(v.clone());
                }
            }
        }
        out
    }

    /// Every variable in it outside the functions it holds, in order of first appearance: a
    /// tuple that holds none there is not entered.
    pub fn vars_outside(&self, out: &mut Vars) {
        for v in &self.vars {
            if out.seen.insert(v.clone()) {
                out.order.push(v.clone());
            }
        }
        for c in self.tuples.iter().filter(|r| r.open()).flatten() {
            c.vars_outside(out);
        }
        for s in self.payloads.values().flatten().flatten() {
            s.items.iter().for_each(|t| t.vars_outside(out));
            s.fields.values().for_each(|t| t.vars_outside(out));
        }
    }

    /// Whether the value `v` is in it; a variable or the unknown holds every value.
    pub fn contains(&self, v: &Value) -> bool {
        if self.dynamic || !self.vars.is_empty() {
            return true;
        }
        match v {
            Value::Tuple(items) => {
                self.set.contains(v)
                    || self.tuples.iter().any(|cs| {
                        cs.len() == items.len() && cs.iter().zip(items).all(|(c, x)| c.contains(x))
                    })
            }
            Value::Family(_) => self.fns.iter().any(|s| s.data),
            Value::Path(_) => !self.fns.is_empty() || self.set.contains(v),
            _ => self.set.contains(v),
        }
    }

    /// Whether `self` and `other` may share a value.
    pub fn meets(&self, other: &Ty) -> bool {
        if !self.closed() || !other.closed() {
            return true;
        }
        // A shape meets the other side's kind-wide part when the kernel finds a common value;
        // a shape with no kernel type may.
        let wide_meets = |a: &Ty, b: &Ty| {
            let w = &b.set & &wide();
            !w.is_empty()
                && a.tuples
                    .iter()
                    .any(|cs| shape_kernel(cs).is_none_or(|k| !(&k & &w).is_empty()))
        };
        !(&self.set & &other.set).is_empty()
            || wide_meets(self, other)
            || wide_meets(other, self)
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
/// of `t` holds it. A variable of `cx.rigid` stands for each carrier of its mask in turn: as
/// `p`, `t` must hold each; in `t`, it holds what each carrier, with the rest of `t`, holds. A
/// variable of `cx.fns` is the function it stands for.
fn accepts(t: &Ty, p: &Piece, of: &Ty, binds: &mut Binds, cx: &mut Cx) -> bool {
    if t.dynamic {
        return true;
    }
    let ok = match p {
        Piece::Dyn => false,
        Piece::Set(s) => {
            s.subtype(&t.set)
                || t.vars.iter().any(|w| {
                    cx.rigid.get(w).is_some_and(|&m| {
                        Carrier::of_mask(m).all(|c| s.subtype(&(&t.set | &c.ty())))
                    })
                })
        }
        // A kind-wide part that holds every tuple of the length holds it, whatever it holds.
        Piece::Tuple(cs) if KType::tuple(vec![KType::top(); cs.len()]).subtype(&t.set) => true,
        Piece::Tuple(cs) => t.tuples.iter().any(|ds| {
            ds.len() == cs.len() && {
                let mut b = binds.clone();
                let ok = cs
                    .iter()
                    .zip(ds)
                    .all(|(c, d)| c.sub_by_shape(d, &mut b, cx));
                if ok {
                    *binds = b;
                }
                ok
            }
        }),
        // A type outside every comparison of function types holds its functions as written.
        Piece::Fn(s) => t
            .fns
            .iter()
            .any(|q| fits_in(s, &Env::new(), q, &Env::new(), cx)),
        Piece::Var(v) => match cx.fns.get(v).cloned() {
            Some((s, se)) => t.vars.iter().any(|w| match cx.fns.get(w).cloned() {
                Some((q, qe)) => fits_in(&s, &se, &q, &qe, cx),
                None => false,
            }),
            None => {
                t.vars.contains(v)
                    || cx
                        .rigid
                        .get(v)
                        .is_some_and(|&m| Carrier::of_mask(m).all(|c| c.ty().subtype(&t.set)))
            }
        },
    };
    if ok {
        return true;
    }
    match t
        .vars
        .iter()
        .find(|v| !cx.rigid.contains_key(*v) && !cx.fns.contains_key(*v))
    {
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
/// returns within its result, or arrows of `s` that do so together ([`covered`]).
pub fn fits_sig(s: &Sig, q: &Sig) -> bool {
    fits_in(s, &Env::new(), q, &Env::new(), &mut Cx::default())
}

/// [`fits_sig`], read as [`Ty::sub_with`] reads.
pub fn fits_sig_with(s: &Sig, q: &Sig, solve: Solve) -> bool {
    let mut cx = Cx {
        solve: Some(solve),
        ..Cx::default()
    };
    fits_in(s, &Env::new(), q, &Env::new(), &mut cx)
}

/// [`fits_sig`] inside the expected function types whose bounded variables `cx.rigid` holds,
/// `s` read by `se` and `q` by `qe`. `q`'s own bounded variables that a parameter holds join
/// `cx.rigid`: the caller of a function of type `q` picks one carrier of each bound, so `s`
/// must take every carrier of it. Each gets a new name, since `s` may use the same name for a
/// variable of its own. A bounded variable no parameter holds, of `q` or of `s`, is fixed by
/// no argument, so it stands for any carrier of its bound, as at a call ([`Sig::unheld`]).
///
/// The two sides are read through their environments, not rewritten: rewriting `q` at each
/// depth cost the size of `q` at each, the square of the depth for a function type nested
/// that deep. Each depth now costs its own parameters and bounds, and a lookup for each
/// variable (COMPLEXITY.md F60).
fn fits_in(s: &Sig, se: &Env, q: &Sig, qe: &Env, cx: &mut Cx) -> bool {
    let explain = cx.why.take().is_some();
    if !s.needs.is_empty() {
        // Compared as written: the same signature, each variable read alike on both sides,
        // each solved class variable read as its type at every depth. That walk costs what
        // the comparison of the two as written costs.
        let solved;
        let (s, q) = match cx.solve {
            Some(f) => {
                solved = (s.solved_with(f), q.solved_with(f));
                (&solved.0, &solved.1)
            }
            None => (s, q),
        };
        if s != q {
            return false;
        }
        let mut vs = Vars::default();
        for a in &s.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut vs));
            a.result.vars_in(&mut vs);
        }
        s.needs.iter().for_each(|n| n.vars_in(&mut vs));
        return vs.order.iter().all(|v| se.get(v) == qe.get(v));
    }
    let same_params = s.params.len() == q.params.len()
        && s.params
            .iter()
            .zip(&q.params)
            .all(|(a, b)| a.positional == b.positional && (a.positional || a.name == b.name));
    if !same_params {
        return false;
    }
    let mark = cx.made.len();
    // Each own variable names its own binder here, so the reading of the same name around it
    // is dropped, or replaced as above.
    let mut qe = qe.clone();
    for v in &q.own {
        match q.bounds.get(v) {
            Some(&m) if q.held.contains(v) => {
                let w = cx.fresh(v);
                cx.rigid.insert(w.clone(), m);
                qe.insert(v.clone(), Read::Rigid(w));
            }
            Some(&m) => {
                qe.insert(v.clone(), Read::Mask(m));
            }
            None => {
                qe.remove(v);
            }
        }
    }
    let mut se = se.clone();
    for v in &s.own {
        match s.bounds.get(v) {
            Some(&m) if !s.held.contains(v) => {
                se.insert(v.clone(), Read::Mask(m));
            }
            _ => {
                se.remove(v);
            }
        }
    }
    let read = |a: &Arrow, env: &Env, cx: &mut Cx| Arrow {
        params: a.params.iter().map(|p| cx.read(p, env)).collect(),
        result: cx.read(&a.result, env),
    };
    let sas: Vec<Arrow> = s.arrows.iter().map(|a| read(a, &se, cx)).collect();
    let qas: Vec<Arrow> = q.arrows.iter().map(|a| read(a, &qe, cx)).collect();
    let fits = every_arrow_fits(s, &sas, &qas, cx);
    if explain && !fits {
        // The first arrow of `q` not covered, compared again alone: only on the way to an
        // error, at the cost of one more comparison of each arrow of `q`.
        let k =
            (0..qas.len()).find(|&k| !every_arrow_fits(s, &sas, std::slice::from_ref(&qas[k]), cx));
        cx.why = Some(k.and_then(|k| refused_cover(s, q, &sas, &qas[k], k, cx)));
    }
    cx.forget(mark);
    fits
}

/// Why a function of signature `s` is not a function of signature `q`, when the cover of an
/// arrow of `q` that rule 6 of sec:type_resolution may give is one the checker refuses
/// ([`refused_cover`]): the clause a message adds after what it rejects. `None` when `s`
/// fits, or does not for a plain reason, a value no arrow takes or a result outside.
pub fn why_unfit(s: &Sig, q: &Sig) -> Option<String> {
    why_unfit_in(s, q, Cx::default())
}

/// [`why_unfit`], read as [`fits_sig_with`] reads.
pub fn why_unfit_with(s: &Sig, q: &Sig, solve: Solve) -> Option<String> {
    why_unfit_in(
        s,
        q,
        Cx {
            solve: Some(solve),
            ..Cx::default()
        },
    )
}

fn why_unfit_in(s: &Sig, q: &Sig, mut cx: Cx) -> Option<String> {
    cx.why = Some(None);
    if fits_in(s, &Env::new(), q, &Env::new(), &mut cx) {
        return None;
    }
    cx.why.flatten()
}

#[cfg(test)]
thread_local! {
    /// How [`every_arrow_fits`] decides, when not by the index: the forms the differential
    /// tests compare the index with.
    static REFERENCE: std::cell::Cell<tests::Reference> =
        const { std::cell::Cell::new(tests::Reference::None) };
}

/// Whether each arrow `qa` of `qas`, those of `q` as read, is covered by arrows of `sas`, those
/// of `s` as read: by one arrow that takes its parameters and returns within its result
/// ([`arrow_fits`]), or, at one parameter `j`, by arrows whose parameter types there together
/// hold `qa`'s, each taking `qa`'s other parameters and returning within its result
/// ([`covered`]). Rule 6 of sec:type_resolution types an application region by region, so a
/// call of `qa` at any value of its parameters reaches an arrow of `s` that returns within
/// `qa`'s result.
fn every_arrow_fits(s: &Sig, sas: &[Arrow], qas: &[Arrow], cx: &mut Cx) -> bool {
    #[cfg(test)]
    if REFERENCE.get() != tests::Reference::None {
        return tests::reference(s, sas, qas, cx);
    }
    // Each arrow of `q` is tried first on an arrow of `s` equal to it, found by hash, so that
    // an overload passed where the same overload is expected costs one comparison per arrow.
    let mut equal: HashMap<&Arrow, &Arrow> = HashMap::with_capacity(sas.len());
    for sa in sas {
        equal.entry(sa).or_insert(sa);
    }
    // Then on the arrows of `s` the index leaves, in order, until one fits: the arrows whose
    // parameter types offer, at each parameter, each carrier and bare atom that `qa`'s holds,
    // and those whose parameter type there is open, and whose result types need no key that
    // `qa`'s closed result does not offer. An arrow it leaves out does not fit, so the verdict
    // is that of trying every arrow of `s`. The index is built at the first arrow of `q` that
    // no arrow of `s` equals, in the size of the parameter and result types of `s`.
    //
    // Complexity tradeoff: none is given up for one arrow, every arrow of `q` gets the verdict
    // of comparing it with every arrow of `s`, but the comparisons are bounded by the
    // candidates, not below n·m in the worst case: the candidates come from the shortest of
    // the lists, by parameter key or by result key, and an arrow of `s` that offers every key
    // `qa` needs at each parameter and in its result and does not fit, or is open there, is
    // still compared. So `s` and `q` of n arrows that all share one parameter piece and one
    // result piece, and differ in pieces of both, cost n^2/2 comparisons; arrows that share a
    // parameter piece and differ in their results cost n (scaling test
    // l01_26_type_resolution::scaling::passing_an_overload_whose_arrows_share_a_parameter_piece_scales;
    // COMPLEXITY.md F82). A tuple, a kind-wide part, a payload-only atom or a cofinite set of
    // atoms in `qa`'s parameter needs no key, since a parameter type may hold it without
    // offering one piece of it; a result that is open (a variable, the unknown, a cofinite set
    // of atoms) filters nothing. Why no complete bound: the question "each arrow of `q` has an
    // arrow of `s` whose parameters hold its parameters and whose result its result holds" is
    // a containment join between two families of sets, quantified for all and then exists;
    // with parameter and result types unions of many distinct members it is the complement of
    // Hitting Set, for which no n^(2-e) algorithm is expected (Abboud, Vassilevska Williams and
    // Wang, SODA 2016, the Hitting Set conjecture; a conjecture, not a theorem).
    let mut index: Option<ArrowIndex> = None;
    qas.iter().all(|qa| {
        if equal.get(qa).is_some_and(|sa| arrow_fits(s, sa, qa, cx)) {
            return true;
        }
        let index = index.get_or_insert_with(|| ArrowIndex::new(sas, s.params.len()));
        index.first(qa, |i| arrow_fits(s, &sas[i], qa, cx)) || covered(s, sas, index, qa, cx)
    })
}

/// Why the arrow `qa` of `q`, its `k`th, as read, is covered neither by one arrow of `s`, of
/// `sas` as read, nor by its arrows together ([`covered`]), when the reason is a cover the
/// checker refuses, though rule 6 of sec:type_resolution may give it: the clause a message
/// adds. In order: an arrow that takes `qa`'s parameters only with a bounded variable bound
/// to values of several carriers that it does not stand for alone ([`one_place`]); an arrow
/// that would take part only by binding a variable ([`binds_nothing`], case (2) of
/// [`covered`]); two or more arrows that take parts and return outside `qa`'s result, whose
/// intersection the checker does not build (case (3)); an arrow that takes values at every
/// parameter but misses more than one (case (1)). `None` for a plain reason: a value no arrow
/// takes, or one arrow that returns outside. One pass over the arrows, on the way to an error.
fn refused_cover(
    s: &Sig,
    q: &Sig,
    sas: &[Arrow],
    qa: &Arrow,
    k: usize,
    cx: &mut Cx,
) -> Option<String> {
    let mut shared = None;
    let mut free = None;
    let mut outside = Vec::new();
    let mut split = None;
    for (i, sa) in sas.iter().enumerate() {
        let mut b = Binds::new();
        let mut miss = Vec::new();
        for (j, (x, y)) in qa.params.iter().zip(&sa.params).enumerate() {
            if !x.sub_in(y, &mut b, cx) {
                miss.push(j);
            }
        }
        // An arrow that takes no value of `qa` at some parameter takes no part.
        if !miss.iter().all(|&j| qa.params[j].meets(&sa.params[j])) {
            continue;
        }
        match miss[..] {
            [_, _, ..] => {
                split.get_or_insert(i);
            }
            [j] if !binds_nothing(&sa.params[j], cx) => {
                free.get_or_insert((i, j));
            }
            _ if !bounds_hold(s, sa, &b, cx) => {
                let several = s
                    .bounds
                    .keys()
                    .filter_map(|v| Some((v, b.get(v)?)))
                    .find(|(v, t)| !one_carrier(t) && !one_place(sa, v, cx));
                if let Some((v, t)) = several {
                    shared.get_or_insert((i, v.clone(), t.clone(), Places::of(sa, v, cx)));
                }
            }
            _ if !result_within(sa, qa, &b, cx) => {
                outside.push((i, miss.is_empty().then(|| sa.result.subst(&b))));
            }
            _ => {}
        }
    }
    let slot = arrow_text(q, &q.arrows[k]);
    let result = text_at(&q.arrows[k].result, q, cx);
    let reason = if let Some((i, v, t, places)) = shared {
        let place = match places {
            Places { taken: 1.., .. } => format!(
                "`{v}` stands where the arrow takes values of it inside a function type, which \
                 need not be of the carrier its argument fixes"
            ),
            Places { given: 0, .. } => format!(
                "no argument gives values of `{v}` outside a function type, so none fixes its \
                 carrier"
            ),
            Places { given, .. } => format!(
                "`{v}` stands at {given} places the arguments give, which could be given values \
                 of two carriers"
            ),
        };
        format!(
            "the arrow `{}` takes it only with `{v}` bound to `{}`, values of more than one \
             carrier, but a call fixes `{v}` to one carrier, and {place}",
            arrow_text(s, &s.arrows[i]),
            text_at(&t, q, cx)
        )
    } else if let Some((i, j)) = free {
        format!(
            "the arrow `{}` would take part of `{}` only by binding its type variable there, \
             and arrows that cover a parameter together bind no variable: which part each \
             takes is a choice per arrow, and fixing a bounded variable to each carrier of \
             its bound multiplies the arrows by the product of the bounds",
            arrow_text(s, &s.arrows[i]),
            s.params[j].name
        )
    } else if outside.len() >= 2 {
        let arrows: Vec<String> = outside
            .iter()
            .map(|&(i, _)| format!("`{}`", arrow_text(s, &s.arrows[i])))
            .collect();
        // When each takes all of `qa`, the intersection is the result at every value: a plain
        // reason, not a refused cover, with the intersection when the results have kernel types.
        let whole: Option<Vec<&Ty>> = outside.iter().map(|(_, r)| r.as_ref()).collect();
        if let Some(whole) = whole {
            let kernels: Option<Vec<KType>> = whole.iter().map(|r| r.kernel()).collect();
            let meet = match kernels.and_then(|ks| ks.into_iter().reduce(|a, b| &a & &b)) {
                Some(k) => format!(", `{}`,", Ty::set(k)),
                // Not built value by value ([`meet_within`]): the message says how.
                None => ", as the checker builds it (a piece of a result that holds a function, \
                          a variable or the unknown is left out only where another result \
                          holds none of its carriers, or no function),"
                    .into(),
            };
            return Some(format!(
                "at `{slot}`, the arrows {} each take all of it, and the intersection of their \
                 results{meet} is not within `{result}` (rule 6 of sec:type_resolution)",
                arrows.join(", "),
            ));
        }
        format!(
            "the arrows {} each return outside `{result}`; where several take one value, the \
             intersection of their results is the result, and the checker builds it only from \
             arrows that each take all that the arrows returning within `{result}` leave of one \
             parameter, since finding the values each set of arrows shares is as hard as \
             Orthogonal Vectors",
            arrows.join(", ")
        )
    } else {
        let i = split?;
        format!(
            "the arrow `{}` takes a part of more than one parameter, and arrows are combined \
             only when they differ at one parameter: whether arrows that split several \
             parameters cover them is coNP-complete",
            arrow_text(s, &s.arrows[i])
        )
    };
    Some(format!(
        "at `{slot}`, {reason} (rule 6 of sec:type_resolution)"
    ))
}

/// `t` as a message about a comparison with `q` prints it: the variables `q` bounds by
/// carriers by their names, and the rigid variables made from them ([`Cx::fresh`]) by the
/// names they were made from, not as `_`. Only on the way to an error.
fn text_at(t: &Ty, q: &Sig, cx: &Cx) -> String {
    let carriers = |v: &str| q.bounds.get(v).is_some_and(|&m| m & OTHER == 0);
    let own = (q.bounds.keys())
        .filter(|v| carriers(v))
        .map(|v| (v.clone(), v.clone()));
    let rigid = cx.rigid.keys().filter_map(|w| {
        let (v, _) = w.rsplit_once('\'')?;
        carriers(v).then(|| (w.clone(), Arc::from(v)))
    });
    let mut scope = Scope::default();
    for (v, name) in own.chain(rigid) {
        scope.printed.insert(name.clone());
        scope.names.entry(v).or_default().push(Some(name));
    }
    let mut out = String::new();
    t.write(&mut out, &mut scope);
    out
}

/// The arrow `a` of `s`, as a function type of one arrow is written, with the bounds of the
/// variables it holds: at the cost of `a`, not of the other arrows of `s` (a message names each
/// arrow of an overload of `n`).
fn arrow_text(s: &Sig, a: &Arrow) -> String {
    let mut vs = Vars::default();
    a.params.iter().for_each(|p| p.vars_in(&mut vs));
    a.result.vars_in(&mut vs);
    let mut one = Sig {
        params: s.params.clone(),
        arrows: vec![a.clone()],
        bounds: (vs.order.iter())
            .filter_map(|v| Some((v.clone(), *s.bounds.get(v)?)))
            .collect(),
        data: s.data,
        needs: Vec::new(),
        own: vs
            .order
            .iter()
            .filter(|v| s.own.contains(*v))
            .cloned()
            .collect(),
        held: BTreeSet::new(),
        named: s.named,
        facts: Facts::default(),
    };
    one.note_held();
    Ty::func(Arc::new(one)).to_string()
}

/// Whether arrows of `sas` together cover `qa`, as rule 6 of sec:type_resolution types a call:
/// at each value of `qa`'s parameters, the arrows that take it are not none, and the
/// intersection of their results is within `qa`'s result. Two forms are built, each from the
/// candidates of the index ([`ArrowIndex::covering`]), each arrow compared once, its
/// parameters in one pass ([`part_of`]), so the cost is linear in the width, not its square.
///
/// By union: at some parameter `j`, the arrows that take `qa`'s other parameters and return
/// within its result together hold `qa`'s parameter type at `j`. Each value reaches one of
/// them, which gives a result within `qa`'s, whatever other arrows it reaches.
///
/// By intersection ([`met`]): the arrows that return within `qa`'s result take a part of
/// `qa`'s parameter at `j`, and every arrow of a set `H` takes all that they leave (or all of
/// `qa`'s parameters), and the intersection of the results of `H` is within `qa`'s. A value
/// outside the part reaches every arrow of `H`, so its result is within that intersection.
///
/// A parameter type at `j` that would bind a variable takes part in neither: one that holds a
/// type variable of `s` at any depth, as `(T,)`, since the union would bind it with no check
/// of its bound. A function type (read as a variable of `cx.fns`), a rigid variable and the
/// unknown bind nothing, and take part.
///
/// Complexity tradeoff: some overloads whose arrows together cover `qa` are refused, each
/// with its own reason ([`refused_cover`]). (1) Arrows that cover `qa` only by splitting two
/// or more parameters at once: `((x: int, y: int) -> R) & ((x: bool, y: bool) -> R) & ((x:
/// int, y: bool) -> R) & ((x: bool, y: int) -> R)` covers `(x: int | bool, y: int | bool) ->
/// R`, and is refused. Whether a union of products covers a product is DNF tautology when
/// each parameter has two values, coNP-complete, so a complete check is exponential in the
/// number of parameters. (2) An arrow whose parameter type at `j` holds a type variable of
/// `s`: which part of `qa`'s parameter the variable would be bound to is a choice per arrow,
/// and fixing a bounded variable to each carrier of its bound multiplies the arrows by the
/// product of the bounds, exponential in the variables. (3) Arrows that return outside `qa`'s
/// result, overlapping so that no one set of them takes every value the arrows within leave:
/// `((x: int | bool) -> String | #a) & ((x: int) -> String | #b) & ((x: bool) -> String |
/// #c)` covers `(x: int | bool) -> String`, the intersection `String` at `int` from the first
/// two and at `bool` from the first and third, and is refused. Deciding that is the
/// all-subsets condition of semantic subtyping on arrows (Frisch, Castagna and Benzaken, J.
/// ACM 2008); it is as hard as Orthogonal Vectors even with one parameter of atoms (each
/// arrow a coordinate, each atom of the parameter a vector of the arrows that take it, each
/// atom outside the result a vector of the arrows whose results leave it out), so no
/// n^(2-e) algorithm is expected under the Strong Exponential Time Hypothesis (Williams,
/// TCS 2005; a conjecture). Tests: l01_26_type_resolution::fits (each case, its message and a
/// near miss), and the differential tests below, against every subset of arrows and against
/// the values of small types; COMPLEXITY.md F82. A complete solution would split `qa`'s
/// parameters into the regions the arrows' parameter types cut, and intersect the results per
/// region.
///
/// Complexity tradeoff: the candidates, as those of one arrow ([`every_arrow_fits`]), are not
/// below n·m in the worst case. Arrows that all offer one piece of the slot's parameter are
/// each compared with each arrow of the slot: `(x: #c | #ai) -> String` for i below n, passed
/// where `(x: #c | #ak | #a(k+1)) -> String | #zk` is expected for each k, cost n·m
/// comparisons (63.3 times the bytes at n = 100 and 800). Covering together includes fitting
/// by one arrow, so the containment join of [`every_arrow_fits`] bounds it from below; stopping
/// at the first arrow that holds each key is not exact, since a key (a carrier, an atom's name)
/// does not decide which values of it an arrow holds. The intersection takes the candidates
/// whatever their results, since the arrows of `H` return outside `qa`'s.
fn covered(s: &Sig, sas: &[Arrow], index: &ArrowIndex, qa: &Arrow, cx: &mut Cx) -> bool {
    // The parts at each parameter, by parameter; a BTreeMap, so the parameters are tried in
    // order, and only those some arrow misses are held.
    let mut parts: BTreeMap<usize, Vec<&Ty>> = BTreeMap::new();
    for i in index.covering(qa, true) {
        if let Some((Part::At(j, true), _)) = part_of(s, &sas[i], qa, cx) {
            parts.entry(j).or_default().push(&sas[i].params[j]);
        }
    }
    parts
        .into_iter()
        .any(|(j, ps)| qa.params[j].sub_in(&Ty::union_all(ps), &mut Binds::new(), cx))
        || met(s, sas, &index.covering(qa, false), qa, cx)
}

/// How the arrow `sa` of `s` takes `qa`'s parameters ([`part_of`]).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Part {
    /// It takes all of them; it returns outside `qa`'s result, or it would fit alone.
    Whole,
    /// It takes all but the parameter `j`, at which its type binds nothing, and returns within
    /// `qa`'s result or not.
    At(usize, bool),
}

/// How the arrow `sa` of `s` takes the parameters of `qa`: all of them, or all but one `j`,
/// at which its type binds nothing ([`binds_nothing`]), each bounded variable of `s` it binds
/// bound as [`bounds_hold`] requires, with what it binds. [`arrow_fits`] with `j` left out: a type that binds
/// nothing, so the pass over every parameter binds what the pass without `j` binds.
fn part_of(s: &Sig, sa: &Arrow, qa: &Arrow, cx: &mut Cx) -> Option<(Part, Binds)> {
    let mut b = Binds::new();
    let mut miss = None;
    for (j, (x, y)) in qa.params.iter().zip(&sa.params).enumerate() {
        if !x.sub_in(y, &mut b, cx) {
            if miss.is_some() || !binds_nothing(y, cx) {
                return None;
            }
            miss = Some(j);
        }
    }
    if !bounds_hold(s, sa, &b, cx) {
        return None;
    }
    let part = match miss {
        None => Part::Whole,
        Some(j) => Part::At(j, result_within(sa, qa, &b, cx)),
    };
    Some((part, b))
}

/// Whether comparing a type with `t` binds nothing: each variable it holds outside functions,
/// at any depth, is a rigid variable or a function read as one ([`Cx::read`]). The unknown
/// binds nothing; a type variable of the given side would be bound.
fn binds_nothing(t: &Ty, cx: &Cx) -> bool {
    t.vars
        .iter()
        .all(|v| cx.rigid.contains_key(v) || cx.fns.contains_key(v))
        && t.tuples
            .iter()
            .all(|r| r.iter().all(|c| binds_nothing(c, cx)))
}

/// Whether the candidates `cands` of `sas` cover `qa` by intersection ([`covered`]): with
/// `U` the union of the parameter types at `j` of the arrows that take a part there and
/// return within `qa`'s result, and `H` the arrows that take all of `qa`'s parameters with
/// those that take, at `j`, all of `qa`'s type there outside `U`, `H` is not empty and the
/// intersection of its results is within `qa`'s; or `H` is the arrows that take all of `qa`.
/// [`Ty::diff`] keeps a part it cannot subtract, so `H` takes at least what the arrows within
/// leave. The results are intersected by [`meet_within`]. The cost is one comparison of each
/// candidate and, for each `j`, one of each arrow that takes a part there with what the others
/// leave.
fn met(s: &Sig, sas: &[Arrow], cands: &[usize], qa: &Arrow, cx: &mut Cx) -> bool {
    // An arrow of `q` that takes no value is left to one arrow and the union, as before this
    // form: the index leaves out arrows of `s` that take part of no parameter of it.
    if qa.params.iter().any(Ty::is_empty) {
        return false;
    }
    // The results of the arrows that take all of `qa`, and, at each parameter, the parameter
    // types of the arrows within and of those outside, with their results.
    let mut whole: Vec<Ty> = Vec::new();
    let mut within: BTreeMap<usize, Vec<&Ty>> = BTreeMap::new();
    let mut outside: BTreeMap<usize, Vec<(&Ty, Ty)>> = BTreeMap::new();
    for &i in cands {
        let sa = &sas[i];
        match part_of(s, sa, qa, cx) {
            Some((Part::Whole, b)) => whole.push(sa.result.subst(&b)),
            Some((Part::At(j, true), _)) => within.entry(j).or_default().push(&sa.params[j]),
            Some((Part::At(j, false), b)) => outside
                .entry(j)
                .or_default()
                .push((&sa.params[j], sa.result.subst(&b))),
            None => {}
        }
    }
    if !whole.is_empty() && meet_within(&whole, &qa.result, cx) {
        return true;
    }
    // At a parameter no arrow outside takes a part of, `H` is the arrows that take all of `qa`.
    outside.iter().any(|(&j, parts)| {
        let left = match within.get(&j) {
            Some(ps) => qa.params[j].diff(&Ty::union_all(ps.iter().copied())),
            None => qa.params[j].clone(),
        };
        let mut h = whole.clone();
        for (p, r) in parts {
            if left.sub_in(p, &mut Binds::new(), cx) {
                h.push(r.clone());
            }
        }
        !h.is_empty() && meet_within(&h, &qa.result, cx)
    })
}

/// Whether the intersection of `results` is within `result`. Each result is split into its
/// kernel part, its scalars and atoms and the tuple shapes that hold no function, variable or
/// unknown at any depth, and the rest. The kernel parts are intersected exactly. A value in
/// every result outside that intersection is outside the kernel part of some result `i`, so
/// in a piece of the rest of `i` and in every other result: each such piece must be within
/// `result`, unless no value of it is in every other result. That is known of a function,
/// when another result holds no function, and of a rigid variable bounded by carriers, when
/// the carriers the other results may hold miss its bound. Linear in the results: the
/// carriers of all but one are read off a pass from each end.
///
/// Complexity tradeoff: a piece of the rest is not intersected value by value, so some
/// intersections within `result` are refused: `(U,) | String` and `(bool,) | String` meet
/// only on `String`, but the tuple piece `(U,)` is not within `String`. Intersecting rigid
/// variables value by value would fix each to each carrier of its bound, the product of the
/// bounds in the variables; the tuple pieces would need the intersection per component of
/// each pair of shapes of one width, quadratic in the shapes.
fn meet_within(results: &[Ty], result: &Ty, cx: &mut Cx) -> bool {
    if results.is_empty() {
        return false;
    }
    let masks: Vec<u8> = results.iter().map(|r| carriers_of(r, cx)).collect();
    let mut after = vec![EVERY; masks.len() + 1];
    for (i, &m) in masks.iter().enumerate().rev() {
        after[i] = after[i + 1] & m;
    }
    let no_function = results.iter().any(|r| holds_no_function(r, cx));
    let mut before = EVERY;
    let mut kernels = Vec::with_capacity(results.len());
    let mut rest = Ty::empty();
    for (i, r) in results.iter().enumerate() {
        let others = before & after[i + 1];
        before &= masks[i];
        let mut shapes = Vec::new();
        for row in &r.tuples {
            match row.iter().map(Ty::kernel).collect::<Option<Vec<_>>>() {
                Some(cs) => shapes.push(KType::tuple(cs)),
                None => rest.tuples.push(row.clone()),
            }
        }
        kernels.push(KType::union_all(
            std::iter::once(r.set.clone()).chain(shapes),
        ));
        if !no_function {
            rest.fns.extend(r.fns.iter().cloned());
        }
        for v in &r.vars {
            let missed = match cx.rigid.get(v) {
                Some(&m) => m & OTHER == 0 && m & others == 0,
                None => no_function && cx.fns.contains_key(v),
            };
            if !missed {
                rest.vars.insert(v.clone());
            }
        }
        rest.dynamic |= r.dynamic;
    }
    let Some(k) = kernels.into_iter().reduce(|a, b| &a & &b) else {
        return false;
    };
    let mut b = Binds::new();
    let kernel_within = match result.kernel() {
        Some(r) => k.subtype(&r),
        None => Ty::set(k).sub_in(result, &mut b, cx) && b.is_empty(),
    };
    kernel_within && (rest.is_empty() || rest.sub_in(result, &mut b, cx) && b.is_empty())
}

/// The carriers a value of `t`, as a comparison reads it, may be of, and [`OTHER`] if it may
/// be another value: a rigid variable stands for its bound, and a function read as a variable
/// for no carrier.
fn carriers_of(t: &Ty, cx: &Cx) -> u8 {
    if t.dynamic {
        return EVERY;
    }
    let split = t.set.split();
    let set = Carrier::ALL
        .into_iter()
        .filter(|c| split.bases[c.base()].is_some())
        .fold(0, |m, c| m | c.bit());
    t.vars.iter().fold(set, |m, v| match cx.rigid.get(v) {
        Some(&bound) => m | bound,
        None if cx.fns.contains_key(v) => m | OTHER,
        None => EVERY,
    })
}

/// Whether no value of `t`, as a comparison reads it, is a function: it holds no function, no
/// function read as a variable, no unknown, and only rigid variables bounded by carriers.
fn holds_no_function(t: &Ty, cx: &Cx) -> bool {
    t.fns.is_empty()
        && !t.dynamic
        && t.vars
            .iter()
            .all(|v| cx.rigid.get(v).is_some_and(|&m| m & OTHER == 0))
}

/// What a parameter type of an arrow must hold to hold a piece of a parameter type: the
/// values of one carrier, by [`Carrier::base`], or the bare atom of one name.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Key<'t> {
    Carrier(usize),
    Atom(&'t str),
}

/// The keys every type that holds `t` offers, unless it is open ([`offered_keys`]): the
/// carriers of its scalars and its bare atoms, of a set of atoms that lists its names. A piece
/// of `t` a key does not decide, a tuple, a kind-wide part, a function, a variable or the
/// unknown, adds none.
fn needed_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) {
    let split = t.set.split();
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    if let Some(names) = t.set.atom_names() {
        out.extend(names.filter(|&(_, bare)| bare).map(|(n, _)| Key::Atom(n)));
    }
}

/// The keys the parameter type `t` offers, and whether it is closed: it holds no variable and
/// no unknown, and lists the names of its atoms. A closed type holds a scalar or bare atom only
/// if it offers its key ([`accepts`]: a set piece is held by the set alone, unless `t` has a
/// variable or the unknown). An open one may hold any piece. It may offer a key it holds no
/// value of, an atom name listed with an empty payload, which makes only a candidate more.
fn offered_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) -> bool {
    let Some(names) = t
        .set
        .atom_names()
        .filter(|_| !t.dynamic && t.vars.is_empty())
    else {
        return false;
    };
    out.extend(names.map(|(n, _)| Key::Atom(n)));
    let split = t.set.split();
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    true
}

/// The keys of every piece of `t`, when each piece has one: the carriers of its scalars and the
/// names of its atoms. A parameter type that holds a value of `t` and is closed
/// ([`offered_keys`]) offers that value's key. False when `t` has a piece no key decides: a
/// tuple, a kind-wide part, a function, a variable, the unknown or a cofinite set of atoms.
fn piece_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) -> bool {
    if t.dynamic || !t.vars.is_empty() || !t.tuples.is_empty() || !t.fns.is_empty() {
        return false;
    }
    let split = t.set.split();
    let Some(names) = t.set.atom_names().filter(|_| split.rest.is_none()) else {
        return false;
    };
    out.extend(names.map(|(n, _)| Key::Atom(n)));
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    true
}

/// The arrows of a signature, as read, by what their parameter types offer and their result
/// types need: for the arrows of an expected signature, the arrows that may fit each, found
/// from the keys of its parameter and result types ([`every_arrow_fits`], [`covered`]).
struct ArrowIndex<'t> {
    /// The number of arrows.
    n: usize,
    /// For each parameter and each key, the arrows whose parameter type there is closed and
    /// offers the key, in order.
    post: HashMap<(usize, Key<'t>), Vec<usize>>,
    /// For each parameter, whether each arrow's type there is open (or missing).
    open: Vec<Vec<bool>>,
    /// For each parameter, the arrows whose type there is open, in order.
    always: Vec<Vec<usize>>,
    /// For each arrow, the keys its result type needs ([`needed_keys`]): a closed type that
    /// holds the result offers each.
    result_needs: Vec<Vec<Key<'t>>>,
    /// The arrows whose result type needs a key, each under one of them, the one the fewest
    /// results need, in order.
    by_result: HashMap<Key<'t>, Vec<usize>>,
    /// The arrows whose result type needs no key, in order.
    any_result: Vec<usize>,
}

impl<'t> ArrowIndex<'t> {
    /// The index of `sas`, arrows of `width` parameters, in the size of their parameter and
    /// result types.
    fn new(sas: &'t [Arrow], width: usize) -> ArrowIndex<'t> {
        let mut post: HashMap<(usize, Key<'t>), Vec<usize>> = HashMap::new();
        let mut open = vec![vec![false; sas.len()]; width];
        let mut keys = Vec::new();
        for (i, sa) in sas.iter().enumerate() {
            for (j, row) in open.iter_mut().enumerate() {
                keys.clear();
                match sa.params.get(j) {
                    Some(t) if offered_keys(t, &mut keys) => {
                        for &k in &keys {
                            post.entry((j, k)).or_default().push(i);
                        }
                    }
                    _ => row[i] = true,
                }
            }
        }
        let always = open
            .iter()
            .map(|row| {
                (0..)
                    .zip(row)
                    .filter(|&(_, &o)| o)
                    .map(|(i, _)| i)
                    .collect()
            })
            .collect();
        let result_needs: Vec<Vec<Key<'t>>> = sas
            .iter()
            .map(|sa| {
                let mut keys = Vec::new();
                needed_keys(&sa.result, &mut keys);
                keys
            })
            .collect();
        let mut count: HashMap<Key<'t>, usize> = HashMap::new();
        for k in result_needs.iter().flatten() {
            *count.entry(*k).or_default() += 1;
        }
        let mut by_result: HashMap<Key<'t>, Vec<usize>> = HashMap::new();
        let mut any_result = Vec::new();
        for (i, keys) in result_needs.iter().enumerate() {
            match keys.iter().min_by_key(|k| count[*k]) {
                Some(&k) => by_result.entry(k).or_default().push(i),
                None => any_result.push(i),
            }
        }
        ArrowIndex {
            n: sas.len(),
            post,
            open,
            always,
            result_needs,
            by_result,
            any_result,
        }
    }

    /// For each key `qa`'s parameters need, at each parameter: the parameter and the arrows
    /// whose closed type there offers the key.
    fn needed(&self, qa: &'t Arrow) -> Vec<(usize, &[usize])> {
        let mut need = Vec::new();
        let mut keys = Vec::new();
        for (j, t) in qa.params.iter().enumerate().take(self.open.len()) {
            keys.clear();
            needed_keys(t, &mut keys);
            need.extend(
                keys.iter()
                    .map(|k| (j, self.post.get(&(j, *k)).map_or(&[][..], Vec::as_slice))),
            );
        }
        need
    }

    /// The keys `qa`'s result type offers, when it is closed: an arrow whose result needs a
    /// key outside them returns outside it.
    fn result_keys(qa: &'t Arrow) -> Option<HashSet<Key<'t>>> {
        let mut keys = Vec::new();
        offered_keys(&qa.result, &mut keys).then(|| keys.into_iter().collect())
    }

    /// The arrows whose results may be within a closed type that offers `keys`: those filed
    /// under one of them, and those whose results need no key.
    fn by_results(&self, keys: &HashSet<Key<'t>>) -> Vec<&[usize]> {
        let mut lists: Vec<&[usize]> = keys
            .iter()
            .filter_map(|k| self.by_result.get(k).map(Vec::as_slice))
            .collect();
        lists.push(&self.any_result);
        lists
    }

    /// The arrows of the shortest of `sources`, each the union of its lists, in order, kept
    /// when, at each parameter of `need`, the arrow is open or offers the key, and when
    /// `result` is given, it offers every key the arrow's result needs. Every arrow when there
    /// is no source. The cost is the shortest source's length, times its logarithm and the
    /// keys tested.
    fn candidates(
        &self,
        need: &[(usize, &[usize])],
        result: Option<&HashSet<Key<'t>>>,
        sources: Vec<Vec<&[usize]>>,
    ) -> Vec<usize> {
        let keep = |&i: &usize| {
            need.iter()
                .all(|&(k, l)| self.open[k][i] || l.binary_search(&i).is_ok())
                && result.is_none_or(|r| self.result_needs[i].iter().all(|k| r.contains(k)))
        };
        let Some(lists) = sources
            .into_iter()
            .min_by_key(|lists| lists.iter().map(|l| l.len()).sum::<usize>())
        else {
            return (0..self.n).filter(keep).collect();
        };
        let mut out: Vec<usize> = lists.into_iter().flatten().copied().collect();
        out.sort_unstable();
        out.dedup();
        out.retain(keep);
        out
    }

    /// Whether `fits` holds for an arrow that may fit `qa`, tried in order, stopping at the
    /// first. The candidates come from the shortest list: the arrows that offer one key `qa`'s
    /// parameters need, with the arrows open at that parameter, or the arrows whose results
    /// may be within `qa`'s closed result. Each is kept if, at every parameter, it is open or
    /// offers every key `qa` needs there, and its result needs no key `qa`'s closed result
    /// lacks.
    fn first(&self, qa: &'t Arrow, fits: impl FnMut(usize) -> bool) -> bool {
        let need = self.needed(qa);
        let result = Self::result_keys(qa);
        let mut sources: Vec<Vec<&[usize]>> = need
            .iter()
            .map(|&(j, l)| vec![l, &self.always[j][..]])
            .collect();
        if let Some(r) = &result {
            sources.push(self.by_results(r));
        }
        self.candidates(&need, result.as_ref(), sources)
            .into_iter()
            .any(fits)
    }

    /// The arrows that offer one key of `qa`'s parameter at `j` there, or are open there, when
    /// each piece of it has a key ([`piece_keys`]): an arrow outside them holds no value of it.
    fn pieces_at(&self, qa: &'t Arrow, j: usize) -> Option<Vec<&[usize]>> {
        let mut keys = Vec::new();
        piece_keys(&qa.params[j], &mut keys).then(|| {
            let mut lists: Vec<&[usize]> = keys
                .iter()
                .map(|k| self.post.get(&(j, *k)).map_or(&[][..], Vec::as_slice))
                .collect();
            lists.push(&self.always[j]);
            lists
        })
    }

    /// The arrows that may take part in covering `qa` at some parameter ([`covered`]): those
    /// that, at every parameter but at most one, are open or offer every key `qa` needs there,
    /// and whose results need no key `qa`'s closed result lacks. They come from the shortest
    /// source that holds every such arrow: the arrows whose results may be within `qa`'s; or
    /// the arrows that offer the key of the shortest list, at parameter `a`, or are open there,
    /// which hold each arrow that misses another parameter, with, for the arrows that miss
    /// `a`, the shortest list at another parameter or the arrows that offer a piece of `qa`'s
    /// parameter at `a`; or, when `qa` needs no key at any parameter, the arrows that offer a
    /// piece at some parameter. Every arrow when there is no source. With `by_result` false, the
    /// results filter nothing: the arrows that may take part in covering `qa` by intersection,
    /// whose results are outside `qa`'s ([`met`]).
    fn covering(&self, qa: &'t Arrow, by_result: bool) -> Vec<usize> {
        let need = self.needed(qa);
        let result = Self::result_keys(qa).filter(|_| by_result);
        let len = |lists: &[&[usize]]| lists.iter().map(|l| l.len()).sum::<usize>();
        let mut sources: Vec<Vec<&[usize]>> = Vec::new();
        if let Some(r) = &result {
            sources.push(self.by_results(r));
        }
        // The shortest source of one needed key, at a parameter `at` admits, with its parameter.
        let shortest = |at: &dyn Fn(usize) -> bool| {
            need.iter()
                .filter(|e| at(e.0))
                .map(|&(k, l)| (k, vec![l, &self.always[k][..]]))
                .min_by_key(|(_, lists)| len(lists))
        };
        if let Some((a, first)) = shortest(&|_| true) {
            let other = [shortest(&|k| k != a).map(|e| e.1), self.pieces_at(qa, a)]
                .into_iter()
                .flatten()
                .min_by_key(|lists| len(lists));
            if let Some(other) = other {
                sources.push(first.into_iter().chain(other).collect());
            }
        } else {
            let width = qa.params.len().min(self.open.len());
            let pieces: Option<Vec<Vec<&[usize]>>> =
                (0..width).map(|j| self.pieces_at(qa, j)).collect();
            if let Some(pieces) = pieces.filter(|p| !p.is_empty()) {
                sources.push(pieces.into_iter().flatten().collect());
            }
        }
        let keep = |i: usize| {
            let mut missed = None;
            need.iter().all(|&(k, l)| {
                self.open[k][i]
                    || l.binary_search(&i).is_ok()
                    || missed.replace(k).is_none_or(|m| m == k)
            }) && result
                .as_ref()
                .is_none_or(|r| self.result_needs[i].iter().all(|k| r.contains(k)))
        };
        let mut out: Vec<usize> = match sources.into_iter().min_by_key(|lists| len(lists)) {
            Some(lists) => lists.into_iter().flatten().copied().collect(),
            None => (0..self.n).collect(),
        };
        out.sort_unstable();
        out.dedup();
        out.retain(|&i| keep(i));
        out
    }
}

impl std::hash::Hash for Sig {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.digest());
    }
}

/// Whether the arrow `sa` of `s` takes the parameters of the arrow `qa` and returns within its
/// result, each bounded variable of `s` bound to carriers of its bound ([`fits_in`]).
fn arrow_fits(s: &Sig, sa: &Arrow, qa: &Arrow, cx: &mut Cx) -> bool {
    let mut b = Binds::new();
    qa.params
        .iter()
        .zip(&sa.params)
        .all(|(x, y)| x.sub_in(y, &mut b, cx))
        && bounds_hold(s, sa, &b, cx)
        && result_within(sa, qa, &b, cx)
}

/// Whether each bounded variable of `s` that `b` binds is bound to carriers of its bound, and,
/// when bound to values of more than one carrier, stands where the arrow `sa` may take them
/// ([`one_place`]). A call fixes the variable to one carrier, so `(x: T, y: T) -> T for T in
/// int | f64` bound to `int | f64` would be called with an `int` and an `f64`, which no call
/// of it is.
fn bounds_hold(s: &Sig, sa: &Arrow, b: &Binds, cx: &Cx) -> bool {
    s.bounds.iter().all(|(v, &m)| {
        b.get(v)
            .is_none_or(|t| match t.as_var().and_then(|w| cx.rigid.get(w)) {
                // Each carrier the caller of `q` may pick is one `s` takes.
                Some(&mq) => mq & !m == 0,
                // `v` is one carrier at a call, so it cannot be a rigid variable and
                // something else at once.
                None => {
                    t.pieces().iter().all(|p| match p.carrier() {
                        Some(c) => m & c.bit() != 0,
                        None => {
                            m & OTHER != 0
                                && !matches!(p, Piece::Dyn)
                                && !matches!(p, Piece::Var(w) if cx.rigid.contains_key(w))
                        }
                    }) && (one_carrier(t) || one_place(sa, v, cx))
                }
            })
    })
}

/// Whether the values of `t` are of one carrier, or of none.
fn one_carrier(t: &Ty) -> bool {
    let mut carriers = t.pieces().into_iter().map(|p| p.carrier());
    let first = carriers.next().flatten();
    carriers.all(|c| c == first)
}

/// Whether the variable `v` stands in the arrow `sa`, as read, at one place where an argument
/// gives its values, outside every function type, and elsewhere only where the arrow gives
/// values of it: in its result, or in a parameter of a function type a parameter takes. Then
/// `v` bound to values of several carriers takes, at each value of that place, the arrow at
/// that value's carrier, which returns within the arrow at all of them. A second place an
/// argument fixes, or a place the arrow takes values at inside a function type (a parameter of
/// a function it returns, the result of a function it takes), would need one carrier at both.
/// The cost is a walk of `sa`.
fn one_place(sa: &Arrow, v: &str, cx: &Cx) -> bool {
    let places = Places::of(sa, v, cx);
    places.given == 1 && places.taken == 0
}

/// The places of a variable in an arrow ([`one_place`]).
#[derive(Default)]
struct Places {
    /// Those where an argument gives its values, outside every function type.
    given: usize,
    /// Those where the arrow takes values of it, inside a function type.
    taken: usize,
}

impl Places {
    /// The places of `v` in the arrow `sa`, as read.
    fn of(sa: &Arrow, v: &str, cx: &Cx) -> Places {
        let mut places = Places::default();
        for p in &sa.params {
            places.walk(p, v, false, true, cx);
        }
        places.walk(&sa.result, v, true, true, cx);
        places
    }

    /// Counts the places of `v` in `t`, which the arrow gives values of when `out` and takes
    /// values of when not, outside every function type when `top`. A function type read as a
    /// variable ([`Cx::read`]) is walked as its signature; one that binds `v` itself does not
    /// hold this `v`.
    fn walk(&mut self, t: &Ty, v: &str, out: bool, top: bool, cx: &Cx) {
        if !out && t.vars.contains(v) {
            match top {
                true => self.given += 1,
                false => self.taken += 1,
            }
        }
        for c in t.tuples.iter().flat_map(|r| r.iter()) {
            self.walk(c, v, out, top, cx);
        }
        let read = t.vars.iter().filter_map(|w| cx.fns.get(w).map(|e| &e.0));
        for s in t.fns.iter().chain(read) {
            if s.own.contains(v) {
                continue;
            }
            for a in &s.arrows {
                for p in &a.params {
                    self.walk(p, v, !out, false, cx);
                }
                self.walk(&a.result, v, out, false, cx);
            }
        }
    }
}

/// Whether the result of `sa`, its variables bound by `b`, is within `qa`'s, binding nothing.
fn result_within(sa: &Arrow, qa: &Arrow, b: &Binds, cx: &mut Cx) -> bool {
    let mut rb = Binds::new();
    sa.result.subst(b).sub_in(&qa.result, &mut rb, cx) && rb.is_empty()
}

impl Sig {
    /// Sets [`Sig::held`] from its parameters, at any depth, on any arrow: for a signature
    /// built from parts, at the cost of a walk of its parameters.
    pub fn note_held(&mut self) {
        debug_assert!(
            self.facts.0.get().is_none() && self.facts.2.get().is_none(),
            "a signature is changed after its facts were read"
        );
        self.held.clear();
        if self.bounds.is_empty() {
            return;
        }
        let mut vs = Vars::default();
        for a in &self.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut vs));
        }
        self.held = vs
            .order
            .into_iter()
            .filter(|v| self.own.contains(v) && self.bounds.contains_key(v))
            .collect();
    }

    /// It with each class variable `solve` gives a type replaced by that type at every depth.
    pub fn solved_with(&self, solve: Solve) -> Sig {
        let mut vs = Vars::default();
        for a in &self.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut vs));
            a.result.vars_in(&mut vs);
        }
        self.needs.iter().for_each(|n| n.vars_in(&mut vs));
        let binds: Binds = (vs.order.into_iter())
            .filter_map(|v| solve(&v).map(|t| (v, t)))
            .collect();
        self.replace(&binds)
    }

    /// Its own bounded variables no parameter holds, each bound to [`Ty::of_mask`] of its
    /// bound: no argument fixes its carrier, so a call returns a value of some carrier of it.
    pub fn unheld(&self) -> Binds {
        self.bounds
            .iter()
            .filter(|(v, _)| self.own.contains(*v) && !self.held.contains(*v))
            .map(|(v, &m)| (v.clone(), Ty::of_mask(m)))
            .collect()
    }

    /// Its hash, made at the first call from its parts, each function it holds by its own
    /// hash: so it is asked of a signature held in a type, which no longer changes. Hashed
    /// whole, a set of the functions of `g(0)(1)…(n)` cost the depth of each (CHK-carrier).
    pub fn digest(&self) -> u64 {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        *self.facts.2.get_or_init(|| {
            let parts = (&self.params, &self.arrows, &self.bounds, self.data);
            let more = (&self.needs, &self.own, &self.held, self.named);
            BuildHasherDefault::<DefaultHasher>::default().hash_one((parts, more))
        })
    }

    /// The variables it holds at any depth: worked out at the first call, so it is asked of
    /// a signature held in a type, which no longer changes.
    pub fn facts(&self) -> &VarFacts {
        self.facts.0.get_or_init(|| VarFacts::of(self))
    }

    /// It with each class variable `solve` gives a type replaced by that type at every depth:
    /// made at the first call and kept, so it is asked only when no class changes after,
    /// as the checker finishes. A signature that holds no class variable is itself.
    pub fn settle(self: &Arc<Sig>, solve: Solve) -> Arc<Sig> {
        if self.facts().classes.is_empty() {
            return self.clone();
        }
        // A variable `solve` gives a type is replaced, so no longer bounded, own or held.
        let open = |v: &&Arc<str>| solve(v).is_none();
        let made = || {
            Arc::new(Sig {
                arrows: (self.arrows.iter())
                    .map(|a| Arrow {
                        params: a.params.iter().map(|p| p.settle(solve)).collect(),
                        result: a.result.settle(solve),
                    })
                    .collect(),
                needs: self
                    .needs
                    .iter()
                    .map(|n| n.map_tys(|t| t.settle(solve)))
                    .collect(),
                bounds: (self.bounds.iter())
                    .filter(|(v, _)| open(v))
                    .map(|(v, m)| (v.clone(), *m))
                    .collect(),
                own: self.own.iter().filter(open).cloned().collect(),
                held: self.held.iter().filter(open).cloned().collect(),
                ..(**self).clone()
            })
        };
        self.facts.1.get_or_init(made).clone()
    }

    /// The class variables of `want` that its arrows and needs hold, in the order in which
    /// [`Ty::vars_in`] meets them. The walk enters no function whose facts hold none of those
    /// still unseen, and it stops once all are seen, so it costs no more than replacing them.
    pub fn first_seen(&self, want: &HashSet<Arc<str>>) -> Vec<Arc<str>> {
        enum Item<'a> {
            Ty(&'a Ty),
            Sig(&'a Sig),
        }
        let mut out = Vec::new();
        let mut left = want.clone();
        let mut stack = vec![Item::Sig(self)];
        while let Some(item) = stack.pop()
            && !left.is_empty()
        {
            match item {
                Item::Sig(s) => {
                    // `self` may still change, so its facts are not kept; it is entered.
                    if !std::ptr::eq(s, self) {
                        let classes = &s.facts().classes;
                        let any = match classes.len() < left.len() {
                            true => classes.iter().any(|v| left.contains(v)),
                            false => left.iter().any(|v| classes.contains(v)),
                        };
                        if !any {
                            continue;
                        }
                    }
                    let tys = s
                        .arrows
                        .iter()
                        .flat_map(|a| a.params.iter().chain([&a.result]));
                    let needs = s.needs.iter().flat_map(Need::tys);
                    let at = stack.len();
                    stack.extend(tys.chain(needs).map(Item::Ty));
                    stack[at..].reverse();
                }
                Item::Ty(t) => {
                    out.extend(t.vars.iter().filter(|v| left.remove(*v)).cloned());
                    let at = stack.len();
                    stack.extend(t.tuples.iter().flatten().map(Item::Ty));
                    let shapes = t.payloads.values().flatten().flatten();
                    stack.extend(
                        shapes.flat_map(|s| s.items.iter().chain(s.fields.values()).map(Item::Ty)),
                    );
                    stack.extend(t.fns.iter().map(|s| Item::Sig(s)));
                    stack[at..].reverse();
                }
            }
        }
        out
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
            held: BTreeSet::new(),
            named: 0,
            facts: Default::default(),
        }
    }

    /// It with its variables replaced by `binds` at every depth; a bounded variable replaced
    /// by another variable keeps its bound under the new name.
    pub fn replace(&self, binds: &Binds) -> Sig {
        self.replace_in(binds, Mode::Replace)
    }

    /// It with the variables `names` gives other names, as [`Ty::renamed`] does.
    pub fn renamed(&self, names: &Binds) -> Sig {
        self.replace_in(names, Mode::Rename)
    }

    /// It with its variables replaced by `binds` in its arrows and needs, outside the functions
    /// they hold ([`Ty::replace_outside`]).
    pub fn replace_outside(&self, binds: &Binds) -> Sig {
        self.replace_in(binds, Mode::Outside)
    }

    /// [`Sig::replace`], or as `mode` says: renamed, its own and held variables take their new
    /// names.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Sig {
        // Its own or held variable `v` under `binds`: renamed, kept, or dropped as replaced.
        let keep = |v: &Arc<str>| match binds.get(v) {
            None => Some(v.clone()),
            Some(t) if mode == Mode::Rename => t.vars.first().cloned(),
            Some(_) => None,
        };
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
                    params: a.params.iter().map(|p| p.replace_in(binds, mode)).collect(),
                    result: a.result.replace_in(binds, mode),
                })
                .collect(),
            bounds,
            data: self.data,
            needs: self
                .needs
                .iter()
                .map(|n| n.replace_in(binds, mode))
                .collect(),
            own: self.own.iter().filter_map(keep).collect(),
            held: self.held.iter().filter_map(keep).collect(),
            named: self.named,
            facts: Facts::default(),
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
        self.write(&mut text, &mut Scope::default());
        #[cfg(feature = "printed-types")]
        printed::record(self, &text);
        f.write_str(&text)
    }
}

/// The type variables the signatures around a place being printed bind: each by its name in
/// the type, with the name it is printed with, or none when it is printed `_`. A variable no
/// signature around it bounds by carriers is printed `_`, the type of every value, since type
/// syntax writes a type variable only with its bound (DESIGN.md L1.26, sec:diagnostics).
#[derive(Default)]
struct Scope {
    /// Each variable's printed names, innermost signature last.
    names: HashMap<Arc<str>, Vec<Option<Arc<str>>>>,
    /// The printed names in scope, so a signature inside another that bounds a name already
    /// printed takes a fresh one: a bounds clause inside another's may not bound its name again.
    printed: HashSet<Arc<str>>,
    /// The index in `T`, `U`, … of the next fresh name to try. It only grows, so each name is
    /// tried once however many signatures take a fresh one.
    fresh: usize,
}

impl Scope {
    /// How the variable `v` is printed here: its printed name, or `None` for `_`.
    fn name(&self, v: &Arc<str>) -> Option<&Arc<str>> {
        self.names.get(v)?.last()?.as_ref()
    }

    /// Opens the variables `sig` binds, giving each bounded one a printed name, and returns
    /// them with their masks, in the order of `sig.bounds`. A name not printed around the
    /// signature is kept; otherwise the next of `T`, `U`, … not yet tried that is neither
    /// printed around it nor a name of its own.
    fn open(&mut self, sig: &Sig) -> Vec<(Arc<str>, u8)> {
        let mut out = Vec::new();
        for (v, &m) in &sig.bounds {
            if m & OTHER != 0 {
                self.names.entry(v.clone()).or_default().push(None);
                continue;
            }
            let name = if self.printed.contains(v) {
                loop {
                    let name = super::var_name(self.fresh);
                    self.fresh += 1;
                    if !self.printed.contains(&name) && !sig.bounds.contains_key(&name) {
                        break name;
                    }
                }
            } else {
                v.clone()
            };
            self.printed.insert(name.clone());
            self.names
                .entry(v.clone())
                .or_default()
                .push(Some(name.clone()));
            out.push((name, m));
        }
        for v in sig.own.iter().filter(|v| !sig.bounds.contains_key(*v)) {
            self.names.entry(v.clone()).or_default().push(None);
        }
        out
    }

    /// Closes the variables `sig` binds, which [`Scope::open`] opened.
    fn close(&mut self, sig: &Sig) {
        let own = sig.own.iter().filter(|v| !sig.bounds.contains_key(*v));
        for v in sig.bounds.keys().chain(own) {
            let names = self.names.get_mut(v).expect("opened");
            if let Some(Some(name)) = names.pop() {
                self.printed.remove(&name);
            }
        }
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
    /// function type n deep. A variable `scope` does not name is printed `_`, once.
    fn write(&self, out: &mut String, scope: &mut Scope) {
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
                s.write(n, out, scope);
            }
        }
        for cs in &self.tuples {
            separate(out, &mut first, " | ");
            out.push('(');
            let mut one = true;
            for c in cs {
                separate(out, &mut one, ", ");
                c.write(out, scope);
            }
            if cs.len() == 1 {
                out.push(',');
            }
            out.push(')');
        }
        for s in &self.fns {
            separate(out, &mut first, " | ");
            out.push('(');
            s.write(out, scope);
            out.push(')');
        }
        let mut free = false;
        for v in &self.vars {
            match scope.name(v) {
                Some(name) => {
                    separate(out, &mut first, " | ");
                    out.push_str(name);
                }
                None => free = true,
            }
        }
        if self.dynamic || free {
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
        self.write(&mut text, &mut Scope::default());
        #[cfg(feature = "printed-types")]
        printed::record(&Ty::func(Arc::new(self.clone())), &text);
        f.write_str(&text)
    }
}

impl Sig {
    /// Writes its text, in type syntax, to `out`: its variables bounded by carriers by name, in
    /// a bounds clause after the arrows, and the others `_`.
    fn write(&self, out: &mut String, scope: &mut Scope) {
        let bounds = scope.open(self);
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
                t.write(out, scope);
            }
            out.push_str(") -> ");
            a.result.write(out, scope);
            if several {
                out.push(')');
            }
        }
        for (i, (v, m)) in bounds.iter().enumerate() {
            out.push_str(if i == 0 { " for " } else { ", " });
            out.push_str(v);
            out.push_str(" in ");
            out.push_str(&mask_text(*m));
        }
        scope.close(self);
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

#[cfg(test)]
mod tests {
    use super::*;

    /// How [`every_arrow_fits`] decides in a differential test.
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub(super) enum Reference {
        /// By the index.
        None,
        /// By every pair of arrows, as before the index, with no arrows covering together.
        Pairs,
        /// By every pair, then, at each parameter, by every set of arrows ([`together`]).
        Subsets,
    }

    /// The most arrows whose every subset [`together`] tries.
    const SUBSETS: usize = 10;

    /// The search with no index (COMPLEXITY.md F82): each arrow of `q` on an arrow of `s`
    /// equal to it, then on every arrow of `s` in order, then, under [`Reference::Subsets`],
    /// on every set of arrows of `s` ([`together`]).
    pub(super) fn reference(s: &Sig, sas: &[Arrow], qas: &[Arrow], cx: &mut Cx) -> bool {
        let wide = REFERENCE.get() == Reference::Subsets;
        let mut equal: HashMap<&Arrow, &Arrow> = HashMap::with_capacity(sas.len());
        for sa in sas {
            equal.entry(sa).or_insert(sa);
        }
        qas.iter().all(|qa| {
            equal.get(qa).is_some_and(|sa| arrow_fits(s, sa, qa, cx))
                || sas.iter().any(|sa| arrow_fits(s, sa, qa, cx))
                || (wide && together(s, sas, qa, cx))
                || (wide && met(s, sas, &(0..sas.len()).collect::<Vec<_>>(), qa, cx))
        })
    }

    /// [`arrow_fits`] with the parameter `skip` left out.
    fn fits_but(s: &Sig, sa: &Arrow, qa: &Arrow, skip: usize, cx: &mut Cx) -> bool {
        let mut b = Binds::new();
        qa.params
            .iter()
            .zip(&sa.params)
            .enumerate()
            .all(|(j, (x, y))| j == skip || x.sub_in(y, &mut b, cx))
            && bounds_hold(s, sa, &b, cx)
            && result_within(sa, qa, &b, cx)
    }

    /// Whether, at some parameter, a set of arrows of `sas` covers `qa`: each arrow of the set
    /// has a parameter type there that binds nothing ([`binds_nothing`]), takes `qa`'s other parameters and returns within its
    /// result, and the union of their parameter types there holds `qa`'s. Every nonempty set is
    /// tried when there are at most [`SUBSETS`] arrows; with more, the set of every arrow that
    /// qualifies, which holds what any of its subsets holds.
    fn together(s: &Sig, sas: &[Arrow], qa: &Arrow, cx: &mut Cx) -> bool {
        (0..qa.params.len().min(s.params.len())).any(|j| {
            let ok: Vec<bool> = sas
                .iter()
                .map(|sa| {
                    let p = &sa.params[j];
                    binds_nothing(p, cx) && fits_but(s, sa, qa, j, cx)
                })
                .collect();
            let holds = |set: &dyn Fn(usize) -> bool, cx: &mut Cx| {
                let u = Ty::union_all(
                    (0..sas.len())
                        .filter(|&i| set(i))
                        .map(|i| &sas[i].params[j]),
                );
                qa.params[j].sub_in(&u, &mut Binds::new(), cx)
            };
            if sas.len() <= SUBSETS {
                (1u32..1 << sas.len()).any(|m| {
                    let has = |i: usize| m & (1 << i) != 0;
                    (0..sas.len()).all(|i| !has(i) || ok[i]) && holds(&has, cx)
                })
            } else {
                ok.contains(&true) && holds(&|i| ok[i], cx)
            }
        })
    }

    /// splitmix64, so the cases are the same on every run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (z ^ (z >> 31)) % n
        }
    }

    /// The bound of the variable `B` of the signatures below: `int | f64`.
    const B_MASK: u8 = 0b11;

    /// A random member: an atom of eight, a carrier, a literal, an atom with a payload, or,
    /// when `open`, a type variable, the bounded variable `B`, the unknown or a function.
    fn member(rng: &mut Rng, open: bool) -> Ty {
        match rng.below(if open { 14 } else { 10 }) {
            0..=4 => Ty::set(KType::atom(&format!("a{}", rng.below(8)))),
            5 => Ty::carrier(Carrier::Int),
            6 => Ty::carrier(Carrier::Str),
            7 => Ty::carrier(Carrier::Bool),
            8 => Ty::lit(&Value::Int(rng.below(3) as i64)),
            9 => Ty::set(KType::atom_with("p", &KType::tuple(vec![KType::int()]))),
            10 => Ty::var("T".into()),
            11 => Ty::var("B".into()),
            12 => Ty::dynamic(),
            _ => {
                let a = Arrow {
                    params: vec![Ty::set(KType::atom("a0"))],
                    result: Ty::set(KType::atom(&format!("a{}", rng.below(2)))),
                };
                Ty::func(Arc::new(sig(vec![a], 1, false)))
            }
        }
    }

    /// A union of one to three random members.
    fn union(rng: &mut Rng, open: bool) -> Ty {
        let k = 1 + rng.below(3);
        (0..k).fold(Ty::empty(), |t, _| t.union(&member(rng, open)))
    }

    /// A signature of `width` named parameters with `arrows`, its own variables `T` and `B`,
    /// `B` bounded by `int | f64` when `bounded`.
    fn sig(arrows: Vec<Arrow>, width: usize, bounded: bool) -> Sig {
        let mut s = Sig {
            params: (0..width)
                .map(|j| SParam {
                    name: format!("x{j}").into(),
                    positional: false,
                    default: None,
                })
                .collect(),
            arrows,
            bounds: BTreeMap::new(),
            data: false,
            needs: Vec::new(),
            own: ["T".into(), "B".into()].into_iter().collect(),
            held: BTreeSet::new(),
            named: 0,
            facts: Facts::default(),
        };
        if bounded {
            s.bounds.insert("B".into(), B_MASK);
        }
        s.note_held();
        s
    }

    /// An arrow of `q` near `sa`: each parameter type narrowed to some of its members or
    /// widened by one, the result widened or narrowed alike, so that about half fit.
    fn near(rng: &mut Rng, sa: &Arrow) -> Arrow {
        let mut vary = |t: &Ty| match rng.below(3) {
            0 => t.clone(),
            1 => t.union(&member(rng, false)),
            _ => {
                let ps = t.pieces();
                ps[rng.below(ps.len() as u64) as usize].ty()
            }
        };
        Arrow {
            params: sa.params.iter().map(&mut vary).collect(),
            result: vary(&sa.result),
        }
    }

    /// An arrow of `q` that two arrows of `s` may cover only together: at one parameter the
    /// union of theirs, at the others a piece of `a`'s, and the union of their results.
    fn joined(rng: &mut Rng, a: &Arrow, b: &Arrow) -> Arrow {
        let at = rng.below(a.params.len() as u64) as usize;
        let params = (0..a.params.len())
            .map(|j| {
                let ps = a.params[j].pieces();
                if j == at || ps.is_empty() {
                    a.params[j].union(&b.params[j])
                } else {
                    ps[rng.below(ps.len() as u64) as usize].ty()
                }
            })
            .collect();
        Arrow {
            params,
            result: a.result.union(&b.result),
        }
    }

    /// One arrow of `q` for the arrows `sas` of `s`: random, near an arrow of `s`, or joined
    /// from two.
    fn arrow_of_q(rng: &mut Rng, sas: &[Arrow], width: usize, wider: bool, open: bool) -> Arrow {
        let pick = |rng: &mut Rng| &sas[rng.below(sas.len() as u64) as usize];
        match rng.below(6) {
            0 if wider => Arrow {
                params: (0..width).map(|_| wider_union(rng, open)).collect(),
                result: wider_union(rng, false),
            },
            0 => Arrow {
                params: (0..width).map(|_| union(rng, false)).collect(),
                result: union(rng, false),
            },
            1 | 2 => {
                let (a, b) = (pick(rng), pick(rng));
                joined(rng, a, b)
            }
            _ => {
                let sa = pick(rng);
                if wider {
                    wider_near(rng, sa)
                } else {
                    near(rng, sa)
                }
            }
        }
    }

    /// `fits_sig` by the index, by every pair and by every set of arrows, on one pair of
    /// signatures.
    fn three(s: &Sig, q: &Sig) -> (bool, bool, bool) {
        let new = fits_sig(s, q);
        REFERENCE.set(Reference::Pairs);
        let pairs = fits_sig(s, q);
        REFERENCE.set(Reference::Subsets);
        let subsets = fits_sig(s, q);
        REFERENCE.set(Reference::None);
        (new, pairs, subsets)
    }

    /// Counts of verdicts: fit, do not fit, and fit only by arrows together.
    #[derive(Default)]
    struct Counts {
        fit: usize,
        unfit: usize,
        together: usize,
    }

    impl Counts {
        /// Compares the index with every set of arrows on `q` in `s`, and counts the verdict.
        fn compare(&mut self, s: &Sig, q: &Sig, what: &str) {
            let (new, pairs, subsets) = three(s, q);
            assert_eq!(new, subsets, "{what}: {q} in {s}");
            assert!(subsets || !pairs, "{what}: a fit by one arrow is a fit");
            match (new, pairs) {
                (true, false) => self.together += 1,
                (true, true) => self.fit += 1,
                _ => self.unfit += 1,
            }
        }

        /// Both verdicts occur often, and a fit by arrows together, so the comparison is not of
        /// one answer.
        fn enough(&self) {
            let Counts {
                fit,
                unfit,
                together,
            } = self;
            assert!(
                *fit > 200 && *unfit > 200 && *together > 40,
                "{fit} fit, {unfit} do not, {together} fit only together"
            );
        }
    }

    #[test]
    fn the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows() {
        // Over random overloads, with unions of atoms and carriers and some open parameter
        // types, each arrow of `q` alone and `q` whole get the verdict of comparing with every
        // arrow of `s` and then with every set of arrows of `s` (every subset of at most
        // SUBSETS arrows), every arrow of `s` that fits an arrow of `q` is a candidate, and
        // every arrow that may take part in covering one together is a candidate for it.
        let mut rng = Rng(0x5eed);
        let mut counts = Counts::default();
        for case in 0..60 {
            let n = [1, 2, 5, 8, 20, 60, 300][case % 7];
            let width = 1 + rng.below(2) as usize;
            let open = case % 3 != 0;
            let sas: Vec<Arrow> = (0..n)
                .map(|_| {
                    let params = (0..width).map(|_| union(&mut rng, open)).collect();
                    let wide = open && rng.below(4) == 0;
                    Arrow {
                        params,
                        result: union(&mut rng, wide),
                    }
                })
                .collect();
            let qas: Vec<Arrow> = (0..n.min(60))
                .map(|_| arrow_of_q(&mut rng, &sas, width, false, false))
                .collect();
            let s = sig(sas.clone(), width, case % 2 == 0);
            for qa in &qas {
                let q = sig(vec![qa.clone()], width, false);
                counts.compare(&s, &q, &format!("case {case}"));
                same_in_every_order(&s, &q, case as u64, &format!("case {case}"));
            }
            let q = sig(qas.clone(), width, false);
            counts.compare(&s, &q, &format!("case {case}, the whole of q"));
            same_in_every_order(&s, &q, case as u64, &format!("case {case}"));
            index_keeps(&s, &qas, width, &format!("case {case}"));
        }
        counts.enough();
    }

    /// Every pair and every arrow, on the arrows as written: the index never leaves out an
    /// arrow of `s` that fits an arrow of `qas`, or one that may cover one together with
    /// others, whichever key list or result list it draws from.
    fn index_keeps(s: &Sig, qas: &[Arrow], width: usize, what: &str) {
        let index = ArrowIndex::new(&s.arrows, width);
        let mut cx = Cx::default();
        for qa in qas {
            let mut candidates = Vec::new();
            index.first(qa, |i| {
                candidates.push(i);
                false
            });
            for (i, sa) in s.arrows.iter().enumerate() {
                if arrow_fits(s, sa, qa, &mut cx) {
                    assert!(
                        candidates.binary_search(&i).is_ok(),
                        "{what}: arrow {i} fits but is no candidate"
                    );
                }
            }
            let covering = index.covering(qa, true);
            let meeting = index.covering(qa, false);
            for (i, sa) in s.arrows.iter().enumerate() {
                // An arrow that misses a parameter takes part only where it meets it there, and
                // one that takes a parameter of no value takes no value.
                let part = part_of(s, sa, qa, &mut cx).map(|p| p.0);
                let meets = |j: usize| sa.params[j].meets(&qa.params[j]);
                if (part == Some(Part::Whole) && qa.params.iter().all(|t| !t.is_empty()))
                    || matches!(part, Some(Part::At(j, _)) if meets(j))
                {
                    assert!(
                        meeting.binary_search(&i).is_ok(),
                        "{what}: arrow {i} takes part of an arrow of q but is no candidate: {part:?} {:?} {:?} {:?}",
                        sa.params.iter().map(|t| t.to_string()).collect::<Vec<_>>(),
                        qa.params.iter().map(|t| t.to_string()).collect::<Vec<_>>(),
                        (sa.result.to_string(), qa.result.to_string())
                    );
                }
            }
            for j in 0..width {
                for (i, sa) in s.arrows.iter().enumerate() {
                    let p = &sa.params[j];
                    if binds_nothing(p, &cx)
                        && p.meets(&qa.params[j])
                        && fits_but(s, sa, qa, j, &mut cx)
                    {
                        assert!(
                            covering.binary_search(&i).is_ok(),
                            "{what}: arrow {i} may cover at {j} but is no candidate"
                        );
                    }
                }
            }
        }
    }

    /// The verdict on `q` in `s` is the same with the arrows of `s` reversed, rotated by one
    /// and shuffled, and with the arrows of `q` reversed: the index and the cover try arrows
    /// in their order, and the verdict must not depend on it.
    fn same_in_every_order(s: &Sig, q: &Sig, seed: u64, what: &str) {
        let verdict = fits_sig(s, q);
        let mut rng = Rng(seed ^ 0x0bde_5eed);
        let n = s.arrows.len();
        let mut shuffled = s.arrows.clone();
        for i in (1..n).rev() {
            shuffled.swap(i, rng.below(i as u64 + 1) as usize);
        }
        let mut rotated = s.arrows.clone();
        rotated.rotate_left(1.min(n));
        let reversed: Vec<Arrow> = s.arrows.iter().rev().cloned().collect();
        for (how, arrows) in [
            ("reversed", reversed),
            ("rotated", rotated),
            ("shuffled", shuffled),
        ] {
            let p = Sig {
                arrows,
                ..s.clone()
            };
            assert_eq!(fits_sig(&p, q), verdict, "{what}: s {how}: {q} in {s}");
        }
        let q_reversed = Sig {
            arrows: q.arrows.iter().rev().cloned().collect(),
            ..q.clone()
        };
        assert_eq!(
            fits_sig(s, &q_reversed),
            verdict,
            "{what}: q reversed: {q} in {s}"
        );
    }

    /// A random member of the wider family: those of [`member`], and a cofinite set of atoms,
    /// every atom, an atom whose payload type is empty, a `bool` literal, every `rat`
    /// and `f64`, tuples of carriers and atoms, a kind-wide part, and, when `open`, a tuple
    /// holding the variable `T` or the bounded variable `B`.
    fn wider_member(rng: &mut Rng, open: bool) -> Ty {
        match rng.below(if open { 13 } else { 12 }) {
            0..=1 => member(rng, open),
            2 => Ty::set(&atoms() - &KType::atom(&format!("a{}", rng.below(8)))),
            3 => Ty::set(atoms()),
            4 => Ty::set(KType::atom_with("e", &KType::empty())),
            5 => Ty::lit(&Value::Bool(rng.below(2) == 0)),
            6 => Ty::carrier(Carrier::Rat),
            7 => Ty::carrier(Carrier::F64),
            8 => Ty::tuple(vec![
                Ty::carrier(Carrier::Int),
                Ty::set(KType::atom(&format!("a{}", rng.below(3)))),
            ]),
            9 => Ty::tuple(vec![
                Ty::carrier(Carrier::Int).union(&Ty::carrier(Carrier::Str)),
            ]),
            10 => Ty::set(KType::tuple(vec![KType::top(); 2])),
            11 => Ty::set(wide()),
            _ => Ty::tuple(vec![Ty::var(
                if rng.below(2) == 0 { "T" } else { "B" }.into(),
            )]),
        }
    }

    /// A union of one to three members of the wider family, sometimes with a member of the
    /// first family.
    fn wider_union(rng: &mut Rng, open: bool) -> Ty {
        let k = 1 + rng.below(3);
        (0..k).fold(Ty::empty(), |t, _| t.union(&wider_member(rng, open)))
    }

    /// [`near`] with the members of the wider family, a type of no piece kept as it is.
    fn wider_near(rng: &mut Rng, sa: &Arrow) -> Arrow {
        let mut vary = |t: &Ty| match (rng.below(3), t.pieces()) {
            (1, _) => t.union(&wider_member(rng, false)),
            (2, ps) if !ps.is_empty() => ps[rng.below(ps.len() as u64) as usize].ty(),
            _ => t.clone(),
        };
        Arrow {
            params: sa.params.iter().map(&mut vary).collect(),
            result: vary(&sa.result),
        }
    }

    /// [`sig`] with `B` bounded by `mask` when given.
    fn sig_mask(arrows: Vec<Arrow>, width: usize, mask: Option<u8>) -> Sig {
        let mut s = sig(arrows, width, false);
        if let Some(m) = mask {
            s.bounds.insert("B".into(), m);
            s.note_held();
        }
        s
    }

    #[test]
    fn the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes() {
        // As above, on cofinite and empty-payload atoms, tuples, kind-wide parts and literals,
        // with `B` of each side bounded or not: `B` of `q` that a parameter holds is a rigid
        // variable, a bound with OTHER reads `B` of `s` unheld as the unknown.
        let masks = [None, Some(B_MASK), Some(0b1001), Some(OTHER | 0b1)];
        let mut rng = Rng(0x00dd_5eed);
        let mut counts = Counts::default();
        for case in 0..150 {
            let n = [1, 3, 6, 10, 30, 90][case % 6];
            let width = 1 + rng.below(2) as usize;
            let open = case % 3 != 0;
            let sas: Vec<Arrow> = (0..n)
                .map(|_| {
                    let params = (0..width).map(|_| wider_union(&mut rng, open)).collect();
                    let wide = open && rng.below(4) == 0;
                    Arrow {
                        params,
                        result: wider_union(&mut rng, wide),
                    }
                })
                .collect();
            let qas: Vec<Arrow> = (0..n.min(30))
                .map(|_| arrow_of_q(&mut rng, &sas, width, true, open))
                .collect();
            let s = sig_mask(sas, width, masks[rng.below(4) as usize]);
            let qm = masks[rng.below(4) as usize];
            for qa in &qas {
                let q = sig_mask(vec![qa.clone()], width, qm);
                counts.compare(&s, &q, &format!("case {case}"));
                same_in_every_order(&s, &q, case as u64, &format!("case {case}"));
            }
            index_keeps(&s, &qas, width, &format!("wider case {case}"));
            let q = sig_mask(qas, width, qm);
            counts.compare(&s, &q, &format!("case {case}, the whole of q"));
            same_in_every_order(&s, &q, case as u64, &format!("case {case}, the whole of q"));
        }
        counts.enough();
    }

    /// The values of the small types below, one for each class no type of them splits: `int`,
    /// `bool`, `String`, `f64` and the atoms `#v0` to `#v2`, a bit each.
    const VALUES: usize = 7;

    /// The type of the values of the mask `m`.
    fn of_values(m: u8) -> Ty {
        let carriers = [Carrier::Int, Carrier::Bool, Carrier::Str, Carrier::F64];
        (0..VALUES)
            .filter(|&b| m & (1 << b) != 0)
            .fold(Ty::empty(), |t, b| match carriers.get(b) {
                Some(&c) => t.union(&Ty::carrier(c)),
                None => t.union(&Ty::set(KType::atom(&format!("v{}", b - carriers.len())))),
            })
    }

    /// The bits of `int` and `f64`, the bound of `B` below.
    const B_VALUES: u8 = 0b1001;

    /// A place of a small arrow: the values of a mask, alone or with the variable `B` bounded by
    /// `int | f64`.
    #[derive(Clone, Copy)]
    enum Small {
        Values(u8),
        B(u8),
    }

    impl Small {
        fn ty(self) -> Ty {
            match self {
                Small::Values(m) => of_values(m),
                Small::B(m) => Ty::var("B".into()).union(&of_values(m)),
            }
        }

        /// The mask at `B` fixed to the carrier of the bit `c`.
        fn at(self, c: u8) -> u8 {
            match self {
                Small::Values(m) => m,
                Small::B(m) => m | c,
            }
        }
    }

    /// Whether arrows of the places `arrows` cover the arrow of masks `params -> result` as
    /// rule 6 of sec:type_resolution types a call, by the values: at each value of the
    /// parameters, some arrow takes it, and the intersection of the results of every arrow
    /// that takes it is within `result`. An arrow that holds `B` is each arrow it is at a
    /// carrier of its bound ([`Sig::expand`]).
    fn covers_by_values(arrows: &[(Vec<Small>, Small)], params: &[u8], result: u8) -> bool {
        let fixed: Vec<(Vec<u8>, u8)> = arrows
            .iter()
            .flat_map(|(ps, r)| {
                let held = ps.iter().chain([r]).any(|p| matches!(p, Small::B(_)));
                let cs: Vec<u8> = match held {
                    true => (0..VALUES)
                        .map(|b| 1 << b)
                        .filter(|c| B_VALUES & c != 0)
                        .collect(),
                    false => vec![0],
                };
                cs.into_iter()
                    .map(move |c| (ps.iter().map(|p| p.at(c)).collect(), r.at(c)))
            })
            .collect();
        // Every value of the parameters, one bit at each.
        let mut values: Vec<Vec<u8>> = vec![Vec::new()];
        for &m in params {
            values = values
                .into_iter()
                .flat_map(|v| {
                    (0..VALUES)
                        .filter(move |&b| m & (1 << b) != 0)
                        .map(move |b| {
                            let mut v = v.clone();
                            v.push(1 << b);
                            v
                        })
                })
                .collect();
        }
        values.iter().all(|v| {
            let mut met: Option<u8> = None;
            for (ps, r) in &fixed {
                if ps.iter().zip(v).all(|(p, x)| p & x != 0) {
                    met = Some(met.map_or(*r, |m| m & r));
                }
            }
            met.is_some_and(|m| m & !result == 0)
        })
    }

    /// A random mask of [`VALUES`], not empty.
    fn mask(rng: &mut Rng) -> u8 {
        loop {
            let m = rng.below(1 << VALUES) as u8;
            if m != 0 {
                break m;
            }
        }
    }

    /// `B` one time in eight, else the values of a random mask; when `narrow`, of the meet of
    /// two and one of the first three values, so that results outside a slot's are common.
    fn small(rng: &mut Rng, narrow: bool) -> Small {
        if rng.below(8) == 0 {
            return Small::B(0);
        }
        Small::Values(match narrow {
            true => mask(rng) & mask(rng) | 1 << rng.below(3),
            false => mask(rng),
        })
    }

    #[test]
    fn a_fit_of_small_types_is_a_cover_of_their_values() {
        // Over random overloads of one or two parameters whose types are unions of the values
        // of [`VALUES`], some arrows with `B`: every fit `fits_sig` gives holds at every value,
        // as rule 6 types a call there, whether by one arrow, by a union at one parameter or
        // by the intersection of results ([`covered`]). The checker refuses some covers
        // (cases (1) to (3) of [`covered`]), so a cover it does not take is counted, not
        // asserted, and the counts show each form of fit occurs.
        let mut rng = Rng(0x0005_eed5);
        let (mut fit, mut cover, mut refused, mut neither) = (0, 0, 0, 0);
        for case in 0..4000 {
            let width = 1 + case % 2;
            let n = 1 + rng.below(4) as usize;
            let mut arrows: Vec<(Vec<Small>, Small)> = Vec::new();
            for _ in 0..n {
                let ps = (0..width).map(|_| small(&mut rng, false)).collect();
                arrows.push((ps, small(&mut rng, true)));
            }
            let params: Vec<u8> = (0..width)
                .map(|_| (mask(&mut rng) & mask(&mut rng)).max(1))
                .collect();
            let result = mask(&mut rng) | 1 << rng.below(3);
            let sas = arrows
                .iter()
                .map(|(ps, r)| Arrow {
                    params: ps.iter().map(|p| p.ty()).collect(),
                    result: r.ty(),
                })
                .collect();
            let mut s = sig(sas, width, false);
            s.bounds
                .insert("B".into(), Carrier::Int.bit() | Carrier::F64.bit());
            s.note_held();
            let qa = Arrow {
                params: params.iter().map(|&m| of_values(m)).collect(),
                result: of_values(result),
            };
            let q = sig(vec![qa.clone()], width, false);
            let truth = covers_by_values(&arrows, &params, result);
            let pairs = {
                REFERENCE.set(Reference::Pairs);
                let v = fits_sig(&s, &q);
                REFERENCE.set(Reference::None);
                v
            };
            match (fits_sig(&s, &q), truth) {
                (true, false) => panic!("case {case}: {q} in {s} is no cover of the values"),
                (true, true) if pairs => fit += 1,
                (true, true) => cover += 1,
                (false, true) => refused += 1,
                (false, false) => neither += 1,
            }
        }
        assert!(
            fit > 200 && cover > 100 && neither > 200,
            "{fit} fit by one arrow, {cover} together, {refused} refused, {neither} no cover"
        );
    }

    #[test]
    fn a_fit_at_a_bounded_variable_is_a_cover_of_its_values() {
        // As above, with the slot generic: `U`, bounded by `int | f64`, stands at some of its
        // parameters and in its result, and the arrows hold `B`, alone or with other values,
        // at parameters and in results, so a result may hold the rigid `U` (by `B` bound to
        // it) beside values ([`meet_within`]). A fit holds at each carrier the caller may fix
        // `U` to, at every value, as rule 6 types a call there.
        let mut rng = Rng(0x0005_eed6);
        let (mut fit, mut refused, mut neither) = (0, 0, 0);
        let place = |rng: &mut Rng, narrow: bool| match small(rng, narrow) {
            Small::B(_) if narrow && rng.below(2) == 0 => Small::B(1 << rng.below(VALUES as u64)),
            p => p,
        };
        for case in 0..4000 {
            let width = 1 + case % 2;
            let n = 1 + rng.below(4) as usize;
            let mut arrows: Vec<(Vec<Small>, Small)> = Vec::new();
            for _ in 0..n {
                let ps = (0..width).map(|_| place(&mut rng, false)).collect();
                arrows.push((ps, place(&mut rng, true)));
            }
            // A slot's place: `U`, alone or with values, one time in three, else values.
            let slot = |rng: &mut Rng, m: u8| match rng.below(3) {
                0 => (true, m & mask(rng) & mask(rng)),
                _ => (false, m.max(1)),
            };
            let params: Vec<(bool, u8)> = (0..width)
                .map(|_| {
                    let m = mask(&mut rng) & mask(&mut rng);
                    slot(&mut rng, m)
                })
                .collect();
            let m = mask(&mut rng) | 1 << rng.below(3);
            let result = slot(&mut rng, m);
            let u = |(held, m): (bool, u8)| match held {
                true => Ty::var("U".into()).union(&of_values(m)),
                false => of_values(m),
            };
            let sas = arrows
                .iter()
                .map(|(ps, r)| Arrow {
                    params: ps.iter().map(|p| p.ty()).collect(),
                    result: r.ty(),
                })
                .collect();
            let mut s = sig(sas, width, false);
            s.bounds
                .insert("B".into(), Carrier::Int.bit() | Carrier::F64.bit());
            s.note_held();
            let qa = Arrow {
                params: params.iter().map(|&p| u(p)).collect(),
                result: u(result),
            };
            let mut q = sig(vec![qa], width, false);
            q.own.insert("U".into());
            q.bounds
                .insert("U".into(), Carrier::Int.bit() | Carrier::F64.bit());
            q.note_held();
            let at = |(held, m): (bool, u8), c: u8| if held { m | c } else { m };
            // `U` that no parameter holds is no carrier a caller fixes: it is read as its bound.
            let fixed: &[u8] = match params.iter().any(|&(held, _)| held) {
                true => &[1, 1 << 3],
                false => &[1 | 1 << 3],
            };
            let truth = fixed.iter().all(|&c| {
                let ps: Vec<u8> = params.iter().map(|&p| at(p, c)).collect();
                covers_by_values(&arrows, &ps, at(result, c))
            });
            match (fits_sig(&s, &q), truth) {
                (true, false) => panic!("case {case}: {q} in {s} is no cover of the values"),
                (true, true) => fit += 1,
                (false, true) => refused += 1,
                (false, false) => neither += 1,
            }
        }
        assert!(
            fit > 200 && neither > 200,
            "{fit} fit, {refused} refused, {neither} no cover"
        );
    }
}
