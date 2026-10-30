//! Types (step L1.22, DESIGN.md sec:type_language): sets of values, closed under union,
//! intersection and complement.
//!
//! A type has one part per universe (sec:type_language, the kinding of the connectives): the
//! scalars, which are the literals of each base type and the atoms; the tuples; the structs;
//! and the morphisms. A connective acts on each part on its own, so a complement is taken
//! within each universe. A scalar part is exact: a finite or cofinite set of literals per base
//! type, and per atom name whether the bare atom is in it and which payloads are. The tuple
//! and morphism parts are unions of clauses, each the intersection of some types of its
//! universe and the complements of others; whether one is empty is decided by subtyping (step
//! L1.23), so two of them may denote one set and differ. Structs join at L2: until then the
//! struct part is every struct or none.
//!
//! A morphism type bounds its domain from both sides: the keys it guarantees and the keys it
//! permits, with every present key's value in the value type. `K -> V` is exact and
//! `K ->? V` guarantees no key.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::{BitAnd, BitOr, Not, Sub};
use std::sync::Arc;

use crate::value::Value;

/// A type: the set of values it denotes.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Type(Arc<Parts>);

/// The universes of values, within each of which a complement is taken.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Universe {
    /// Booleans, numbers, strings and atoms.
    Scalar,
    /// Tuples of every length, and keypaths.
    Tuple,
    /// Structs, which join at L2.
    Struct,
    /// Functions and families.
    Morphism,
}

impl Universe {
    /// The universe of `v`. A keypath is a tuple of keys; an atom with its payload is a scalar.
    pub fn of(v: &Value) -> Universe {
        match v {
            Value::Tuple(_) | Value::Path(_) => Universe::Tuple,
            Value::Family(_) => Universe::Morphism,
            _ => Universe::Scalar,
        }
    }
}

/// A morphism type: `(guarantee ⊆ dom ⊆ permission) -> value`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Morphism {
    /// The keys certainly present.
    pub guarantee: Type,
    /// The keys possibly present.
    pub permission: Type,
    /// The type of every present key's value.
    pub value: Type,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Parts {
    /// Bit 0 for `false`, bit 1 for `true`.
    bools: u8,
    ints: Lits,
    rats: Lits,
    floats: Lits,
    strings: Lits,
    atoms: Atoms,
    tuples: Dnf<Vec<Type>>,
    structs: bool,
    morphisms: Dnf<Morphism>,
}

/// A finite set of literals, or the complement of one within its base type.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Lits {
    cofinite: bool,
    values: BTreeSet<Value>,
}

/// Per atom name, its part; a name not listed has every payload when `cofinite`, else none.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Atoms {
    cofinite: bool,
    names: BTreeMap<Arc<str>, AtomPart>,
}

/// The atoms of one name in a type: the bare atom, and those whose payload is in `payload`, a
/// type within the tuples and structs.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct AtomPart {
    bare: bool,
    payload: Type,
}

/// A union of clauses; the empty union is no value of the universe, and the empty clause is
/// every value of it.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Dnf<A: Ord>(BTreeSet<Clause<A>>);

/// The intersection of `pos` and the complements of `neg`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Clause<A: Ord> {
    pos: BTreeSet<A>,
    neg: BTreeSet<A>,
}

impl Type {
    fn new(p: Parts) -> Type {
        Type(Arc::new(p))
    }

    /// No value.
    pub fn empty() -> Type {
        Type::new(Parts {
            bools: 0,
            ints: Lits::default(),
            rats: Lits::default(),
            floats: Lits::default(),
            strings: Lits::default(),
            atoms: Atoms::default(),
            tuples: Dnf::none(),
            structs: false,
            morphisms: Dnf::none(),
        })
    }

    /// Every value, `_`.
    pub fn top() -> Type {
        !Type::empty()
    }

    fn with(f: impl FnOnce(&mut Parts)) -> Type {
        let mut p = (*Type::empty().0).clone();
        f(&mut p);
        Type::new(p)
    }

    /// `bool`.
    pub fn bool() -> Type {
        Type::with(|p| p.bools = 3)
    }

    /// `int`.
    pub fn int() -> Type {
        Type::with(|p| p.ints.cofinite = true)
    }

    /// `rat`.
    pub fn rat() -> Type {
        Type::with(|p| p.rats.cofinite = true)
    }

    /// `f64`.
    pub fn f64() -> Type {
        Type::with(|p| p.floats.cofinite = true)
    }

    /// `String`.
    pub fn string() -> Type {
        Type::with(|p| p.strings.cofinite = true)
    }

    /// The type of one scalar literal or bare atom; `None` for any other value.
    pub fn lit(v: &Value) -> Option<Type> {
        let one = |l: &mut Lits| {
            l.values.insert(v.clone());
        };
        Some(match v {
            Value::Bool(b) => Type::with(|p| p.bools = 1 << u8::from(*b)),
            Value::Int(_) | Value::Big(_) => Type::with(|p| one(&mut p.ints)),
            Value::Rat(_) => Type::with(|p| one(&mut p.rats)),
            Value::Float(_) => Type::with(|p| one(&mut p.floats)),
            Value::Str(_) => Type::with(|p| one(&mut p.strings)),
            Value::Atom(a) if a.args.is_empty() => Type::atom(&a.name),
            _ => return None,
        })
    }

    /// The bare atom `#name`.
    pub fn atom(name: &str) -> Type {
        Type::atom_part(name, true, Type::empty())
    }

    /// `#name(payload)`: the atoms of that name whose payload, a tuple or struct, is in
    /// `payload`.
    pub fn atom_with(name: &str, payload: &Type) -> Type {
        Type::atom_part(name, false, payload & &Type::payloads())
    }

    fn atom_part(name: &str, bare: bool, payload: Type) -> Type {
        let part = AtomPart { bare, payload };
        let mut atoms = Atoms::default();
        if !part.is_none() {
            atoms.names.insert(name.into(), part);
        }
        Type::with(|p| p.atoms = atoms)
    }

    /// The tuple type `(t1, …, tn)`.
    pub fn tuple(items: Vec<Type>) -> Type {
        Type::with(|p| p.tuples = Dnf::literal(items))
    }

    /// The morphism type with the given bounds and value type.
    pub fn morphism(guarantee: Type, permission: Type, value: Type) -> Type {
        Type::with(|p| {
            p.morphisms = Dnf::literal(Morphism {
                guarantee,
                permission,
                value,
            })
        })
    }

    /// `K -> V`, exact: every key of `K` is present.
    pub fn exact(key: Type, value: Type) -> Type {
        Type::morphism(key.clone(), key, value)
    }

    /// `K ->? V`: the keys are drawn from `K`, none promised.
    pub fn partial(key: Type, value: Type) -> Type {
        Type::morphism(Type::empty(), key, value)
    }

    /// Every value of `u`.
    pub fn universe(u: Universe) -> Type {
        Type::with(|p| match u {
            Universe::Scalar => {
                p.bools = 3;
                for l in [&mut p.ints, &mut p.rats, &mut p.floats, &mut p.strings] {
                    l.cofinite = true;
                }
                p.atoms.cofinite = true;
            }
            Universe::Tuple => p.tuples = Dnf::all(),
            Universe::Struct => p.structs = true,
            Universe::Morphism => p.morphisms = Dnf::all(),
        })
    }

    /// The values an atom's payload may be: tuples and structs.
    fn payloads() -> Type {
        Type::universe(Universe::Tuple) | Type::universe(Universe::Struct)
    }

    /// The values of `self` in `u`.
    pub fn part(&self, u: Universe) -> Type {
        self & &Type::universe(u)
    }

    /// Whether the morphism part of `self` is neither every morphism nor none. A run-time
    /// test against such a type is not decidable (sec:type_notation: run-time type tests are
    /// restricted to decidable checks).
    fn has_morphism_bounds(&self) -> bool {
        let m = &self.0.morphisms;
        !(m.0.is_empty() || m.is_all())
    }

    /// Whether membership in `self` is decidable at run time: no part of it, nor of a tuple
    /// component or atom payload it holds, is a proper subset of the morphisms.
    pub fn decidable(&self) -> bool {
        let p = &*self.0;
        !self.has_morphism_bounds()
            && p.atoms.names.values().all(|a| a.payload.decidable())
            && p.tuples
                .0
                .iter()
                .all(|c| c.pos.iter().chain(&c.neg).flatten().all(Type::decidable))
    }

    /// Whether every function is in `self`; for a decidable type, either every function is or
    /// none is.
    pub fn functions(&self) -> bool {
        self.0.morphisms.is_all()
    }

    /// Whether `v` is in `self`, for a decidable `self`.
    pub fn contains(&self, v: &Value) -> bool {
        let p = &*self.0;
        match v {
            Value::Bool(b) => p.bools & (1 << u8::from(*b)) != 0,
            Value::Int(_) | Value::Big(_) => p.ints.contains(v),
            Value::Rat(_) => p.rats.contains(v),
            Value::Float(_) => p.floats.contains(v),
            Value::Str(_) => p.strings.contains(v),
            Value::Atom(a) => {
                let Some(part) = p.atoms.names.get(&a.name) else {
                    return p.atoms.cofinite;
                };
                if a.args.is_empty() {
                    part.bare
                } else if a.fields.is_empty() {
                    part.payload.contains(&Value::Tuple(a.args.clone()))
                } else {
                    part.payload.0.structs
                }
            }
            Value::Tuple(xs) | Value::Path(xs) => p.tuples.0.iter().any(|c| {
                let fits = |t: &Vec<Type>| {
                    t.len() == xs.len() && t.iter().zip(xs).all(|(t, x)| t.contains(x))
                };
                c.pos.iter().all(fits) && !c.neg.iter().any(fits)
            }),
            Value::Family(_) => self.functions(),
        }
    }

    fn zip(&self, other: &Type, op: Op) -> Type {
        let (a, b) = (&*self.0, &*other.0);
        Type::new(Parts {
            bools: match op {
                Op::Or => a.bools | b.bools,
                Op::And => a.bools & b.bools,
            },
            ints: a.ints.zip(&b.ints, op),
            rats: a.rats.zip(&b.rats, op),
            floats: a.floats.zip(&b.floats, op),
            strings: a.strings.zip(&b.strings, op),
            atoms: a.atoms.zip(&b.atoms, op),
            tuples: a.tuples.zip(&b.tuples, op),
            structs: match op {
                Op::Or => a.structs || b.structs,
                Op::And => a.structs && b.structs,
            },
            morphisms: a.morphisms.zip(&b.morphisms, op),
        })
    }
}

#[derive(Clone, Copy)]
enum Op {
    Or,
    And,
}

impl Lits {
    fn contains(&self, v: &Value) -> bool {
        self.values.contains(v) != self.cofinite
    }

    fn zip(&self, other: &Lits, op: Op) -> Lits {
        let (a, b) = (&self.values, &other.values);
        let (cofinite, values) = match (op, self.cofinite, other.cofinite) {
            (Op::Or, false, false) => (false, a | b),
            (Op::Or, false, true) => (true, b - a),
            (Op::Or, true, false) => (true, a - b),
            (Op::Or, true, true) => (true, a & b),
            (Op::And, false, false) => (false, a & b),
            (Op::And, false, true) => (false, a - b),
            (Op::And, true, false) => (false, b - a),
            (Op::And, true, true) => (true, a | b),
        };
        Lits { cofinite, values }
    }

    fn not(&self) -> Lits {
        Lits {
            cofinite: !self.cofinite,
            values: self.values.clone(),
        }
    }
}

impl AtomPart {
    fn all() -> AtomPart {
        AtomPart {
            bare: true,
            payload: Type::payloads(),
        }
    }

    fn none() -> AtomPart {
        AtomPart {
            bare: false,
            payload: Type::empty(),
        }
    }

    fn is_none(&self) -> bool {
        *self == AtomPart::none()
    }

    fn zip(&self, other: &AtomPart, op: Op) -> AtomPart {
        AtomPart {
            bare: match op {
                Op::Or => self.bare || other.bare,
                Op::And => self.bare && other.bare,
            },
            payload: self.payload.zip(&other.payload, op),
        }
    }

    fn not(&self) -> AtomPart {
        AtomPart {
            bare: !self.bare,
            payload: Type::payloads() - &self.payload,
        }
    }
}

impl Atoms {
    fn get(&self, name: &str) -> AtomPart {
        match self.names.get(name) {
            Some(p) => p.clone(),
            None if self.cofinite => AtomPart::all(),
            None => AtomPart::none(),
        }
    }

    /// Drops the names whose part is what an unlisted name has.
    fn normal(cofinite: bool, names: BTreeMap<Arc<str>, AtomPart>) -> Atoms {
        let default = if cofinite {
            AtomPart::all()
        } else {
            AtomPart::none()
        };
        let names = names.into_iter().filter(|(_, p)| *p != default).collect();
        Atoms { cofinite, names }
    }

    fn zip(&self, other: &Atoms, op: Op) -> Atoms {
        let cofinite = match op {
            Op::Or => self.cofinite || other.cofinite,
            Op::And => self.cofinite && other.cofinite,
        };
        let names = self
            .names
            .keys()
            .chain(other.names.keys())
            .map(|n| (n.clone(), self.get(n).zip(&other.get(n), op)))
            .collect();
        Atoms::normal(cofinite, names)
    }

    fn not(&self) -> Atoms {
        let names = self
            .names
            .iter()
            .map(|(n, p)| (n.clone(), p.not()))
            .collect();
        Atoms::normal(!self.cofinite, names)
    }
}

/// How the clauses of a universe simplify: by default, a clause is empty when one type is in
/// both its positive and negated sets.
trait Literal: Ord + Clone {
    /// The clause simplified, or `None` when it is empty.
    fn clause(c: Clause<Self>) -> Option<Clause<Self>> {
        c.pos.is_disjoint(&c.neg).then_some(c)
    }
}

impl Literal for Morphism {}

/// Two tuple types of one length intersect component by component, and of two lengths are
/// disjoint; a tuple type with an empty component is empty.
impl Literal for Vec<Type> {
    fn clause(c: Clause<Self>) -> Option<Clause<Self>> {
        let mut pos = c.pos.into_iter();
        let pos = match pos.next() {
            None => BTreeSet::new(),
            Some(first) => {
                let mut meet = first;
                for p in pos {
                    if p.len() != meet.len() {
                        return None;
                    }
                    meet = meet.iter().zip(&p).map(|(a, b)| a & b).collect();
                }
                if meet.iter().any(|t| *t == Type::empty()) {
                    return None;
                }
                BTreeSet::from([meet])
            }
        };
        let neg = match pos.first() {
            Some(p) => c.neg.into_iter().filter(|n| n.len() == p.len()).collect(),
            None => c.neg,
        };
        let c = Clause { pos, neg };
        c.pos.is_disjoint(&c.neg).then_some(c)
    }
}

impl<A: Literal> Dnf<A> {
    fn none() -> Dnf<A> {
        Dnf(BTreeSet::new())
    }

    fn all() -> Dnf<A> {
        Dnf(BTreeSet::from([Clause {
            pos: BTreeSet::new(),
            neg: BTreeSet::new(),
        }]))
    }

    fn is_all(&self) -> bool {
        *self == Dnf::all()
    }

    fn literal(a: A) -> Dnf<A> {
        Dnf::normal(
            [Clause {
                pos: BTreeSet::from([a]),
                neg: BTreeSet::new(),
            }]
            .into_iter(),
        )
    }

    /// The union of `clauses`, each simplified, with a clause dropped when another's types are
    /// a subset of its own, and two clauses merged when they differ only in the sign of one
    /// type, to a fixed point.
    fn normal(clauses: impl Iterator<Item = Clause<A>>) -> Dnf<A> {
        let mut set: BTreeSet<Clause<A>> = clauses.filter_map(A::clause).collect();
        loop {
            let v: Vec<Clause<A>> = set.iter().cloned().collect();
            let mut merged = None;
            'outer: for (i, a) in v.iter().enumerate() {
                for b in &v[i + 1..] {
                    if let Some(c) = a.resolve(b) {
                        merged = Some((a.clone(), b.clone(), c));
                        break 'outer;
                    }
                }
            }
            match merged {
                Some((a, b, c)) => {
                    set.remove(&a);
                    set.remove(&b);
                    set.extend(A::clause(c));
                }
                None => break,
            }
        }
        let v: Vec<Clause<A>> = set.iter().cloned().collect();
        Dnf(v
            .iter()
            .filter(|b| !v.iter().any(|a| a != *b && a.within(b)))
            .cloned()
            .collect())
    }

    fn zip(&self, other: &Dnf<A>, op: Op) -> Dnf<A> {
        match op {
            Op::Or => Dnf::normal(self.0.iter().chain(&other.0).cloned()),
            Op::And => Dnf::normal(self.0.iter().flat_map(|a| {
                other.0.iter().map(move |b| Clause {
                    pos: &a.pos | &b.pos,
                    neg: &a.neg | &b.neg,
                })
            })),
        }
    }

    /// De Morgan: the complement of a union is the intersection of the complements, and the
    /// complement of a clause is the union of its types' complements.
    fn not(&self) -> Dnf<A> {
        self.0.iter().fold(Dnf::all(), |acc, c| {
            let flipped = c
                .pos
                .iter()
                .map(|p| Clause {
                    pos: BTreeSet::new(),
                    neg: BTreeSet::from([p.clone()]),
                })
                .chain(c.neg.iter().map(|n| Clause {
                    pos: BTreeSet::from([n.clone()]),
                    neg: BTreeSet::new(),
                }));
            acc.zip(&Dnf::normal(flipped), Op::And)
        })
    }
}

impl<A: Ord + Clone> Clause<A> {
    /// Whether every type of `self` is one of `other`'s, so that `other` is within `self`.
    fn within(&self, other: &Clause<A>) -> bool {
        self.pos.is_subset(&other.pos) && self.neg.is_subset(&other.neg)
    }

    /// `(X & t) | (X & !t)` is `X`.
    fn resolve(&self, other: &Clause<A>) -> Option<Clause<A>> {
        for t in self.pos.intersection(&other.neg) {
            let mut a = self.clone();
            let mut b = other.clone();
            a.pos.remove(t);
            b.neg.remove(t);
            if a == b {
                return Some(a);
            }
        }
        for t in self.neg.intersection(&other.pos) {
            let mut a = self.clone();
            let mut b = other.clone();
            a.neg.remove(t);
            b.pos.remove(t);
            if a == b {
                return Some(a);
            }
        }
        None
    }
}

impl Not for &Type {
    type Output = Type;
    fn not(self) -> Type {
        let p = &*self.0;
        Type::new(Parts {
            bools: !p.bools & 3,
            ints: p.ints.not(),
            rats: p.rats.not(),
            floats: p.floats.not(),
            strings: p.strings.not(),
            atoms: p.atoms.not(),
            tuples: p.tuples.not(),
            structs: !p.structs,
            morphisms: p.morphisms.not(),
        })
    }
}

impl Not for Type {
    type Output = Type;
    fn not(self) -> Type {
        !&self
    }
}

impl BitOr for &Type {
    type Output = Type;
    fn bitor(self, other: &Type) -> Type {
        self.zip(other, Op::Or)
    }
}

impl BitAnd for &Type {
    type Output = Type;
    fn bitand(self, other: &Type) -> Type {
        self.zip(other, Op::And)
    }
}

/// The difference `a \ b`, which is `a & !b`.
impl Sub<&Type> for &Type {
    type Output = Type;
    fn sub(self, other: &Type) -> Type {
        self & &!other
    }
}

impl BitOr for Type {
    type Output = Type;
    fn bitor(self, other: Type) -> Type {
        &self | &other
    }
}

impl BitAnd for Type {
    type Output = Type;
    fn bitand(self, other: Type) -> Type {
        &self & &other
    }
}

impl Sub<&Type> for Type {
    type Output = Type;
    fn sub(self, other: &Type) -> Type {
        &self - other
    }
}

/// The parts as a prefix expression, the form of the syntax tree's types: `_` is every value
/// and `(|)` none; `int` every integer, `(\ int 3)` every one but 3; `#_` every atom; `(#a _)`
/// the atoms `#a` with any payload; `(tuple A B)`, `(! X)`, `(& X Y)`, and `tuple`, `struct`
/// and `morphism` every value of those universes; `(-> K V)` exact, `(->? K V)` with no
/// guarantee, `(-> L U V)` otherwise.
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == Type::top() {
            return f.write_str("_");
        }
        let p = &*self.0;
        let mut items: Vec<String> = Vec::new();
        match p.bools {
            1 => items.push("false".into()),
            2 => items.push("true".into()),
            3 => items.push("bool".into()),
            _ => {}
        }
        for (name, l) in [
            ("int", &p.ints),
            ("rat", &p.rats),
            ("f64", &p.floats),
            ("String", &p.strings),
        ] {
            match (l.cofinite, l.values.is_empty()) {
                (true, true) => items.push(name.into()),
                (true, false) => items.push(format!("(\\ {name} {})", spaced(&l.values))),
                (false, _) => items.extend(l.values.iter().map(Value::to_string)),
            }
        }
        let atom = |name: &str, part: &AtomPart| {
            let mut out = Vec::new();
            if part.bare {
                out.push(format!("#{name}"));
            }
            if part.payload == Type::payloads() {
                out.push(format!("(#{name} _)"));
            } else if part.payload != Type::empty() {
                out.push(format!("(#{name} {})", part.payload));
            }
            out
        };
        if p.atoms.cofinite {
            let except: Vec<String> = p
                .atoms
                .names
                .iter()
                .flat_map(|(n, part)| atom(n, &part.not()))
                .collect();
            match except.is_empty() {
                true => items.push("#_".into()),
                false => items.push(format!("(\\ #_ {})", except.join(" "))),
            }
        } else {
            items.extend(p.atoms.names.iter().flat_map(|(n, part)| atom(n, part)));
        }
        let tuple = |t: &Vec<Type>| {
            let mut s = String::from("(tuple");
            for c in t {
                s += &format!(" {c}");
            }
            s + ")"
        };
        clauses(&mut items, "tuple", &p.tuples, tuple);
        if p.structs {
            items.push("struct".into());
        }
        let morphism = |m: &Morphism| {
            if m.guarantee == m.permission {
                format!("(-> {} {})", m.permission, m.value)
            } else if m.guarantee == Type::empty() {
                format!("(->? {} {})", m.permission, m.value)
            } else {
                format!("(-> {} {} {})", m.guarantee, m.permission, m.value)
            }
        };
        clauses(&mut items, "morphism", &p.morphisms, morphism);
        match items.len() {
            1 => f.write_str(&items[0]),
            _ => write!(
                f,
                "(|{})",
                items.iter().map(|i| format!(" {i}")).collect::<String>()
            ),
        }
    }
}

fn spaced(vs: &BTreeSet<Value>) -> String {
    vs.iter()
        .map(Value::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

fn clauses<A: Ord>(
    items: &mut Vec<String>,
    universe: &str,
    dnf: &Dnf<A>,
    show: impl Fn(&A) -> String,
) {
    for c in &dnf.0 {
        let mut lits: Vec<String> = c.pos.iter().map(&show).collect();
        if lits.is_empty() {
            lits.push(universe.into());
        }
        lits.extend(c.neg.iter().map(|n| format!("(! {})", show(n))));
        match lits.len() {
            1 => items.push(lits.remove(0)),
            _ => items.push(format!(
                "(&{})",
                lits.iter().map(|l| format!(" {l}")).collect::<String>()
            )),
        }
    }
}
