//! Types (step L1.22, DESIGN.md sec:type_language): sets of values, closed under union,
//! intersection and complement.
//!
//! A type has one part per universe (sec:type_language, the kinding of the connectives): the
//! scalars, which are the literals of each base type and the atoms; the tuples; the structs;
//! and the morphisms. A connective acts on each part on its own, so a complement is taken
//! within each universe. A scalar part is exact: a finite or cofinite set of literals per base
//! type, and per atom name whether the bare atom is in it and which payloads are. The tuple
//! part is, per length, and the morphism part is, a decision diagram over types of the universe
//! (module `bdd`): a Boolean function of tuple or morphism types. Whether one is empty is
//! decided by subtyping (step L1.23), so two of them may denote one set and differ. Structs
//! join at L2: until then the struct part is every struct or none.
//!
//! A morphism type bounds its domain from both sides: the keys it guarantees and the keys it
//! permits, with every present key's value in the value type. `K -> V` is exact and
//! `K ->? V` guarantees no key.
//!
//! A recursive type (step L1.23, module `rec`) is a node that stands for its definition's body
//! and unfolds to it when a connective needs its parts. A node unfolds one level at a time: a
//! tuple component, atom payload or morphism bound that mentions a recursive type is kept
//! as written rather than met with another, so no connective unfolds a type without end.
//! Whether a type is empty, and so subtyping, is decided in module `empty`.

mod bdd;
mod empty;
pub mod rec;

use imbl::{OrdMap, OrdSet};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::{BitAnd, BitOr, Not, Sub};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use crate::value::Value;
use bdd::{Form, Part};

/// A type: the set of values it denotes. Types are ordered by their digests first, so two
/// types are ordered without reading their contents unless their digests are equal.
#[derive(Clone, Debug)]
pub struct Type(Arc<Node>);

impl Ord for Type {
    fn cmp(&self, other: &Type) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        self.digest()
            .cmp(&other.digest())
            .then_with(|| self.0.cmp(&other.0))
    }
}

impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Type) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for Type {}

/// Combines two hashes; the digests of types, nodes and expressions are built with it from
/// their children's, so that each is computed once, when it is made.
pub(crate) fn mix(a: u64, b: u64) -> u64 {
    // splitmix64's finalizer.
    let mut z = (a.rotate_left(29) ^ b).wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// FNV-1a over `b`.
fn bytes(b: &[u8]) -> u64 {
    b.iter().fold(0xcbf2_9ce4_8422_2325, |h, &x| {
        (h ^ u64::from(x)).wrapping_mul(0x100_0000_01b3)
    })
}

/// A hash of a literal: equal literals print alike.
fn scalar(v: &Value) -> u64 {
    match v {
        Value::Int(i) => mix(1, *i as u64),
        Value::Str(s) => mix(2, bytes(s.as_bytes())),
        other => mix(3, bytes(other.to_string().as_bytes())),
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Node {
    Parts(Parts),
    Rec(Rec),
}

/// A recursive type, or a part of a recursive definition's body kept unevaluated: its parts are
/// `make()`, computed on first use. Two nodes are one type only when they are one node.
struct Rec {
    id: u64,
    /// The name, made when first printed: a name spells out its part of the definition, so
    /// making every part's name at once cost the product of the definition's size and depth.
    name: OnceLock<String>,
    naming: Box<dyn Fn() -> String + Send + Sync>,
    body: OnceLock<Type>,
    make: Box<dyn Fn() -> Type + Send + Sync>,
}

impl PartialEq for Rec {
    fn eq(&self, other: &Rec) -> bool {
        self.id == other.id
    }
}

impl Eq for Rec {}

impl PartialOrd for Rec {
    fn partial_cmp(&self, other: &Rec) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rec {
    fn cmp(&self, other: &Rec) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl Rec {
    fn name(&self) -> &str {
        self.name.get_or_init(|| (self.naming)())
    }
}

impl fmt::Debug for Rec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

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
    /// The hash of the other fields, set by [`Type::new`].
    digest: u64,
    /// Bit 0 for `false`, bit 1 for `true`.
    bools: u8,
    ints: Lits,
    rats: Lits,
    floats: Lits,
    strings: Lits,
    atoms: Atoms,
    tuples: Tuples,
    structs: bool,
    morphisms: Part<Morphism>,
}

/// A finite set of literals, or the complement of one within its base type. The set is
/// persistent, so that a union or difference with a small set copies nothing else, and `sum`,
/// the wrapping sum of its literals' hashes, is kept as it changes.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Lits {
    cofinite: bool,
    values: OrdSet<Value>,
    sum: u64,
}

/// Per atom name, its part; a name not listed has every payload when `cofinite`, else none.
/// The map is persistent, and `sum` is the wrapping sum of its entries' hashes.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Atoms {
    cofinite: bool,
    names: OrdMap<Arc<str>, AtomPart>,
    sum: u64,
}

/// The atoms of one name in a type: the bare atom, and those whose payload is in `payload`, a
/// type within the tuples and structs.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct AtomPart {
    bare: bool,
    payload: Type,
}

/// Per length, the tuples of that length, as a part over tuple types of it; a
/// length not listed has every tuple when `rest`, else none. Tuples of two lengths are disjoint.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Tuples {
    rest: bool,
    lens: BTreeMap<usize, Part<Vec<Type>>>,
}

thread_local! {
    static EMPTY: Type = Type::build_empty();
    static TOP: Type = !Type::build_empty();
}

impl Parts {
    fn hash(&self) -> u64 {
        let mut h = mix(0, u64::from(self.bools));
        for l in [&self.ints, &self.rats, &self.floats, &self.strings] {
            h = mix(mix(h, u64::from(l.cofinite)), l.sum);
        }
        h = mix(mix(h, u64::from(self.atoms.cofinite)), self.atoms.sum);
        h = mix(h, u64::from(self.tuples.rest));
        for (len, part) in &self.tuples.lens {
            h = mix(mix(h, *len as u64), part.digest());
        }
        mix(mix(h, u64::from(self.structs)), self.morphisms.digest())
    }
}

impl Type {
    fn new(mut p: Parts) -> Type {
        p.digest = p.hash();
        Type(Arc::new(Node::Parts(p)))
    }

    /// The hash of the contents, computed when the type was made; a recursive node's is its
    /// identity's, since two such nodes are one type only when they are one node.
    pub(crate) fn digest(&self) -> u64 {
        match &*self.0 {
            Node::Parts(p) => p.digest,
            Node::Rec(r) => mix(4, r.id),
        }
    }

    /// The node named `naming()` whose parts are `make()`'s, each computed when first needed.
    /// `make` must not need this node's parts, which a contractive definition ensures.
    fn rec(
        naming: impl Fn() -> String + Send + Sync + 'static,
        make: impl Fn() -> Type + Send + Sync + 'static,
    ) -> Type {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Type(Arc::new(Node::Rec(Rec {
            id: NEXT.fetch_add(1, Ordering::Relaxed),
            name: OnceLock::new(),
            naming: Box::new(naming),
            body: OnceLock::new(),
            make: Box::new(make),
        })))
    }

    /// The parts, unfolding a recursive node.
    fn p(&self) -> &Parts {
        match &*self.0 {
            Node::Parts(p) => p,
            Node::Rec(r) => r.body.get_or_init(|| (r.make)()).p(),
        }
    }

    /// No value.
    pub fn empty() -> Type {
        EMPTY.with(Type::clone)
    }

    fn build_empty() -> Type {
        Type::new(Parts {
            digest: 0,
            bools: 0,
            ints: Lits::default(),
            rats: Lits::default(),
            floats: Lits::default(),
            strings: Lits::default(),
            atoms: Atoms::default(),
            tuples: Tuples::default(),
            structs: false,
            morphisms: Part::leaf(false),
        })
    }

    /// Every value, `_`.
    pub fn top() -> Type {
        TOP.with(Type::clone)
    }

    /// The union of `ts`, joined in pairs: `k` tuple or morphism types, each ordered after the
    /// last in the diagrams, cost `O(k log k)` nodes joined this way and `O(k²)` one at a time.
    pub fn union_all(ts: impl IntoIterator<Item = Type>) -> Type {
        Type::pairwise(ts, Type::empty(), |a, b| a | b)
    }

    /// The intersection of `ts`, joined in pairs as in [`Type::union_all`].
    pub fn meet_all(ts: impl IntoIterator<Item = Type>) -> Type {
        Type::pairwise(ts, Type::top(), |a, b| a & b)
    }

    fn pairwise(
        ts: impl IntoIterator<Item = Type>,
        unit: Type,
        op: impl Fn(Type, Type) -> Type,
    ) -> Type {
        let mut ts: Vec<Type> = ts.into_iter().collect();
        while ts.len() > 1 {
            let mut it = std::mem::take(&mut ts).into_iter();
            while let Some(a) = it.next() {
                ts.push(match it.next() {
                    Some(b) => op(a, b),
                    None => a,
                });
            }
        }
        ts.pop().unwrap_or(unit)
    }

    fn with(f: impl FnOnce(&mut Parts)) -> Type {
        let mut p = Type::empty().p().clone();
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
        let one = |l: &mut Lits| l.insert(v);
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
        atoms.set(&name.into(), part);
        Type::with(|p| p.atoms = atoms)
    }

    /// The tuple type `(t1, …, tn)`.
    pub fn tuple(items: Vec<Type>) -> Type {
        Type::with(|p| p.tuples = Tuples::literal(items))
    }

    /// The morphism type with the given bounds and value type.
    pub fn morphism(guarantee: Type, permission: Type, value: Type) -> Type {
        Type::with(|p| {
            p.morphisms = Part::literal(Morphism {
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
            Universe::Tuple => {
                p.tuples = Tuples {
                    rest: true,
                    lens: BTreeMap::new(),
                }
            }
            Universe::Struct => p.structs = true,
            Universe::Morphism => p.morphisms = Part::leaf(true),
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
        self.p().morphisms.is_leaf().is_none()
    }

    /// Whether membership in `self` is decidable at run time: no part of it, nor of a tuple
    /// component or atom payload it holds, is a proper subset of the morphisms.
    pub fn decidable(&self) -> bool {
        self.decidable_from(&mut BTreeSet::new())
    }

    /// `decidable`, with `seen` the recursive nodes already being checked.
    fn decidable_from(&self, seen: &mut BTreeSet<Type>) -> bool {
        if matches!(&*self.0, Node::Rec(_)) && !seen.insert(self.clone()) {
            return true;
        }
        let p = self.p();
        !self.has_morphism_bounds()
            && p.atoms
                .names
                .values()
                .all(|a| a.payload.decidable_from(seen))
            && p.tuples
                .atoms(&mut |t| t.iter().all(|t| t.decidable_from(seen)))
    }

    /// Whether every function is in `self`; for a decidable type, either every function is or
    /// none is.
    pub fn functions(&self) -> bool {
        self.p().morphisms.is_leaf() == Some(true)
    }

    /// Every value of `self`, when there are at most `cap` of them and each can be listed:
    /// bools, finite literal sets, bare atoms, and tuples of such components. `None` for a
    /// type with more values, an infinite part, a payload, a struct or a function, and for a
    /// tuple type one of whose paths has more than `cap` rows before its negated tuples are
    /// taken out.
    pub fn values(&self, cap: usize) -> Option<Vec<Value>> {
        if !matches!(&*self.0, Node::Parts(_)) {
            return None;
        }
        let p = self.p();
        if p.structs || p.morphisms.is_leaf() != Some(false) || p.atoms.cofinite || p.tuples.rest {
            return None;
        }
        let mut out = BTreeSet::new();
        let add = |v: Value, out: &mut BTreeSet<Value>| {
            out.insert(v);
            out.len() <= cap
        };
        for b in [false, true] {
            if p.bools & (1 << u8::from(b)) != 0 && !add(Value::Bool(b), &mut out) {
                return None;
            }
        }
        for lits in [&p.ints, &p.rats, &p.floats, &p.strings] {
            if lits.cofinite {
                return None;
            }
            for v in &lits.values {
                if !add(v.clone(), &mut out) {
                    return None;
                }
            }
        }
        for (name, part) in &p.atoms.names {
            if part.payload != Type::empty() {
                return None;
            }
            if part.bare && !add(Value::atom(name), &mut out) {
                return None;
            }
        }
        for (len, part) in &p.tuples.lens {
            let Part::Bdd(b) = part else {
                return None;
            };
            let mut rows = None;
            let listed = b.paths(&mut { bdd::WALK }, &mut |pos, neg| {
                let meet = pos.iter().fold(vec![Type::top(); *len], |m, p| {
                    m.iter().zip(p.iter()).map(|(a, b)| a & b).collect()
                });
                let mut found = vec![Vec::new()];
                for item in &meet {
                    let Some(vs) = item.values(cap) else {
                        return false;
                    };
                    // Compared with the cap before the product is built, which can be `cap²`.
                    if found.len().saturating_mul(vs.len()) > cap {
                        return false;
                    }
                    found = found
                        .iter()
                        .flat_map(|r| {
                            vs.iter().map(move |v| {
                                let mut r = r.clone();
                                r.push(v.clone());
                                r
                            })
                        })
                        .collect();
                }
                let fits =
                    |t: &Vec<Type>, r: &Vec<Value>| t.iter().zip(r).all(|(t, v)| t.contains(v));
                found.retain(|r| !neg.iter().any(|n| fits(n, r)));
                // The paths are disjoint, so their rows are distinct values.
                let rows = rows.get_or_insert_with(Vec::new);
                rows.extend(found);
                rows.len() <= cap
            });
            if listed != Some(true) {
                return None;
            }
            for r in rows.into_iter().flatten() {
                if !add(Value::Tuple(r), &mut out) {
                    return None;
                }
            }
        }
        Some(out.into_iter().collect())
    }

    /// Whether `v` is in `self`, for a decidable `self`.
    pub fn contains(&self, v: &Value) -> bool {
        let p = self.p();
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
                    part.payload.contains_tuple(&a.args)
                } else {
                    part.payload.p().structs
                }
            }
            Value::Tuple(xs) | Value::Path(xs) => self.contains_tuple(xs),
            Value::Family(_) => self.functions(),
        }
    }

    /// Whether the tuple of `xs` is in `self`, read in place: an atom's payload was copied
    /// into a tuple to be tested, so a value nested `d` deep was copied `d` times.
    fn contains_tuple(&self, xs: &[Value]) -> bool {
        self.p()
            .tuples
            .get(xs.len())
            .eval(&|t: &Vec<Type>| t.iter().zip(xs).all(|(t, x)| t.contains(x)))
    }

    fn zip(&self, other: &Type, op: Op) -> Type {
        let (a, b) = (self.p(), other.p());
        Type::new(Parts {
            digest: 0,
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    Or,
    And,
}

impl Lits {
    fn contains(&self, v: &Value) -> bool {
        self.values.contains(v) != self.cofinite
    }

    fn insert(&mut self, v: &Value) {
        if self.values.insert(v.clone()).is_none() {
            self.sum = self.sum.wrapping_add(scalar(v));
        }
    }

    fn remove(&mut self, v: &Value) {
        if self.values.remove(v).is_some() {
            self.sum = self.sum.wrapping_sub(scalar(v));
        }
    }

    /// The sets combined by `op`, each in `O(s log l)` steps for the smaller set's `s`
    /// literals and the larger's `l`: the result is the larger set changed by the smaller's
    /// literals, or the smaller set's literals filtered.
    fn zip(&self, other: &Lits, op: Op) -> Lits {
        let (a, b) = (self, other);
        let (cofinite, mut out) = match (op, a.cofinite, b.cofinite) {
            (Op::Or, false, false) => (false, Lits::union(a, b)),
            (Op::Or, false, true) => (true, Lits::minus(b, a)),
            (Op::Or, true, false) => (true, Lits::minus(a, b)),
            (Op::Or, true, true) => (true, Lits::meet(a, b)),
            (Op::And, false, false) => (false, Lits::meet(a, b)),
            (Op::And, false, true) => (false, Lits::minus(a, b)),
            (Op::And, true, false) => (false, Lits::minus(b, a)),
            (Op::And, true, true) => (true, Lits::union(a, b)),
        };
        out.cofinite = cofinite;
        out
    }

    fn union(a: &Lits, b: &Lits) -> Lits {
        let (large, small) = if a.values.len() >= b.values.len() {
            (a, b)
        } else {
            (b, a)
        };
        let mut out = large.clone();
        for v in &small.values {
            out.insert(v);
        }
        out
    }

    fn meet(a: &Lits, b: &Lits) -> Lits {
        let (large, small) = if a.values.len() >= b.values.len() {
            (a, b)
        } else {
            (b, a)
        };
        let mut out = Lits::default();
        for v in small.values.iter().filter(|&v| large.values.contains(v)) {
            out.insert(v);
        }
        out
    }

    /// The literals of `a` not in `b`.
    fn minus(a: &Lits, b: &Lits) -> Lits {
        if a.values.len() <= b.values.len() {
            let mut out = Lits::default();
            for v in a.values.iter().filter(|&v| !b.values.contains(v)) {
                out.insert(v);
            }
            return out;
        }
        let mut out = a.clone();
        for v in &b.values {
            out.remove(v);
        }
        out
    }

    fn not(&self) -> Lits {
        Lits {
            cofinite: !self.cofinite,
            ..self.clone()
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

    fn entry(name: &str, p: &AtomPart) -> u64 {
        mix(
            mix(bytes(name.as_bytes()), u64::from(p.bare)),
            p.payload.digest(),
        )
    }

    /// Gives `name` the part `p`, unlisting it when `p` is what an unlisted name has.
    fn set(&mut self, name: &Arc<str>, p: AtomPart) {
        if let Some(old) = self.names.remove(name) {
            self.sum = self.sum.wrapping_sub(Atoms::entry(name, &old));
        }
        let default = if self.cofinite {
            AtomPart::all()
        } else {
            AtomPart::none()
        };
        if p != default {
            self.sum = self.sum.wrapping_add(Atoms::entry(name, &p));
            self.names.insert(name.clone(), p);
        }
    }

    /// The parts combined by `op`, in `O(s log l)` steps for the smaller map's `s` names and
    /// the larger's `l`. A name the smaller map does not list has every payload or none, and
    /// a part combined with all or none is itself, all or none: so the result is the larger
    /// map, or nothing, changed at the smaller map's names.
    fn zip(&self, other: &Atoms, op: Op) -> Atoms {
        let cofinite = match op {
            Op::Or => self.cofinite || other.cofinite,
            Op::And => self.cofinite && other.cofinite,
        };
        let (large, small) = if self.names.len() >= other.names.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut out = match (op, small.cofinite) {
            (Op::Or, false) | (Op::And, true) => large.clone(),
            _ => Atoms::default(),
        };
        out.cofinite = cofinite;
        for (n, p) in &small.names {
            out.set(n, large.get(n).zip(p, op));
        }
        out
    }

    fn not(&self) -> Atoms {
        let mut out = Atoms {
            cofinite: !self.cofinite,
            ..Atoms::default()
        };
        for (n, p) in &self.names {
            out.set(n, p.not());
        }
        out
    }
}

impl Tuples {
    fn literal(items: Vec<Type>) -> Tuples {
        Tuples {
            rest: false,
            lens: BTreeMap::from([(items.len(), Part::literal(items))]),
        }
    }

    fn get(&self, len: usize) -> Part<Vec<Type>> {
        match self.lens.get(&len) {
            Some(b) => b.clone(),
            None => Part::leaf(self.rest),
        }
    }

    /// Drops the lengths whose part is what an unlisted length has.
    fn normal(rest: bool, lens: BTreeMap<usize, Part<Vec<Type>>>) -> Tuples {
        let lens = lens
            .into_iter()
            .filter(|(_, b)| b.is_leaf() != Some(rest))
            .collect();
        Tuples { rest, lens }
    }

    fn zip(&self, other: &Tuples, op: Op) -> Tuples {
        let rest = match op {
            Op::Or => self.rest || other.rest,
            Op::And => self.rest && other.rest,
        };
        let lens = self
            .lens
            .keys()
            .chain(other.lens.keys())
            .map(|n| (*n, self.get(*n).zip(&other.get(*n), op)))
            .collect();
        Tuples::normal(rest, lens)
    }

    fn not(&self) -> Tuples {
        let lens = self.lens.iter().map(|(n, b)| (*n, b.not())).collect();
        Tuples::normal(!self.rest, lens)
    }

    /// Whether `f` holds of every tuple type in a part.
    fn atoms(&self, f: &mut impl FnMut(&Vec<Type>) -> bool) -> bool {
        self.lens.values().all(|b| b.atoms(f))
    }
}

impl Not for &Type {
    type Output = Type;
    fn not(self) -> Type {
        let p = self.p();
        Type::new(Parts {
            digest: 0,
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
        let p = match &*self.0 {
            Node::Parts(p) => p,
            Node::Rec(r) => return f.write_str(r.name()),
        };
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
        tuples(&mut items, &p.tuples);
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
        clauses(&mut items, "morphism", &p.morphisms, &morphism);
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

fn spaced(vs: &OrdSet<Value>) -> String {
    vs.iter()
        .map(Value::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

/// The items of a tuple part. With `rest`, it is every tuple outside its complement's items.
fn tuples(items: &mut Vec<String>, t: &Tuples) {
    if t.rest {
        let mut except = Vec::new();
        tuples(&mut except, &t.not());
        items.push(match except.len() {
            0 => "tuple".into(),
            1 => format!("(& tuple (! {}))", except[0]),
            _ => format!(
                "(& tuple (! (|{})))",
                except.iter().map(|i| format!(" {i}")).collect::<String>()
            ),
        });
        return;
    }
    let tuple = |t: &Vec<Type>| {
        let mut s = String::from("(tuple");
        for c in t {
            s += &format!(" {c}");
        }
        s + ")"
    };
    for (len, b) in &t.lens {
        clauses(items, &tuple(&vec![Type::top(); *len]), b, &tuple);
    }
}

/// One item per path of a diagram: the intersection of the atoms it takes, or `all` when it
/// takes none, and the complements of those it refuses. The items, and the atoms within each,
/// are sorted as text, since the diagram's order of atoms is that of their digests. Past the budget of nodes visited
/// (`bdd::WALK`) the rest is `…`. A part kept as an expression is its connective applied to the items of its operands.
fn clauses<A: bdd::Literal>(
    items: &mut Vec<String>,
    all: &str,
    part: &Part<A>,
    show: &impl Fn(&A) -> String,
) {
    let b = match part.view() {
        Ok(b) => b,
        Err(form) => {
            let item = |p: &Part<A>| {
                let mut sub = Vec::new();
                clauses(&mut sub, all, p, show);
                match sub.len() {
                    0 => "(|)".to_string(),
                    1 => sub.remove(0),
                    _ => format!(
                        "(|{})",
                        sub.iter().map(|i| format!(" {i}")).collect::<String>()
                    ),
                }
            };
            items.push(match form {
                Form::Not(a) => format!("(& {all} (! {}))", item(a)),
                Form::Or(a, b) => format!("(| {} {})", item(a), item(b)),
                Form::And(a, b) => format!("(& {} {})", item(a), item(b)),
            });
            return;
        }
    };
    let mut budget = bdd::WALK;
    let mut found = Vec::new();
    let done = b.paths(&mut budget, &mut |pos, neg| {
        let mut lits: Vec<String> = pos.iter().map(|a| show(a)).collect();
        lits.sort();
        if lits.is_empty() {
            lits.push(all.into());
        }
        let mut refused: Vec<String> = neg.iter().map(|n| format!("(! {})", show(n))).collect();
        refused.sort();
        lits.extend(refused);
        match lits.len() {
            1 => found.push(lits.remove(0)),
            _ => found.push(format!(
                "(&{})",
                lits.iter().map(|l| format!(" {l}")).collect::<String>()
            )),
        }
        true
    });
    found.sort();
    items.extend(found);
    if done.is_none() {
        items.push("…".into());
    }
}
