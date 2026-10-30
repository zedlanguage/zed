//! Kernel values: scalars, atoms with their payloads, tuples, keypaths and families
//! (step L1.17).
//!
//! Values are totally ordered by the natural order of DESIGN.md sec:keys: kinds in the order
//! atoms, `bool`, numbers, strings, tuples, keypaths, families; numbers by value across
//! `int`, `rat` and floats, an `int` before a `rat` before a float of equal value. Rust's `==`
//! on values is the ties of that order: the bitwise identity that keys and the law catalog
//! read. The language's `==` is [`Value::surface_eq`], which differs only at floats.

use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::family::Family;
use crate::num::{Exact, Rat};

/// A 64-bit float that compares bitwise after NaN canonicalization, as every kernel equation
/// on a float-bearing value does (sec:kernel, the law catalog): `-0.0` and `0.0` are different
/// values, and every NaN is the one canonical NaN.
#[derive(Clone, Copy)]
pub struct F64(f64);

impl F64 {
    /// Wraps `x`, replacing any NaN by the canonical NaN.
    pub fn new(x: f64) -> Self {
        if x.is_nan() { F64(f64::NAN) } else { F64(x) }
    }

    /// The wrapped float.
    pub fn get(self) -> f64 {
        self.0
    }
}

impl PartialEq for F64 {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for F64 {}

impl Ord for F64 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl PartialOrd for F64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for F64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// An atom such as `#empty`, `#ioError("disk full")` or `#err(code: 3)`. Failure is data
/// (sec:failure): an atom is an ordinary value that flows through the kernel like any other.
/// A payload is a tuple, by position, or a struct, by name (sec:syntax, the `#name(args)`
/// row); a struct payload keeps its fields in the code point order of their names, so the
/// written order of a construction is not part of the value.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Atom {
    /// The name, without the leading `#`.
    pub name: Arc<str>,
    /// The field names of a struct payload, sorted; empty for a tuple payload.
    pub fields: Vec<Arc<str>>,
    /// The payload's values, one per field of a struct payload; empty for a bare atom.
    pub args: Vec<Value>,
}

/// A kernel value. Values are totally ordered, so any value can be a key; the order of keys
/// is the order a family's entries are visited in.
#[derive(Clone, Debug)]
pub enum Value {
    /// `true` or `false`.
    Bool(bool),
    /// An integer in the 64-bit range.
    Int(i64),
    /// An integer outside the 64-bit range; never one inside it.
    Big(Arc<BigInt>),
    /// A rational, `3r` or `1r/3r`.
    Rat(Arc<Rat>),
    /// A float, compared bitwise.
    Float(F64),
    /// A string.
    Str(Arc<str>),
    /// A failure atom.
    Atom(Atom),
    /// A tuple, such as a composite key.
    Tuple(Vec<Value>),
    /// A keypath as a value: what a `reindex` key map reads and returns (sec:keypaths).
    Path(Vec<Value>),
    /// A family: one level of keys, whose values may be families in turn.
    Family(Family),
}

impl Value {
    /// A string value.
    pub fn str(s: &str) -> Self {
        Value::Str(s.into())
    }

    /// A float value.
    pub fn float(x: f64) -> Self {
        Value::Float(F64::new(x))
    }

    /// A bare atom such as `#empty`, given its name without the `#`.
    pub fn atom(name: &str) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            fields: Vec::new(),
            args: Vec::new(),
        })
    }

    /// An atom with a tuple payload, such as `#ioError("disk full")`.
    pub fn atom_with(name: &str, args: Vec<Value>) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            fields: Vec::new(),
            args,
        })
    }

    /// An atom with a struct payload, such as `#err(code: 3)`, its fields in any order;
    /// `None` when a name repeats.
    pub fn atom_named(name: &str, fields: Vec<(Arc<str>, Value)>) -> Option<Self> {
        let mut fields = fields;
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        if fields.windows(2).any(|w| w[0].0 == w[1].0) {
            return None;
        }
        let (fields, args) = fields.into_iter().unzip();
        Some(Value::Atom(Atom {
            name: name.into(),
            fields,
            args,
        }))
    }

    /// The failure several loose atoms make together (DESIGN.md sec:failure): the set of the
    /// distinct ones as `#errs({…})`, an `#errs` among them giving its members, and a single
    /// failure as itself.
    pub fn merge_failures<'a>(atoms: impl IntoIterator<Item = &'a Value>) -> Value {
        let mut set = std::collections::BTreeSet::new();
        for a in atoms {
            match a.errs() {
                Some(members) => set.extend(members.iter().map(|(k, _)| k.clone())),
                None => {
                    set.insert(a.clone());
                }
            }
        }
        if set.len() == 1 {
            return set.pop_first().expect("one member");
        }
        let members = Family::of(set.into_iter().map(|a| (a.clone(), a)));
        Value::atom_with("errs", vec![Value::Family(members)])
    }

    /// The set of an `#errs({…})`.
    pub fn errs(&self) -> Option<&Family> {
        match self {
            Value::Atom(a) if &*a.name == "errs" && a.fields.is_empty() => {
                match a.args.as_slice() {
                    [Value::Family(f)] => Some(f),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The integer `n`, as an `Int` when it is in the 64-bit range.
    pub fn int(n: BigInt) -> Self {
        match n.to_i64() {
            Some(n) => Value::Int(n),
            None => Value::Big(Arc::new(n)),
        }
    }

    /// The integer whose digits, in base `radix`, are `digits`.
    pub fn int_text(digits: &str, radix: u32) -> Option<Self> {
        BigInt::parse_bytes(digits.as_bytes(), radix).map(Value::int)
    }

    /// The rational `r`.
    pub fn rat(r: Rat) -> Self {
        Value::Rat(Arc::new(r))
    }

    /// The integer inside, of either width.
    pub fn as_bigint(&self) -> Option<BigInt> {
        match self {
            Value::Int(n) => Some(BigInt::from(*n)),
            Value::Big(n) => Some((**n).clone()),
            _ => None,
        }
    }

    /// The value as a key (sec:type_resolution, "Equality and order corner rules"): `-0.0` becomes `0.0` at any depth, since `0.0 == -0.0`
    /// makes the two zeros one key, which then holds the same bits whichever zero arrived
    /// first. NaN is already one value.
    pub fn key(&self) -> Value {
        let all = |vs: &[Value]| vs.iter().map(Value::key).collect();
        match self {
            Value::Float(x) if x.get() == 0.0 => Value::float(0.0),
            Value::Tuple(vs) => Value::Tuple(all(vs)),
            Value::Path(vs) => Value::Path(all(vs)),
            Value::Atom(a) if !a.args.is_empty() => Value::Atom(Atom {
                args: all(&a.args),
                ..a.clone()
            }),
            v => v.clone(),
        }
    }

    /// The language's order on two values of one kind: structural, except that two floats
    /// compare as IEEE 754 does, so `-0.0` and `0.0` are equal and a NaN is unordered, and
    /// tuples compare component by component in that order. `None` when they are unordered.
    pub fn surface_cmp(&self, other: &Value) -> Option<Ordering> {
        match (self, other) {
            (Value::Float(a), Value::Float(b)) => a.get().partial_cmp(&b.get()),
            (Value::Tuple(a), Value::Tuple(b)) => {
                for (x, y) in a.iter().zip(b) {
                    match x.surface_cmp(y)? {
                        Ordering::Equal => {}
                        o => return Some(o),
                    }
                }
                Some(a.len().cmp(&b.len()))
            }
            (a, b) => Some(a.cmp(b)),
        }
    }

    /// The language's `==` (sec:failure, M0.11): structural, except that two floats compare
    /// as IEEE 754 does, so `NaN != NaN` and `0.0 == -0.0`, at any depth.
    pub fn surface_eq(&self, other: &Value) -> bool {
        let all = |a: &[Value], b: &[Value]| {
            a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.surface_eq(y))
        };
        match (self, other) {
            (Value::Float(a), Value::Float(b)) => a.get() == b.get(),
            (Value::Tuple(a), Value::Tuple(b)) | (Value::Path(a), Value::Path(b)) => all(a, b),
            (Value::Atom(a), Value::Atom(b)) => {
                a.name == b.name && a.fields == b.fields && all(&a.args, &b.args)
            }
            (Value::Family(a), Value::Family(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|((k, v), (l, w))| k == l && v.surface_eq(w))
            }
            _ => self == other,
        }
    }

    /// The kind of a value, by its rank in the natural order; the numbers are one kind.
    fn kind(&self) -> u8 {
        match self {
            Value::Atom(_) => 0,
            Value::Bool(_) => 1,
            Value::Int(_) | Value::Big(_) | Value::Rat(_) | Value::Float(_) => 2,
            Value::Str(_) => 3,
            Value::Tuple(_) => 4,
            Value::Path(_) => 5,
            Value::Family(_) => 6,
        }
    }

    /// The numeric kind: `int` (either width), `rat` or float; `None` for any other value.
    pub fn number_kind(&self) -> Option<u8> {
        match self {
            Value::Int(_) | Value::Big(_) => Some(0),
            Value::Rat(_) => Some(1),
            Value::Float(_) => Some(2),
            _ => None,
        }
    }

    /// The number's exact place on the extended line.
    pub(crate) fn exact(&self) -> Exact {
        match self {
            Value::Int(n) => Exact::Finite(Rat::int(BigInt::from(*n))),
            Value::Big(n) => Exact::Finite(Rat::int((**n).clone())),
            Value::Rat(r) => Exact::Finite((**r).clone()),
            Value::Float(x) => Exact::float(x.get()),
            _ => unreachable!("only numbers are placed on the line"),
        }
    }

    /// The integer inside, if this is one.
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// The family inside, if this is one.
    pub fn as_family(&self) -> Option<&Family> {
        match self {
            Value::Family(f) => Some(f),
            _ => None,
        }
    }
}

/// Two numbers by value; equal values by kind, `int` before `rat` before a float, and two
/// floats by their total order, which puts `-0.0` before `0.0` and NaN last.
fn number_cmp(a: &Value, b: &Value) -> Ordering {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::Float(x), Value::Float(y)) => x.cmp(y),
        (Value::Rat(x), Value::Rat(y)) => x.cmp(y),
        _ => a
            .exact()
            .cmp(&b.exact())
            .then(a.number_kind().cmp(&b.number_kind())),
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        use Value::*;
        match (self, other) {
            (Bool(a), Bool(b)) => a.cmp(b),
            (Str(a), Str(b)) => a.cmp(b),
            (Atom(a), Atom(b)) => a.cmp(b),
            (Tuple(a), Tuple(b)) | (Path(a), Path(b)) => a.cmp(b),
            (Family(a), Family(b)) => a.cmp(b),
            _ if self.kind() == 2 && other.kind() == 2 => number_cmp(self, other),
            _ => self.kind().cmp(&other.kind()),
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Value {
    /// Equal exactly when [`Ord::cmp`] says so. Two families are compared by their maps,
    /// which differ at once in size and skip the nodes they share, so the test of a lattice
    /// `fix` for its fixpoint does not read the whole iterate each round.
    fn eq(&self, other: &Self) -> bool {
        use Value::*;
        match (self, other) {
            (Family(a), Family(b)) => a == b,
            (Tuple(a), Tuple(b)) | (Path(a), Path(b)) => a == b,
            _ => self.cmp(other) == Ordering::Equal,
        }
    }
}

impl Eq for Value {}

impl From<i64> for Value {
    fn from(n: i64) -> Self {
        Value::Int(n)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::str(s)
    }
}

impl From<Family> for Value {
    fn from(f: Family) -> Self {
        Value::Family(f)
    }
}

fn write_list(f: &mut fmt::Formatter<'_>, items: &[Value]) -> fmt::Result {
    for (i, v) in items.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{v}")?;
    }
    Ok(())
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Int(n) => write!(f, "{n}"),
            Value::Big(n) => write!(f, "{n}"),
            Value::Rat(r) => write!(f, "{r}"),
            Value::Float(x) => write!(f, "{}", crate::num::show_f64(x.get())),
            Value::Str(s) => write!(f, "{s:?}"),
            Value::Atom(a) => {
                write!(f, "#{}", a.name)?;
                if !a.args.is_empty() {
                    write!(f, "(")?;
                    for (i, v) in a.args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        if let Some(k) = a.fields.get(i) {
                            write!(f, "{k}: ")?;
                        }
                        write!(f, "{v}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Value::Tuple(items) => {
                write!(f, "(")?;
                write_list(f, items)?;
                write!(f, ")")
            }
            Value::Path(keys) => {
                write!(f, "[")?;
                for (i, k) in keys.iter().enumerate() {
                    if i > 0 {
                        write!(f, " -> ")?;
                    }
                    write!(f, "{k}")?;
                }
                write!(f, "]")
            }
            Value::Family(fam) => write!(f, "{fam}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signed_zeros_differ_and_nans_are_one_value() {
        assert_ne!(Value::float(0.0), Value::float(-0.0));
        assert!(Value::float(-0.0) < Value::float(0.0));
        let other_nan = f64::from_bits(f64::NAN.to_bits() ^ 1);
        assert!(other_nan.is_nan());
        assert_eq!(Value::float(other_nan), Value::float(f64::NAN));
    }

    #[test]
    fn display_forms() {
        assert_eq!(Value::atom("empty").to_string(), "#empty");
        let io = Value::atom_with("ioError", vec![Value::str("disk full")]);
        assert_eq!(io.to_string(), "#ioError(\"disk full\")");
        let t = Value::Tuple(vec![Value::Int(1), Value::Bool(true), Value::float(-0.0)]);
        assert_eq!(t.to_string(), "(1, true, -0.0)");
        let p = Value::Path(vec![Value::str("ann"), Value::Int(2)]);
        assert_eq!(p.to_string(), r#"["ann" -> 2]"#);
    }

    #[test]
    fn accessors() {
        assert_eq!(Value::Int(3).as_int(), Some(3));
        assert_eq!(Value::str("x").as_int(), None);
        assert!(Value::Int(3).as_family().is_none());
        assert!(Value::from(Family::default()).as_family().is_some());
        assert_eq!(Value::from(true), Value::Bool(true));
        assert_eq!(F64::new(2.5).get(), 2.5);
        assert_eq!(
            F64::new(1.0).partial_cmp(&F64::new(2.0)),
            Some(Ordering::Less)
        );
    }
}
