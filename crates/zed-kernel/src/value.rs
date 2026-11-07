//! Kernel values: scalars, atoms with their payloads, tuples, keypaths and families
//! (step L1.17).
//!
//! Values are totally ordered by the natural order of DESIGN.md sec:order: kinds in the order
//! atoms, `bool`, numbers, strings, tuples, keypaths, families; numbers by value across
//! `int`, `rat` and floats, an `int` before a `rat` before a float of equal value. Rust's `==`
//! on values is the ties of that order: the bitwise identity that keys and the law catalog
//! read. The language's `==` is [`Value::surface_eq`], which differs only at floats.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::Deref;
use std::slice;
use std::sync::Arc;

use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

use crate::deep::{self, Part};
use crate::family::{Family, Id, fresh_id};
use crate::num::{Exact, Rat, TooLarge, read_decimal, room, sign_of};
use crate::text::Text;

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
/// A payload is a tuple, by position, or a struct, by name (sec:lexical, the `#name(args)`
/// row); a struct payload keeps its fields in the code point order of their names, so the
/// written order of a construction is not part of the value.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Atom {
    /// The name, without the leading `#`.
    pub name: Arc<str>,
    /// The field names of a struct payload, sorted; empty for a tuple payload. Shared, so a
    /// copy of the atom is O(1).
    pub fields: Fields,
    /// The payload's values, one per field of a struct payload; empty for a bare atom.
    pub args: Items,
}

/// The field names of a struct payload, shared, with the [`Id`] of the list as it was built, so
/// a walk can read a list shared by many atoms once. It is one pointer wide, and `None` for no
/// fields, which keeps an [`Atom`] at 48 bytes and a [`Value`] at 56 next to the id in
/// [`Items`].
#[derive(Clone, Default)]
pub struct Fields(Option<Arc<Names>>);

struct Names {
    id: Id,
    names: Box<[Arc<str>]>,
}

impl Fields {
    /// The id of the list: copies share it, and no other list has it. Empty lists have id 0.
    pub(crate) fn id(&self) -> Id {
        self.0.as_ref().map_or(0, |n| n.id)
    }
}

impl Deref for Fields {
    type Target = [Arc<str>];

    fn deref(&self) -> &[Arc<str>] {
        self.0.as_ref().map_or(&[], |n| &n.names)
    }
}

impl From<Vec<Arc<str>>> for Fields {
    fn from(names: Vec<Arc<str>>) -> Self {
        match names.is_empty() {
            true => Fields::default(),
            false => Fields(Some(Arc::new(Names {
                id: fresh_id(),
                names: names.into(),
            }))),
        }
    }
}

impl FromIterator<Arc<str>> for Fields {
    fn from_iter<I: IntoIterator<Item = Arc<str>>>(names: I) -> Self {
        Fields::from(names.into_iter().collect::<Vec<_>>())
    }
}

impl PartialEq for Fields {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id() || **self == **other
    }
}

impl Eq for Fields {}

impl Ord for Fields {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.id() == other.id() {
            true => Ordering::Equal,
            false => (**self).cmp(&**other),
        }
    }
}

impl PartialOrd for Fields {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Fields {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

/// The values inside a tuple, a keypath or a payload, shared: a copy is a reference count, so
/// reading a variable that holds a tuple of any size is O(1). It owns its drop, comparison and
/// `Debug` form so that each runs on the heap, whatever the depth (see `crate::deep`).
///
/// The second field is the sequence's [`Id`], drawn when the sequence is built: copies share
/// it, no other sequence has it, and the sequence is never changed in place, so a walk that
/// meets a shared sequence again knows it by its id (memo keys are ids or structure, never
/// addresses). Empty sequences have id 0.
#[derive(Clone, Default)]
pub struct Items(Arc<[Value]>, Id);

impl Items {
    /// The values, in order.
    pub fn as_slice(&self) -> &[Value] {
        &self.0
    }

    /// Whether `self` and `other` are one shared sequence, so equal without reading them.
    pub(crate) fn same(&self, other: &Items) -> bool {
        self.1 == other.1
    }

    /// The id of the sequence.
    pub(crate) fn id(&self) -> Id {
        self.1
    }

    /// Whether another holder shares the sequence, so a walk of a value can meet it twice. A
    /// sequence held once is reached by one path only, through its one holder.
    pub(crate) fn is_shared(&self) -> bool {
        Arc::strong_count(&self.0) > 1
    }

    /// The ids of `a` and `b` when a walk over both can meet the pair again: when either is
    /// shared. Empty sequences are read at once.
    pub(crate) fn pair(a: &Items, b: &Items) -> Option<deep::Pair> {
        let again = (a.is_shared() || b.is_shared()) && !(a.is_empty() && b.is_empty());
        again.then_some((a.1, b.1))
    }

    /// The values, as a vector: moved out when this is their only holder, and each copied by
    /// a reference count otherwise.
    pub fn into_vec(mut self) -> Vec<Value> {
        match Arc::get_mut(&mut self.0) {
            // A placeholder takes each value's place; what is left is a slice of scalars.
            Some(only) => only
                .iter_mut()
                .map(|v| mem::replace(v, Value::Bool(false)))
                .collect(),
            None => self.0.to_vec(),
        }
    }
}

impl Deref for Items {
    type Target = [Value];

    fn deref(&self) -> &[Value] {
        &self.0
    }
}

impl From<Vec<Value>> for Items {
    fn from(values: Vec<Value>) -> Self {
        // The empty slice is one static allocation; `Arc::from` would allocate per call.
        match values.is_empty() {
            true => Items::default(),
            false => Items(values.into(), fresh_id()),
        }
    }
}

impl FromIterator<Value> for Items {
    fn from_iter<I: IntoIterator<Item = Value>>(values: I) -> Self {
        Items::from(values.into_iter().collect::<Vec<_>>())
    }
}

impl IntoIterator for Items {
    type Item = Value;
    type IntoIter = std::vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<'a> IntoIterator for &'a Items {
    type Item = &'a Value;
    type IntoIter = slice::Iter<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl Drop for Items {
    fn drop(&mut self) {
        if !self.0.is_empty() {
            deep::free(Part::Items(mem::take(&mut self.0)));
        }
    }
}

impl PartialEq for Items {
    fn eq(&self, other: &Self) -> bool {
        deep::items_eq(self, other)
    }
}

impl Eq for Items {}

impl Ord for Items {
    fn cmp(&self, other: &Self) -> Ordering {
        deep::items_cmp(self, other)
    }
}

impl PartialOrd for Items {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A kernel value. Values are totally ordered, so any value can be a key; the order of keys
/// is the order a family's entries are visited in.
#[derive(Clone)]
pub enum Value {
    /// `true` or `false`.
    Bool(bool),
    /// An integer in the 64-bit range.
    Int(i64),
    /// An integer outside the 64-bit range, never one inside it: a [`Rat`] that is an integer,
    /// which may hold its prime powers unbuilt.
    Big(Arc<Rat>),
    /// A rational, `3r` or `1r/3r`.
    Rat(Arc<Rat>),
    /// A float, compared bitwise.
    Float(F64),
    /// A string.
    Str(Text),
    /// A failure atom.
    Atom(Atom),
    /// A tuple, such as a composite key.
    Tuple(Items),
    /// A keypath as a value: what a `reindex` key map reads and returns (sec:keypaths).
    Path(Items),
    /// A family: one level of keys, whose values may be families in turn.
    Family(Family),
}

impl Value {
    /// A string value.
    pub fn str(s: &str) -> Self {
        Value::Str(s.into())
    }

    /// A tuple value.
    pub fn tuple(items: Vec<Value>) -> Self {
        Value::Tuple(items.into())
    }

    /// A keypath value.
    pub fn path(keys: Vec<Value>) -> Self {
        Value::Path(keys.into())
    }

    /// A float value.
    pub fn float(x: f64) -> Self {
        Value::Float(F64::new(x))
    }

    /// A bare atom such as `#empty`, given its name without the `#`.
    pub fn atom(name: &str) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            fields: Fields::default(),
            args: Items::default(),
        })
    }

    /// An atom with a tuple payload, such as `#ioError("disk full")`; a shared name is kept,
    /// not copied.
    pub fn atom_with(name: impl Into<Arc<str>>, args: Vec<Value>) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            fields: Fields::default(),
            args: args.into(),
        })
    }

    /// `#ioError(op:, path:, why:)`: a failed read or write of a port, its operation (`read`
    /// or `write`), its path and the operating system's reason (DESIGN.md sec:ports).
    pub fn io_error(op: &str, path: &str, why: &str) -> Self {
        // The fields in name order, as `atom_named` sorts them.
        Value::Atom(Atom {
            name: "ioError".into(),
            fields: vec![Arc::from("op"), "path".into(), "why".into()].into(),
            args: vec![Value::str(op), Value::str(path), Value::str(why)].into(),
        })
    }

    /// An atom with a struct payload, such as `#err(code: 3)`, its fields in any order;
    /// `None` when a name repeats. A shared name is kept, not copied.
    pub fn atom_named(name: impl Into<Arc<str>>, fields: Vec<(Arc<str>, Value)>) -> Option<Self> {
        let mut fields = fields;
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        if fields.windows(2).any(|w| w[0].0 == w[1].0) {
            return None;
        }
        let (fields, args): (Vec<Arc<str>>, Vec<Value>) = fields.into_iter().unzip();
        Some(Value::Atom(Atom {
            name: name.into(),
            fields: fields.into(),
            args: args.into(),
        }))
    }

    /// The failure several loose atoms make together (DESIGN.md sec:failure): the set of the
    /// distinct ones as `#errs({…})`, an `#errs` among them giving its members, and a single
    /// failure as itself.
    pub fn merge_failures<'a>(atoms: impl IntoIterator<Item = &'a Value>) -> Value {
        // The largest set is extended, not copied, so a chain of n merges costs O(n log n).
        let atoms: Vec<&Value> = atoms.into_iter().collect();
        let base = atoms
            .iter()
            .filter_map(|a| a.errs())
            .max_by_key(|f| f.len());
        let mut set = base.cloned().unwrap_or_default();
        let mut added = Vec::new();
        for a in &atoms {
            match a.errs() {
                Some(m) if base.is_some_and(|b| std::ptr::eq(m, b)) => {}
                Some(m) => added.extend(m.iter().map(|(k, v)| (k.clone(), v.clone()))),
                None => added.push((a.key(), (*a).clone())),
            }
        }
        set.extend(added);
        if set.len() == 1 {
            return set.iter().next().expect("one member").1.clone();
        }
        Value::atom_with("errs", vec![Value::Family(set)])
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
            None => Value::Big(Arc::new(Rat::int(n))),
        }
    }

    /// The integer `r`, which must be one, as an `Int` when it is in the 64-bit range.
    pub fn integer(r: Rat) -> Self {
        match r.small_integer() {
            Some(n) => Value::int(n),
            None => Value::Big(Arc::new(r)),
        }
    }

    /// The integer whose digits, in base `radix` (2 to 36), are `text`, after an optional `-` or
    /// `+`; `Ok(None)` when they are not, and [`TooLarge`] when the system refuses the memory for
    /// reading them, asked before anything is built.
    pub fn int_text(text: &str, radix: u32) -> Result<Option<Self>, TooLarge> {
        let (sign, digits) = sign_of(text);
        let int = |n: BigUint| Value::int(BigInt::from_biguint(sign, n));
        if radix == 10 {
            return Ok(read_decimal(digits)?.map(int));
        }
        if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
            return Ok(None);
        }
        // Complexity tradeoff: the memory asked for is twice a byte per digit plus the
        // integer's width, a measured bound, not a proved one, on num-bigint's reading of a
        // text in a base other than 10, which holds the digits as bytes and then packs them
        // into words: the peak heap was 8 bits per digit plus the width (9, 11 and 12 bits per
        // digit in bases 2, 8 and 16) over texts of 2^12 to 2^22 digits, half the ask. A width
        // alone undercounts base 2, whose byte per digit is eight times its width. So a text
        // needing less is refused when the free memory lies between the two, and none aborts.
        // Tested by `a_long_integer_literal_is_refused_when_memory_is_short` (COMPLEXITY.md
        // K30). A complete solution would pack the digits into words with memory reserved once.
        let per_digit = radix.ilog2() + u32::from(!radix.is_power_of_two());
        room((BigUint::from(digits.len()) * (8 + per_digit)) << 1u32)?;
        Ok(BigUint::parse_bytes(digits.as_bytes(), radix).map(int))
    }

    /// The rational `r`.
    pub fn rat(r: Rat) -> Self {
        Value::Rat(Arc::new(r))
    }

    /// The integer inside, of either width.
    pub fn as_integer(&self) -> Option<Cow<'_, Rat>> {
        match self {
            Value::Int(n) => Some(Cow::Owned(Rat::int(BigInt::from(*n)))),
            Value::Big(n) => Some(Cow::Borrowed(n)),
            _ => None,
        }
    }

    /// The value as a key (sec:type_resolution, "Equality and order corner rules"): `-0.0`
    /// becomes `0.0` at any depth, since `0.0 == -0.0` makes the two zeros one key, which then
    /// holds the same bits whichever zero arrived first. NaN is already one value. A value that
    /// is its own key is shared, not copied.
    pub fn key(&self) -> Value {
        match self {
            Value::Tuple(_) | Value::Path(_) | Value::Atom(_) if self.is_key() => self.clone(),
            Value::Tuple(_) | Value::Path(_) | Value::Atom(_) => {
                let mut one = deep::copy(slice::from_ref(self), key_leaf);
                one.pop().expect("a copy of one value holds one value")
            }
            leaf => key_leaf(leaf),
        }
    }

    /// Whether the value is its own key: whether it holds no `-0.0`.
    pub fn is_key(&self) -> bool {
        deep::all_leaves(slice::from_ref(self), |v| match v {
            Value::Float(x) => !(x.get() == 0.0 && x.get().is_sign_negative()),
            _ => true,
        })
    }

    /// The language's order on two values of one kind: structural, except that two floats
    /// compare as IEEE 754 does, so `-0.0` and `0.0` are equal and a NaN is unordered, and
    /// tuples compare component by component in that order. `None` when they are unordered.
    pub fn surface_cmp(&self, other: &Value) -> Option<Ordering> {
        deep::surface_cmp(self, other)
    }

    /// The language's `==` (sec:failure, M0.11): structural, except that two floats compare
    /// as IEEE 754 does, so `NaN != NaN` and `0.0 == -0.0`, at any depth.
    pub fn surface_eq(&self, other: &Value) -> bool {
        deep::surface_eq(self, other)
    }

    /// The order on two values at least one of which holds no parts: the two values' kinds,
    /// or their scalars. Two values of one kind with parts are compared in [`crate::deep`].
    pub(crate) fn scalar_cmp(&self, other: &Value) -> Ordering {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
            (Value::Str(a), Value::Str(b)) => a.cmp(b),
            _ if self.kind() == 2 && other.kind() == 2 => number_cmp(self, other),
            _ => self.kind().cmp(&other.kind()),
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

    /// The type of every value of this one's kind, as a program writes it (DESIGN.md L1.40d):
    /// `int` for an integer of either width, `#a` for a bare atom and `#a(..)` for one with a
    /// payload, `(..)` for a tuple or a keypath, `_ ->? _` for a family. A type error names
    /// this, not the value, which may be too large to print; its cost is the atom's name.
    pub fn kind_type(&self) -> String {
        match self {
            Value::Bool(_) => "bool".into(),
            Value::Int(_) | Value::Big(_) => "int".into(),
            Value::Rat(_) => "rat".into(),
            Value::Float(_) => "f64".into(),
            Value::Str(_) => "String".into(),
            Value::Atom(a) if a.args.is_empty() => format!("#{}", a.name),
            Value::Atom(a) => format!("#{}(..)", a.name),
            Value::Tuple(_) | Value::Path(_) => "(..)".into(),
            Value::Family(_) => "_ ->? _".into(),
        }
    }

    /// The number's exact place on the extended line. A wide number is borrowed, not copied:
    /// a copy would be built without asking the system for the memory.
    pub(crate) fn exact(&self) -> Exact<'_> {
        match self {
            Value::Int(n) => Exact::Finite(Cow::Owned(Rat::int(BigInt::from(*n)))),
            Value::Big(n) | Value::Rat(n) => Exact::Finite(Cow::Borrowed(n)),
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

/// A value `Value::key` keeps: anything but a zero, which is made positive.
fn key_leaf(v: &Value) -> Value {
    match v {
        Value::Float(x) if x.get() == 0.0 => Value::float(0.0),
        v => v.clone(),
    }
}

/// Two numbers by value; equal values by kind, `int` before `rat` before a float, and two
/// floats by their total order, which puts `-0.0` before `0.0` and NaN last.
fn number_cmp(a: &Value, b: &Value) -> Ordering {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::Float(x), Value::Float(y)) => x.cmp(y),
        (Value::Rat(x), Value::Rat(y)) => x.cmp(y),
        (Value::Big(x), Value::Big(y)) => x.cmp(y),
        // A `Big` is never in the 64-bit range.
        (Value::Int(_), Value::Big(y)) => match y.is_negative() {
            true => Ordering::Greater,
            false => Ordering::Less,
        },
        (Value::Big(x), Value::Int(_)) => match x.is_negative() {
            true => Ordering::Less,
            false => Ordering::Greater,
        },
        _ => a
            .exact()
            .cmp(&b.exact())
            .then(a.number_kind().cmp(&b.number_kind())),
    }
}

/// Whether two numbers are the same: of one kind and one value, two floats bitwise. Two exact
/// numbers are compared by their normal forms ([`Rat`]'s `==`), which builds nothing unless a
/// coefficient is divisible by a prime the other keeps as a power.
pub(crate) fn number_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Big(x), Value::Big(y)) | (Value::Rat(x), Value::Rat(y)) => x == y,
        (Value::Float(x), Value::Float(y)) => x.cmp(y) == Ordering::Equal,
        _ => false,
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        deep::cmp(self, other)
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
            (Atom(a), Atom(b)) => a == b,
            _ if self.kind() == 2 && other.kind() == 2 => number_eq(self, other),
            _ => self.scalar_cmp(other) == Ordering::Equal,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_value_is_56_bytes() {
        // Each value of every tuple, list and family costs this much; an id in `Items` with an
        // atom's fields two words wide made it 64 and cost 13 to 27% more peak memory on runs
        // without provenance (COMPLEXITY.md K25). The fields are one word wide, so the atom,
        // the widest kind, holds the id in 48 bytes (ADDR-keys).
        assert_eq!(size_of::<Value>(), 56);
        assert_eq!(size_of::<Atom>(), 48);
        assert_eq!(size_of::<Items>(), 24);
        assert_eq!(size_of::<Fields>(), 8);
    }

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
        let t = Value::tuple(vec![Value::Int(1), Value::Bool(true), Value::float(-0.0)]);
        assert_eq!(t.to_string(), "(1, true, -0.0)");
        let p = Value::path(vec![Value::str("ann"), Value::Int(2)]);
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
