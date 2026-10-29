//! Kernel values: scalars, failure atoms, tuples and families.

use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

use crate::family::Family;

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

/// A failure atom such as `#empty` or `#ioError("disk full")`. Failure is data (sec:failure):
/// an atom is an ordinary value that flows through the kernel like any other.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Atom {
    /// The name, without the leading `#`.
    pub name: Arc<str>,
    /// The payload; empty for a bare atom.
    pub args: Vec<Value>,
}

/// A kernel value. Values are totally ordered, so any value can be a key; the order of keys
/// is the order a family's entries are visited in.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Value {
    /// `true` or `false`.
    Bool(bool),
    /// A machine integer.
    Int(i64),
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
            args: Vec::new(),
        })
    }

    /// An atom with a payload, such as `#ioError("disk full")`.
    pub fn atom_with(name: &str, args: Vec<Value>) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            args,
        })
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
            Value::Float(x) => write!(f, "{x:?}"),
            Value::Str(s) => write!(f, "{s:?}"),
            Value::Atom(a) => {
                write!(f, "#{}", a.name)?;
                if !a.args.is_empty() {
                    write!(f, "(")?;
                    write_list(f, &a.args)?;
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
    }
}
