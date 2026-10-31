//! Float classes (DESIGN.md sec:domains, "float classes (finite / non-NaN facets; width
//! f16/f32/f64)"; step L1.24).
//!
//! An element is the set of kinds a float may be — negative infinity, finite, positive
//! infinity, NaN — and a width: the narrowest IEEE binary format that holds each value
//! exactly. Every infinity and the NaN are in every format, and a finite value is in a format
//! when its significand fits the format's precision and its exponent the format's range.
//! Join is union of kinds and the wider width, meet intersection and the narrower; the empty
//! set of kinds is the bottom, whatever the width. The lattice has finite height, so its
//! widening is the join.

use std::fmt;

use super::lattice::{Landmarks, Lattice};

/// An IEEE binary format, narrowest first.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Width {
    /// binary16.
    F16,
    /// binary32.
    F32,
    /// binary64.
    F64,
}

impl Width {
    /// The significand bits, the least exponent of a subnormal's last bit, and the largest
    /// finite value.
    fn format(self) -> (u32, i32, f64) {
        match self {
            Width::F16 => (11, -24, 65504.0),
            Width::F32 => (24, -149, f32::MAX as f64),
            Width::F64 => (53, -1074, f64::MAX),
        }
    }

    /// Whether the finite `x` is exactly a value of this format.
    fn holds(self, x: f64) -> bool {
        if x == 0.0 {
            return true;
        }
        let (bits, least, max) = self.format();
        if x.abs() > max {
            return false;
        }
        // x = m · 2^e with m odd.
        let raw = x.abs().to_bits();
        let (field, frac) = ((raw >> 52) as i32, raw & ((1 << 52) - 1));
        let (mut m, mut e) = if field == 0 {
            (frac, -1074)
        } else {
            (frac | (1 << 52), field - 1075)
        };
        let tz = m.trailing_zeros();
        m >>= tz;
        e += tz as i32;
        m < (1u64 << bits) && e >= least
    }

    /// The narrowest format holding `x`.
    pub fn of(x: f64) -> Width {
        if !x.is_finite() {
            return Width::F16;
        }
        [Width::F16, Width::F32, Width::F64]
            .into_iter()
            .find(|w| w.holds(x))
            .expect("every f64 is an f64")
    }
}

/// A kind a float may be.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// Negative infinity.
    NegInf,
    /// A finite value, zero included.
    Finite,
    /// Positive infinity.
    PosInf,
    /// A NaN.
    NaN,
}

impl Kind {
    const ALL: [Kind; 4] = [Kind::NegInf, Kind::Finite, Kind::PosInf, Kind::NaN];

    fn bit(self) -> u8 {
        1 << self as u8
    }

    /// The kind of `x`.
    pub fn of(x: f64) -> Kind {
        match x {
            _ if x.is_nan() => Kind::NaN,
            f64::INFINITY => Kind::PosInf,
            f64::NEG_INFINITY => Kind::NegInf,
            _ => Kind::Finite,
        }
    }
}

/// A float class.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FloatClass {
    kinds: u8,
    width: Width,
}

impl FloatClass {
    /// The floats of the given kinds at the given width.
    pub fn new(kinds: &[Kind], width: Width) -> FloatClass {
        let kinds = kinds.iter().fold(0, |k, x| k | x.bit());
        if kinds == 0 {
            FloatClass::bottom()
        } else {
            FloatClass { kinds, width }
        }
    }

    /// The class of the one value `x`.
    pub fn of(x: f64) -> FloatClass {
        FloatClass::new(&[Kind::of(x)], Width::of(x))
    }

    /// Every float of the given width.
    pub fn width(width: Width) -> FloatClass {
        FloatClass::new(&Kind::ALL, width)
    }

    /// Whether `x` is in the class.
    pub fn contains(&self, x: f64) -> bool {
        self.kinds & Kind::of(x).bit() != 0 && (!x.is_finite() || self.width.holds(x))
    }

    /// Whether no value of the class is a NaN: the condition for a float key or a sort key
    /// (sec:corner_cases).
    pub fn excludes_nan(&self) -> bool {
        self.kinds & Kind::NaN.bit() == 0
    }

    /// Whether every value of the class is finite.
    pub fn is_finite(&self) -> bool {
        self.kinds & !Kind::Finite.bit() == 0
    }
}

impl Lattice for FloatClass {
    fn bottom() -> Self {
        FloatClass {
            kinds: 0,
            width: Width::F16,
        }
    }
    fn top() -> Self {
        FloatClass::width(Width::F64)
    }
    fn join(&self, other: &Self) -> Self {
        match (self.kinds, other.kinds) {
            (0, _) => *other,
            (_, 0) => *self,
            _ => FloatClass {
                kinds: self.kinds | other.kinds,
                width: self.width.max(other.width),
            },
        }
    }
    fn meet(&self, other: &Self) -> Self {
        match self.kinds & other.kinds {
            0 => FloatClass::bottom(),
            kinds => FloatClass {
                kinds,
                width: self.width.min(other.width),
            },
        }
    }
    fn widen(&self, next: &Self, _: &Landmarks) -> Self {
        self.join(next)
    }
    fn narrow(&self, next: &Self, _: &Landmarks) -> Self {
        *next
    }
}

impl fmt::Display for FloatClass {
    /// `f64{finite, nan}`; the bottom is `{}`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.kinds == 0 {
            return write!(f, "{{}}");
        }
        let names: Vec<&str> = Kind::ALL
            .into_iter()
            .filter(|k| self.kinds & k.bit() != 0)
            .map(|k| match k {
                Kind::NegInf => "-inf",
                Kind::Finite => "finite",
                Kind::PosInf => "inf",
                Kind::NaN => "nan",
            })
            .collect();
        let w = match self.width {
            Width::F16 => "f16",
            Width::F32 => "f32",
            Width::F64 => "f64",
        };
        write!(f, "{w}{{{}}}", names.join(", "))
    }
}
