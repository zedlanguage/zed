//! The landmarks of a program, at which the widenings and narrowings of the store's lattices
//! (`super::lattice`) stop a bound (step M0.5).

use std::collections::BTreeSet;

use zed_kernel::Value;

use super::int::Num;

/// The values written in a program, at which a widening stops a bound and a narrowing stops a
/// descent (step M0.5): each integer literal and each declared bound `k`, as `k - 1`, `k` and
/// `k + 1`, and the other literal values. A program has finitely many, so a chain that moves
/// only to landmarks and old endpoints is finite, with no count of its steps. A cell takes the
/// landmarks of its loop only (`iterate::Scopes`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Landmarks {
    ints: BTreeSet<Num>,
    values: BTreeSet<Value>,
}

impl Landmarks {
    /// No landmarks: a bound that moves goes to an old endpoint or to infinity.
    pub fn none() -> Self {
        Landmarks::default()
    }

    /// The landmarks of the given integer literals and other values.
    pub fn of(
        ints: impl IntoIterator<Item = impl Into<Num>>,
        values: impl IntoIterator<Item = Value>,
    ) -> Self {
        let mut out = Landmarks {
            values: values.into_iter().collect(),
            ..Landmarks::default()
        };
        for k in ints {
            let k: Num = k.into();
            out.ints.extend([&k - &Num::ONE, &k + &Num::ONE, k]);
        }
        out
    }

    /// Adds the landmarks of `other`.
    pub fn extend(&mut self, other: &Landmarks) {
        self.ints.extend(other.ints.iter().cloned());
        self.values.extend(other.values.iter().cloned());
    }

    /// The integer landmarks, in order.
    pub fn ints(&self) -> &BTreeSet<Num> {
        &self.ints
    }

    /// Whether `v` is a landmark.
    pub fn has(&self, v: &impl Mark) -> bool {
        v.marked(self)
    }
}

/// A member of a finite set, which a widening keeps exact when it is a landmark.
pub trait Mark {
    /// Whether the value is one of `marks`.
    fn marked(&self, marks: &Landmarks) -> bool;
}

impl Mark for i64 {
    fn marked(&self, marks: &Landmarks) -> bool {
        marks.ints.contains(&Num::from(*self))
    }
}

impl Mark for Value {
    fn marked(&self, marks: &Landmarks) -> bool {
        match self {
            Value::Int(n) => marks.ints.contains(&Num::from(*n)),
            Value::Big(n) => marks.ints.contains(&Num::from(&**n)),
            v => marks.values.contains(v),
        }
    }
}
