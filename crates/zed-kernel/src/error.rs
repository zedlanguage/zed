//! The ways a kernel evaluation stops without a value.
//!
//! Failure atoms such as `#empty` are values, not errors (sec:failure). These errors are the
//! cases the checker rejects statically, which the reference evaluator detects when it meets
//! them, plus the divergence that fuel bounds.

use std::fmt;

use crate::family::Keypath;

/// Why a kernel evaluation stopped without a value.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum KernelError {
    /// Two entries were written to one keypath, or one entry's keypath is a prefix of
    /// another's: the collision rule (sec:grouping), the premise of T-Reindex.
    Collision {
        /// The keypath written twice.
        keypath: Keypath,
    },
    /// A leaf with no keys, which only a key map that returns an empty keypath can make.
    EmptyKeypath,
    /// A fold met a family with a leaf at another depth than the fold's, so it has no one
    /// level to collapse.
    MixedDepth,
    /// A value had the wrong shape for the construct reading it, which a well-typed term
    /// never does.
    Type(String),
    /// The term named a port the world does not have.
    UnknownPort(String),
    /// The evaluation used up its fuel: a `fix` whose ascent or a `gen` that did not stop
    /// within the step budget (sec:generations, divergence).
    OutOfFuel,
    /// Calls nested deeper than the reference evaluator follows ([`crate::eval::MAX_DEPTH`]).
    TooDeep,
    /// A number beyond the size the reference evaluator builds ([`crate::num::MAX_BITS`]): a
    /// limit of its memory, since `int` and `rat` are unbounded.
    Overflow,
    /// A definedness `fix` stopped with these entries undefined: each reads an entry of the
    /// cycle, which is divergence (T-Fix), never `#notFound`.
    Stalled {
        /// The undefined keys, in order.
        keys: Vec<crate::value::Value>,
    },
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelError::Collision { keypath } => {
                write!(f, "collision: two writers for keypath [")?;
                for (i, k) in keypath.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}")?;
                }
                write!(f, "]")
            }
            KernelError::EmptyKeypath => write!(f, "a key map returned an empty keypath"),
            KernelError::MixedDepth => write!(f, "fold over leaves at another depth than its own"),
            KernelError::Type(msg) => write!(f, "type error: {msg}"),
            KernelError::UnknownPort(name) => write!(f, "unknown port `{name}`"),
            KernelError::OutOfFuel => write!(f, "out of fuel"),
            KernelError::TooDeep => write!(f, "calls nested too deeply"),
            KernelError::Overflow => write!(f, "a number beyond the evaluator's size limit"),
            KernelError::Stalled { keys } => {
                write!(f, "recursion stalled: entries ")?;
                for (i, k) in keys.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}")?;
                }
                write!(f, " depend on each other")
            }
        }
    }
}

impl std::error::Error for KernelError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Value;

    #[test]
    fn messages() {
        let c = KernelError::Collision {
            keypath: vec![Value::str("ann"), Value::Int(2)],
        };
        assert_eq!(
            c.to_string(),
            r#"collision: two writers for keypath ["ann", 2]"#
        );
        assert_eq!(
            KernelError::EmptyKeypath.to_string(),
            "a key map returned an empty keypath"
        );
        assert_eq!(
            KernelError::MixedDepth.to_string(),
            "fold over leaves at another depth than its own"
        );
        assert_eq!(KernelError::Type("x".into()).to_string(), "type error: x");
        assert_eq!(
            KernelError::UnknownPort("p".into()).to_string(),
            "unknown port `p`"
        );
        assert_eq!(KernelError::OutOfFuel.to_string(), "out of fuel");
        assert_eq!(KernelError::TooDeep.to_string(), "calls nested too deeply");
        assert_eq!(
            KernelError::Overflow.to_string(),
            "a number beyond the evaluator's size limit"
        );
        let s = KernelError::Stalled {
            keys: vec![Value::Int(1), Value::Int(2)],
        };
        assert_eq!(
            s.to_string(),
            "recursion stalled: entries 1, 2 depend on each other"
        );
    }
}
