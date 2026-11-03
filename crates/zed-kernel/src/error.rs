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
    /// A lookup port could not answer a read: the port and why.
    Port(String, String),
    /// The evaluation used up its fuel: a `fix` whose ascent or a `gen` that did not stop
    /// within the step budget (sec:generations, divergence).
    OutOfFuel,
    /// A definedness `fix` stopped with these entries undefined: each reads an entry of the
    /// cycle, which is divergence (T-Fix), never `#notFound`.
    Stalled {
        /// The undefined keys, in order.
        keys: Vec<crate::value::Value>,
    },
    /// An arithmetic operation had to build a number in full, of at most `bits` bits, and the
    /// system refused the memory for it (sec:domains says when a number is built). The number
    /// is a value of the language; this evaluator cannot run the program on this machine.
    NumberTooLarge {
        /// The operator: `+`, `-`, `div`, `mod`, `**`, or `String` printing a number.
        op: &'static str,
        /// At most this many bits: the size of the number to build.
        bits: num_bigint::BigUint,
    },
    /// `String` of a tuple, keypath, atom or family must write a text of up to `bytes` bytes,
    /// the digits of the numbers inside it counted at their widest, and the system refused the
    /// memory for it, with the widest number's build; `None` for more than `u128::MAX` bytes.
    TextTooLarge {
        /// At most this many bytes: the length of the text.
        bytes: Option<u128>,
    },
    /// Two numbers agree in so many leading bits that ordering them, for `<`, `<=`, `>`,
    /// `>=`, `min` or `max`, needs bounds of up to `bits` bits, or the two in full, and the
    /// system refused the memory for it.
    OrderTooLarge {
        /// The operator.
        op: &'static str,
        /// At most this many bits: the size of the widest bound or number to build.
        bits: num_bigint::BigUint,
    },
    /// `==` or `!=` of two numbers, one of whose coefficients is divisible by a prime the other
    /// keeps as a power, must copy and divide the coefficients to compare their normal forms,
    /// which needs up to `bits` bits, and the system refused the memory for it.
    EqualityTooLarge {
        /// The operator.
        op: &'static str,
        /// At most this many bits: the size of the copy and the division.
        bits: num_bigint::BigUint,
    },
    /// Two numbers among a family's keys, or a key looked up and one in the family, agree in
    /// so many leading bits that placing them in key order needs up to `bits` bits, and the
    /// system refused the memory for it.
    KeyOrderTooLarge {
        /// At most this many bits: the size of the widest bound or number to build.
        bits: num_bigint::BigUint,
    },
    /// A number lies so near a rounding boundary of a float that telling which side it is on
    /// needs bounds of up to `bits` bits, or the number in full, and the system refused the
    /// memory for it.
    RoundTooLarge {
        /// The float it is rounded to, as the cast is written: `f64`.
        to: &'static str,
        /// At most this many bits: the size of the widest bound or number to build.
        bits: num_bigint::BigUint,
    },
    /// `++` of two strings whose lengths in bytes add up past `usize::MAX`, the most a length
    /// holds: the joined string's length is not representable, whatever memory there is.
    StringTooLong {
        /// The left string's length in bytes.
        left: usize,
        /// The right string's length in bytes.
        right: usize,
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
            KernelError::Port(name, why) => write!(f, "port `{name}`: {why}"),
            KernelError::OutOfFuel => write!(f, "out of fuel"),
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
            KernelError::NumberTooLarge { op, bits } => write!(
                f,
                "`{op}` must build a number of up to {bits} bits in full, and the system \
                 refused the memory for it; the number is exact and has no size limit, but this \
                 machine cannot hold its digits"
            ),
            KernelError::TextTooLarge { bytes } => {
                match bytes {
                    Some(n) => write!(f, "`String` must write a text of up to {n} bytes")?,
                    None => write!(
                        f,
                        "`String` must write a text of more than {} bytes",
                        u128::MAX
                    )?,
                }
                write!(
                    f,
                    ", counting each number inside it at its widest, and the system refused the \
                     memory for it; the value has no size limit, but this machine cannot hold \
                     its text"
                )
            }
            KernelError::OrderTooLarge { op, bits } => write!(
                f,
                "`{op}` must compare two numbers that agree in their leading digits, which \
                 needs up to {bits} bits of each, and the system refused the memory for it; \
                 the numbers are exact and have no size limit, but this machine cannot hold \
                 enough of their digits to order them"
            ),
            KernelError::EqualityTooLarge { op, bits } => write!(
                f,
                "`{op}` must compare two numbers in the same normal form, which moves a prime \
                 one keeps as a power out of the other's digits and needs up to {bits} bits, \
                 and the system refused the memory for it; the numbers are exact and have no \
                 size limit, but this machine cannot hold enough of their digits to compare them"
            ),
            KernelError::KeyOrderTooLarge { bits } => write!(
                f,
                "two numbers placed in a family's key order agree in their leading digits, \
                 which needs up to {bits} bits of each to order them, and the system refused \
                 the memory for it; the numbers are exact and have no size limit, but this \
                 machine cannot hold enough of their digits to order them"
            ),
            KernelError::RoundTooLarge { to, bits } => write!(
                f,
                "`{to}` must round a number that lies near a rounding boundary, which needs up \
                 to {bits} bits of it, and the system refused the memory for it; the number \
                 is exact and has no size limit, but this machine cannot hold enough of its \
                 digits to round it"
            ),
            KernelError::StringTooLong { left, right } => write!(
                f,
                "`++` cannot join a string of {left} bytes to one of {right} bytes: the result \
                 would be {} bytes, more than the {} bytes a string's length can hold; keep \
                 the parts apart, as a list of strings written out one at a time, or join \
                 fewer of them",
                *left as u128 + *right as u128,
                usize::MAX
            ),
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
        let s = KernelError::Stalled {
            keys: vec![Value::Int(1), Value::Int(2)],
        };
        assert_eq!(
            s.to_string(),
            "recursion stalled: entries 1, 2 depend on each other"
        );
    }
}
