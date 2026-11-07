//! The memory the system gives for building a number, and the errors of a number it refuses,
//! in a file of their own so that the bounds (`bound`) and the numbers (`num`) both reach them
//! without importing each other (step S.1f: no import cycle between files).

use num_bigint::BigUint;
use num_traits::ToPrimitive;

/// A number the evaluator must build, or read, for which the system refused the memory
/// (DESIGN.md sec:domains): the number is a value of the language, and building it is the
/// machine's failure, not the program's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TooLarge {
    /// The memory asked for, in bits: a measured multiple of the size of what is built, not
    /// the size of the number.
    pub bits: BigUint,
}

impl TooLarge {
    /// The memory asked for, in bytes, rounded up.
    pub fn bytes(&self) -> BigUint {
        bytes_of(&self.bits)
    }
}

/// `bits` bits of memory in bytes, rounded up.
pub fn bytes_of(bits: &BigUint) -> BigUint {
    (bits + 7u32) >> 3u32
}

/// `Ok` when the system gives `bits` bits of memory, asked of the allocator itself and freed
/// at once, so the answer is the machine's and the evaluator sets no limit. A build that would
/// ask for more than the system gives is reported before it starts, where num-bigint would
/// abort the process.
pub fn room(bits: BigUint) -> Result<(), TooLarge> {
    match given(&bits) {
        true => Ok(()),
        false => Err(TooLarge { bits }),
    }
}

/// Whether the allocator gives `bits` bits at once, asked and freed at once.
fn given(bits: &BigUint) -> bool {
    let words = (bits + 63u32) >> 6u32;
    words
        .to_usize()
        .is_some_and(|w| Vec::<u64>::new().try_reserve_exact(w).is_ok())
}

/// Why a float literal has no value at a binary float carrier (DESIGN.md sec:domains), or why
/// a number could not be rounded to one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralRounding {
    /// It rounds to infinity: it is beyond the largest finite float.
    Infinite,
    /// It is not zero, but it rounds to zero: it is below half the least subnormal.
    Zero,
    /// It lies so near a rounding boundary that telling which side it is on needs more
    /// memory than the system gives.
    TooLarge(TooLarge),
    /// The literal has so many digits that reading them needs more memory than the system
    /// gives.
    Unread(TooLarge),
}
