//! The coefficient terms of the linear-relation domain (DESIGN.md sec:domains, step L1.38),
//! shared by the Omega test, `twovar` and `utvpi`. Its rationals are [`zedc_int::q::Q`].

use zedc_int::int::Int;

/// A coefficient at a variable.
pub type Term = (usize, Int);
