//! Step L1.37: the differential oracle. The interpreter and the native code of L1.36 run every
//! enabled fence, every corpus program and every step unit, and their outputs are compared
//! byte for byte: a program's port writes, and for a unit with no port the printing of each
//! top-level binding whose type has no function component. The oracle runs in CI from this
//! step on, so every later step keeps the two in agreement.

mod controls;
mod oracle;
