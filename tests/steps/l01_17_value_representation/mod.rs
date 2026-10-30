//! Step L1.17: the representation of values. Integers are unbounded and rationals exact;
//! every value has a place in one total order, numbers by value across kinds; the language's
//! `==` is IEEE 754 at floats and the bitwise identity of keys elsewhere; an atom carries a
//! payload by position or by name; and `==` on functions waits for the enumerable domain
//! their types give.

mod atoms;
mod equality;
mod numbers;
mod order;
