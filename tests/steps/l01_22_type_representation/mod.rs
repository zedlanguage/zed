//! Step L1.22: types as sets of values, with union, intersection, difference and complement
//! taken within each universe; tuple, atom and morphism types; and the `is` test, which
//! elaborates to a match on a type. The connectives are checked against membership computed
//! from the type expression itself, over a sample of values from every universe.

mod forms;
mod is;
mod laws;
