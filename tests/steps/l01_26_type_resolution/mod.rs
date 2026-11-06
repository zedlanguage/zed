//! Step L1.26: resolution rules 1, 3 and 4. Each declared function gets a signature from its
//! body; a bare numeric literal adopts the carrier an operator or a parameter expects,
//! exactly or not at all; an `is` test narrows the name it tests; a function argument fits
//! the function type its slot expects.

mod adoption;
mod atom_scaling;
mod bounds;
mod calls;
mod curried_classes;
mod deep_scaling;
mod docs;
mod fits;
mod given;
mod handled;
mod held_functions;
mod literals;
mod named_calls;
mod narrowing;
mod random;
mod scaling;
mod signatures;
mod soundness;
mod tuple_keys;

pub(crate) use zed_tests::step_helpers::l01_26_type_resolution::{
    Resolved, info, sig, sig_of, type_errors,
};
