//! Step L1.16: elaboration of the L1 surface to kernel terms. Each program is elaborated and
//! its definitions evaluated by the kernel evaluator; where a term's shape is the point, it is
//! printed; and each error elaboration reports has a case.

mod bench;
mod calls;
mod complete;
mod errors;
mod handled;
mod order;
mod programs;
mod scaling;

pub(crate) use zed_tests::step_helpers::l01_16_elaboration::{
    Checked, checked, elab, errors, term, value, with_prelude,
};
