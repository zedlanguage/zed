//! What an atom pattern matches, as a kernel type: shared by the checker's handlers
//! (`mod.rs`, `walk.rs`) and by the table of where an atom goes (`fate.rs`). It is a module of
//! its own, importing neither, so that `fate.rs` can use it without an import cycle through
//! `mod.rs` (step S.1f, `tests/steps/s_01f_import_graph`).

use zed_kernel::types::Type as KType;
use zedc_syntax::ast::Pattern;

/// The atom `#name` with any payload or none: what a bare pattern `#name` matches. It lives in
/// zedc-types, whose printer writes what an `else #name ->` removes (else1x1).
pub use zedc_types::ty::any_payload;

/// The atom `#name()`, whose payload is the empty tuple: what the pattern `#name()` matches.
pub fn empty_payload(name: &str) -> KType {
    KType::atom_with(name, &KType::tuple(Vec::new()))
}

/// What the atom pattern `#name` (`items` `None`) or `#name()` (`Some` of none) matches:
/// [`any_payload`] or [`empty_payload`]. `None` for a pattern with parts, which the caller
/// does not take here.
pub(super) fn matched_by(
    name: &str,
    fields: &[(String, Option<Pattern>)],
    items: Option<&[Pattern]>,
) -> Option<KType> {
    match items {
        _ if !fields.is_empty() => None,
        None => Some(any_payload(name)),
        Some([]) => Some(empty_payload(name)),
        Some(_) => None,
    }
}
