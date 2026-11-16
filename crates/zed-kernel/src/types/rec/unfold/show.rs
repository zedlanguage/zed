//! The text of an expression of a recursive group ([`Show`]). It is a file of its own, apart from
//! `unfold.rs`, because it prints through module `print`, which decides subtypes by module
//! `empty`, which evaluates expressions by `unfold.rs`: written in `unfold.rs`, it closed an
//! import cycle (plan row S1F-kernel-print-empty-cycle).

use std::fmt;

use super::Show;
use crate::types::{Piece, Rope, Type};

/// In the surface syntax, the types the expression holds are written together by name
/// ([`Type::surfaces_by_name`]): a part used more than once among them gets a definition, declared
/// on a line of its own before the whole expression, so the text is linear in the expression and the types' graph.
impl fmt::Display for Show<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.surface {
            return self.rope().strs().try_for_each(|s| f.write_str(s));
        }
        let mut leaves = Vec::new();
        self.rope_with(
            &mut |t, at| {
                leaves.push((t.clone(), at));
                Rope::cat([])
            },
            None,
        );
        let texts = Type::surfaces_by_name(&leaves);
        for (name, body) in &texts.defs {
            crate::types::defs::declare(f, name, body)?;
        }
        let mut roots = texts.roots.into_iter();
        self.rope_with(
            &mut |_, _| Rope::cat([Piece::from(roots.next().expect("a text for each type"))]),
            None,
        )
        .strs()
        .try_for_each(|s| f.write_str(s))
    }
}
