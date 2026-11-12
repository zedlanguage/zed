//! A definition as the summaries of `extend` read it ([`Def`]), and the two readings of a
//! formula it is made from. A file of its own so that `extend` and `extend::images`, which both
//! read it, import it without an import cycle between them (step S.1f).

use std::collections::BTreeSet;

use super::super::formula::{Atom, Formula, Id};

/// A definition as the summaries read it: its formula and key, the variables it defines in
/// order, the variables of other definitions it reads, and every atom it reads.
pub(super) struct Def {
    pub(super) f: Formula,
    pub(super) id: Id,
    pub(super) own: Vec<u32>,
    pub(super) inputs: Vec<u32>,
    pub(super) reads: BTreeSet<Atom>,
}

impl Def {
    /// The definition `f`, `None` where no summary is made of it: one that defines no variable it
    /// reads. A product of variables is read as an atom of its own, as the solver reads it
    /// ([`decide`](super::super::decide)), and the definitions of its factors as inputs. Time of `f`.
    pub(super) fn of(f: Formula, def: &dyn Fn(u32) -> Formula) -> Option<Def> {
        let id = Id::any(&f);
        let reads = reads(&f);
        let (mut own, mut inputs) = (Vec::new(), Vec::new());
        for a in &reads {
            match a {
                Atom::Product(..) | Atom::Sym(_) => {}
                Atom::Aux(n) => {
                    let d = def(*n);
                    if Id::any(&d) == id {
                        own.push(*n);
                    } else if !free(&d) {
                        inputs.push(*n);
                    }
                }
            }
        }
        (!own.is_empty()).then_some(Def {
            f,
            id,
            own,
            inputs,
            reads,
        })
    }
}

/// Whether `f` is the definition of a variable with no definition: `true`.
pub(super) fn free(f: &Formula) -> bool {
    matches!(f, Formula::And(gs) if gs.is_empty())
}

/// The atoms `f` reads, a product with its factors: the solver reads a product as an atom of
/// its own ([`decide`](super::super::decide)), and its factors' definitions are among those `f` reaches ([`reached`](super::reached)).
pub(super) fn reads(f: &Formula) -> BTreeSet<Atom> {
    let mut out = BTreeSet::new();
    for a in f.atoms() {
        if let Atom::Product(g, h) = &a {
            out.insert(g.atom());
            out.insert(h.atom());
        }
        out.insert(a);
    }
    out
}
