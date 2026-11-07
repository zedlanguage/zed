//! What this back end asks of legalization, in a file of its own so that the executable's
//! start (`exe`) and the tests of the runtime's hooks reach it without importing the crate root,
//! which imports them (step S.1f: no import cycle between files).

use zedc::zir::Region;
use zedc::zir::legalize::{Expansion, Expansions, Legalized};

/// The expansions this back end asks of legalization (DESIGN.md sec:ir, "Legalization"): a
/// derived node runs through its certificate, and `>` and `>=` are compiled as `<` and `<=`
/// on their inputs swapped, so the code generator compiles only the latter two.
pub const EXPANSIONS: Expansions =
    Expansions::of(&[Expansion::Derived, Expansion::Gt, Expansion::Ge]);

/// `g` legalized for this back end: what [`run`](crate::run) and [`object()`](crate::object)
/// take, with a plan of its graph.
pub fn legalize(g: Region) -> Legalized {
    zedc::zir::legalize::legalize(g, EXPANSIONS)
}
