//! Work counts of [`Extending`](super::Extending) on this thread, read by tests and benchmarks
//! to find which step of a question grows with a chain (LOAD-defined-with): each is a count the
//! same on every run, one thread-local add at its site. A file of its own, so that `plane.rs`
//! counts its steps without importing `extend.rs`, which imports it (s_01f_import_graph).

use std::cell::Cell;

/// Atoms read by `Extending::closure`: those of the parts after the largest, of
/// the conjunction's own atoms and of the definitions it reaches.
pub const CLOSURE_ATOMS: usize = 0;
/// Atoms looked up by `apart`, the smaller side of each test.
pub const APART_ATOMS: usize = 1;
/// Definitions `Extending::fill` reads with a part it fills (`reached`).
pub const FILL_REACHED: usize = 2;
/// Definitions read by every `reached_by`, `fill`'s among them.
pub const REACHED: usize = 3;
/// Rows of the summaries `Summaries::make` makes.
pub const MADE_ROWS: usize = 4;
/// Rows read by `lean`: each row tested reads the others once.
pub const LEAN_ROWS: usize = 5;
/// Questions decided whole with every definition they reach (`holds_whole`,
/// `fails_whole`, `decide_defined` when no summary answers).
pub const WHOLE: usize = 6;
/// Atoms of the formulas decided whole, their definitions included.
pub const WHOLE_ATOMS: usize = 7;
/// Conjunctions extended from a part and decided from the integer hull of their rows
/// (`plane::Plane`, LOAD-chain-move-tangent, META3 H2: the hull inherited).
pub const PLANE: usize = 8;
/// Rows that state those hulls, summed over the conjunctions decided from them.
pub const PLANE_ROWS: usize = 9;
/// Hulls built from a whole conjunction (`plane::Plane::of`, META3 H2: the hull seeded).
pub const PLANE_FRESH: usize = 10;
/// Rows added to a hull kept by a part (`plane::Plane::with`).
pub const HULL_UPDATES: usize = 11;
/// Rows added by Harvey's case 1: the new line holds an integer point between its
/// neighbors.
pub const HULL_CASE1: usize = 12;
/// Rows added by Harvey's case 2: the new line holds no integer point between its
/// neighbors.
pub const HULL_CASE2: usize = 13;
/// Hulls that lost their area: a Line or a Point (META3 H1).
pub const HULL_COLLAPSE: usize = 14;
/// Tree nodes of the hulls made or read (META3 H3: every node touched).
pub const HULL_NODES: usize = 15;
/// Conjunctions without a kept part decided by the solver (`whole` when no hull answers
/// them; META3 H2), whether or not a summary answers the question, which [`WHOLE`] does
/// not count.
pub const BASE_SOLVED: usize = 16;
/// The number of counts.
pub const N: usize = 17;

thread_local! {
    static COUNTS: [Cell<u64>; N] = const { [const { Cell::new(0) }; N] };
}

/// Adds `n` to the count `i`.
pub(crate) fn add(i: usize, n: usize) {
    COUNTS.with(|c| c[i].set(c[i].get() + n as u64));
}

/// The counts on this thread, each set back to 0.
pub fn take() -> [u64; N] {
    COUNTS.with(|c| std::array::from_fn(|i| c[i].replace(0)))
}
