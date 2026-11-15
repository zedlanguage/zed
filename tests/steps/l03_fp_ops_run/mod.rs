//! The standard operations on lists and maps, compiled and run (plan row FP-ops-run, author
//! P229; docs/fp-ops-inventory.md). Each case is the example or test DESIGN.md gives for the
//! word: steps L3.2 (`split`, `lines`, `concat`, folds), L3.15a (`.any`, `.all`, `.find`),
//! L5.1 (`sort`, `.orderedValues`, positional selection), L5.1c (the reverse of an order),
//! L5.2 (`++`, `zip`) and L5.3 (`scan`, `.chunkBy`), and the laws the row names: `zip` then the
//! two projections gives back both operands, and the last entry of a scan equals the fold.
//!
//! Every case runs a whole program through `zedc run` and compares what it prints, so a case
//! passes only when the word parses, resolves, elaborates, checks and runs.

mod cases;
