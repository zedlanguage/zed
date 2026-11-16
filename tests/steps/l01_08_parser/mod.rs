//! Step L1.8: the parser runs the grammar of sec:grammar, copied into `zed/grammar/`, and its
//! trees are the trees of the spec's bracketing cases and the rings of the fences.

mod alternatives;
mod assign_in_condition;
mod bare_key;
mod bench;
mod cases;
mod deep;
mod errors;
mod grammar_cases;
mod grammar_errors;
mod grammar_read;
mod grammar_scaling;
mod grammar_shape;
mod head_cases;
mod heads;
mod later_names;
mod left_recursion;
mod lr4_assoc;
mod plain_names;
mod push_or_less;
mod recovery_edges;
mod reserved;
mod rings;
mod scaling;
