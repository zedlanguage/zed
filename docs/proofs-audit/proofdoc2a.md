# Proofs in comments: audit of proofdoc2a (DOC-proofs-in-comments-audit-rest)

This audit covers the crates zedc-resolve, zedc-stage, zedc, zedc-syntax, zedc-lattice, zed-cert
and zed-meter-settings, and two leftovers of proofdoc1b: the code of 15657d994 "remainders read
class by class", now zedc-preimage preimage.rs `split_classes`, and the stale pointer in
tests/steps/l08_02_remaps/empty.rs. The sources are, in order: the commit messages since
2026-11-01 that touch each crate (`git log --since=2026-11-01 -- crates/<crate>`: zedc-resolve
112, zedc-stage 48, zedc 551, zedc-syntax 131, zedc-lattice 55, zed-meter-settings 3, zed-cert
0), ranked by how often a message names a proof, bound, invariant, derivation, lemma,
"cannot", "never", "exact" or an argument, the highest read first; the sites those commits
name; and `command grep -a -n -i -E 'proof|prove|invariant|unreachable|expect\(|SAFETY|unsafe|cannot happen|never happens|by construction|not proved'`
over each crate's src (zedc-resolve 40 lines, zedc-stage 62, zedc 68, zedc-syntax 131,
zedc-lattice 47, zed-meter-settings 29, zed-cert 0). Most high-ranked commits of zedc and
zedc-syntax name code that has since moved out of these crates (crates/zedc/src/check,
store, elab, the old ast paths), which is now in zedc-check, zedc-preimage, zedc-elab and
zedc-types and is outside this part; so most rows below come from the grep. Each grep hit was
read at its site on base 6b9edf7fb; for an `expect`, `unreachable!` or `unsafe` the callers
were traced (each caller named in the comment was read) and the argument written as a `//` or
`///` comment at the code: the claim, the steps, the facts with where each is established, and
the test that checks it and what that test cannot catch.

One bug was found and fixed (P377): a `main` declared in a block inside a string's hole made
the syntax-tree builder panic at zedc-syntax ast/stmts.rs `main_header`, `expect("a main's body
is in the table")`, since `Mains::new` read only the text's tree, and each hole is a tree of
its own (`with_holes` in ast/mod.rs). `Mains::new` now reads the `main`s of every tree of
`with_holes`' list (`Mains::bodies`); the outside reads of `main::files` are still found on
the text's tree, as the reads in holes are recorded by `Builder::main_files` as they are
built. Test `l01_19_whole_file_ports::main_args::a_main_in_a_string_hole_is_built`, red before
(the panic) and green after; the program runs and prints the hole's value.

Counts per crate (claims, the rows below; a row may cover several grep lines; grep lines that
are keyword matches with no claim, test-only `expect`s, and `expect`s whose message states a
local fact in full are counted under "already there" only where listed):

| Crate | Found | Already there | Added or completed | Marked unproved | Corrected |
| --- | --- | --- | --- | --- | --- |
| zed-meter-settings | 2 | 0 | 2 | 1 (the same row as one added) | 0 |
| zedc-lattice | 16 | 0 | 16 | 0 | 0 |
| zedc-preimage (leftover) | 2 | 0 | 2 | 0 | 0 |
| zedc-resolve | 15 | 0 | 15 | 0 | 0 |
| zedc-stage | 24 | 0 | 24 | 0 | 0 |
| zedc-syntax | 25 | 3 | 21 | 0 | 1 (bug fixed, test) |
| zedc | 13 | 6 | 7 | 0 | 0 |
| zed-cert | 0 | 0 | 0 | 0 | 0 |
| tests (leftover) | 1 | 0 | 0 | 0 | 1 |

Tests added: `past_i64::an_exponent_with_no_exact_form_bounds_outward` (zedc-lattice
`pow_end`, a negative base and an odd and an even exponent); `main_args::
a_main_in_a_string_hole_is_built` (the bug); two cases of `l25_08_mutate::set::
h4_a_decimal_literal_moves_by_one_unit_of_its_last_digit` (`9.9`, the carry out of the first
digit, and `0.1`, a borrow to 0 that is not below zero).

Not swept: the zedc-syntax grammar-shape `unreachable!`s and `expect`s (ast/mod.rs, stmts.rs,
types.rs, infix.rs, builder.rs), whose messages name the grammar rule and which rest on the
PEG engine building the tree from zed/grammar/syntax.peg, are counted as already there as a
class and not traced one by one; zedc unit.rs `pinned` and `write_pins` ("a unit that gains a
pin has text") were not traced; zedc-syntax builder.rs at line 1039 (a hole taken once) was not
traced; the commits that name code now in other crates (above) were not followed into those
crates; test files' `expect`s were not read.

| Source | Claim | Code site | Status |
| --- | --- | --- | --- |
| (grep) | No other thread exists while the `.init_array` constructor runs, which the SAFETY comments of `remove_var`, `prctl` and the re-exec rely on: (a) loader and (c) the program's own `.init_array` start none; (b) the four shared libraries' constructors shown by `strace` only | zed-meter-settings lib.rs `START`, `start` | added; Not proved, sub-case (b), row PROOF-meter-no-thread-before-main |
| (grep) | The `CString::new` `expect`s cannot fire: no string passed holds a NUL | zed-meter-settings lib.rs `start` | added |
| (grep) | `Width::F64.holds(x)` for every finite `x` | zedc-lattice float.rs `Width::of` | added |
| (grep) | One task tree leaves one item, so `split_off`, `Bind` and the `Combine` arm cannot fail | zedc-lattice grade.rs `grade` | added |
| (grep) | Ends between two pieces are finite | zedc-lattice interval.rs `run_between` | added |
| (grep) | The `expect`s of `join_right` and its rotations (AVL heights) | zedc-lattice interval.rs `join_right`, `join_left` | added |
| (grep) | `build` finds every item it counts | zedc-lattice interval.rs `build` | added |
| (grep) | Only a subtree opens | zedc-lattice interval.rs `Walk::open` | added |
| (grep) | The smallest-gap merge: finite ends, heap invariant, current entries, the loop ends | zedc-lattice interval.rs `cap_pieces` | added |
| (grep) | `fin` is called on finite ends only | zedc-lattice interval.rs `fin` | added |
| (grep) | `bounds` is `Some` for a non-empty operand | zedc-lattice interval.rs `bit_word` | added |
| (grep) | A chain of narrowings is finite, so the loop returns | zedc-lattice iterate.rs `narrow` | added |
| (grep) | `[lo, hi]` holds `x ^ k` for every member pair | zedc-lattice revision.rs `forward_pow` | added |
| (grep) | At most `4(k + 2)` pairs | zedc-lattice revision.rs `map2` | added |
| (grep) | The fallback bound of a power with no exact form is outward | zedc-lattice revision.rs `pow_end` | added (test) |
| (grep) | `FiniteSet::of` never builds `Top` | zedc-lattice revision.rs `reduce_finite` | added |
| (grep) | The cycle search's two `expect`s | zedc-lattice schedule.rs `Demand::cycle` | added |
| (grep) | Every member of a head's component is built before the head | zedc-lattice wto.rs `weak_topological_order` | added |
| 15657d994 | The union of the class runs is the exact preimage | zedc-preimage preimage.rs `split_classes` (doc) | added |
| 15657d994 | `run.residue` is still set after `tx.back` | zedc-preimage preimage.rs `split_classes` | added |
| proofdoc1b | The proof is at zedc-elab `Elab::check_instances`, not `Ck::finish` | tests/steps/l08_02_remaps/empty.rs | corrected |
| (grep) | A `Bound` at this level exists after the push | zedc-resolve resolve.rs `bind` | added |
| (grep) | Scopes nest, and each `pop` removes the closing scope's binding | zedc-resolve resolve.rs `Resolver::close` | added |
| (grep) | A field's scope was opened above | zedc-resolve resolve.rs `fields` | added |
| (grep) | An annotated declaration or unit item is never a `Decl` | zedc-resolve resolve.rs `stmt` (`local` arm) | added |
| (grep) | Every alternative has a binder when `one` | zedc-resolve resolve.rs or-pattern menu | added |
| (grep) | The `ors` and `scopes` `expect`s of an or-pattern; it has two alternatives | zedc-resolve resolve.rs `pattern` (`Pattern::Or`) | added |
| (grep) | `type_var` is called with a bounded variable | zedc-resolve resolve.rs `type_var` | added |
| (grep) | Free-variable tables nest; `v.pop()` removes this table's index | zedc-resolve resolve.rs `free_end`, `free_var` | added |
| (grep) | The `tvars.remove` follows the `continue` that skips absent names | zedc-resolve resolve.rs (bounded variables) | added |
| (grep) | `Pick::Arm(b)` only when `b` is the one overload that can run the call | zedc-resolve resolve/pick.rs `Index::pick` | added |
| (grep) | No L2 or L6 statement reaches `Tables` (precondition on callers: `Tables::new` takes any `Resolution`; other test callers not each traced) | zedc-resolve resolve/tables.rs `binders_of`, `what` | added |
| (grep) | A cycle has a statement | zedc-resolve resolve/tables.rs `cycle_report` | added |
| (grep) | `step_repair` sees a `Bind` | zedc-resolve resolve/tables.rs `step_repair` | added |
| (grep) | Only a statement that binds a name is in a cycle | zedc-resolve resolve/tables.rs `what` | added |
| (grep) | The `expect`s of the cycle walk | zedc-resolve resolve/topo.rs `topo`, `cycle` | added |
| (grep) | The read stack leaves one number per part | zedc-stage stage.rs `Reader::read`, `needs_of` | added |
| (grep) | `split` sees only Split nodes | zedc-stage stage.rs `Sets::union` | added |
| (grep) | The same stack invariant | zedc-stage stage.rs `Frees::summary` | added |
| (grep) | Empty nodes are answered above | zedc-stage stage.rs `Maps::restrict` | added |
| (grep) | Each pop follows its push | zedc-stage stage.rs `Scope::pop` | added |
| (grep) | `known` is `None` only for a tuple or keypath; `next` is read from `open`'s top | zedc-stage stage.rs `Namer::canon` | added |
| (grep) | A stub is asked with a tuple | zedc-stage stage.rs `Stub::term_at` | added |
| (grep) | No lock is poisoned: no thread, guards dropped, mixes not resumed after a panic | zedc-stage stage.rs `Run` (doc) | added |
| (grep) | A port's key is a tuple | zedc-stage stage.rs `Port::with` | added |
| (grep) | `get` is asked only keys `refuses` let through | zedc-stage stage.rs `Port::get` | added |
| (grep) | `fill` leaves the key answered | zedc-stage stage.rs `Port::get` | added |
| (grep) | Every leaf index is a `Node::Leaf` | zedc-stage stage.rs `Mixer::trie` | added |
| (grep) | Indices on `todo` are build-stage entries | zedc-stage stage.rs `Mixer::needs` | added |
| (grep) | `stub` is called with an arity | zedc-stage stage.rs `Mixer::stub` | added |
| (grep) | `closed`'s two `expect`s | zedc-stage stage.rs `Mixer::closed` | added |
| (grep) | The `any(.. is_none())` above returned | zedc-stage stage.rs `Mixer` | added |
| (grep) | Every entry whose `known` is `Some` has a `global` | zedc-stage stage.rs `Mixer::eval` | added |
| (grep) | The watch stack is not empty in `take` | zedc-stage stage.rs `Mixer::take` | added |
| (grep) | A `Probe::Call` key is a tuple | zedc-stage stage.rs `Mixer` (probes) | added |
| (grep) | An Ask node is still an Ask after `answer` | zedc-stage stage.rs `Mixer` (trie walk) | added |
| (grep) | `walks.last()` is still there | zedc-stage stage.rs `Mixer` (walks) | added |
| (grep) | The mix job stack leaves one `Out` per part; `Let` and `LetBody` jobs hold a `let` | zedc-stage stage.rs `Mixer::mix` | added |
| (grep) | `build_from` sees no `Lit`, `PrimFn` or `Read` | zedc-stage stage.rs `Mixer::build_from` | added |
| (grep) | Every path of a `not_every_path` branch has its role | zedc-syntax ast/initial.rs `branch` | added |
| (grep) | One net result per statement; the root join | zedc-syntax ast/initial.rs (`results.pop`) | added |
| (grep) | Entries come only from statements with an `initial_of` | zedc-syntax ast/initial.rs `site` | added |
| (grep) | `keyed(b)` holds `line: Some` only from `Keys::Written` | zedc-syntax ast/initial.rs `shared` | added |
| (grep) | `runs` gets at most two pushes | zedc-syntax ast/initial.rs `narrowed` | added |
| (grep) | `NonAsciiName` comes only from `Word::Foreign` | zedc-syntax lex/token.rs `non_ascii` | added |
| (grep) | A character follows where `run_on` is called | zedc-syntax lex/number.rs `run_on` | added |
| (grep) | A Hole is pushed only at the bottom or above a Str | zedc-syntax lex/string.rs `hole_end` | added |
| (grep) | Escapes are valid when decoded, and strip cuts fall outside escapes | zedc-syntax lex/string.rs `decode` | added |
| (grep) | A rule node's kids are on the stack | zedc-syntax parse/engine.rs `rule_node` | added |
| (grep) | `saved` is pushed and popped with `Frame::Not` | zedc-syntax parse/engine.rs `Frame::Not` | added |
| (grep) | A `Choice` has two alternatives or more | zedc-syntax parse/engine.rs (Choice) | added |
| (grep) | A loop body is one expression or a `Sep` | zedc-syntax parse/engine.rs `iteration` | added |
| (grep) | The marked rule was read above | zedc-syntax parse/grammar.rs `marked_rule` | added |
| (grep) | The layers' rules exist | zedc-syntax parse/grammar.rs `lowest_layers` | added |
| (grep) | `Expected::Class` is not reached for a `Grammar::read` grammar (`parse_with` precondition for a `read_open` one) | zedc-syntax parse/tree.rs | added |
| (grep) | The fixed grammar text has the rules `Unit`, `Item`, `Expr` | zedc-syntax parse/tree.rs `grammar` | added |
| (grep) | Every binary primitive has a level | zedc-syntax format.rs `binary_level` | added |
| (grep) | `Err` comes only with errors | zedc-syntax ast/mod.rs `unit` | added |
| (grep) | Writing to a `String` cannot fail (std::fmt contract) | zedc-syntax ast/mod.rs `shown` | added |
| (grep) | `main_field`, `main_use` and the parameter of `main` | zedc-syntax ast/builder.rs | added |
| (grep) | A `main`'s body is in the table | zedc-syntax ast/stmts.rs `main_header`; ast/builder.rs `Mains::new` | corrected: bug (a `main` in a string's hole), fixed with test |
| (grep) | `main_handles` is called only under `mains.of(body).is_some_and(..)` | zedc-syntax ast/stmts.rs `main_handles` | added |
| (grep) | Grammar-shape `unreachable!`s and `expect`s | zedc-syntax ast/*.rs | already there (as a class, not traced) |
| (grep) | Test-only `expect`s | zedc-syntax fixed_width.rs tests, walk/tests.rs | already there |
| (grep) | A `main` reached at stmts.rs line 946 | zedc-syntax ast/stmts.rs | already there (`is_some_and` guard above) |
| (grep) | Only the operators `mark::mutable` admits reach `neighbors` | zedc mutate.rs `neighbors` | added |
| (grep) | The digit loop of a decimal neighbor stops before `i` passes 0 | zedc mutate.rs `stepped` | added (tests) |
| (grep) | `parsed` is `Some` exactly when `text` is `Some(Ok)`; a unit with imports has text | zedc unit.rs `load` (loader loop) | added (covers the `unreachable!`s of `load`, `pin_units`, `cycle_error`) |
| (grep) | An import outside the unit's component is resolved before it | zedc unit.rs `load` | added |
| (grep) | The breadth-first cycle search never runs out of units | zedc unit.rs `report` | added |
| (grep) | `main`'s parameters are the four `MainArgs` inputs | zedc run.rs `main_program` (`kind`) | added |
| (grep) | Each `PROOF-address-reads-literals-only` pointer | zedc query.rs, pin.rs, run.rs | already there (points to the proof) |
| (grep) | `PROOF-replay-missing-read-status` | zedc run.rs | already there |
| (grep) | A position lies in its definition (stated precondition) | zedc mutate.rs `apply` | already there |
| (grep) | A block just made has one owner | zedc run.rs `read_shared` | already there |
| (grep) | A second non-UTF-8 read cannot happen, and its `set` result is ignored | zedc run.rs | already there |
| (grep) | Each problem is in its file's group | zedc unit.rs | already there |
