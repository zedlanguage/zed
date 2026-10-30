# Implementation status

This file records where the implementation stands, so that the work can be restarted from it.
The plan is Part G of DESIGN.md, in the spec repository (`../zed`). The repository layout is
in docs/layout.md.

## Current position

- Done: **M0.1** (repository scaffolding), **M0.4** (the corpus, in `zed/corpus/`), **M0.9**
  (kernel reference evaluator), and in the spec, M0.2 and M0.3 (the desugaring rules, spec
  commit e3b217f).
- Done: **M0.10**, the finite-model harness (`tests/steps/m0_10_finite_model_harness/`): laws
  1–28, witness bijectivity, the recursion checks, the metatheory smoke cases; budget values
  in DESIGN.md M0.10 (spec commit fc58a1f).
- Done: **M0.5**, widening and iteration (`zedc::store`, `tests/steps/m0_05_widening_and_iteration/`,
  prelude units in `zed/prelude/`); values in DESIGN.md M0.5.
- Done: **M0.6**, the cost scalarization (`zedc::cost`, `zedc::address`, prelude unit `cost`).
- Done: **M0.7**, the canonicalizer (`zedc::canon`); values in DESIGN.md M0.7.
- Done: **M0.8**, the Zed₀ checklist (`zed/compiler/ZED0.md`): L6 completes Zed₀, so row S
  follows L6.
- Done: **M0.11**, the built-in operator axioms (`zedc::axioms`, prelude unit `axioms`), unit
  addresses (`zedc::canon::unit_address`, prelude unit `unit`), and the minimum resource
  limits (`zed_kernel::eval::MIN_*`, prelude unit `limits`). M0 is complete.
- Done: **L1.1**, source loading (`zedc::source`): UTF-8 and NFC checked, rejected with a
  span, line endings normalized.
- Done: **L1.2**, names and the wildcard (`zedc::lex`), with the one-script rule.
- Done: **L1.3**, integer literals (`zedc::lex::number`).
- Done: **L1.4**, float and rational literals (`zedc::lex::number`).
- Done: **L1.5**, string literals (`zedc::lex::string`), and `//` and nesting `/* */` comments (`zedc::lex::comment`), which a hole may hold.
- Done: **L1.6**, the lexical grammar whole: atoms, annotations, keywords, operators, doc comments (`zedc::lex::punct`, `lex_with_docs`).
- Done: **L1.7**, the fence extractor: the 149 `zed` fences of DESIGN.md and EXAMPLES.md are
  copied into `zed/fences/` with their layers, lexed, and their ✗ marks recorded (`zedc::fence`).
- Done: **L1.8**, the parser (`zedc::parse`): the grammar of sec:grammar, copied into
  `zed/grammar/`, run as a packrat parser at a ring; all 319 bracketing cases give their trees.
- Done: **L1.9**, postfix chains (`zedc::ast`): the syntax tree of an expression's operators
  and postfix chains, built from the parse tree.
- Done: **L1.10**, lambdas, `is` / `is not`, `else` and tuples (`zedc::ast`), with the L1 type
  expressions, parameter lists and atom patterns they are written with (`zedc::ast::types`).
- Done: **L1.11**, statements (`zedc::ast::stmts`): a block's bindings, with tuple
  destructuring targets and `_`, and its one export, `return` or the trailing expression.
- Done: **L1.12**, declarations (`zedc::ast::stmts`, `zedc::ast::unit`): functions in
  equation and block form with their `test` tables, `main`'s port header, the push `p <- e`,
  and `if`/`else`.
- Done: **L1.14**, name resolution (`zedc::resolve`).
- Done: **L1.15**, the kernel terms whole (the evidence record of `fold` and `fix`) and the
  kernel pretty-printer (`zed_kernel::print`).
- Done: **L1.16**, elaboration of the L1 surface to kernel terms (`zedc::elab`).
- Done: **L1.17**, value representation: unbounded integers, rationals, the natural order
  across number kinds, IEEE `==`, atom payloads by name (`zed_kernel::num`, `Value`).
- Done: **L1.18**, the interpreter's scalar tier: the L1 prelude words (`zedc::interp`,
  `zed_kernel::words`), the `#errs` merge, float printing with the exact round trip.
- Done: **L1.19**, whole-file ports (`zedc::run`, `zedc run` and `zedc replay`): `Lines` and
  `Files` inputs read once, `Lines` outputs written once when the wave ends, acknowledgments,
  and the replay record.
- Done: **L1.20**, provenance (`zed_kernel::provenance`, `Evaluator::with_provenance`,
  `Program::provenance`): fact addresses, the run graph, and the origin sets of failures.
- Done: **L1.21**, the test runner (`zedc::testing`, `zedc test <file> …`): function tables,
  `main` tables run as waves, and `// ✗` marks as expected diagnostics. Zed-written tests
  live in each step's `zed/` folder.
- Done: **L1.22**, types (`zed_kernel::types`): one part per universe, the connectives, tuple,
  atom and two-bound morphism types, and `e is T` / `e is not T`.
- Done: **L1.23**, subtyping (`Type::is_empty`, `subtype`, `equiv`; `zed_kernel::types::rec`):
  memoized coinductive emptiness, and recursive groups checked for regularity, contractivity
  and monotonicity at the definition.
- Done: **L1.24**, the refinement lattices (`zedc::store::{affine, float, cell}`): intervals
  with symbolic affine bounds, float classes, lengths, and the cell holding each element with
  its premises.
- Done: **L1.25**, the scalar preimage catalog (`zedc::store::preimage`): boxes marked exact
  or necessary, the forward confirmation, the enumeration, the stops.
- Done: **L1.26**, resolution rules 1, 3 and 4 (`zedc::check`): per-definition signatures by
  search, literal adoption, narrowing by `is`, the fit of function arguments; elaboration
  reads the checker's adoptions, fits and call signatures.
- Done: **L1.27**, absences and narrowing: types mark the atoms of named families; `else`
  strips only loose atoms, the pattern form strips the atom it names, and a family atom that
  selects no arrow is rejected.
- Done: **L1.28**, staging (`zedc::stage`): the build evaluates the demanded build-stage
  terms to literals and leaves the rest to run; the Trick splits a function on a parameter
  whose domain lists at most 1024 values (`Type::values` in the kernel).
- Done: **L1.29**, diagnostics: each checker rejection carries its derivation (`Error.notes`,
  `run::Diagnostic.steps`), rendered as numbered steps with the source underlined; failed
  signature searches list each failing combination; repairs that the checker discharges
  (wrapping in `String`, `int`, `rat` or `f64`) are offered only when the re-check passes.
- Done: **L1.30**, the compiler as queries (`zedc::query`): the front end keyed by the text,
  each table row keyed by the definitions its check reaches, so an edit reruns only the rows
  whose definitions changed; `zedc test` shares one database across its files.
- Done: **L1.31**, ZIR (`zedc::zir`): regions, value and state edges, the node inventory, the
  validator, and the text and binary forms.
- Done: **L1.32**, the canonicalizer on ZIR (`zedc::zir::canon`) and the graph's content address.
- Done: **L1.33**, the lowering of kernel terms to ZIR (`zedc::zir::lower`), with CSE by
  content address and the inverse `raise`.
- Done: **L1.34**, memory (`zedc::zir::memory`): the plan of owned and borrowed edges, dups,
  last-use drops and fused `match` releases, and a machine that runs a graph under the plan and
  checks every count after every node.
- Done: **L1.35**, the MLIR study (`zed/compiler/MLIR.md`): ZIR is lowered into MLIR's
  dialects, not written as one; the compact back end stays Cranelift.
- Done: **L1.36**, codegen via Cranelift (`zed-native`, with the runtime `zed-rt`): one
  generator for the JIT and object files, scalar nodes inline, every other node run by the
  runtime as the counting machine runs it, strings as ropes, `Lines` ports in the runtime.
- Done: **L1.37**, the differential oracle (`zed_tests::oracle`): the interpreter against native
  code, fused and unfused, on every enabled fence, the step units, the enabled corpus programs
  and each step program on every corpus input, byte-compared; permanent in CI.
- Done: **L1.38**, the linear-relation domain (`zedc::store::presburger`): the Omega test,
  projection, and rung 2 with products of two symbols as atoms; the preimage keeps the relation
  a necessary box was projected from.
- Done: **L1.39**, the reduced product (`zedc::store::product`): each name's cell, type and
  binding time, the scope's linear relation and written constraints, the reductions in rounds,
  the enumeration within its budget and fuel, narrowing by tests, and the arms of a body.
- Complexity audit (2026-10-30, DESIGN.md Part G, "Every algorithm is of low complexity"):
  every finding is listed in COMPLEXITY.md with its state. Fixed so far: the preimage transfer
  (exponential in `let` depth and guard nesting, now one computation per term and scope) and
  the projection (one split into conjunctions for all names, galloping bounds), the scope
  relation (shared conjuncts factored out of a join, at most 64 constraints and 64
  conjunctions kept), and the interval unions (forward images and operands capped to the piece
  limit, `cap` by a heap, `join` by a merge, `contains` by binary search), and the Omega test
  (dark shadow first, the real shadows alone before both recurse, a budget of 4,096 problems
  solved), and phase 1 of the store's iteration (head changes counted over the phase, and a
  component whose outside inputs did not change is skipped; nested loops cost linear work, where
  they were exponential in the depth). Scaling tests
  use `zed_tests::scaling::check` (n against 8n, at most 24 times as long).
- Next: the remaining COMPLEXITY.md items, then L1.40.
- Plan extended (spec, 2026-10-30): **L30 — the editor**, a VS Code extension on the L25
  language server (static information per position, the dependency margin, recomputation of
  dirty nodes, values in place with visualizers), steps L30.1–L30.6.

## Test baseline

Last full run: `cargo test --workspace` gave 815 passed and 0 failed (22 unit tests of
`zed-kernel`, 10 of `zed-tests`, 24 of `zedc`, 6 of `zed-rt`, 753 step tests: 6 in `l01_01_source_loading`, 8 in `l01_02_lexer_names`, 5 in `l01_03_lexer_integers`, 5 in `l01_04_lexer_floats_and_rationals`, 10 in `l01_05_lexer_strings`, 10 in `l01_06_lexer_tokens`, 11 in `l01_07_fences`, 7 in `l01_08_parser`, 9 in `l01_09_postfix_chains`, 9 in `l01_10_lambdas_types_else_tuples`, 7 in `l01_11_statements`, 11 in `l01_12_declarations`, 12 in `l01_13_formatter`, 20 in `l01_14_name_resolution`, 18 in `l01_15_kernel_terms`, 27 in `l01_16_elaboration`, 19 in `l01_17_value_representation`, 22 in `l01_18_scalar_interpreter`, 19 in `l01_19_whole_file_ports`, 16 in `l01_20_provenance`, 18 in `l01_21_test_runner` (with the checks of every step's `zed/` units), 12 in `l01_22_type_representation`, 14 in `l01_23_subtyping`, 24 in `l01_24_refinement_lattices`, 29 in `l01_25_preimage_catalog`, 36 in `l01_26_type_resolution`, 11 in `l01_27_absences`, 11 in `l01_28_staging`, 16 in `l01_29_diagnostics`, 9 in `l01_30_queries`, 20 in `l01_31_zir`, 10 in `l01_32_canonical_zir`, 27 in `l01_33_lowering`, 20 in `l01_34_memory`, 4 in `l01_35_mlir_study`, 18 in `l01_36_cranelift`, 7 in `l01_37_oracle`, 15 in `l01_38_presburger`, 21 in `l01_39_reduced_product`, 3 in `m0_01_scaffolding`, 27 in
`m0_05_widening_and_iteration`, 8 in `m0_06_cost_scalarization`, 14 in
`m0_07_canonicalization`, 1 in `m0_08_zed0_checklist`, 32 in
`m0_09_kernel_evaluator`, 83 in `m0_10_finite_model_harness`, 12 in
`m0_11_prelude_axioms_and_limits`). `cargo fmt --all --check` and
`cargo clippy --workspace --all-targets -- -D warnings` are clean. The steps binary takes
about 48 s in a debug build, with `zed-kernel` built at opt-level 2.

## Steps

| Step | State | Notes |
|---|---|---|
| M0.1 | done | workspace (`zedc`, `zed-kernel`, `zed-rt`, `zed-cert`, `zed-tests`), CI workflow, insta snapshots. Both negative controls fail as they should: a corrupted snapshot, and an undeclared step folder |
| M0.10 | done | `zed_kernel::budgets` holds the ladder budgets and the rung 6 instance. `zed_tests::{instances, check, kernel}` hold the enumerators, the equation checker, and the derived forms. Laws 1–28 with a counterexample per side condition; the eight layer-free witness entries with their side-condition counterexamples (truncated division fails the packing inverse on row -1); every schedule agrees on all 512 three-node graphs and 512 random ones, stalls included; smoke cases. Negative control: making an undefined read ignore which `fix` it belongs to fails both nested-fix tests. 11 s in a release build |
| M0.5 | done | `zedc::store::{interval, lattice, wto, iterate, revision}`: interval unions with the piece limit and widening, congruences, finite sets, cardinalities; Bourdoncle's order and recursive strategy (phase 1) and Jacobi narrowing rounds (phase 2); the tonicity and HC4 tables and the reductions. Oracles: a declarative weak topological order (2,048 graphs), a stack machine for phase 1 (512 systems × 5 delays × 2 bounds), the concrete least fixpoint in a window, and brute-force soundness of one revision round (over 10^6 solutions). The prelude units `lattice`, `iteration`, `revision` parse (`ring.py`) and check at L6 together (`layer.py`). Negative controls: widening at `changes >= delay` fails 2 tests; dropping the zero guard of backward `*` fails 2; reversed successor order fails the order oracle; Gauss-Seidel narrowing fails 2 |
| M0.6 | done | `zedc::cost`: target profiles (default: one 8-core CPU, 16 GiB), per-device Brent bounds plus one transfer per cut edge, the per-device Pareto frontier, the pick with content-address tie-break. `zedc::address::ContentAddress` (bytes, hex, byte order; hashing comes at M0.7). Negative controls: reversing the tie-break, dropping the transfer latency, a frontier over totals, ignoring capacity, and flooring the Brent bound each fail a test |
| M0.7 | done | `zedc::canon`: four rules (binders to de Bruijn levels with the written name kept as a hint, hints dropped, facets sorted and deduplicated, domain normal form), each with a rank; the tagged serialization; BLAKE3 address over a domain tag, `VERSION` = 1 and the serialization, with resolved free names hashed as their definitions' addresses. Over kernel terms until ZIR exists (L1.32). Oracles: de Bruijn-index α-equivalence on 2,048 random term pairs; domain normal forms against membership in -60..=60 on 4,096 random domains; rank decrease and rule-order independence on 512 random definitions. Negative controls: ignoring shadowing (two places), dropping a lambda's arity, ignoring resolution, hashing `abs` of floats, skipping the run merge, skipping the point-class join, keeping the first duplicate facet, and dropping the version each fail a test |
| M0.8 | done | `zed/compiler/ZED0.md` and `audit.py`: program 31 needs 91 grammar alternatives (L1, L2, L3, L6) and 13 words (up to L5), each found by deleting the alternative and reparsing; Part B adds the compiler's needs beyond program 31, all at L1–L6 but the built-in Cranelift ports (step S.4). The audit needs the spec's grammar tools, so it runs by hand; the step test keeps the stated layer equal to the highest item and to program 31's label. Negative controls: one entry deleted from the checklist makes the audit exit 1 naming it; program 17 audits to `window` at L7; stating L5 fails the step test |
| M0.11 | done | `zedc::axioms`: 86 axioms, one per operator, carrier and law, over the kernel's carriers `int`, `f64`, `bool`, `String`; each holds on the M0.10 instances (rung 6 ints and floats, both bools, strings over `a`, `b` up to length 3), run on the reference evaluator, and `zed/prelude/axioms.zed` is checked equal to the table. `zedc::canon::unit_address` hashes the exports by name and address. `MIN_STEPS` 10^7, `MIN_MEMORY` 1 GiB, `MIN_NESTED_CALLS` 20,000, with a compile-time assertion that the evaluator's fuel and depth meet them; tests run a 9,999,999-step program, a 20,000-deep chain and a 2^30 - 1 byte live string, and one step or call more is shown to cross the step and depth limits. Negative controls: a false claim of each kind of law is refuted (16 claims); claiming `+` associative at `f64` fails on 1.0, 0.1, 0.1; dropping the name length from the unit hash breaks the pinned address; `MAX_DEPTH` 19,999 does not compile |
| L1.1 | done | `zedc::source::load`: UTF-8 (the first invalid sequence's bytes are the span), no leading byte order mark, NFC (the span is the first piece cut before a character of combining class 0, or pair of such pieces, that NFC changes, and the message gives its NFC spelling); `\r\n` and `\r` become `\n`. Golden rejections of ten files as tools write them (ISO-8859-1, a macOS decomposed name, Notepad's mark, a truncated download, CESU-8, an overlong `/`, U+212B, marks out of order, Hangul jamo, a CRLF file), each repaired by its NFC spelling; a 20,000-string fuzz checks the span against `is_nfc`. Negative controls: checking the pair before the single piece widens the span and fails the fuzz; dropping the lone-`\r` rule fails the line-ending test |
| L1.2 | done | `zedc::lex`: the lexer, whose token kinds grow through L1.6 (a character no rule reads yet is an `Unexpected` error); `lex::name` reads `Name` and `Wildcard` by the lexical grammar, and `is_single_script` is UTS #39 Highly Restrictive. Tests: names in eleven scripts and three Latin-with-East-Asian mixes lex; Cyrillic and Greek lookalikes, `ΔT` and Hangul with kana are rejected with the span and the scripts named; `_`, `_x`, `__init__`, one trailing `'`. Negative controls: without the East Asian sets `user名` is rejected; reading a bare `_` as a name fails the wildcard test (the test's helper first printed both as `_` and missed it; fixed) |
| L1.3 | done | `lex::number`: `Tok::Int { radix, digits }`, the digits kept exactly with `_` removed, so `2^128 + 1` lexes; a number running into a name character is one `BadNumber` error over the run, naming the defect (`_` not between digits, a digit outside base 2 or 8, `0x` with no digit, a letter as in `200ms`). Golden snapshot of ten malformed numbers. Negative controls: accepting a `_` with no digit after it, and dropping the `!XID_CONTINUE` check, each fail the golden test |
| L1.4 | done | `Tok::Float` and `Tok::Rat` keep the decimal text without `_`; a digit must follow `.`, so `5.double`, `1..10`, `1.e5` and `12.` end the number before the `.`, and `.5` is no number; an exponent with no digits, an `r` after a hex, octal or binary literal, and a letter after a float are `BadNumber` errors. Golden snapshot of ten malformed literals. Negative controls: reading `.` without a following digit, and accepting `r` after any base, each fail a test |
| L1.5 | done | `Tok::Str(Vec<Part>)`: decoded text parts and `Part::Hole { tokens, span }`, each hole lexed once into tokens with spans in the whole file; a hole's end is found by the `HoleText` rule, so a string or comment inside it neither opens nor closes it; the `"""` indentation rule; golden snapshots of eleven malformed strings and six malformed holes. Comments are skipped from here on, since a hole may hold one. Negative controls: dropping the indentation cut, scanning an inner string as plain characters, and dropping the one-line check each fail a test |
| L1.6 | done | `Tok::Keyword`, `Tok::Op` (41 operators, longest first), `Tok::Atom`, `Tok::Annot`; `where` and `sep` stay names; `if'` is the keyword and a stray `'`; `lex_with_docs` returns the `///` comments beside the tokens. Golden snapshots: the `sec:tour_failure` example of EXAMPLES.md (copied into the test) and nine lexical errors. Negative controls: `->` ahead of `->?`, `////` read as a doc comment, and keywords read as names each fail a test |
| L1.7 | done | `zedc::fence` (`extract`, `marks`, `label`) and `lex::lex_fence`, which reads `…` as a name. `zed/fences/sync.py` records each fence's layer with the spec's grammar tools: its lowest ring (as a `Unit`, or else under the documentation notation; 13 fences), raised to its defined words and its label; the rings agree with `check.py` on all 149. All 149 fences lex; their tokens and ✗ marks are golden snapshots. The 11 commented ✗ variants each have a fixture in `zed/fences/variants/`, matched by the variant's text, with exactly one live ✗ line. Negative controls: no variant rule, a label read from the first line only, `…` not elided, a stale copy (also `sync.py --check`), and a layer recorded below its label each fail a test |
| L1.8 | done | `zedc::parse`: `Grammar::read` reads `zed/grammar/syntax.peg` and `notation.peg` (copied by `sync.py`, with a drift test); `parse(text, tokens, start, ring)` matches as `check.py`'s `Parser` does (ordered choice, packrat memo on rule, token and the `head` flag, alternatives above the ring skipped, a literal matching a keyword, operator or name by text) and gives a tree whose nodes record rule, alternative and token span, plus a tree per string hole. All 319 cases of `cases.txt` give their s-expressions; all 149 fences first parse at the ring `sync.py` recorded, as a `Unit` or a `DocFence`; each variant fixture parses as its fence does. An error names the furthest token reached and what was expected there (golden snapshot). Negative controls: the ring filter off, `head(…)` ignored, `!` keeping its failures, inline choices reversed each fail a test |
| L1.9 | done | `zedc::ast::{build, expr}`: literals, names, atoms, grouping, the L1 prefix and binary operators (left-associative but `**`), and the suffixes call, index, `.` and `?.`; a call keeps positional, named and `...` apart, `x:` is `x: x`, and a name given twice is an error at the second. A form of a later step or layer is an error naming it (`this form (Expr) is built from step L1.10`). Every postfix chain in the 149 fences builds (512) or names its later form (170), and a built chain's span is its parse node's. Negative controls: right-associative folding, `?.` read as `.`, no duplicate check, `...` ignored, and every string reading the first hole each fail a test; the fence test found that grouped expressions lost their parentheses from the span (fixed) |
| L1.10 | done | `zedc::ast`: lambdas (one name, or a declaration's parameter list with `positional`, types and defaults; a brace after the arrow is a block, built at L1.11), `is` and `is not`, `else` chains read left to right with an optional atom pattern (`#e(pos:)`, `#add(#zero, #zero)`), and tuples of two or more. `zedc::ast::types`: the L1 type expressions (names with unit paths, atoms, tuples, `\|`, `&`, `\`, arrows with `->` and `->?`, one parameter level per arrow, right-associative, parameter names and `positional`). Every expression in the 149 fences builds (1505) or names its later form (309), none of them an L1.10 form. Negative controls: `is not` read as `is`, the atom pattern dropped, `->?` read as `->`, a lambda's name read as positional, a tuple type read as a union, the operands of `\` swapped, and `positional` dropped from a type parameter each fail a test |
| L1.11 | done | `zedc::ast::stmts`: `ExprKind::Block` of `Stmt`s: `a, _ = e;` bindings (`Target::Name`, `Target::Wild`) and `return e;` / `return a, b;`, the trailing expression built as its `return`. A block in expression position exports exactly once: a second export is an error at it, naming the first's byte, and a block with none is an error. A function or push in a block names L1.12, an expression statement `e;` layer L6, a `with` boundary L6. The fences hold one block in expression position, which builds; most blocks sit in `if`, loops and declaration bodies, built with those forms. Negative controls: a second export allowed, a missing export allowed, `_` read as a name, and the first export's position misreported each fail a test; the `_` test found that `Target = Name \| WILD` is one alternative, so a wildcard is told by its missing `Name` child (fixed) |
| L1.12 | done | `StmtKind::Function` (name, parameters, the port header `-> (stdout: Lines, …)`, an equation body or a block body, the cases of every `test` table in written order), `StmtKind::Push` for `p <- e`, `ExprKind::If` with `else if` nested in the `else` branch, and `zedc::ast::unit` for a whole unit. A body block may export nothing; an `if` branch block, being an expression, must export. `return` at a unit's top level is an error. Every L1 form is now built, so a form not built names its layer from the grammar (`-> T` L10, `t[i] <- e` L7). Of the 136 code fences, 23 build as whole units and 113 name a later-layer form. Negative controls: a body block required to export, a test case's sides swapped, the indexed push read as the whole push, equation and block bodies swapped, the `else` branch read as the `then` branch, and a top-level `return` allowed each fail a test |
| L1.13 | done | `zedc::format::format` writes a unit in one layout: two-space indentation, one statement per line, a block of one export on one line, the export last, the `test` cases of a function as one table on one line under it, and parentheses only where the grammar needs them (an `if` condition holding a block, a default or lambda body starting with one, a number receiving `.`). Comments are kept with their statements; blank lines collapse to one. `zedc::lex::comments` finds the comments between tokens; `zedc fmt <file>` prints the result or `line:col: error`. The AST builder now stores a block's export last, so a formatted unit builds to the same AST exactly. The 23 fences that build and the one corpus program that builds (09) format to a fixed point with the same AST and comments; the corpus program is already in the layout. Negative controls: no parentheses around a block condition, the export written first, a blank line kept for every newline, a comment on the next line taken as trailing, a left-associative chain's right operand left unparenthesized, `x: x` not shortened, comments dropped, the builder storing the export first, and a three-space indent each fail a test |
| L1.14 | done | `zedc::resolve::resolve` ties each name a unit uses to its binders (an overload set's arrows together) or to an L1 prelude word, in the order block scopes, top level, prelude; it reports rebinding in one scope, unknown names and types, and prelude words of later layers. Tests: `tests/steps/l01_14_name_resolution/`, one per rule, the building fences and the corpus program. |
| L1.15 | done | `Term::Fold` and `Term::Fix` carry the evidence record `ev` of sec:kernel (each tracked property with its grade, `zed_kernel::Grade`), which goes into the content address (canonicalization VERSION 2, both pinned addresses re-pinned) and which the evaluator does not read. `zed_kernel::print`: `Display` writes a term on one line in the notation of sec:kernel, `pretty(t, width)` breaks it into indented parts. Tests: `tests/steps/l01_15_kernel_terms/`, one term per generator, the evidence in the address, and the layout, with a random check that breaking changes only whitespace. |
| L1.16 | done | `zedc::elab::elaborate` turns a resolved unit into its top-level definitions in dependency order (`Unit::close` wraps a term in them) and the cases of its `test` tables. Blocks are lets in dependency order over the export; calls of a declared function place the receiver, positional and named arguments, fill defaults and curry with `...`; `x.f` is the uniform call or an L1 prelude word; `f[k]` is a section, `t[1]` a tuple component; `&&` and `||` are `if` forms; strings are `++` chains with `String(hole)`; `else` and `?.` match any atom. New kernel primitives `Concat` (`++`) and `Pow` (`**`), and the pattern `AnyAtom` (`#_`). Tests: `tests/steps/l01_16_elaboration/`, programs elaborated and run on the kernel evaluator, printed terms, and one case per error. |
| L1.17 | done | `int` is unbounded: `Value::Int(i64)` while it fits, `Value::Big` beyond, arithmetic widening instead of failing. `Value::Rat`, exact and reduced, from `0.1r` literals, with `+ - * /` and `#divByZero`. A manual `Ord` gives the natural order: kinds atom, bool, number, string, tuple, path, family; numbers by exact value across kinds (`num::Exact`), tie broken int, rat, float. Language `==` is `Value::surface_eq` (IEEE at floats, at any depth) and compares atoms as data; `<` and the others are IEEE on floats and same-kind only. Atoms gain `fields`: `#e(code: 3)` builds by `Prim::Atom`, matches by `Pattern::Fields` (a subset of fields). Canon tags 8–10 for big, rat and named atoms; positional atoms keep their addresses. Four f64 axioms that IEEE breaks are removed (82 left). Tests: `tests/steps/l01_17_value_representation/`. Negative controls: bitwise float `==`, no kind tie-break, exact-field matching, unreduced rationals, wrapping `+`, and `==` passing atoms through each fail a test |
| L1.18 | done | `zedc::interp::prelude` binds the ten L1 words to new kernel primitives (`Show`, `CastInt`, `CastRat`, `CastF64`, `Abs`, `Len`, `Lower`, `Upper`, `Trim`, `Sum`; `zed_kernel::words`). Several loose atoms of one application merge by `Value::merge_failures` into `#errs({…})`: set union, flattened, a singleton unwrapped; a family mapping each key to itself prints `{a, b}`. Casts are exact, `#inexact` or `#invalid`; `f64` of a number checks exact representability (`num::exact_f64`). Floats print by `num::show_f64`: shortest digits, fixed for exponents -6..<21, else `d.ddde-7`, and `inf`, `-inf`, `nan`; 20 000 random bit patterns read back bit for bit. Tests: `tests/steps/l01_18_scalar_interpreter/`. Negative controls: leftmost atom winning, no flattening, no singleton unwrap, both ends of the fixed range, f32 digits, truncating `int`, rounding `f64` casts, overflow not `#inexact`, non-finite `int` as `#inexact`, byte `len`, ASCII `trim`, a `+` sign accepted, `sum` ignoring atoms, and one-step scaling in `exact_f64` each fail a test |
| L1.19 | done | `zedc::run` loads a program, binds `main`'s parameters as input ports and its header's ports as outputs, runs one wave, and commits the buffered writes with their acknowledgments (`commit`). A `Lines` input is the family of its lines from key 1 (`split_lines`); a `Files` port is a kernel lookup port (`zed_kernel::Lookup`, `V::Source`), answered once per path and kept in `World::reads`. A second push to one port in a wave is an error naming L7. `Record` saves the inputs in a length-prefixed text format, and `Program::replay` runs from it alone. `zedc run` and `zedc replay` (`run::command`). Tests: `tests/steps/l01_19_whole_file_ports/`. Negative controls: no memo of reads, lines from 0, `\r` kept, a trailing empty line kept, two pushes allowed, commit going on after a failure, a failed write ignored, no `\n` after a line, `#notFound` as `#ioError`, replay reading the disk, the record dropping `#notFound` reads, a record's entry end unchecked, a family applied as a type error, and outputs kept after an error each fail a test |
| L1.20 | done | `Evaluator::with_provenance(root)` records one `Fact` per node instance: a `FactAddress` of a `NodeAddress` (the call-site positions, then the node's preorder position in the run's term) and a keypath (`root`, then the region coordinates), with the facts it read. Variables are edges and pass on their binding's fact. `Provenance::repeated` lists addresses held twice; `Provenance::origins` gives the facts where each atom of a failure first appeared. `Program::provenance` runs a wave with stamp 0. The term is copied without shared subterms before positions are numbered, since a clone shares them. Tests: `tests/steps/l01_20_provenance/`. Negative controls: no call site pushed, the term left shared, the wave root dropped, no coordinate entered for `fam`, `reindex`, `discard` or a `fold` group, the combine index not counted, a fixed lattice iterate, a definedness retry not dropped, a fixed `gen` step or guard `t`, the fact of a parameter, a `let` or a `match` binding dropped, every visited fact taken as an origin, and payloads not searched each fail a test |
| L1.21 | done | `zedc::testing::test(text)` gives one `Outcome` per check: a row of a function's table passes when the call `==` the expected value; a row of `main`'s table runs a wave whose key gives the input ports (a `Lines` port as the `String` of its bytes, a `Files` port as a function from path to contents) and whose value gives the `String` each output port writes, `""` for one not pushed; a rejected unit passes when each diagnostic is on a `// ✗` line and each such line has one. `zedc test <file> …` prints the failures as `file:line:col: why` and the counts, and exits 0, 1, or 2 for usage. `run::compile` gives the diagnostics with line and column, and `load` is built on it. Every step's `tests/steps/*/zed/*.zed` unit is run by one harness test; this step's four units (greeting, Fahrenheit, a config file with a fallback, a username on two ports) hold 22 checks. The L1 fences run: the rebinding fence passes its mark, the lambda fence elaborates, and the two fragments fail only on their free names. Tests: `tests/steps/l01_21_test_runner/`. Negative controls: a mark never checked, an unmarked diagnostic ignored, a mark in an accepted unit passing, `main` rows skipped, a row's verdict always true, writes not compared, only the first port compared, input bytes trimmed, a non-string `Lines` input accepted, and the exit status always 0 each fail a test |
| L1.22 | done | `zed_kernel::types::Type` is a set of values with one part per universe (`Universe`: scalar, tuple, struct, morphism), and `|`, `&`, `-` and `!` act on each part separately, so a complement stays within each universe. The scalar part is exact (per base type a finite or cofinite set of literals; per atom name the bare atom and a payload type); the tuple and morphism parts are unions of clauses, with tuple types of one length met componentwise and of two lengths disjoint, and clauses merged and subsumed. Morphism types carry a guarantee and a permission bound (`exact`, `partial`, `morphism`). `contains` decides membership for a type whose function part is all or none (`decidable`). In `zedc`, a type expression elaborates to a `Type` (function types curried, `->?` partial at each level), and `e is T` to a match with the kernel pattern `Pattern::Is(T)` and a `_` arm; `is` rejects `Lines`, `Files` and types that bound functions. Tests: `tests/steps/l01_22_type_representation/` (membership against the type expression read as a predicate over a sample of every universe, 1500 random expressions; the laws; printed forms; elaboration) and three `zed/` units. Negative controls: a cofinite union dropping its exclusions, a cofinite meet keeping too few, a clause complement taken as a join, tuple lengths not compared, either merge of clauses without an equal rest, subsumption reversed, negated tuples ignored, an atom complement keeping its payload, a struct payload always in, no function in any type, a keypath as a scalar, `is not` ignored, and function bounds accepted each fail a test |
| L1.23 | done | `Type::is_empty` decides emptiness by a memoized coinductive search (`types/empty.rs`): a type met again while it is decided is assumed empty, and results resting on an assumption found false are dropped; a tuple clause is empty when the meet of its positive tuples is covered by its negated ones (split on each negated type's components), a morphism clause when its bounds cross, a promised key has no value, or one negated type contains all it admits (sound, incomplete for covers by several). `subtype` is emptiness of the difference, `equiv` subtyping both ways. `types::rec::Group` takes a group of recursive definitions and rejects one that is not regular, not contractive or not monotone in emptiness; `instance` builds lazy recursive nodes. Tests: `tests/steps/l01_23_subtyping/` (emptiness and subtyping against a value oracle over 1500 random expressions each; the spec's morphism examples, flow narrowing, tuple and Boolean identities, atom payloads; `Tree`, `W` accepted and `Nest`, `T` rejected, the other rejections and their accepted neighbors, coinductive emptiness, recursive subtyping, decidability). Negative controls: the product split keeping the component, no coinductive assumption, results on false assumptions kept, each variance of the morphism check reversed or dropped, crossing bounds allowed, a promised key with no value allowed, tuples without a positive type taken as empty, atom payload emptiness ignored, regularity, contractivity, the complement, difference and value checks off, a shrinking parameter ignored, parameters taken as nonempty, recursive components met, no lazy component (the build hangs) and `decidable` looping on recursion each fail a test |
| L1.24 | done | `store::affine::Bounds` is an interval union with symbolic bounds, each an affine expression in at least one symbol (`Sym` by source text) with an optional numeric floor, `max(c, a)` above and `min(c, a)` below; meet keeps every bound and is exact, join keeps the looser of each same-terms pair and each bound loosened by the other side's numeric end, the order is sound and incomplete, and widening keeps only the old element's bounds. `store::float::FloatClass` is a set of kinds and the narrowest exact IEEE width. `store::cell` holds per fact address an `Entry` per domain (bounds, congruence, finite set, float class, length) with its `Premise` set: a written constraint by address, or a widening that gave more than the join; `proof_grade` is no widening premise. `Lattice` gains `leq`. Tests: `tests/steps/l01_24_refinement_lattices/` (meet, join, widening, order and offset against members at 49 symbol values over 512 random elements; finite widening chains; the M0.5 solver on `for i in 0..<n` giving `[0..=max(0, n)]` and the body's `[0..=n - 1]`, a loop counting down, and 128 random loop systems against runs; float widths, meet and join over every class; premises through meet, join and widening; literal cells; lengths). Negative controls: the join with the numeric end dropped, pairs joined at the tighter constant, widening keeping new bounds, the vacuous test reversed, crossing at equal constants, the lower floor taken as max, implication ignoring the floor, the order ignoring the union, an offset leaving the floor, `plus` ignoring its constant, a loosening keeping the tighter floor, the f16 subnormal floor one bit higher, the float join and meet at the wrong width, a meet adding premises when it changes nothing, a join dropping the other side's premises, a widening not recorded, a length counted in bytes and a widened length not clamped each fail a test |
| L1.25 | done | `store::preimage::preimage(term, inputs, demand)` gives a box of integer sets over the inputs, marked exact or necessary, with the stops met. The backward pass inverts shifts and scalings by a constant, Euclidean `div` and `mod` by a constant (`mod` within the operand's bounded forward interval), `x ** k` and `x * x` (read as a power), `-x` and `abs` at their endpoints, comparisons as rays (a comparison of two terms through their difference), `!`, `&&`, `||`, branches as the union of guarded arms, `min`/`max`, and calls to the unit's definitions and the prelude words; anything else takes the HC4 table, necessary. A forward pass that tracks ints, bools, failures and other kinds confirms a necessary box, and a finite box within the budget is enumerated. `preimage::tonicity` gives each scalar primitive's tonicity per argument. Stops: a string operation, a foreign name, a term outside the scalar catalog. Tests: `tests/steps/l01_25_preimage_catalog/` (preconditions and guards from Zed source against the interpreter, among them `x * x <= 99` to `[-9..=9]`; 500 random integer and test terms with divisions that can fail, `min`/`max`, powers and branches over random domains, sound everywhere and exact where claimed; each stop with its term; each tonicity claim run over every pair in a sign part). Negative controls: a union exact without a box, a meet exact from one side, capping keeping exactness, no forward confirmation, the `<` ray off by one, `<=` negated to `>=`, the mirror as identity, `times_pre` taking the floor for the ceiling, `div_pre` dropping the remainders or ignoring a negative divisor, the strict `||` always exact, a failing operand meeting `!=`, ordered comparisons on data not failing, division by zero not a failure, the forward `<=` false case at equal ends, `==` never false, `max` over its whole range taking the meet, `!` without tonicity, `len` not read through, the scan descending into strings and the shift ignoring its constant each fail a test; `mod` by a constant with every remainder returning every integer instead of the operand's interval survives, and is equivalent, since the operand's backward pass gives the same box for both |
| L1.26 | done | `check::check(unit, resolution)` gives each declared function a signature (an intersection of arrows over its parameters' names and kinds), the literal adoptions, the fits of function arguments and the signatures of calls through values, and the type errors; `elab` takes its adoptions, fits and call signatures. Undeclared parameters are typed by search: type variables first, then carriers for one parameter, two, and so on. A bare integer literal adopts int, f64 or rat, a float literal f64 or rat, exactly or with an error; `is` narrows through `not`, `&&` and `||`; a declared function fits a function type by its names, reordered by an adapter, and a lambda by its own names, with its defaults for parameters the type leaves out. Tests: `tests/steps/l01_26_type_resolution/` (signatures of everyday functions, `pick` generic as `(bool, T, U) -> T \| U`; adoption, including the exact-or-rejected error and decorated literals; narrowing in both branches and in the right operand of `&&` and `\|\|`; fits by adapter and lambda, and their errors; calls through values with named arguments, closed defaults and `...`; 700 random bodies whose evaluated values all lie in their arrow's result type, 748 values). Negative controls: a float literal adopting int, the search not stopping at its first level, `&&` narrowing as `\|\|`, the adapter passing in declared order, a nonzero divisor still adding `#divByZero`, an arrow kept that an argument cannot meet, and a default left unchecked each fail a test |
| L1.27 | done | `Ty.family` holds the atoms of named families: kept by a join when either side has it, by `meet` and `diff`, cleared by `written()`; `Ty::named()` sets it (L2.1's `type` will). `e else d` strips the loose atoms only; `e else #a -> d` removes `#a` from the type and keeps the other absences; a family atom reaching an operator, a call, an index, `sum`, destructuring or a condition is rejected; `?.` passes loose atoms only. `check::operator(op, args)` types one operator application. Tests: `l01_27_absences` (11): the three absences defaulted, handled one at a time and merged into `#errs`, with run values; the family rules on the type representation and the operator rule. Negative controls: `else` stripping family atoms, a join dropping one side's marking, a written type keeping it, the pattern form not removing its atom, family atoms passing operators, `meet` dropping the marking, `else` keeping loose atoms; each fail a test |
| L1.28 | done | `stage::color`, `stage::mix`, `Program::stage`: demand from `main` and the tests, one fuel of 10^6 per build-stage term, a stopped term left whole and its name made run-stage, `if` on a literal cut; `stage::trick`/`split` over `Domain::Type` (via `Type::values(cap)`) or `Domain::Ints`, the general body kept as the last arm. 11 tests in `l01_28_staging`; 9 mutants caught. |
| L1.29 | done | `ast::Note`, `Error.notes`; `check::Ck` records each expression's type and source (`seen`) and each binder's origin (`whence`, narrowing chained), derives at the error (`derive`, at most 16 steps back, deduplicated); `applied` lists argument derivations and the callee's arrows; `infer` collects failing combinations (at most 12, the rest counted); `repairs` re-checks each wrapped argument; `run::Step` and the renderer; duplicate bindings, arguments and exports point at the first. Tests: full rendered chains, search failures, caps, layout, repairs applied and re-loaded, the ✗ variants pinned. |
| L1.30 | done | `query::{Db, Key, Query, key, cone}`: `Db::front` memoizes `run::compile` by the text's hash; `Db::row` memoizes a table row under the hash of `cone` (the printed definitions its roots reach, closed by one backward pass over the unit's dependency order); `testing::test_in` runs a unit against a database, and the outcome of a diagnostic now carries its derivation. Mutants caught: the cone unclosed, the roots omitted, the parts unprefixed, the name unhashed, the wave key without `main`, either memo bypassed. |
| L1.31 | done | `zir::{Region, Node, Op, Edge, Src, validate}`, `zir::text::{print, parse, parse_edge, parse_type, parse_value, parse_pattern}`, `zir::binary::{encode, decode}`. Ten graphs of real shapes (a price total, a greeting, an echo, a default, a countdown, reachability, a group, tiered shipping, mutual recursion, constants) go through every round trip; 29 text and 7 binary rejections pinned. Mutants caught (16): fold depth 0, state in any region, state reused, a forward or own-output reference, capture types unchecked, the certificate flag dropped, duplicate lines, a sibling region's edge, header order, interval facts, hints read as facets, the one-tuple mark, the identity bit, trailing bytes, bad tags, unsorted fields. |
| L1.32 | done | `zir::canon::{ranks, step, canonicalize, address}`: the M0.7 rules on ZIR, the binder rule on match patterns, the other three per edge. Addresses kept under binder renaming (top level and nested), hint changes, facet order and repeats, and three spellings of one integer set; changed by an operator, an input order, a domain, a pattern, a result, a port name. Fuzz: 300 random graphs, every step lowering the ranks, normal forms checked; 200 seeds renamed and with facets reversed keep their address. Mutants caught (9): the binder rule off, levels uncounted, the hint rule skipped, outputs or nested regions not rewritten, nested binders not renamed, the raw graph hashed, the rank ignoring nesting or outputs. |
| L1.33 | done | `zir::lower::{lower, raise}`: one node per operation, lets as name hints, primitives as values kept as no-input `prim` nodes (a fold of `+` stays exact), literal lambda calls lowered in place, captures and state edges taken on demand, port-using functions inlined, CSE by content address. Every corpus row passes through lower, validate and raise with its outcome unchanged; mutation-tested (15 mutants caught). |
| L1.34 | done | `zir::memory::{plan, run}`: values as cells (strings, big numbers, keypaths, families; tuples, atoms with payloads and closures with children), edges owned or borrowed, parameters borrowed unless consumed, a dup before each consuming use but the last, a drop at each last use that borrows, `match` releasing its scrutinee fused (1 count write against 4 for a fresh destructured pair). The checking machine runs every corpus row, fused and unfused, with outcomes unchanged and no cell left; it reports a missed drop, an extra or missing dup and a borrowed argument to a consuming parameter. Mutation-tested: 20 of 21 mutants caught; the survivor is the mode for a known lambda called with the wrong number of arguments, which no row reaches. |
| L1.35 | done | `zed/compiler/MLIR.md`: a lowering into MLIR's `func`, `arith`, `math`, `scf`, `memref`, `async` and `llvm` dialects for each of the 19 operations, the 5 region kinds and both edge kinds; ZIR is not an MLIR dialect; graph regions are not used, since the lowering starts after scheduling; state edges become call order, or `!async.token`s between concurrent regions of a wave; content addresses become locations; certificates stop at the lowering, with the differential oracle checking MLIR and LLVM; the compact back end stays Cranelift. The step test fails when an operation or region kind lacks a row (negative control: two rows removed, two tests fail). |
| L1.36 | done | `zed-native::{run, object, through}` on `zed-rt::{Heap, Word, Rope, ports}`: values as two-word tags and payloads; integer, float and boolean arithmetic and comparisons inline with overflow, least-integer negation and NaN canonicalization matching the kernel; direct calls of resolved callees, entry functions for the rest; dups, drops and fused releases as runtime calls. Every corpus row, fused and unfused, gives the interpreter's outcome with the machine's allocations, count writes, frees, peak and sharing per run (58 runs, 125 cells, 129/139 writes). Strings are ropes copied once at the end; `Lines` ports equal the interpreter's on all 19 531 strings up to length 6 over a five-symbol alphabet; object files are reproducible. Negative controls: a missed drop, a missing dup, a missing result dup and a borrowed argument to a consuming parameter each fail; mutants: skipping one drop per node fails the corpus test. |
| L1.37 | done | `zed_tests::oracle::{unit, program, native}`: each top-level binding with no function component (by the checker's type, `elab::Def::first_order`) and every table check, `main`'s waves included, run by the interpreter and by native code fused and unfused, outcomes compared as printed text; programs compared by the bytes of each port. Covers the L1 fences (6 comparisons), the step units (12), the enabled corpus programs (none at L1; each must also write its `.out`) and the four step programs on all 31 corpus inputs (248). Negative controls: an engine off by one on integers, one that drops a wave's writes and one that fails are each caught with both outcomes named; mutant: inline integer `+` emitted as `-` fails three of the four oracle tests. |
| L1.38 | done | `zedc::store::presburger::{satisfiable, project, entails}`: the Omega test (Pugh's equality reduction, real and dark shadows, splinters) on negation normal form split into conjunctions; `preimage::relations` states a kernel term over its inputs (`+ - neg`, constant products, `** 0..=2`, `div`/`mod` by a constant, `abs min max`, branches, comparisons, `! && ||`). Tests: rung 2 proves `y * w + x < h * w` from the bounds and refutes it from `y <= h` with countermodel `h = 0, w = 1, x = 0, y = 0`; `xs[i + 1]`'s bound refuted at `i = 0, n = 1`; the z3 fixture `x ∈ [0..=49]` exact; the relation `a + b + c <= 49` kept past the enumeration budget; 60 random terms checked point by point, by model, by projection and by entailment against the interpreter on `[-5..=5]²`; budgets (17 symbols, 65 constraints) dropped; controls for each check. |
| L1.39 | done | `zedc::store::product::{Product, Scope, arms, forward}`: the reduced product of the cell, the type and the binding time, with the scope's linear relation and written constraints; `Scope::reduce` in at most 16 rounds; enumeration within 4,096 members and 10,000 steps of fuel; `Scope::assume` narrows by a test's preimage, relation, congruence and literal equality. Tests: the design's arms (`n` in `1..=9`; an unreachable arm accepted; a static `if` read as static); negated equality by complement; a two-name relation; binding times; each reduction and budget alone; 300 random bodies checked against the interpreter at every point of a window, with a control that a wrong scope is caught. |
| M0.4 | done | `zed/corpus/`: 31 programs with inputs, outputs and Python reference scripts (`refcheck.sh`, run in CI). The layer checker is the spec's `tools/grammar/layer.py`; every label equals its enabled layer, and the four negative controls fail. Four ledger descriptions corrected in the spec (programs 6, 8, 13, 19) |
| M0.9 | done | `zed-kernel`: values, families, terms, exact float sum and canonical tree, big-step evaluator with a world of ports. Done ahead of M0.3–M0.8 because later steps test against it. Its decisions are the "Reference semantics" paragraph of DESIGN.md sec:kernel. Negative controls: disabling the exact sum fails 2 step tests; changing the tree split fails 2 unit tests |

## Decisions made

- Toolchain: Fedora's rustc and cargo 1.99.1, edition 2024. CI uses the stable toolchain.
- Cargo's target directory is `build/cargo`, set in `.cargo/config.toml`.
- Language tests: `tests/steps/<step>/`, all in one test binary. Unit tests of internal
  functions: `#[cfg(test)]` beside the code.
- Fences: CI must not read the spec repository (the author's instruction, 2026-10-29).
  `zed/fences/sync.py`, run by hand, copies the fences into `zed/fences/design.md` and
  `examples.md`, each under a header with its source line and layer; `sync.py --check` exits 1
  when a copy is stale, and the step test `the_copies_match_the_spec_where_it_is_present`
  compares the texts where `../zed` exists (it passes without checking in CI).
- The reference evaluator computes integers in `i64` and widens to a big integer instead of
  overflowing; a number past 2^20 bits is its `Overflow` error (L1.17). It has a fuel
  of 10^8 calls, at most 20 000 nested calls, and runs on its own thread with a 1 GiB stack.
- Coverage runs in CI (`cargo llvm-cov`, job `coverage`), not locally: this machine has no
  LLVM tools, and installing them is a system package change.
- Workspace lints: `missing_docs` warns, `unsafe_code` is forbidden. `zed-native` denies it
  instead and allows it at the two places that call and free JIT code; `zed-rt` needs none.

- No step waits for a person (the author's instruction, 2026-10-29; spec commit 827385b).
  M0(d) is now a prediction suite kept as tests, the M0(e) postmortems run alongside and gate
  nothing, and the corpus programs are corrected to fit the language rather than the reverse.
  When the spec is unclear, I choose, record the choice in DESIGN.md and here, and continue.

- Budgets (M0.10, in `zed_kernel::budgets`): enumeration of at most 4,096 bindings per
  obligation; rung 6 cuts integers to `-8..=8`, sequences to length 4, loops to 16
  generations, floats to 0.0, -0.0, 1.0, 0.1, 0.2, 0.3, ±inf and NaN, and runs at most 65,536
  bindings in shortlex order; rung 3 saturates for at most 8 iterations or 10,000 e-nodes.
- M0.5 values (DESIGN.md M0.5): piece limit 8; widening delay 3; 64 head updates per
  stabilization, then the component goes to ⊤; 64 narrowing rounds; finite sets widen to ⊤
  past 64 members; Presburger relations of at most 16 variables and 64 atoms, eliminations of at
  most 4,096 atoms. Rule 1 of sec:constraints now says phase 1 is Bourdoncle's recursive
  strategy and only phase 2 runs in rounds; the sec:domains example is the tested three-cell
  loop. `flat(elems, top:)` is defined there (bottom `#empty`).
- M0.6 (DESIGN.md M0.6): the scalar sums devices as if run in sequence, an upper bound on
  the running time; L24 may refine the estimate but must keep it monotone in the frontier's
  quantities. The frontier is per device, because the scalar is not monotone in plan totals
  (work moved to a slower device costs more).
- M0.7 (DESIGN.md M0.7): the canonicalizer runs over kernel terms now and moves onto ZIR at
  L1.32. A canonical binder name is NUL then its level, which no source name can contain. The
  definition's own name, port names, atom names and catalog witnesses are part of the
  interface and so of the address. Renaming one binder per pass is O(n²) in the binders;
  L1.32 may do it in one pass if it gives the same normal form.
- M0.11 (DESIGN.md M0.11): an axiom is per arrow; a law every arrow of a name must have is
  listed at each kernel carrier. `+` at `f64` has identity -0.0, not 0.0. `min` and `max`
  have no identity. A unit has no version number: its address covers its exported
  declarations only, so its path and unused local declarations do not change it. The
  reference evaluator sets no memory limit; a step is a call, a `fix` round or a `gen` step.
  The old comment on `DEFAULT_FUEL` cited a 10^8-step budget in sec:verification that the spec
  does not state; it now says the fuel is ten times `MIN_STEPS`.
- L1.1 (DESIGN.md sec:lexical): a leading byte order mark is rejected, like a file not in NFC;
  a lone `\r` is a line break. A U+FEFF after the start is the lexer's to reject. Dependency:
  `unicode-normalization`.
- L1.2 (DESIGN.md sec:lexical): mixed script is the complement of UTS #39 Highly Restrictive,
  so Greek with Latin (`ΔT`) is rejected. Dependencies: `unicode-ident`, `unicode-script`.
- L1.3: an integer token keeps its base and digits, not a value; `0755` is decimal, as the
  grammar reads it.
- L1.4: a float or rational token keeps its decimal text, not a value, so `1e400` lexes and its
  range is checked where its type is known; `0x10r` is rejected because `Rational` takes only
  decimal digits.
- L1.5: `"""` stripping applies only when both delimiters are on their own lines (DESIGN,
  sec:lexical, string row); a `"` string has no line break, its holes included, and a `//`
  comment in such a hole is its own error. An empty string is `Str([])`.
- L1.6: doc comments are kept outside the token stream, since the grammar discards every
  comment; the parser attaches them by span.
- L1.7: a fence's `// layer Lk` label may be on any whole comment line, since a fence's first
  line is usually its `// [d4]` header; the spec's `layer.label_of` reads only a program's first
  line, which gave EXAMPLES.md:432 layer L1 under its `// layer L2`. `sync.py` reads every line.
- L1.7: where a variant replaces a line instead of adding one (the loop variants of the fence
  at DESIGN.md:2420, a second `q =` or `rows =`), its fixture replaces that line, so the fixture has one
  error. The two column variants of the `orders` store edit its field type and put the ✗ there.
- L1.7: `…` is the name `…` (sec:grammar, "Documentation notation"); Part G said "a hole, not a
  token", now aligned to sec:grammar in DESIGN.md.
- L1.8: the parser runs the copied grammar instead of a hand-written precedence climber, so
  its trees are `check.py`'s by construction and the grammar cannot drift from the spec
  unnoticed (DESIGN.md L1.8 now says so). It parses every form of every layer at L1; steps
  L1.9–L1.12 add the elaboration of their forms, and the elaborator rejects a node whose
  alternative's layer (`Tree::layer`) is above the program's.
- L1.8: a variant of a documentation-notation fence is parsed as a `DocFence`, as its fence
  is (`exec : … -> Rows | #sqlError` is a signature without its `;`).
- L1.9: the expression syntax tree is built from the parse tree after parsing, not by the
  parser, which only records rule, alternative and tokens. Each later step adds its forms to
  `zedc::ast`, and the fence test's counts of built and later chains move with them. `**` is
  built here with the other operators of the L1.8 ladder, ahead of its L1.10 listing. The
  uniform call stays a call of a member until resolution (L1.14, L1.16).
- L1.10: the type expressions are built here, ahead of their L1.12 listing, since `is T` and a
  lambda's `x: T` are written with them; L1.12 still adds the declarations that use them. A
  destructuring parameter `((s, c)) -> …` and patterns other than atom patterns are L2.
- L1.11: a block in expression position must export; a declaration's body block need not
  (`Counter.tick() { n' = n + 1; }`), and L1.12 builds those. Statement order has no
  meaning, so a `return` may precede a binding. A name bound twice in one block is left to
  name resolution (L1.14).
- L1.12: a unit's top level holds declarations and pushes, not an export, so `return` there
  is an error. A function's several `test` tables are one list of cases in written order.
  The result form `f(x) -> T = …` is L10 by the grammar and is not built at L1.
- L1.13: the formatter's layout is not given in full by DESIGN.md, so these choices are
  recorded there: two-space indentation; no line breaking by width (a known limit, revisit
  when the corpus has long lines); a block on one line only when it holds just a one-line
  export and no comment; a function body always on several lines; several `test` tables
  joined into one; a comment inside a statement but outside its blocks moved to the end of
  the statement. A block that is an operand opens with a statement at L1, so its export is
  written `return e;`. The builder stores a block's export last, so "the same AST" holds
  exactly.
- L1.14: where DESIGN.md is silent, recorded there: a function's or lambda's parameters and
  output ports share one scope with its body block's statements; a parameter's type and
  default see the parameters but not the body; `test` cases are read around the function;
  an `else` pattern's `f:` fields are in scope in its default only; functions of one name
  whose written parameter types differ form an overload set; a member `x.f` is recorded only
  when `f` is bound in the unit (fields are told apart at L1.16); the L1 prelude words are the
  numeric casts and `abs`, `len`, `lower`, `upper`, `trim`, `sum` (`count` takes a family, so
  L3); the L1 type names are `int`, `rat`, `f64`, `bool`, `String`, `Lines`, `Files`.
- L1.15: the kernel already had all seven generators (M0.9); "whole" adds the `ev` of
  `fold(F, op, ev)` and `fix(F0, step, ev)`. The record maps a property name to a grade; a
  property absent is Unknown, and a derived property is stored at the meet of its premises'
  grades (the rule and premises are the property tracker's), so the tags are Axiom,
  CheckedExhaustive, Proved, Bounded, Obligated, Assumed, and only the first three are proof
  grade. The record is part of the term, so it is serialized into the address, and VERSION is
  now 2. The printer's notation: binary primitives infix and always parenthesized, other
  primitives as functions, a generator's named parts as `depth: 2`, `witness: residue`,
  `join: union`, `guard: before`, `definedness`, the record as `ev: { associative: axiom }`;
  ports as `port.read(stdin)` and `port.push(stdout, e)`. A term that does not fit puts each
  part of its outermost list on its own line, two spaces in, and an `if` breaks both branches
  together.
- L1.16: `++` is its own kernel primitive `Concat`, not `Add`, since `+` and `++` are distinct
  operators with different laws (DESIGN.md, Property tracking); `**` is `Pow`. Every binder
  gets a kernel name unique in the unit: its own name, or `name@k` when another binder shares
  the name or the name is a prelude word (so the word stays a free variable for the
  interpreter, L1.18); temporaries are `$k`. Because names are unique, a default is filled by
  let-binding the call's arguments under the parameters' names and then the defaults in their
  own dependency order, with no capture. Statements of a scope are ordered by their uses; a
  cycle, self-reference included, is an error that names layer L6 (recursion). `e else d` and
  `x?.f` match any atom (`AnyAtom`, `#_`), exact while atoms are loose (before L2). A call
  through a value (lambda, prelude word) passes arguments by position only; named arguments
  there wait for types (L1.26). `test` tables belong to top-level functions; a key is the
  argument, or the tuple of all arguments in declaration order. Deferred as errors: rationals,
  integers beyond 64 bits and named atom payloads (L1.17), `is` (L1.22), lambda defaults
  (L1.26), overloads and fields (L2).
  Self-reference resolves to itself; cycles are a later step's.
- L1.17: the spec said both IEEE `==` (sec:numeric) and "`==` reflexive at f64, bitwise"
  (M0.11); IEEE wins for the language's `==` and the comparisons, and bitwise identity stays
  for keys and law checks (Rust `Eq` on `Value`). M0.11 and the axioms are corrected. `==`
  compares atoms instead of passing them through, since it has an arrow at every type; the
  m0.10 helpers that used `x == x` to pass a failure now match `#_`. Comparing numbers of two
  kinds, or `1r + 1`, is a type error; `1 == 1.0` is false. A payload is all by position or
  all by name; field order is not part of the value. `==` on functions is a type error naming
  L1.22. The size limit is 2^20 bits; a rat literal past it is an elaboration error.
- L1.18: several failing operands now merge into `#errs` of the set of them, replacing M0.9's
  "leftmost atom wins" (DESIGN.md M0.9 (a) is corrected), so `#a + #b` and `#b + #a` agree.
  The set is a family mapping each failure to itself. Origin sets wait for origin tokens
  (L1.20). Cast grammars: `int` reads `-?digits`; `rat` reads `3r`, `-1r/3r`, `2/4` or
  `0.25`; `f64` reads `-?` then `inf`, `nan` or `digits[.digits][e-?digits]`, and a finite
  text past the float range is `#inexact`. `+5`, `.5` and `infinity` are `#invalid`.
  `upper` uses full case mapping (`"straße"` to `"STRASSE"`). Fixed notation up to 10^21
  means `1e16` prints as `10000000000000000.0`.
- L1.19: read failures are the bare `#ioError` the types write (`Files = Path ->? String |
  #ioError`, `LineNo -> String | #ioError`), since payload patterns arrive at L2; only the
  write acknowledgment carries `#ioError(why)`, and the program never sees it. A port pushed
  twice is caught at run time, not statically, because two push sites on two branches are
  legal. Elaboration turns `v[k]` into `tupleGet` for a literal key and an application
  otherwise, so until L1.22 the evaluator reads a family or a lookup port either way.
  Files are written through `Lines` ports bound to paths (`out=path`); a `Files` output
  waits for families (L3).
- L1.20: a non-recursive call is named by its call site in the static half of the address
  (the spec's list of region instances leaves calls out); recursion is keyed by entry key
  at L6. A region's operator calls are aimed at the operand's position, so two operators of
  one region differ though their keypaths match. A primitive a region calls is no fact.
  Recording is opt-in and does not change the value; retention policy arrives with
  sec:security's lineage sampling.
- L1.21: the spec left the program test form to this step; it is a table on `main` (a
  `Files` port given as a lambda, since a family display is L3) and the `// ✗` marks, the
  convention the documentation's fences already use. Only the first rejecting phase reports,
  so marks in a later phase go unchecked; an aborting wave fails its row. The spec's command
  is `zed test`; the binary is `zedc`, as for `run`.
- L1.22: the tuple and morphism parts are not reduced to a canonical form, so equal sets can
  print differently; type equality is subtyping both ways (L1.23). `is` can tell a function
  from other values and nothing finer until families carry their types (L3). A keypath is a
  tuple, a family a morphism; `() -> V` is keyed by the empty tuple; `->?` is partial at
  each level. `Lines` and `Files` are port types only.
- L1.23: a clause of morphism types is decided one negated type at a time, so it is sound
  and incomplete when several negated types together cover the positive part. A value type
  with a parameter under a complement or right of `\` counts as possibly empty (monotonicity).
  All members of a group take the same parameters. Tuple components that mention the group
  stay lazy nodes, so building a recursive type never unfolds it. The memo is per thread and
  never cleared. `Env` and its members form a reference cycle that leaks, once per instance.
  Recursive types are kernel `Group`s here; `type` declarations map onto them at L2.
- L1.24: the spec's "symbolic affine bounds" are given a numeric floor, since the join of
  `[0]` and `[1..=n]` is `[0..=max(0, n)]` and not `[0..=n]`; without it every counting loop
  loses its bound. Ends stay 64-bit and saturate outward. A symbol is named by its source text
  and its range is not known to the domain (so `a::len >= 0` is not used); the reduction with
  the other domains, which would supply it, is L1.39. Bounds with different terms are not
  compared, so `int[0..=n]` and `int[0..=n + m]` are both kept by a meet. The finite-set domain
  holds kernel values; strings' lengths are counted in characters (code points after NFC).
- L1.25: a preimage is a box; a relation among inputs is projected and marked necessary until
  L1.38. `x * x <= 99` reaches `[-9..=9]` through the power reading, exact, rather than by the
  enumeration the plan names. Because `==` and `!=` compare failures as data, a comparison whose
  operands may fail keeps its box unless the other side is a constant integer; the kernel's own
  `&&` and `||` pass failures through, so their union is exact only when neither side can fail
  (the surface `&&` elaborates to a branch). There is no hash primitive in the kernel, so the
  stops are string operations, foreign names and terms outside the scalar catalog. Congruences
  for `mod` over unbounded operands are L1.39.
- L1.26: undeclared parameters are typed by search (type variables, then carriers for one
  parameter, then two, …, in the order int, f64, rat, String, bool); the arrows kept share the
  fewest literal adoptions, since a body elaborates once, so `f(x) = x * 2` is `(x: int) ->
  int` only. A float literal never adopts int. A type variable used as a tuple or a function
  gives `_` (`first(p) = p[0]` is `(p: T) -> _`). Atoms pass through operators but not into
  declared functions or lambdas. A divisor whose type holds no zero adds no `#divByZero`. The
  first arrow that fits a combination gives its result. Caps: 20000 body checks per function,
  256 argument combinations per call, each giving `_` past it.
- L1.27: L1 has no `type` declaration, so every atom an L1 program meets is loose, and
  run-time `else` defaults every atom; step L2.1 must set the family marking from `type` and
  make elaboration keep the atoms the checker protected (an arm before `#_`). A pattern with a
  payload keeps its atom in the type.
- L1.28: a local binding counts as demanded when its body names it, even in a branch cut
  later. `Program::stage` is not yet used by the `zed` command; the residual program is used
  by lowering (L1.33). The `left` entries of `stage::Report` carry the term and the stop;
  L1.29 turns them into derivations (DESIGN.md sec:diagnostics now requires every rejection
  to show the full derivation: each constraint, its site, and the path it took).
- L1.29: no ✗ variant in `zed/fences/variants` reaches its documented error at L1: four
  stop at an L2 declaration, three fail to parse at L1, two use `…`, and the two that pass
  the mark check pass for other reasons (`Point` undefined; a parse error on the marked line). The test pins what
  each gives; the step that enables a variant must change its pin to the documented error.
  The staging report (`stage::Report.left`) is not a rejection and gives each left term its
  reason without a derivation. A first exclusion of "stale" search records cut the chain of
  a top-level value read in a searched body; it was removed, since every run re-records each
  subexpression before deriving any error in it. A step of a block derives no further than
  the block (its export is not followed yet), and a literal binding shows as "this
  expression is 4" rather than as a literal.
- L1.30: keys are syntactic (the `Debug` print of kernel terms), so an alpha-renaming or a
  renumbered `name@k` binder reruns a row that a canonical key would reuse. Kernel names are
  numbered per source name in binder order, so adding a same-named binder before another
  renames it and reruns the rows that reach it. Results are never evicted. `zedc run`
  compiles its one unit once, so it calls `run::compile` directly. Found on the way:
  `zedc test` printed a rejection's message without its derivation; fixed.
- L1.31 (DESIGN.md L1.31): regions are isolated; a value from outside enters as a capture,
  an input after the node's fixed ones received as a trailing argument. State edges are linear
  and enter only match and port regions. A certificate region holds only kernel nodes. The
  validator checks structure only; edge-type fit is the checker's, for the term lowered from.
  The text form starts `zir 1`, one line per header, node and results, keyed by path, read
  back in any order; a literal pattern is `=v`; a recursive type has no text form until L2.
  The binary form starts `ZIR\0` and the version, stores edges as their text, floats by their
  bits. Errors give line and column, or byte offset.
- L1.32 (DESIGN.md L1.32): on ZIR the binder rule renames match-pattern binders to their
  index in the pattern, the written name a hint on the argument edge; the other rules run per
  value edge in preorder. The address hashes `zed-zir\0`, the M0.7 version and the binary
  form of the normal form (a level name begins with NUL, which the text form cannot read).
- The two zeros (DESIGN sec:type_resolution, "Equality and order corner rules"): `==` and the orders read `0.0 == -0.0`, and a tuple compares component by component in IEEE order (`Value::surface_cmp`); key formation and lookup turn `-0.0` into `0.0` at any depth (`Value::key`), which the kernel had not done before. Identity keeps them apart: kernel `Eq` on values, laws, and the content address, which hashes a float by its bits and every NaN as `0x7ff8000000000000`. Tests: `m0_11_prelude_axioms_and_limits/signed_zero.rs` and the kernel test `the_two_zeros_are_one_key`.
- L1.33 (DESIGN.md L1.33): a primitive used as a value lowers to a `prim` node with no
  inputs, not to a lambda, since the kernel tells them apart; a variadic primitive has no such
  form. Captures and state edges are taken on demand; a function that uses a port is inlined
  at each call. CSE keys a node by the address of a one-node region; a node with a state input
  never repeats one, so effects are never merged. Edges carry `_` until code generation.
- L1.34 (DESIGN.md L1.34): a constant is static and never counted; integers, floats, booleans,
  the empty tuple and bare atoms are unboxed. A call to a callee the plan cannot see passes
  owned. Loop and family regions run in the kernel, which borrows their inputs; a family's
  entries are kernel data until L3.17. Scalar, family and port nodes take their value from the
  kernel, which runs each node alone; tuples, closures, calls, branches and matches run in the
  checking machine, so it keeps the program's sharing.
- L1.35 (DESIGN.md L1.35): MLIR is reached through its text form and `mlir-opt`/`mlir-translate`,
  so no C++ build enters the tree; the C API is adopted only if compile time measured at L28
  shows the process boundary matters. MLIR's bufferization and ownership-based deallocation
  are not used for Zed values; the L1.34 plan is applied before the lowering.
- L1.36 (DESIGN.md L1.36): a value is a word of a tag and a payload, returned in two
  registers. Arms are inline; a lambda body is a function, with an entry function taking every
  argument owned for calls the plan cannot resolve. Nodes outside the inline tier are run by
  the runtime through the kernel, so the native and machine counts agree one for one; the
  runtime's state is thread-local, and a hook never calls generated code. A match that native
  pattern matching does not decide is decided by the kernel, and the two must agree. The
  object file is checked for reproducibility and its symbols; linking it into an executable
  comes with `zed build`. The workspace's `unsafe_code` lint is relaxed only in `zed-native`.
- L1.37 (DESIGN.md L1.37): the checker records each top-level `=` binding's type, and
  `elab::Def::first_order` says whether it has no function component. A binding typed `_`, as
  a higher-order call's result is at L1, is compared too, since both engines refuse a function
  result with the same error. Outcomes are compared as text: the printed value or the error,
  and for a wave each port's bytes. A `Files` port in the harness holds the input text at every
  path. `oracle::ENABLED` is the enabled layer and rises with each layer; the corpus joins at
  L3. The reorder-facet rule (a float compared by its type and keys) is due at L9.
- L1.38 (DESIGN.md L1.38): 128-bit arithmetic, an overflow counted as past the M0.5 budget;
  the 4,096 bound also caps conjunctions and splinters; a projection is each conjunction's
  bounds, unioned; a product atom's countermodel is checked against the real product, and a
  point where it fails is "not proved". `Preimage::relation` is kept only on a result that is
  not exact. The congruence `x mod 7 != 3` is left to the enumeration until L1.39.
- L1.39 (DESIGN.md L1.39): reductions at most 16 rounds; a type widens to its whole base
  type; enumeration fuel 10,000 steps per evaluation (`zed_kernel::budgets::ENUMERATION_FUEL`),
  out of fuel removes nothing; enumerations remembered per constraint and static values; a
  false static constraint gives bottom; a test's linear relation is kept only when it needs no
  auxiliary variable; the walk to the arms skips tests, function bodies and patterns;
  `zed_kernel::on_stack` and `Evaluator::run_on` let many evaluations share one thread. The
  `isPrime` example waits for L3. The preimage transfer remembers each (term, scope) result
  and stops after `preimage::TRANSFER_FUEL` (100,000) terms with `StopKind::Budget`.
- Checker performance (L1.38): the elaboration retried each carrier combination with full
  derivations, so a sum of five inputs took 23.7 s; the trial runs are now quiet and only a
  shown failure is re-run with its derivation (3.7 s; the step tests 55 s → 45 s; snapshots
  unchanged).
- Known limits of the M0.5 store: the order and the stabilization recurse as deep as the graph
  (revisit at L1.24, where real programs give large graphs); `End::from_i128` saturates at the
  64-bit limits, which the evaluator's integers now pass (L1.17): revisit with the store's
  big-integer bounds at L1.24.
- The kernel `fold` term carries the depth of the folded family (M0.10). The evaluator cannot
  read the depth off a family with no leaves, so without it `fold` of an empty two-level
  family gave `#empty` where its type gives the empty family, and laws 4 and 8 failed on the
  empty input. Typing supplies the depth; a leaf at another depth is the mixed-depth error.
- Kernel values are normalized: a key over an empty level is dropped, so the nonempty-level
  conditions of laws 1, 2 and 7 have no counterexample among values. They constrain the
  guaranteed domains, and are checked where `card` facts are (L1.24, L3.6).
- The size limit on numbers, like fuel and nesting depth, is a limit of the reference
  evaluator and not a meaning (spec reference semantics (i), commit after a1ed53b). Law 11
  deletes a dead binding whose computation would pass a limit; that is not a counterexample,
  and the laws are checked on instances the evaluator can run.
- The harness compares outcomes as values (floats bitwise after NaN canonicalization) or as
  errors of one kind, since two sides that both collide may name different keypaths.

## In progress

- A full read of DESIGN.md by six agents, one line range each, listing what would otherwise need
  the author's input. Each item is to be resolved in the spec before the step it affects.
- Postmortems of related languages, written to the session scratchpad. Their lessons may amend
  the spec.

## Open points

- Corpus outputs that rest on rules the spec has not fixed yet; each is a choice stated in
  the program's `ref/NN.py`, to be revisited at the step that fixes the rule: the `.window`
  signature and late-drop rule (programs 17, 18, 29; step L7.5), where a parse error is
  reported (7, 30), `serialize` writing no whitespace, `++` on int-keyed sets reading in key
  order, `zip` keeping the overlap of two rank ranges (25), stdin keyed by rank from 0.
  The programs are only parsed and layer-checked so far, not type-checked or run.
- Programs 14 and 15 are labeled L7 for incremental reuse (L7.6), though their syntax only
  reaches L6.

- Apply the batch of resolutions from the six-part read of DESIGN.md (scan files in the
  session scratchpad), prose and grammar together, before the steps they affect.

## Postmortem amendments (spec commit after 678e2d1)

The postmortem of related languages (array, dataflow, Datalog and incremental languages; report kept outside the repo) proposed nine amendments. Applied to DESIGN.md:
- A3: `@export("c", "symbol")` lets C call pure Zed functions (sec:ffi; tested in L7.4).
- A1: `zed build --explain-plan` (L5.10).
- A2: a lowering stays within a constant factor of `f::cost`; `@cost(depth: …)`.
- A6: recompute or incremental is chosen per wave by cost; the L7 gate adds a 50%-dirty check.
- A7: the L5 ratios are one core against one core, and efficiency is measured against the Rust baseline. L5.14 now agrees with the gate table.

Not applied:
- A4 (name a first domain): a product decision with no effect on what is built.
- A5 (license): the repo already has LICENSE; the choice belongs to the owner.
- A8 (two-process test at L7): distribution is post-v1 in sec:targets.
- A9 (count programs needing generations): no decision depends on the count.

## M0.3 — desugaring rules (done, in the spec)

The spec's sec:grammar now has a `desugar` fence with one rule per syntactic production (107), and the spec repo's `tools/grammar/check.py` checks that rules and productions match one to one. A negative control (an extra rule and a duplicate) is caught. Nothing in this repo changes until the L1 elaborator, which implements these rules. Decisions:
- `&&` and `||` desugar to `if`, not to the strict primitives; the spec calls them selection nodes that short-circuit observationally.
- Recursion enters at L6. A recursive function is the definedness fix over its parameter domain, evaluated on demand. The M0.9 evaluator computes that fix over a finite domain only; the L1/L6 interpreter evaluates on demand.
- Kernel primitives the rules name that the M0.9 kernel lacks: `pow` (L1), `range` (L3), and the type test `is` (L1). They are added at those steps.
- `break e`: the step's guard returns `#break(e)` and the loop's result is `e`.
