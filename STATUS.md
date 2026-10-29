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
- Next: L1.13.

## Test baseline

Last full run: `cargo test --workspace` gave 325 passed and 0 failed (21 unit tests of
`zed-kernel`, 10 of `zed-tests`, 22 of `zedc`, 272 step tests: 6 in `l01_01_source_loading`, 8 in `l01_02_lexer_names`, 5 in `l01_03_lexer_integers`, 5 in `l01_04_lexer_floats_and_rationals`, 10 in `l01_05_lexer_strings`, 10 in `l01_06_lexer_tokens`, 11 in `l01_07_fences`, 7 in `l01_08_parser`, 9 in `l01_09_postfix_chains`, 9 in `l01_10_lambdas_types_else_tuples`, 7 in `l01_11_statements`, 11 in `l01_12_declarations`, 3 in `m0_01_scaffolding`, 23 in
`m0_05_widening_and_iteration`, 8 in `m0_06_cost_scalarization`, 14 in
`m0_07_canonicalization`, 1 in `m0_08_zed0_checklist`, 32 in
`m0_09_kernel_evaluator`, 83 in `m0_10_finite_model_harness`, 10 in
`m0_11_prelude_axioms_and_limits`). `cargo fmt --all --check` and
`cargo clippy --workspace --all-targets -- -D warnings` are clean. The steps binary takes
about 27 s in a debug build, with `zed-kernel` built at opt-level 2.

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
- The reference evaluator uses `i64` with checked arithmetic (overflow is an error), a fuel
  of 10^8 calls, at most 20 000 nested calls, and runs on its own thread with a 1 GiB stack.
- Coverage runs in CI (`cargo llvm-cov`, job `coverage`), not locally: this machine has no
  LLVM tools, and installing them is a system package change.
- Workspace lints: `missing_docs` warns, `unsafe_code` is forbidden. `zed-rt` will need
  `unsafe` when native code arrives (L1.34 and L1.36), so it will relax that lint for itself.

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
- Known limits of the M0.5 store: the order and the stabilization recurse as deep as the graph
  (revisit at L1.24, where real programs give large graphs); `End::from_i128` saturates at the
  64-bit limits, which lie within the evaluator's own range limit.
- The kernel `fold` term carries the depth of the folded family (M0.10). The evaluator cannot
  read the depth off a family with no leaves, so without it `fold` of an empty two-level
  family gave `#empty` where its type gives the empty family, and laws 4 and 8 failed on the
  empty input. Typing supplies the depth; a leaf at another depth is the mixed-depth error.
- Kernel values are normalized: a key over an empty level is dropped, so the nonempty-level
  conditions of laws 1, 2 and 7 have no counterexample among values. They constrain the
  guaranteed domains, and are checked where `card` facts are (L1.24, L3.6).
- Integer overflow, like fuel and nesting depth, is a limit of the reference evaluator and not
  a meaning (spec reference semantics (i), commit after a1ed53b). Law 11 deletes a dead binding
  whose computation would overflow; that is not a counterexample, and the laws are checked on
  instances the evaluator can run.
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
