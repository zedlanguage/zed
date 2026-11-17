# STUDY-pattern-forms: which built values can be matched

Study by agent pattern-forms, 2026-11-17, plan row STUDY-pattern-forms, from the author's answer to
QUESTIONS C3 (P346): "survey every form in sec:grammar that builds a value, a type or a data
relationship … and list each one that can be written to construct something but cannot be
matched; for each, score the value of a pattern form". The spec side of the same answer
(or-patterns, step L2.7b) is zed commit "DESIGN L2.7b: or-patterns …" (row SPEC-orpat-answer).

The brief named `studies/PATTERN-FORMS.md` in the zed repository "or the directory where other
studies live". zed has no `studies/` directory; zed-impl keeps its studies as `docs/*-study.md`
(`ladder-study.md`, `joined-strings-study.md`), so this file is here.

## Result

No missing form scores 9 or 10, so nothing new goes into DESIGN from this study beyond the
or-patterns of step L2.7b. Four forms score between 3 and 8 and go to the author as QUESTIONS
A131 to A134, one decision each, with rows SPEC-pat-list, SPEC-pat-string-prefix,
SPEC-pat-record and SPEC-pat-map-key. Every other form is decided by a standing rule or is
already matchable; the tables below give the rule.

## Method

1. Read every rule of sec:grammar's PEG (sec:grammar of DESIGN.md at zed 8ee6d35) that
   builds a value or a type: `Literal`, `ArrayExpr`, `TupleExpr`, `Display` (records, families,
   sets), `Range`, `BinOp` `++`, atoms with payloads, struct construction, `Lambda`, `for`/`loop`
   generations, keypaths, `with units(…)`, `grammar` blocks, and the type formers.
2. Read the `Pattern` rule and step L2.7b to list what a pattern can match today.
3. Counted uses in the port of the Rust compiler to Zed (`ZED_PORT_GAPS.md`) and in zed-impl's
   own Rust (`command grep -a -c` over `crates/`).
4. Read what Rust, Elixir and Erlang do (sources recorded in zed's `verification/bib.md`, section
   "Or-patterns and their checking"), and named the pitfalls of each.
5. Worked out the cost of each form to exhaustiveness checking (the residue method of step L2.7b:
   `R_i = R_{i-1} & !⟦p_i⟧`, one emptiness query per arm).
6. Scored each form 0 to 10. Explicit-no-surprises is inviolable: a form whose meaning a reader
   could guess wrong scores 0 to 2. An O(n²) cost needs the author's approval, so a form whose
   only known check is quadratic cannot score 9 or 10 here.

## What can be matched today

| Built by | Example | Pattern | Exhaustiveness |
|---|---|---|---|
| Literals | `0`, `-1.5`, `"x"`, `true` | `SignedLit` | Finite for `bool`; for numbers and strings only with `_` or a name |
| Ranges of numbers (as a set of values) | `0..=9` | `(0..=9)` (L2.7b) | Interval arithmetic |
| Atoms and their payloads | `#ok(v)`, `#err(e: m)` | `#ok(v)`, `#err(e:)`, `#digit(0..=9)` is `#digit((0..=9))` | Finite atom set |
| Tuples | `(a, b)` | `(x, _)` | Product of columns |
| Named structs | `Point(x: 1, y: 2)` | `Point(x:, y: 0)`; fields left out match anything | Product of named fields |
| Unions and other types | `x: int \| Utf8String` | `(n is int)` | Type difference |
| Alternatives | | `(#red \| #green)` (L2.7b) | At most m + 2A queries |

## Forms that build a value but cannot be matched

| Form | Example | Evidence | Cost to exhaustiveness checking | Score | Reasoning |
|---|---|---|---|---|---|
| List pattern with fixed length and a rest | `[]`, `[a, b]`, `[first, ..rest]` | Port: 43 slice patterns in ZED_PORT_GAPS.md, and several of its rows already propose `[a, b]` forms that do not exist. Rust: slice patterns with `..` (Reference, "Slice patterns"); Elixir and Erlang `[h \| t]`; Haskell, OCaml `x :: xs`. Pitfall: in Rust a slice of unknown length needs a wildcard arm, and `[1.., _]` is invalid because a range inside a slice is ambiguous; in Zed the ranges already stand in parentheses (L2.7b), so `[(1..), _]` is unambiguous. | The length becomes a column. The known method (rustc's length splitting, inferred from the Reference's examples, not read in rustc's source) checks one length class per distinct written length plus one class for longer lists: O(L · n) work for L distinct lengths in n tokens of patterns, which is O(n²) in the worst case. With prefixes and a rest only (no `[.., last]`), the classes can share one residue that shrinks as the length grows; that it then stays near linear is not proved. | 8 | High value, real port demand, a written form that mirrors `ArrayExpr`; held below 9 only by the quadratic worst case, which the author must approve or a better method must remove (A131). |
| String prefix | `("GET " ++ path)` | zed-impl's Rust: 94 `strip_prefix(`, 178 `starts_with(`, 48 `strip_suffix(`. Elixir: `"foo" <> x` in a pattern "as long as the left argument is a literal binary"; `x <> "bar"` raises ArgumentError. Erlang binaries: a segment matches one byte unless sized, so `<<x, rest/binary>>` on "über" binds a byte, not a character (Elixir guide). | A trie of the written prefixes: an arm is unreachable when an earlier arm's prefix is a prefix of its own, found in O(total prefix length). No arm list is exhaustive without `_` or `("" ++ s)`. Linear. | 6 | Common need, cheap check. But it adds a second meaning to `++` inside patterns, and a prefix can end before a combining mark (`("e" ++ rest)` on `"e\u{301}x"` leaves `rest` starting with U+0301 COMBINING ACUTE ACCENT; NFC is a rule about source files, never applied to run-time strings, sec:order), a surprise unless the match is on grapheme boundaries. Today `s.take(4) == "GET "` and `s.drop(4)` do the job with the length written by hand; DESIGN has no `stripPrefix`, and a library function `stripPrefix(s, "GET ")` giving `Utf8String | #noPrefix` would make it one `match` with no new pattern (A132). |
| String suffix and templates | `(name ++ ".zed")`, `("a" ++ x ++ "b" ++ y)` | Scala's string interpolation patterns (inferred: `case s"$a-$b"` takes the shortest match, which surprises readers). | Suffix alone: as the prefix trie, reversed. Templates with two holes: several splits match, so a rule must pick one. | 2 | A template with two holes has several splits; any rule that picks one is a surprise (no-surprises). A suffix alone is an option inside A132. |
| Anonymous record | `{x: 1, y: 2}` | No port uses: the port writes named structs. TypeScript and OCaml destructure records; OCaml's warning 9 fires when a record pattern leaves fields out (inferred). | Same as a named struct's fields: O(fields). A record type is open (width subtyping, sec:types), so `{x: p}` matches any value with at least an `x`, as `(r is {x: int})` does now. | 5 | Symmetry with `Display` and `CtorPat`; little demand; the open reading must be stated (A133). |
| Family or map entry | `{"a" -> v}` | Elixir: "a map matches as long as the keys in the pattern exist in the given map … an empty map matches all maps" (guide, "Keywords and maps"). | One key: a membership test, O(keys written). | 3 | `{}` matching every map is the Elixir surprise; reading `m["a"]` and matching its `#notFound` already does it with no new form (A134). |
| Range as a value (its ends) | `r = 2..<5`, match its `lo` and `hi` | None found. | A struct-like product. | 2 | `(2..<5)` already means "a number in the range"; a second meaning for the same written form is a surprise. Read `r.lo`. |
| General concatenation of lists | `(xs ++ ys)` | None found; Haskell and OCaml have no such pattern. | Every split matches: the pattern is ambiguous. | 1 | Ambiguous meaning; surprise. |
| Sets | `{1, 2}`, `({x} ++ rest)` | None found. | The element bound by a set pattern is not determined: any element could be chosen. | 1 | Nondeterministic binding breaks deterministic checking and no-surprises. |
| Keypaths in `match` | `(a.b -> c)` | None. | | 1 | Value patterns and keypath patterns never mix (standing rule). |
| Units | a value `with units("m")` | None. | | 2 | A unit is part of the type; `(x is f64 with units("m"))` already tests it where a test is meaningful. |
| `for`/`loop` generations and streams | a pattern on a generation's frames | None. | Unbounded. | 1 | A generation is not a finished value; matching it would force or run it, and the checker never runs code. |
| Value patterns in `for` binders | `for (a, b) in pairs` | Rust allows it (inferred). | Must be irrefutable. | 2 | `InPattern` binders are names by design; destructuring is one `match` or `.0` away. Not worth a second pattern position. |
| View patterns, active patterns, extractors | Haskell `(f -> p)`, F# active patterns, Scala `unapply`, Swift `~=` | Scala's `unapply` and Swift's `~=` run user code during the match (inferred from their documentation as known; not fetched). | Exhaustiveness becomes undecidable: the checker would have to know what user code returns. | 1 | The checker never runs user code; exhaustiveness lost. |
| `name @ pat` | Rust `n @ 1..=9` | Port: 10 uses. | None. | 0 | The author ruled it out in P346. `(n is int[1..=9])` binds and tests at once. |
| Functions | `x -> x + 1` | None. | Equality of functions is undecidable. | 0 | Not matchable in any language listed. |

## Per-language pitfalls the scores avoid

- **Rust.** A slice of unknown length needs a wildcard arm; a range without both ends inside a
  slice pattern must be parenthesized ("Slice patterns", Rust Reference). Zed's parentheses rule
  of L2.7b already covers the second.
- **Elixir.** `%{}` matches every map; `<>` in a pattern needs a literal on the left, and a
  variable there raises at run time (Kernel docs), not at compile time.
- **Erlang and Elixir binaries.** A segment with no type matches one byte, so a multibyte
  character is split unless `::utf8` is written.
- **OCaml.** Warning 57: a guard on an or-pattern whose sides bind different parts (L2.7b
  rejects it with a witness instead of warning).
- **Haskell.** Incomplete patterns are a warning that is not on by default (inferred; GHC's
  `-Wincomplete-patterns` is part of `-Wall`). Zed rejects a non-exhaustive `match`.
- **Scala and Swift.** Extractors and `~=` run user code inside a match, so the compiler cannot
  check exhaustiveness.

## Evidence

Confirmed:
- The PEG rules quoted (sec:grammar of DESIGN.md at zed 8ee6d35; the copy `zed/grammar/syntax.peg` here is synced by row OR-PAT).
- Counts in zed-impl's Rust at base f4911fa37, by `command grep -a -c`: `strip_prefix(` 94,
  `starts_with(` 178, `strip_suffix(` 48, struct patterns with `..` 528.
- Port counts in `ZED_PORT_GAPS.md` at the same base: or-patterns 180, `@` 10, slice patterns 43.
- The Rust, Elixir and Erlang behavior above, read on 2026-11-17 and recorded in zed's
  `verification/bib.md`.

Inferred, and what would confirm it:
- rustc's length-class method and its cost: reading `rustc_pattern_analysis`'s slice
  constructor splitting.
- Scala's and Swift's extractor behavior, OCaml's warning 9 and Haskell's default warnings: their
  manuals, not fetched here.
- That list-pattern classes can share one shrinking residue in linear total work: a proof or a
  scaling test at n and 8n, which row SPEC-pat-list would require.
- The scores, which are mine and not a cross-review's.
