# Zed₀: the bootstrap subset (step M0.8)

Zed₀ is the part of the language the Rust-hosted compiler must run for the Zed compiler
(row S) to be written in Zed. **The layer that completes it is L6**, so row S follows L6, as
DESIGN.md already places it.

The checklist has two parts. Part A is audited mechanically against corpus program 31, the
typechecker shaped like the compiler. Part B lists what the compiler needs that program 31
does not use, each with the layer and the place in DESIGN.md that provides it. Step S.1
freezes this list against the compiler's design and inserts a step for each gap it finds.

## The audit

`cargo run -q -p zed-tools --bin audit -- ../../../zed ../corpus/31-typechecker.zed --checklist ZED0.md`
(run by hand, since CI does not read the spec repository, which must be beside this one;
last run at spec commit 3f442e8, exit status 0, 117 grammar alternatives and 13 words
needed, none missing). An alternative is needed when program 31's units stop parsing, or parse to a
different tree, without it, so the list is exact for the grammar of DESIGN.md sec:grammar.
`Rule#i` is alternative `i` (from 0) of the rule, in the grammar's order. The words are
those `layer -v` reports. The indices follow the grammar: after a grammar change, rerun
the audit and update the list.

Negative controls: with the entry for alternative 0 of Loop deleted from this file, the audit
exits 1 and names it; corpus program 17 (a stream program, label L7) audits to a word at L7,
above Zed₀.

## Part A: what program 31 needs

| Layer | Grammar alternatives | Defined words |
|---|---|---|
| L1 | `Additive#0` `Additive#1` `And#0` `And#1` `Args#0` `Arrow#3` `AtomExpr#0` `AtomPattern#0` `AtomType#0` `Binding#1` `Block#0` `Body#0` `Body#1` `CallSuffix#0` `Compare#0` `Decl#11` `Decl#14` `Decl#15` `ElseTail#1` `Equality#1` `Equality#2` `Expr#0` `Expr#2` `Expr12#0` `Expr12#1` `FieldPat#0` `Function#0` `Group#0` `If#0` `IndexSuffix#0` `IsTest#0` `Item#2` `Lambda#0` `Literal#0` `MemberSuffix#0` `Multiplicative#1` `Name#0` `NamedArg#0` `Or#0` `Or#1` `Param#0` `Params#0` `Path#1` `Pattern#1` `PlainArg#0` `PlainBinding#0` `Port#0` `Ports#0` `PosArg#1` `PosParam#1` `PositionalParam#0` `Postfix#0` `Postfix#1` `Power#1` `Prefix#1` `Primary#0` `Primary#1` `Primary#2` `Primary#5` `Primary#7` `Primary#13` `Push#1` `Range#1` `Reduce#1` `Relation#2` `Relation#3` `Relation#5` `Result#0` `Suffix#0` `Suffix#1` `Suffix#2` `Target#0` `Type#0` `TypeAnd#1` `TypeName#0` `TypeNot#1` `TypeOr#0` `TypeOr#1` `TypeParam#0` `TypePostfix#1` `TypePrimary#1` `TypePrimary#3` `TypeUnion#1` `Unit#0` `WholePush#0` | `String` |
| L2 | `Arm#0` `AtomApply#0` `Decl#2` `Decl#3` `Decl#4` `Field#1` `Import#0` `Match#0` `NamePat#0` `Pattern#2` `Pattern#7` `Primary#8` `Struct#0` `StructField#1` `TypeDecl#0` `TypePrimary#2` `WildPat#0` | — |
| L3 | `ArrayExpr#0` `Binder#0` `For#0` `Generator#0` `InPattern#0` `Primary#9` `Primary#11` `ReadSuffix#0` `Suffix#5` | `concat` `foldl` `map` `split` `where` |
| L4 | — | `#collision` `flatMap` `group` |
| L5 | — | `drop` `last` `rank` `take` |
| L6 | `Boundary#0` `BoundaryItem#0` `Decl#10` `Loop#0` `Primary#10` `Until#0` | — |

Program 31 also needs two things no parser sees: general recursion through named functions
(its evaluation of the recursive union `Expr`), which is the definedness `fix` of step L6.4,
and a recursive union type, whose recursion is checked at L6.4 and folded at L6.5.

## Part B: what the compiler needs beyond program 31

The audit of 2026-11-03 compared this list with `ZED_PORT_GAPS.md` and with the compiler's
Rust, and moved each need it found after Zed₀ to a step in L1–L6 or in row S before the
step that uses it.

| Need | Zed₀ feature | Layer | Where |
|---|---|---|---|
| read the source units | the `Files` port, `fs[path]`; an import names its unit's path, so no directory listing is needed | L1 | DESIGN.md "Ports are the only outside world", the words table |
| read the command line | the `CommandLine` input port: the arguments after `--`, keyed by position from 1 | L1 | step L1.19a |
| write an executable | `zedc build file -o out`, a deterministic link with the retained runtime | L1 | step L1.36a |
| lex by code point | the `String` functions, and `codePoint`, `scalar`, `utf8`, `fromUtf8` | L1 | step L1.39c |
| identifier and normalization tables | XID_Start, XID_Continue, the scripts and the NFC data as sorted range tables, each lookup O(log n) by `upTo` | L5 | step S.1c, with step L5.8a |
| content addresses (BLAKE3) | `bitAnd`, `bitOr`, `bitXor`, `shl` and the other bit words of step L1.39a, and `mod 2 ** 32` | L1 | step L1.39a; the `&` row of the glyph table |
| syntax trees, ZIR nodes | structs, unions of atoms with fields, `match` | L2 | sec:grammar |
| the types the checker's units share | `Ast` (the node kinds through L6), `Facet`, `Rejection`, `Interval`, `Congruence`, `Bound`, as plain types with no reads | L6 | step S.1b |
| search a family | `.any`, `.all`, `.find`, short-circuiting in key order | L3 | step L3.15a |
| symbol and bound tables | `group` with a `#collision` fold, `rekey` | L4 | as program 31 |
| deterministic output order | `sort`, `rank` | L5 | as program 31 |
| nearest key, priority queues | `m.upTo(k)` and `m.from(k)` on an ordered family, each O(log n) | L5 | step L5.8a |
| memoized parsing, worklists, inference, the ordered rewriter | indexed definitions `f[i] = e`, `loop` with `until`, the definedness `fix` | L6 | steps L6.1, L6.4 |
| folds over trees | `.fold` on a recursive union | L6 | step L6.5 |
| union-find, dense tables, keyed updates in O(1) | reuse in place at count 1: `with`, a one-key `patch`, a `map` over a dying family, a `match` arm rebuilding its node | L6 | step L6.13, with the report of copies of step L6.13b |
| hash-consing and the e-graph | the digest kept in each shared object and the `==` shortcut on it | L6 | step L6.13a; the e-graph itself is step S.3a |
| deep lists and trees | release by a work list, constant stack | L6 | step L6.13c |
| emitting code | the Cranelift port, a built-in output port the Rust-hosted compiler declares, as it declares `main`'s | L1 (port header) | step S.1a |

Not in Zed₀, with the reason:

- streams, `@foreign` and the incremental engine (L7): the compiler reads whole files, and
  reaches Cranelift through the built-in port of step S.1a, not through foreign signatures;
  the port-fed `Seq` of step L5.1c moved to step L7.2a for this reason;
- refinements, proofs and staging (L10 and above) and user facets (L12): the compiler's own
  checks run as ordinary code, so it needs none of them to be written; the checker it
  implements covers L1–L6 first (step S.3), and later layers add their procedures as prelude
  source (G10);
- a byte file port and output paths computed at run time (gaps 5 and 6 of `ZED_PORT_GAPS.md`):
  the compiler reads its sources as text, writes its outputs to the ports its command line
  binds, and needs bytes only as the UTF-8 of a string (step L1.39c).

## Gaps found

The audit of 2026-11-03 found these, each now a step before its first use:

- the command line (gap 6): step L1.19a;
- an executable (DESIGN.md step L1.36 notes): step L1.36a;
- code points and UTF-8 (gap 7): step L1.39c, and the Unicode tables, step S.1c;
- the quantifiers `.any`, `.all`, `.find` (gap 12, early exit): step L3.15a;
- key range queries (gap 9): step L5.8a;
- updates in place, digests, the report of copies and iterative release (gaps 1 and 11):
  steps L6.13 to L6.13c;
- the Cranelift port: step S.1a, before step S.4 uses it;
- the shared checker types, fixed through L6: step S.1b;
- stopping at a broken invariant (gap 8): step S.1d, which waits on the author's decision;
- prelude units slower than their stated cost: step S.1e;
- the file import cycles of the Rust compiler (gap 10): step S.1f;
- the e-graph in Zed: step S.3a, which step L23.1 extends to ZIR.

Gap 4 (the bit words) is built (step L1.39a).
