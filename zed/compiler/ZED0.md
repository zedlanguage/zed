# Zed₀: the bootstrap subset (step M0.8)

Zed₀ is the part of the language the Rust-hosted compiler must run for the Zed compiler
(row S) to be written in Zed. **The layer that completes it is L6**, so row S follows L6, as
DESIGN.md already places it.

The checklist has two parts. Part A is audited mechanically against corpus program 31, the
typechecker shaped like the compiler. Part B lists what the compiler needs that program 31
does not use, each with the layer and the place in DESIGN.md that provides it. Step S.1
freezes this list against the compiler's design and inserts a step for each gap it finds.

## The audit

`dart ../../tools/bin/audit.dart ../corpus/31-typechecker.zed --checklist ZED0.md`
(run by hand, since CI does not read the spec repository, which must be beside this one;
last run at spec commit 17bd42f, exit status 0, 91 grammar alternatives and 13 words needed,
none missing). An alternative is needed when program 31's units stop parsing, or parse to a
different tree, without it, so the list is exact for the grammar of DESIGN.md sec:grammar.
`Rule#i` is alternative `i` (from 0) of the rule, in the grammar's order. The words are
those `layer.dart -v` reports. The indices follow the grammar: after a grammar change, rerun
the audit and update the list.

Negative controls: with the entry for alternative 0 of Loop deleted from this file, the audit
exits 1 and names it; corpus program 17 (a stream program, label L7) audits to a word at L7,
above Zed₀.

## Part A: what program 31 needs

| Layer | Grammar alternatives | Defined words |
|---|---|---|
| L1 | `Additive#0` `And#0` `Args#0` `Args#1` `Arrow#1` `AtomPattern#0` `Binding#1` `Block#0` `Body#0` `Body#1` `Decl#11` `Decl#14` `Decl#15` `ElseTail#1` `Equality#1` `Expr#0` `Expr#2` `Expr12#0` `FieldPat#0` `Function#0` `If#0` `Item#3` `Lambda#0` `Literal#0` `Multiplicative#0` `Name#0` `NamedArg#0` `Or#0` `Param#0` `Params#0` `Params#1` `Path#0` `Pattern#1` `Port#0` `PosArg#1` `PosParam#1` `Postfix#0` `Power#0` `Prefix#1` `Primary#0` `Primary#1` `Primary#2` `Primary#5` `Primary#7` `Primary#13` `Push#1` `Range#0` `Reduce#0` `RelTail#0` `RelTail#1` `Relation#2` `Result#0` `Suffix#0` `Suffix#1` `Suffix#2` `Target#0` `Type#0` `TypeAnd#0` `TypeNot#1` `TypeParam#0` `TypePostfix#0` `TypePrimary#1` `TypePrimary#3` `TypeUnion#1` `Unit#0` | `String` |
| L2 | `Arm#0` `Decl#2` `Decl#3` `Decl#4` `Field#1` `Import#0` `Match#0` `Pattern#2` `Pattern#7` `Primary#8` `Struct#0` `StructField#1` `TypeDecl#0` `TypePrimary#2` | — |
| L3 | `Binder#0` `For#0` `Generator#0` `InPattern#0` `Primary#9` `Primary#11` `Suffix#5` | `map` `where` `foldl` `split` `concat` |
| L4 | — | `group` `flatMap` `#collision` |
| L5 | — | `take` `drop` `last` `rank` |
| L6 | `Boundary#0` `BoundaryItem#0` `Decl#10` `Loop#0` `Primary#10` | — |

Program 31 also needs two things no parser sees: general recursion through named functions
(its evaluation of the recursive union `Expr`), which is the definedness `fix` of step L6.4,
and a recursive union type, whose recursion is checked at L6.4 and folded at L6.5.

## Part B: what the compiler needs beyond program 31

| Need | Zed₀ feature | Layer | Where |
|---|---|---|---|
| read the source units | the `Files` port, `fs[path]`; an import names its unit's path, so no directory listing is needed | L1 | DESIGN.md "Ports are the only outside world", the words table |
| lex by code point | the `String` functions | L1 | the words table |
| content addresses (BLAKE3) | `bitAnd`, `bitOr`, `bitXor`, `shl` and the other named bit functions on domain-typed ints, and `%` by `2^32` | L1 | DESIGN.md "no bitwise operators" row of the glyph table |
| syntax trees, ZIR nodes, facets | structs, unions of atoms with fields, `match` | L2 | sec:grammar |
| symbol and bound tables | `group` with a `#collision` fold, `rekey` | L4 | as program 31 |
| deterministic output order | `sort`, `rank` | L5 | as program 31 |
| memoized parsing, worklists, inference, the ordered rewriter | indexed definitions `f[i] = e`, `loop` with `until`, the definedness `fix` | L6 | steps L6.1, L6.4 |
| folds over trees | `.fold` on a recursive union | L6 | step L6.5 |
| emitting code | the Cranelift operations as built-in ports the Rust-hosted compiler declares, as it declares `main`'s | L1 (port header) | step S.4 |

Not in Zed₀, with the reason:

- streams, `@foreign` and the incremental engine (L7): the compiler reads whole files, and
  reaches Cranelift through built-in ports (step S.4), not through foreign signatures;
- refinements, proofs, user facets and staging (L10 and above): the compiler's own checks run
  as ordinary code, so it needs none of them to be written; the checker it implements covers
  L1–L6 first (step S.3), and later layers add their procedures as prelude source (G10).

## Gaps found

One, already in the plan: the built-in Cranelift ports (step S.4). The rest of Parts A and B
is provided by L1–L6.
