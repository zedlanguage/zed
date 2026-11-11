# The bootstrap subset (step M0.8)

By the author's answer to QUESTIONS Q34 (2026-11-11), Zed₀ is the end of bootstrapping, step
S.11 of DESIGN.md: the point where the Rust-hosted compiler and `zed-rt` leave main, after which
the language server and the editor are built, in Zed. This file lists the bootstrap subset, which
the order of 2026-11-05 and earlier versions of this file called Zed₀; the file keeps its name so
that references to it stay valid.

The bootstrap subset is the part of the language the Rust-hosted compiler must run for the Zed
compiler (row S) to be written in Zed. By the author's order of 2026-11-05, which called the
subset Zed₀, **Zed₀ is the whole core, not
the smallest subset that compiles**: L1–L18 in full, the language parts of L19–L24 and the
back end ZIR → MLIR → LLVM IR → x86-64 of L28 (DESIGN.md step M0.8). Row S follows them. Part
A below records what the compiler needs at least; the audit found that L6 completes that
much, and the subset is larger because few rows should be written twice.

The checklist has two parts. Part A is audited mechanically against corpus program 31, the
typechecker shaped like the compiler. Part B lists what the compiler needs that program 31
does not use, each with the layer and the place in DESIGN.md that provides it. Step S.1
freezes this list against the compiler's design and inserts a step for each gap it finds.

## The audit

`cargo run -q -p zed-tools --bin audit -- ../../../zed ../corpus/31-typechecker.zed --checklist ZED0.md`
(run by hand, since CI does not read the spec repository, which must be beside this one;
last run at spec commit eb34700, exit status 0, 115 grammar alternatives and 13 words
needed, none missing, and 128 entries listed, none not needed). An alternative is needed when program 31's units stop parsing, or parse to a
different tree, without it, so the list is exact for the grammar of DESIGN.md sec:grammar.
`Rule#i` is alternative `i` (from 0) of the rule, in the grammar's order. The words are
those `layer -v` reports. The indices follow the grammar: after a grammar change, rerun
the audit and update the list.

The audit reads only the table of Part A, and Part A lists exactly what the audit finds: the
audit names each needed entry Part A lacks, and each entry Part A lists that program 31 does
not need (a rule or alternative the grammar no longer has, a word the table of defined words
no longer lists, or an alternative or word that exists but program 31 does not use), and exits
1 if either list is not empty. No entry is listed for any other reason; a need of the compiler
that program 31 does not show belongs in Part B.

Step S.1 reruns this audit over the current grammar. Negative controls: with the entry for
alternative 0 of Loop deleted from this file, the audit exits 1 and names it as missing; with
`Prefix#2` written as `Prefix#1` (its index before AnnotExpr was inserted above it), it exits 1
and names `Prefix#2` as missing and `Prefix#1` as not needed; with `Port#0` (a rule the grammar no
longer has), `Result#0` (an alternative program 31 does not use) and the word `String` (no longer
in the table) added, it exits 1 and names all three as not needed; a synthetic program
that uses a word of a layer after row S (L25 or above) audits to that word, above the bootstrap subset.

## Part A: what program 31 needs

| Layer | Grammar alternatives | Defined words |
|---|---|---|
| L1 | `Additive#0` `Additive#1` `And#0` `And#1` `Args#0` `Arrow#3` `AtomExpr#0` `AtomPattern#0` `AtomType#0` `Binding#1` `Block#0` `Body#0` `Body#1` `CallSuffix#0` `Compare#0` `Decl#11` `Decl#14` `Decl#15` `ElseTail#1` `Equality#1` `Equality#2` `Expr#0` `Expr#2` `Expr12#0` `Expr12#1` `FieldPat#0` `Function#0` `Group#0` `If#0` `IndexSuffix#0` `IsTest#0` `Item#2` `Lambda#0` `Literal#0` `MemberSuffix#0` `Multiplicative#1` `Name#0` `NamedArg#0` `Or#0` `Or#1` `Param#0` `Params#0` `Path#1` `Pattern#1` `PlainArg#0` `PlainBinding#0` `PosArg#1` `PosParam#1` `PositionalParam#0` `Postfix#0` `Postfix#1` `Power#1` `Prefix#2` `Primary#0` `Primary#1` `Primary#2` `Primary#5` `Primary#7` `Primary#13` `Push#2` `PushTarget#0` `Range#1` `Reduce#1` `Relation#2` `Relation#3` `Relation#5` `Suffix#0` `Suffix#1` `Suffix#2` `Target#0` `Type#0` `TypeAnd#1` `TypeName#0` `TypeNot#1` `TypeOr#0` `TypeOr#1` `TypeParam#0` `TypePostfix#1` `TypePrimary#1` `TypePrimary#3` `TypeUnion#1` `Unit#0` `WholePush#0` | `MainArgs` |
| L2 | `Arm#0` `AtomApply#0` `Decl#2` `Decl#3` `Decl#4` `Field#1` `Import#0` `Match#0` `NamePat#0` `Pattern#2` `Pattern#7` `Primary#8` `Struct#0` `StructField#3` `TypeDecl#0` `TypePrimary#2` `WildPat#0` | — |
| L3 | `ArrayExpr#0` `Binder#0` `For#0` `Generator#0` `InPattern#0` `Primary#9` `Primary#11` `ReadSuffix#0` `Suffix#5` | `concat` `foldl` `map` `split` `where` |
| L4 | — | `#collision` `flatMap` `group` |
| L5 | — | `drop` `last` `orderedValues` `take` |
| L6 | `Boundary#0` `BoundaryItem#0` `Decl#10` `Loop#0` `Primary#10` `Until#0` | — |

Program 31 also needs two things no parser sees: general recursion through named functions
(its evaluation of the recursive union `Expr`), which is the definedness `fix` of step L6.4,
and a recursive union type, whose recursion is checked at L6.4 and folded at L6.5.

## Part B: what the compiler needs beyond program 31

The audit of 2026-11-03 compared this list with `ZED_PORT_GAPS.md` and with the compiler's
Rust, and moved each need it found after the bootstrap subset to a step in L1–L6 or in row S before the
step that uses it.

| Need | Feature of the subset | Layer | Where |
|---|---|---|---|
| read the source units | the `Files` port, `fs[path]`; an import names its unit's path, so no directory listing is needed | L1 | DESIGN.md "Ports are the only outside world", the words table |
| read the command line | the `CommandLine` input port: the arguments after `--`, keyed by position from 1 | L1 | step L1.19a |
| write an executable | `zedc build file -o out`, a deterministic link with the runtime (`zed-rt`, and libzed after step S.7a) | L1 | step L1.36a |
| lex by code point | the `String` functions, and `codePoint`, `scalar`, `utf8`, `fromUtf8` | L1 | step L1.39c |
| identifier and normalization tables | XID_Start, XID_Continue, the scripts and the NFC data as sorted range tables, each lookup O(log n) by `upTo` | L5 | step S.1c, with step L5.8a |
| content addresses (BLAKE3) | `bitAnd`, `bitOr`, `bitXor`, `shl` and the other bit words of step L1.39a, and `mod 2^32` | L1 | step L1.39a; the `&` row of the glyph table |
| syntax trees, ZIR nodes | structs, unions of atoms with fields, `match` | L2 | sec:grammar |
| the types the checker's units share | `Ast` (the node kinds of every layer before row S), `Facet`, `Rejection`, `Interval`, `Congruence`, `Bound`, as plain types with no reads | L6 | step S.1b |
| search a family | `.any`, `.all`, `.find`, short-circuiting in key order | L3 | step L3.15a |
| symbol and bound tables | `group` with a `#collision` fold, `rekey` | L4 | as program 31 |
| deterministic output order | `sort`, `orderedValues` | L5 | as program 31 |
| nearest key, priority queues | `m.upTo(k)` and `m.from(k)` on an ordered family, each O(log n) | L5 | step L5.8a |
| memoized parsing, worklists, inference, the ordered rewriter | indexed definitions `f[i] = e`, `loop` with `until`, the definedness `fix` | L6 | steps L6.1, L6.4 |
| folds over trees | `.fold` on a recursive union | L6 | step L6.5 |
| union-find, dense tables, keyed updates in O(1) | reuse in place at count 1: `with`, a one-key `patch`, a `map` over a dying family, a `match` arm rebuilding its node | L6 | step L6.13, with the report of copies of step L6.13b |
| hash-consing and the e-graph | the digest kept in each shared object and the `==` shortcut on it | L6 | step L6.13a; the e-graph itself is step S.3a |
| deep lists and trees | release by a work list, constant stack | L6 | step L6.13c |
| emitting code | the MLIR text port, a built-in output port the Rust-hosted compiler declares, as it declares `main`'s; the host runs `mlir-opt`, `mlir-translate` and `llc` | L1 (port header) | step S.1a |
| computed output paths, bytes, exit status | a `U8String` input port, an output path computed at run time, the status from `main`'s failure member | L7 | step L7.3f (row FILE-bytes) |
| the compiler's own later needs | every core row of L7–L24, each in `docs/plan_dag.md` before S.1, and the catalog of routines the Rust calls (row PORT-catalog) | L7–L24 | step S.1 |

After row S, not in the bootstrap subset: the breadth of the standard library beyond the seed (rows STD-seq,
STD-text, STD-num, STD-blake3, then STD-full), other back ends (wasm, GPU, HDL, AArch64 and RV64),
microcontrollers, the language server and the editor (after Zed₀, step S.11), the sketchbook, the libraries of L33 and OS portability.

## After step S.8

The bootstrap subset limits what the Rust-hosted compiler must run, and so what the Zed compiler's own source may
use, only while the Rust-hosted compiler is the bootstrap root. By the answer to QUESTIONS Q52
(author, 2026-11-11), the Rust-hosted compiler is retired at step S.8, the first tagged release
becomes the root (step S.9), and the Rust compiler and `zed-rt` are kept in the `rust-bootstrap`
branch (step S.10) and leave main (step S.11). Nothing stays in Rust: `zed-rt` is ported to libzed
(step S.7a, plan row RT-port-libzed), whose OS layer holds the only foreign calls.

From step S.8 on, the limit on the compiler's own source is the tagging rule of step S.10a, not this
list: the compiler's source may use any feature the latest release compiles, and a commit that
uses a feature it cannot compile is preceded by a new release, recorded in `BOOTSTRAP.md` in the
`rust-bootstrap` branch. The audit above keeps its use until step S.8; after it, the branch's
guide records which release can build which source. The runtime port of step S.7a needs forms
this list does not cover (system calls through the OS layer, the heap's word layout of step
L6.13f); step S.7a records any it finds missing here, under Gaps found, with the step that adds it.
Step S.11 is Zed₀; the language server (step L25.1, in `zed/compiler/lsp/`) and the editor (L30,
L34) follow it, and the server checks its own release version against the version each package's
manifest declares (step L25.1a).

## Gaps found

The audit of 2026-11-03 found these, each now a step before its first use:

- the command line (gap 6): step L1.19a;
- an executable (DESIGN.md step L1.36 notes): step L1.36a;
- code points and UTF-8 (gap 7): step L1.39c, and the Unicode tables, step S.1c;
- the quantifiers `.any`, `.all`, `.find` (gap 12, early exit): step L3.15a;
- key range queries (gap 9): step L5.8a;
- updates in place, digests, the report of copies and iterative release (gaps 1 and 11):
  steps L6.13 to L6.13c;
- the back-end port, now MLIR text: step S.1a, before step S.4 uses it;
- the shared checker types, fixed for every layer before row S: step S.1b;
- stopping at a broken invariant (gap 8): step S.1d, the member `#bug(message)` the author chose on 2026-11-04;
- prelude units slower than their stated cost: step S.1e;
- the file import cycles of the Rust compiler (gap 10): step S.1f;
- the e-graph in Zed: step S.3a, which ports step L23.1's e-graph over ZIR, written first in Rust.

The review of 2026-11-05 added: bytes, computed paths and exit status (gaps 5 and 6): step L7.3f;
the runtime's value layout: step L6.13f; a build constant replacing `cfg!`: step L2.8d; prelude
units that call words that do not exist: step S.1g.

Gap 4 (the bit words) is built (step L1.39a).
