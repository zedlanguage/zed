# M0.4 corpus ledger

The 31 programs of DESIGN.md line 1559, one file each (`NN-name.zed`), with
inputs (`NN-name.in`), expected outputs (`NN-name.out`) computed by
`ref/NN.py`, extra units in `NN-name/`, other spellings in `variants/`, and
checker controls in `controls/`. Each program's first line is its label,
`// layer Lk`; its header comment says which mechanism it tests and how a
wrong mechanism changes its output.

Checks, all run from this directory:

- `python3 -B ring.py FILE...`: the lowest ring at which a file parses, with
  the grammar fences read live from DESIGN.md of the spec repository.
- `python3 -B layer.py [-v] PROGRAM...`: ring, table layer (the highest word of
  the table "Defined words by layer" the program uses), label, and agreement;
  exit status 1 on any disagreement or parse failure.
- `./refcheck.sh`: runs every `ref/NN.py` on its `.in` and compares with the
  `.out` (`--write` regenerates the `.out` files).

Import resolution: for a program with units, the package root is the directory
`NN-name/` next to the main file, and `import u.{...};` names the unit
`NN-name/u.zed`. Each unit's first comment line restates this.

## Table

"layer.py" gives ring / table layer (word) / enabled. "1561" is the layer
DESIGN.md line 1561 assigns. Every label equals the line 1561 layer.

| # | file | mechanism (line 1559) | label | layer.py | 1561 |
|---|---|---|---|---|---|
| 1 | 01-word-count.zed | word count | L4 | L3 / L4 (group) / L4 | L4 |
| 2 | 02-histogram.zed | scatter and filter histograms converge | L4 | L3 / L4 (group) / L4 | L4 |
| 2v | variants/02-histogram-push.zed | keyed push into `with reducer((+))` | L7 | L7 / L7 (reducer) / L7 | L7 |
| 3 | 03-edit-distance.zed | top-down memoized and bottom-up wavefront converge | L6 | L6 / L3 (split) / L6 | L6 |
| 4 | 04-running-variance.zed | scan + tupling synthesis | L5 | L3 / L5 (scan) / L5 | L5 |
| 5 | 05-max-prefix-sum.zed | combiner synthesis | L5 | L3 / L5 (scan) / L5 | L5 |
| 6 | 06-matrix-multiply.zed | matrix multiply | L5 | L3 / L5 (zip) / L5 | L5 |
| 6v | variants/06-matrix-multiply-remap.zed | the remap | L8 | L8 / L5 (slice) / L8 | L8 |
| 6m | variants/06-matrix-multiply-method.zed | the stdlib method `matmul` | L14 | L1 / L14 (matmul) / L14 | (none) |
| 7 | 07-json-parser.zed (+ json.zed) | grammar round trip, error recovery | L20 | L20 / L20 (serialize) / L20 | L20 |
| 8 | 08-utf8-percent.zed | UTF-8 decode fused with percent decoding, zero intermediates | L6 | L6 / L5 (rank) / L6 | L6 |
| 9 | 09-canonical-equal.zed | equality against an unmaterialized canonical form | L3 | L1 / L3 (split) / L3 | L3 |
| 10 | 10-regex-matcher.zed (+ regex.zed) | static regex specialized by `mix` | L19 | L2 / L19 (mix) / L19 | L19 |
| 11 | 11-csv-split.zed | state machine parallelized by scan | L5 | L3 / L5 (slice) / L5 | L5 |
| 12 | 12-cyk-table.zed | grammar-table recurrence (CYK) | L6 | L6 / L3 (where) / L6 | L6 |
| 13 | 13-union-find.zed (+ uf.zed) | union-find, library path | L6 | L6 / L5 (rank) / L6 | L6 |
| 14 | 14-clustering.zed | incremental all-pairs reuse | L7 | L6 / L5 (drop) / L7, label above both | L7 |
| 15 | 15-spreadsheet.zed | incremental spreadsheet | L7 | L6 / L6 (::frames) / L7, label above both | L7 |
| 16 | 16-game-tick.zed | generations, event coalescing | L7 | L7 / L7 (reducer) / L7 | L7 |
| 17 | 17-sensor-pipeline.zed | batch to streaming, waves, windows | L7 | L3 / L7 (window) / L7 | L7 |
| 18 | 18-socket-wordfreq.zed | frontier completion over a socket | L7 | L3 / L7 (window) / L7 | L7 |
| 19 | 19-bank-ledger.zed | insufficient-funds values, failure surfacing | L6 | L6 / L5 (rank) / L6 | L6 |
| 20 | 20-taint.zed | taint compile error, then the fix | L13 | L7 / L13 (taint) / L13 | L13 |
| 20e | variants/20-taint-error.zed | the error version (must be rejected) | L13 | L7 / L13 (taint) / L13 | L13 |
| 21 | 21-stats-module.zed (+ stats.zed) | demand-pruned record outputs sharing one sub-graph | L3 | L3 / L3 (split) / L3 | L3 |
| 22 | 22-top-k.zed | sort pruning | L5 | L5 / L5 (take) / L5 | L5 |
| 23 | 23-join-zoo.zed | all region triples, disjoint concatenation, range domains | L5 | L3 / L5 (rank) / L5 | L5 |
| 23v | variants/23-join-zoo-remap.zed | joins as output-keypath constraints | L8 | L8 / L5 (rank) / L8 | L8 |
| 24 | 24-weighted-pick.zed | prefix sum + binary search, rank domains, sentinels | L6 | L6 / L5 (drop) / L6 | L6 |
| 25 | 25-autocorrelation.zed | implicit valid-range join | L5 | L3 / L5 (zip) / L5 | L5 |
| 26 | 26-heat-stencil.zed | stencil, wavefront skewing | L6 | L6 / L3 (split) / L6 | L6 |
| 27 | 27-parent-chain.zed | three spellings converge | L6 | L6 / L5 (first) / L6 | L6 |
| 28 | 28-precedence-climbing.zed | modular wraparound, inclusive end test | L6 | L6 / L5 (take) / L6 | L6 |
| 29 | 29-late-dedup.zed | waves overtaking, window late policy | L7 | L3 / L7 (window) / L7 | L7 |
| 30 | 30-client-server.zed (+ api.zed, server.zed) | keypath cut, grammar-serialized boundary | L20 | L20 / L20 (serialize) / L20 | L20 (split at L24) |
| 31 | 31-typechecker.zed (+ ast.zed, check.zed) | group + singleton-or-#collision fold, two passes, one fix, diagnostics by address | L6 | L6 / L5 (take) / L6 | L6 |

Counts: the labels give L3: 9, 21; L4: 1, 2; L5: 4, 5, 6, 11, 22, 23, 25;
L6: 3, 8, 12, 13, 19, 24, 26, 27, 28, 31; L7: 14, 15, 16, 17, 18, 29; L13: 20;
L19: 10; L20: 7, 30. This is line 1561's list exactly. 27 programs are at
L7 or below, which matches "Twenty-seven of the thirty-one need only the
core", reading the core as L1 to L7 (line 1501: "L1–L7 build the core").

### Where the label is not the mechanical layer

- **14 and 15** are labeled L7, while ring and table give L6. Both need only
  L6 syntax and words to run; what puts them at L7 is the mechanism they test,
  incremental reuse (step L7.6), which is a property of the plan and has no
  word in the source. layer.py flags both ("label above ring and table"). The
  label follows line 1561; the mechanical rule alone would say L6.
- **6 (method)**: line 1559 says program 6 carries "the remap and the stdlib
  method", and line 1561 enables the extra spellings at L8. The remap is L8, but
  the stdlib method `matmul` is an L14 word in the table, so that spelling
  cannot be enabled at L8. The corpus carries it as
  `variants/06-matrix-multiply-method.zed`, labeled L14; line 1561 has no
  layer for it. The L5 main program uses the iteration register (`zip` of a
  row with a column), which is neither of the two spellings line 1559 names.

## Corrections to the ledger descriptions

1. **Program 6.** The ledger's "the stdlib method" is L14, not L8 (above).
   Fix for DESIGN.md line 1561: "Programs 6 and 23 also carry calculus-register
   spellings, enabled at L8, and program 6 the method spelling `a.matmul(b)`,
   enabled at L14."
2. **Program 8.** "UTF-8 decode fused with percent-escaping": the input is
   Lines, already decoded text, so there are no raw bytes to UTF-8-decode
   unless they arrive percent-encoded. The program percent-*decodes* (%XX gives
   a byte) and UTF-8-decodes the byte runs, fused. Suggested wording:
   "percent-decoding fused with UTF-8 decoding".
3. **Program 19.** "reduction failure surfacing": the failure does not surface
   through a reduction. By the unlifted-carrier rule (sec:reduction, point 2)
   a `+` reduction over `int | #insufficient(...)` is a static error; the
   running failure lives in `patch`, which is total on that carrier (point 3),
   and the program splits the level and reduces the good side. Suggested
   wording: "failures as running values under patch, and the split-and-reduce
   repair".
4. **Program 13.** "certified library path": the prelude names no union-find
   word (the table has none), so the "library" is a unit of the program
   (`13-union-find/uf.zed`) whose `components` is the monotone fixpoint; the
   certified union-find implementation is what the compiler must substitute.
5. **Program 30.** Written as one program in three units; the split itself
   waits for L24, as line 1561 says. No change, but the L20 program can only
   check that the boundary values serialize and parse; the split is untested
   until L24.

Syntax in the ledger that was stale or not in the grammar, and what the
programs use instead:

- **Keyed push below L7.** `hist[s.len] <- 1` is a keyed push, L7 in the
  grammar, and several pushes to one port are L7.2. Programs below L7 push
  once per port and build the whole output with `++` of `.rank`ed families
  (13, 19, 23, 31).
- **`-> Type` results and typed bindings** are L10, so no program below L10
  writes them; types appear only as struct field types and in `type`
  declarations.
- **Statement expressions** (`Expr ';'`) are L6; programs below L6 use none.

## Syntax doubts and how each was resolved

Each is a choice the spec does not fix. The ref scripts implement the choice,
so a different decision changes the named `.out` files.

1. **stdin keys.** `stdin[t]` and `stdin.drop(1)` treat Lines as a rank-keyed
   family from 0 (EXAMPLES' todo example indexes `cmds[t]` the same way).
   Programs 14, 15, 24, 25, 26 depend on it.
2. **`int(s)` and `f64(s)`** are the String casts, giving `int | #invalid`
   (EXAMPLES, sec:domains) and `f64 | #invalid`; `else` supplies the default.
   The `f64(String)` cast is assumed by analogy (21).
3. **`Scalar(cp)` and `"${c}"`** turn a code point into a one-character
   String (08, 10).
4. **`mix(f, x)`** fixes the first parameter of `f` to `x` (10).
5. **JSON (07):** the error position is the farthest position any
   alternative reached, after skipping whitespace; `X* sep ","` allows zero
   items; true/false/null are a token type, not atoms; there is no syntax to
   declare a key order, so the canonical form only removes whitespace; there is
   no character-class negation, so strings hold letters, digits and spaces
   only. The same error-position rule is used in 30.
6. **`serialize` writes no whitespace** (07, 30). In 30 every response
   grammar therefore separates adjacent words by punctuation (`missing:kiwi`).
7. **Constructing a `matching` type from a String** by applying the type,
   `Count("${n}")` (30), by analogy with interpolation's "apply the type".
8. **`.window`** (17, 18, 29): the real signature is written at step L7.5. The
   corpus assumes `xs.window(width: n, time: e -> e.t)` giving tumbling
   windows keyed by start time `t div n * n`, absent when empty, each holding
   its elements under their source keys; 29 adds `lateness: 5, late: #drop`,
   with a reading dropped when its window's end is at or below the watermark
   (largest event time seen so far, minus the lateness) at its arrival.
9. **Stream port type** `Stream(String)` for a socket or sensor feed (18,
   29); the harness feeds it from the `.in` file in line order.
10. **Pushing a nested family to `stdout`** writes it in keypath order, and
    `.rank` of a keyed or two-level family densifies it in keypath order (19,
    23, 31).
11. **`++` of two int-keyed sets** (23, `onlyL ++ onlyR`, `low ++ high`) is the
    disjoint union (overlap `#assertEmpty`), keyed by the original keys and so
    read in int order, not left-then-right.
12. **`zip` of rank families with different domains** (25) is the inner
    equality join, keeping the intersection 0..<n - l; `drop` keeps the
    source keys (DESIGN line 546), hence `.drop(l).rank`.
13. **A missing key reads as `#notFound`** (23, 30, 31), as EXAMPLES' `unpaid2`
    does. Where the looked-up value's own type holds atoms (31's type lattice
    `#unknown`, `#int`, `#bool`, `#error`; 23's and 30's printed absence), the
    programs test it with `match` or `is` rather than `else`, since which atoms
    `else` strips depends on the written type; elsewhere (`w[0] else ""`) they
    use `else`.
14. **`sanitize`** HTML-escapes `& < > " '` (20); the library fixes its text
    at step L13.2.
15. **`return { mean: mx, sd:, cov: }`** in a block-bodied function (21),
    following EXAMPLES lines 233 to 241.
16. **Loop results.** `loop t { x' = f(x) with x = x0; while c; }` runs the step
    at t when c holds at t; `run.x` is the final state and `run::frames` the
    per-step states (14, 15, 16, 19, 24, 28). 28's inclusive test
    `while t <= toks::len` relies on this reading.
17. **Step-local bindings inside a loop body** are avoided; helper functions
    carry the work (14, 15, 19, 24, 28).
18. **"with imports for all 31 programs"** (M0.4) is read as: several
    programs are multi-unit (7, 10, 13, 21, 30, 31), and every program states
    how its imports resolve; single-unit programs import nothing, since the
    prelude needs no import.

## Known limits of layer.py

- `.fold` on a recursive union (L6) is not told apart from `fold` (L3), and
  `abs` on the number algebras (L14) from `abs` on scalars. No program uses
  `.fold` or `abs`, so neither affects a result here.
- Prelude functions that the table does not list (`count`, `sum`, `union`,
  `all`, `lower`, `sqrt`, ...) are not counted.
- The table layer of 14 and 15 is below their label by design (see above);
  layer.py cannot see incrementality.

## Controls

`controls/` holds files that must fail and files that must pass:

- `neg-take-at-L4.zed` parses at L1 but uses `take` (L5) under an L4 label:
  layer.py must say NO. This is the main negative control: the parse ring
  alone would accept it.
- `neg-sort-at-L4.zed`: `sort` (L5) under an L4 label, NO.
- `neg-gpu-target.zed`: `#gpu` as the argument of `target(...)` counts as the
  L27 target value, NO.
- `neg-parse-error.zed`: a missing `;`, must fail to parse.
- `pos-shadow-scan.zed`: the program binds `scan`, so the word is not the L5
  prelude word; yes at L3.
- `pos-gpu-atom.zed`: `#gpu` outside `target(...)` is an ordinary atom; yes at L3.

## Output of the checks

`python3 -B layer.py [0-9][0-9]-*.zed variants/*.zed` (exit status 0):

```
program                            units  ring table (word)     label enabled agree
01-word-count.zed                      1    L3 L4 (group)          L4      L4 yes
02-histogram.zed                       1    L3 L4 (group)          L4      L4 yes
03-edit-distance.zed                   1    L6 L3 (split)          L6      L6 yes
04-running-variance.zed                1    L3 L5 (scan)           L5      L5 yes
05-max-prefix-sum.zed                  1    L3 L5 (scan)           L5      L5 yes
06-matrix-multiply.zed                 1    L3 L5 (zip)            L5      L5 yes
07-json-parser.zed                     2   L20 L20 (serialize)    L20     L20 yes
08-utf8-percent.zed                    1    L6 L5 (rank)           L6      L6 yes
09-canonical-equal.zed                 1    L1 L3 (split)          L3      L3 yes
10-regex-matcher.zed                   2    L2 L19 (mix)          L19     L19 yes
11-csv-split.zed                       1    L3 L5 (slice)          L5      L5 yes
12-cyk-table.zed                       1    L6 L3 (where)          L6      L6 yes
13-union-find.zed                      2    L6 L5 (rank)           L6      L6 yes
14-clustering.zed                      1    L6 L5 (drop)           L7      L7 yes (label above ring and table)
15-spreadsheet.zed                     1    L6 L6 (::frames)       L7      L7 yes (label above ring and table)
16-game-tick.zed                       1    L7 L7 (reducer)        L7      L7 yes
17-sensor-pipeline.zed                 1    L3 L7 (window)         L7      L7 yes
18-socket-wordfreq.zed                 1    L3 L7 (window)         L7      L7 yes
19-bank-ledger.zed                     1    L6 L5 (rank)           L6      L6 yes
20-taint.zed                           1    L7 L13 (taint)        L13     L13 yes
21-stats-module.zed                    2    L3 L3 (split)          L3      L3 yes
22-top-k.zed                           1    L5 L5 (take)           L5      L5 yes
23-join-zoo.zed                        1    L3 L5 (rank)           L5      L5 yes
24-weighted-pick.zed                   1    L6 L5 (drop)           L6      L6 yes
25-autocorrelation.zed                 1    L3 L5 (zip)            L5      L5 yes
26-heat-stencil.zed                    1    L6 L3 (split)          L6      L6 yes
27-parent-chain.zed                    1    L6 L5 (first)          L6      L6 yes
28-precedence-climbing.zed             1    L6 L5 (take)           L6      L6 yes
29-late-dedup.zed                      1    L3 L7 (window)         L7      L7 yes
30-client-server.zed                   3   L20 L20 (serialize)    L20     L20 yes
31-typechecker.zed                     3    L6 L5 (take)           L6      L6 yes
02-histogram-push.zed                  1    L7 L7 (reducer)        L7      L7 yes
06-matrix-multiply-method.zed          1    L1 L14 (matmul)       L14     L14 yes
06-matrix-multiply-remap.zed           1    L8 L5 (slice)          L8      L8 yes
20-taint-error.zed                     1    L7 L13 (taint)        L13     L13 yes
23-join-zoo-remap.zed                  1    L8 L5 (rank)           L8      L8 yes
```

`python3 -B layer.py controls/*.zed` (exit status 1, as intended):

```
program                            units  ring table (word)     label enabled agree
neg-gpu-target.zed                     1    L7 L27 (#gpu)          L7     L27 NO
neg-parse-error.zed                PARSE FAIL neg-parse-error.zed: line 5 near 'stdout'; expected '!=' '&&' '(' '*' '**' '*.' '+' '++' '-' '.' '..' '..<' '..=' '/' '::' ';' '<' '<=' '==' '>' '><' '>=' '?.' '[' 'as' 'div' 'else' 'in' 'into' 'is' 'mod' 'not' 'with' '||'
neg-sort-at-L4.zed                     1    L5 L5 (sort)           L4      L5 NO
neg-take-at-L4.zed                     1    L1 L5 (take)           L4      L5 NO
pos-gpu-atom.zed                       1    L2 L3 (map)            L3      L3 yes
pos-shadow-scan.zed                    1    L1 L3 (map)            L3      L3 yes
```

`python3 -B ring.py [0-9][0-9]-*.zed [0-9][0-9]-*/*.zed variants/*.zed controls/*.zed` (exit status 1, from the parse-error control only):

```
01-word-count.zed L3
02-histogram.zed L3
03-edit-distance.zed L6
04-running-variance.zed L3
05-max-prefix-sum.zed L3
06-matrix-multiply.zed L3
07-json-parser.zed L2
08-utf8-percent.zed L6
09-canonical-equal.zed L1
10-regex-matcher.zed L2
11-csv-split.zed L3
12-cyk-table.zed L6
13-union-find.zed L3
14-clustering.zed L6
15-spreadsheet.zed L6
16-game-tick.zed L7
17-sensor-pipeline.zed L3
18-socket-wordfreq.zed L3
19-bank-ledger.zed L6
20-taint.zed L7
21-stats-module.zed L3
22-top-k.zed L5
23-join-zoo.zed L3
24-weighted-pick.zed L6
25-autocorrelation.zed L3
26-heat-stencil.zed L6
27-parent-chain.zed L6
28-precedence-climbing.zed L6
29-late-dedup.zed L3
30-client-server.zed L2
31-typechecker.zed L6
07-json-parser/json.zed L20
10-regex-matcher/regex.zed L2
13-union-find/uf.zed L6
21-stats-module/stats.zed L3
30-client-server/api.zed L20
30-client-server/server.zed L3
31-typechecker/ast.zed L3
31-typechecker/check.zed L3
variants/02-histogram-push.zed L7
variants/06-matrix-multiply-method.zed L1
variants/06-matrix-multiply-remap.zed L8
variants/20-taint-error.zed L7
variants/23-join-zoo-remap.zed L8
controls/neg-gpu-target.zed L7
controls/neg-parse-error.zed FAIL line 5 near 'stdout'; expected '!=' '&&' '(' '*' '**' '*.' '+' '++' '-' '.' '..' '..<' '..=' '/' '::' ';' '<' '<=' '==' '>' '><' '>=' '?.' '[' 'as' 'div' 'else' 'in' 'into' 'is' 'mod' 'not' 'with' '||'
controls/neg-sort-at-L4.zed L5
controls/neg-take-at-L4.zed L1
controls/pos-gpu-atom.zed L2
controls/pos-shadow-scan.zed L1
```

`./refcheck.sh` (exit status 0):

```
01 ok
02 ok
03 ok
04 ok
05 ok
06 ok
07 ok
08 ok
09 ok
10 ok
11 ok
12 ok
13 ok
14 ok
15 ok
16 ok
17 ok
18 ok
19 ok
20 ok
21 ok
22 ok
23 ok
24 ok
25 ok
26 ok
27 ok
28 ok
29 ok
30 ok
31 ok
```
