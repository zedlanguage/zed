# Inventory: the standard operations on lists and maps, and their Zed spellings

Plan row FP-ops-run (author P229): "make sure all other standard FP operations on maps and lists
are also built (folds, zipWith, etc.), if they are not, yet. [...] Make them as Zed-native as
possible."

This file lists the operations of Haskell (`Data.List`, `Data.Map`), OCaml (`List`, `Map`) and
Scala collections (`Seq`, `Map`), and gives for each the Zed spelling DESIGN.md defines and the
step that builds it. Zed has one data type for both lists and maps, the family (a list is a family
keyed by position `0..<n`), so one row usually covers the list and the map operation of a library.

How to read the columns:

- **Zed** is the spelling. A *word* is a name in the "Defined words by layer" table of DESIGN and
  in `WORDS` of `crates/zedc-resolve/src/resolve.rs`. A *composition* is written from words and
  core forms (`for`, lookup, `++`, `::` reads, operator sections), with no new word. *No word*
  means DESIGN gives neither, and QUESTIONS.md has an entry for it.
- **Step** is the DESIGN step whose tests cover the word. A composition needs the steps of its
  parts.
- **Cost** is the cost of the Zed spelling on a family of `n` entries, where it differs from the
  library's. `k` is the number of entries read before the answer is decided.

Every row was checked against DESIGN.md at zed commit bfab497 (sections sec:reduction,
sec:order, sec:joins, sec:grouping, the kernel appendix's table of defined forms, and steps
L3.2, L3.4, L3.15a, L4.1, L5.1 to L5.3, L5.8, L5.9a). Where a row says "inferred", the spelling
follows from the definitions but no DESIGN example writes it.

## 1. Transforming

| Haskell | OCaml | Scala | Zed | Kind | Step |
|---|---|---|---|---|---|
| `map` | `List.map`, `Map.map` | `map` | `xs.map(f)` | word | L3.2 |
| `Map.mapWithKey` | `List.mapi`, `Map.mapi` | `zipWithIndex.map`, `map` on pairs | `for k -> v in m { f(k, v) }` | composition (`for`) | L3.2 |
| `concatMap`, `>>=` | `List.concat_map` | `flatMap` | `xs.flatMap(f)` | word | L4.1 |
| `mapMaybe` | `List.filter_map` | `collect` | `xs.map(f).where(v -> v != #none)` (inferred), or `flatMap` returning `[]`/`[x]` | composition | L3.2, L4.1 |
| `Map.mapKeys` | (fold rebuilding the map) | `map` on pairs | `m.rekey(f)`, with a collision rule (sec:remap_law) | word | L4.1 |
| `reverse` | `List.rev` | `reverse` | `for i in xs::domain { xs[xs.count - 1 - i] }`, as DESIGN writes `rev` in the tests of the proof ladder; reading a family in reverse order needs no copy: `rev(o)` of sec:order serves `.foldl`, `.first`, `.take`, scans | composition | L3.2; `rev(o)` L5.1c |
| `transpose` | — | `transpose` | `m into (j -> i -> m[i][j])`, a remap | composition (remap) | L8.2 |
| `zip`, `Map.intersectionWith (,)` | `List.combine` | `zip` | `a.zip(b)`; keyspaces must be equal (`#assertEmpty` on both one-sided regions) | word | L5.2 |
| `zipWith f` | `List.map2 f` | `zip(...).map` | `a.zip(b).map(p -> f(p[0], p[1]))` (a lambda `(x, y) -> e` takes two parameters, not one pair, sec:grammar) | composition | L5.2 |
| `zip3`, `zipWith3` | `List.map3` (none) | `lazyZip` | `(a, b, c).join(on: k)` gives one flat triple per key; `a.zip(b).zip(c)` gives nested pairs | composition | L5.2, sec:joins |
| `unzip` | `List.split` | `unzip` | `(z.map(p -> p[0]), z.map(p -> p[1]))` | composition | L3.2 |
| `zip [0..]` | `List.mapi` | `zipWithIndex` | not needed: a list's keys are its positions; `for i -> x in xs` binds both | composition | L3.2 |
| `intersperse`, `intercalate` | `String.concat sep` | `mkString(sep)` | for strings, see `concat` in section 6; for a general list no word (section 9) | — | — |
| `Map.foldrWithKey` | `Map.fold` | `foldRight` on pairs | `for k -> v in m { (k, v) }.foldr(op, init)` (inferred) | composition | L3.2, L3.4 |
| `tapEach` | `List.iter` | `foreach` | no effects in an expression; write to a port (`out <- v`) or use `@log` | not applicable | — |

## 2. Selecting

| Haskell | OCaml | Scala | Zed | Kind | Step |
|---|---|---|---|---|---|
| `filter`, `Map.filter` | `List.filter`, `Map.filter` | `filter` | `xs.where(p)` | word | L3.2 |
| `Map.filterWithKey` | `Map.filter` | `filter` on pairs | `for k -> v in m where p(k, v) { v }` | composition (`for`) | L3.2 |
| `partition`, `Map.partition` | `List.partition`, `Map.partition` | `partition`, `partitionMap` | `xs.group(p)`, giving `{false -> …, true -> …}` with each entry under its old key; or the two `where`s | word | L4.1 |
| `take` | `List.take` (5.3) | `take` | `xs.take(n)` | word | L5.1 |
| `drop` | `List.drop` | `drop` | `xs.drop(n)` | word | L5.1 |
| `splitAt` | — | `splitAt` | `(xs.take(n), xs.drop(n))` | composition | L5.1 |
| (slice by range) | — | `slice` | `xs.slice(r)` | word | L5.1 |
| `takeWhile` | — | `takeWhile` | `xs.takeWhile(p)` | word | L5.1 |
| `dropWhile` | — | `dropWhile` | `xs.drop(xs.takeWhile(p).count)`; O(k + log n), the same as a word would cost | composition | L5.1 |
| `span`, `break` | — | `span` | `(xs.takeWhile(p), xs.drop(xs.takeWhile(p).count))`; `break p` is `span` of `x -> !p(x)` | composition | L5.1 |
| `head`, `Map.lookupMin` | `List.hd`, `Map.min_binding` | `head`, `headOption` | `xs.first` (`#none` on an empty family, which `headOption` also gives) | word | L5.1 |
| `last`, `Map.lookupMax` | `Map.max_binding` | `last`, `lastOption` | `xs.last` | word | L5.1 |
| `tail` | `List.tl` | `tail` | `xs.drop(1)` | composition | L5.1 |
| `init` | — | `init` | `xs.take(xs.count - 1)` | composition | L5.1 |
| `Map.split`, `lookupLE`, `lookupGE` | `Map.split`, `find_first` | `rangeTo`, `rangeFrom` | `m.upTo(k)`, `m.from(k)`; `m.upTo(k).last` is `lookupLE` | word | L5.8 |
| `nub` | `List.sort_uniq` | `distinct` | `xs.group(x -> x)::domain` gives the distinct values in natural order; first-occurrence order is `xs.group(x -> x).map(g -> g::domain.first).orderedValues` (inferred) | composition | L4.1, L5.1 |
| `group` (runs) | — | — | `xs.chunkBy(x -> x)` | word | L5.3 |
| `groupBy eq` (runs) | — | — | `xs.chunkBy(f)` with a key function in place of the equivalence | word | L5.3 |
| `Map.fromListWith`, `groupBy` | — | `groupBy` | `xs.group(f)`, then a fold per group | word | L4.1 |
| — | — | `groupMapReduce(k)(f)(op)` | `xs.group(k).map(g -> g.map(f) >< op)` | composition | L4.1, L3.2 |
| — | — | `grouped(n)` | `for i -> x in xs { … }` regrouped by `i / n`: `xs.group(...)` cannot see the key, so `(xs into (i / n -> i % n -> v))` (inferred, a remap with an arithmetic key) | composition (remap) | L8.2 |
| — | — | `sliding(n)` | `for i in 0..=xs.count - n { xs.slice(i..<i + n) }` | composition | L5.1 |

## 3. Searching and testing

| Haskell | OCaml | Scala | Zed | Kind | Step |
|---|---|---|---|---|---|
| `any` | `List.exists`, `Map.exists` | `exists` | `xs.any(p)`, stops at the first `true` | word | L3.15a |
| `all` | `List.for_all`, `Map.for_all` | `forall` | `xs.all(p)`, `true` on `{}` | word | L3.15a |
| `or`, `and` | — | — | `bs.any(b -> b)`, `bs.all(b -> b)` | composition | L3.15a |
| `find`, `findIndex` | `List.find`, `find_index` | `find`, `indexWhere` | `xs.find(p)` gives the first *key*, or `#none`; the value is `xs[xs.find(p)]` | word | L3.15a |
| `elem` | `List.mem` | `contains` | `xs.any(x -> x == e)` | composition | L3.15a |
| `elemIndex` | — | `indexOf` | `xs.find(x -> x == e)` | composition | L3.15a |
| `Map.member` | `Map.mem` | `contains` | `k in m` | core form (`in`) | L3.2 |
| `lookup`, `Map.lookup` | `List.assoc`, `Map.find_opt` | `get` | `m[k]`, `#notFound` on a miss (`#outOfBounds` on an integer interval) | core form | L3.2 |
| `Map.findWithDefault` | `Option.value` | `getOrElse` | `m[k] else d` | core form | L3.2 |
| `null` | `List.is_empty` | `isEmpty` | `xs.count == 0` | composition | L3.2 |
| `isPrefixOf` | — | `startsWith` | `xs.take(p.count) == p` | composition | L5.1 |
| `isSuffixOf` | — | `endsWith` | `xs.drop(xs.count - p.count).orderedValues == p` (a list compares by keys, so the dropped list is re-ranked first) | composition | L5.1 |

## 4. Folding

| Haskell | OCaml | Scala | Zed | Kind | Step |
|---|---|---|---|---|---|
| `foldl` | `List.fold_left` | `foldLeft` | `xs.foldl(init, op)` with `op: (A, V) -> A` | word | L3.2, L3.4 |
| `foldr` | `List.fold_right` | `foldRight` | `xs.foldr(op, init)` with `op: (V, A) -> A` | word | L3.2, L3.4 |
| `foldl1`, `foldr1` | `List.reduce` (none) | `reduceLeft`, `reduceRight` | `xs >< op` or `xs.reduce(op)`, `#empty` on an empty level unless `op` has an identity; needs `op` associative on an ordered level (Boom table, sec:reduction) | word | L3.2 |
| `foldMap` | — | `aggregate` | `xs.map(f) >< op` | composition | L3.2 |
| `sum` | — | `sum` | `xs.sum` (`0` on empty from the identity of `+`); float sums fold on the canonical tree | word | L3.2 |
| `product` | — | `product` | `xs >< (*)` (identity `1`) | composition | L3.2 |
| `maximum`, `minimum` | — | `max`, `min` | `xs >< max`, `xs >< min`; `T \| #empty` at `int` over a possibly empty level | composition (`><` with the L1 words) | L3.2 |
| `maximumBy`, `minimumBy` | — | `maxBy`, `minBy` | `xs.maxBy(f)`, `xs.minBy(f)`, which keep every tie (a family, not one entry) | word | L5.1 |
| `length`, `Map.size` | `List.length`, `Map.cardinal` | `size`, `length` | `xs.count`, or `xs::len` on a rank-keyed level | word / metadata | L3.2 |
| — | — | `count(p)` | `xs.where(p).count` | composition | L3.2 |
| `scanl` | — | `scanLeft` | `xs.scan((+))`, the prefix folds (DESIGN writes the operator as a section); the last entry equals `xs >< op` | word | L5.3 |
| `scanr` | — | `scanRight` | a scan reading `rev(o)`, the suffix scan | word + order | L5.1c, L5.3 |
| `mapAccumL` | `List.fold_left_map` | — | a `loop` with `initial acc = init;` and a generation per entry (sec:generations) | composition (`loop`) | L6.1 |
| `Map.foldr`, `Map.elems` folds | `Map.fold` | `foldLeft` on a map | the same words on a keyed level, read in key order through the sorted view | word | L3.4 |

## 5. Building

| Haskell | OCaml | Scala | Zed | Kind | Step |
|---|---|---|---|---|---|
| `[]`, `Map.empty` | `[]`, `Map.empty` | `Nil`, `Map.empty` | `[]`, `{}` | display | L3.2 |
| `replicate n x` | `List.init n (fun _ -> x)` | `fill(n)(x)` | `for i in 0..<n { x }` | composition (`for`) | L3.2 |
| `generate`, `[f i \| i <- [0..n-1]]` | `List.init n f` | `tabulate(n)(f)` | `for i in 0..<n { f(i) }` | composition (`for`) | L3.2 |
| `[a..b]` | — | `a to b` | `a..=b`, `a..<b` | core form (range) | L3.2 |
| `iterate`, `unfoldr` | `Seq.unfold` | `iterate`, `unfold` | a `loop` with `initial x = x0; x' = f(x); until …;` (kernel `gen`) | composition (`loop`) | L6.1 |
| `Map.fromList` | `Map.of_list` | `toMap` | `pairs.rekey(p -> p[0]).map(p -> p[1])` with the collision rule, or a map display | composition | L4.1 |
| `Map.toList`, `Map.assocs` | `Map.bindings` | `toList` | `for k -> v in m { (k, v) }.orderedValues` (inferred) | composition | L3.2, L5.1 |
| `Map.keys`, `Map.keysSet` | `Map.bindings \|> List.map fst` | `keys`, `keySet` | `m::domain` (a set), ranked with `.orderedValues` where a list is wanted | metadata | L3.2 |
| `Map.elems` | — | `values` | `m.orderedValues` | word | L5.1 |
| `++` | `@` | `++` | `a ++ b`: offset concatenation on rank keys and on `Seq` | core form | L5.2 |
| `concat` | `List.concat`, `List.flatten` | `flatten` | for strings `concat` (section 6); for a list of lists, `xss.foldl([], (a, x) -> a ++ x)` (inferred; see section 9 on the word) | word for strings | L3.2 |
| — | — | `padTo(n, x)` | `xs ++ for i in 0..<(n - xs.count) { x }` | composition | L5.2 |
| `insert` (sorted list) | — | — | `(xs ++ [x]).sort(asc)` or, for an ordered collection, the substrate of step L5.8 | composition | L5.1, L5.8 |
| `sort` | `List.sort compare` | `sorted` | `xs.sort(asc)` / `xs.sort(desc)`; on a rank-keyed source a flat `[T]` | word | L5.1 |
| `sortOn f` | — | `sortBy(f)` | `xs.sort(asc f)`, several keys as `xs.sort(asc f, desc g)` | word | L5.1 |
| `sortBy cmp` | `List.sort cmp` | `sortWith(lt)` | `xs.sort(by: le)` with a `<=` relation | word | L5.1 |

## 6. Strings

| Haskell | OCaml | Scala | Zed | Kind | Step |
|---|---|---|---|---|---|
| `splitOn` (text) | `String.split_on_char` | `split` | `s.split(sep)`, empty pieces kept | word | L3.2 |
| `lines` | — | `lines` | `s.lines` (`\n`, `\r\n`, a lone `\r`) | word | L3.2 |
| `unlines` | — | `mkString("\n")` | `concat` with a line end after each line (section 9) | word (`concat`) | L3.2 |
| `concat` (strings) | `String.concat ""` | `mkString` | `concat` | word, signature open (section 9) | L3.2 |
| `intercalate sep` | `String.concat sep` | `mkString(sep)` | `concat` with a separator, signature open (section 9) | word, signature open | L3.2 |
| `words` | — | `split("\\s+")` | `s.chunkBy(c -> c == ' ' \|\| c == '\t' \|\| c == '\n')`, keeping the runs that are not space (inferred; DESIGN names no character-class test, so the class is written out) | composition | L5.3 |
| `unwords` | — | `mkString(" ")` | `concat` with `" "` (section 9) | word (`concat`) | L3.2 |

## 7. Maps

| Haskell `Data.Map` | OCaml `Map` | Scala `Map` | Zed | Kind | Step |
|---|---|---|---|---|---|
| `insert k v` | `add` | `updated`, `+` | `m.patch({k -> v})` | word | L5 (item 10 of the L5 list) |
| `delete k` | `remove` | `removed`, `-` | `m.where(k2 -> k2 != k)` is not it (`where` tests values); `for k2 -> v in m where k2 != k { v }` | composition (`for`) | L3.2 |
| `adjust f k` | `update k (Option.map f)` | `updatedWith` | `m.patch({k -> f(m[k])})` where `k in m` | composition | L5.2 |
| `alter`, `Map.update` | `update` | `updatedWith` | `m.patch(delta)`, the full outer join with a per-key fold | word | L5 (item 10 of the L5 list) |
| `union` (left-biased) | `union f` | `++` | `m.patch(n)` (right-biased), or `(m, n) into (m \|\| n -> v)` and a choice per slot | word / join | sec:joins |
| `unionWith f` | `union`, `merge` | `merged` | `(m, n) into (m \|\| n -> v)`, then `map` over the `(V \| #none, V \| #none)` slots | join | sec:joins |
| `intersectionWith f` | `merge` | — | `m.join(n, on: k)` (inner), then `map` | word | sec:joins |
| `difference`, `\\` | `filter` | `--` | `m.diff(n, on: k)` | word | sec:joins |
| `Map.restrictKeys` | — | `filterKeys` | `m.join(keys, on: k)` with a set operand | word | sec:joins |
| `Map.toAscList`, `toDescList` | `bindings` | `toSeq` | `.orderedValues` on the pairs, `rev(o)` for descending | word | L5.1, L5.1c |
| `Map.inverse` (none) | — | — | `m.inverse`, `V ->? K \| #collision` unless the values are proved distinct | word | L4.1 |

## 8. Order and position words found in DESIGN that the libraries have no exact twin for

`.orderedValues` (L5.1), `.chunkBy` (L5.3), `.upTo` / `.from` (L5.8), `.minBy` / `.maxBy`
keeping ties (L5.1), `classes(links)` (L5.9a, union-find classes), `group` / `tag` / `rekey`
(L4.1), `.patch` (L5), `merge` / `latest` / `window` on streams (L7), and `.fold(alg)` on a
recursive union (L6). Each is in the "Defined words by layer" table and in `WORDS`.

## 9. Operations with no word in DESIGN

1. **The signature of `concat`.** DESIGN names `concat` in step L3.2 and in the L3 row of the
   "Defined words by layer" table ("string functions that take or return a family; `split`
   keeps every piece, empty ones included, so joining the pieces with the separator gives back
   the text"), but it never writes a call, and it does not say whether `concat` takes the
   separator. The join law of step L3.2 needs a join with a separator. QUESTIONS.md entry A105 (zed commit 09fcb30).
2. **Flattening a list of lists** (`concat` in Haskell, `flatten` in OCaml and Scala). The fold
   `xss.foldl([], (a, x) -> a ++ x)` copies each prefix and costs O(n²) on a plain array, and
   `xss >< (++)` is offset concatenation, which is associative, so it folds as a tree in
   O(n log n) total (the rope of step L5.2 makes it O(n)). That spelling exists, so no new word
   is asked for; A105 asks whether `concat` also covers it.
3. **Interspersing a general list** (`intersperse`). `for i in 0..<(2 * xs.count - 1) { if i % 2
   == 0 { xs[i / 2] } else { sep } }` writes it with no word. No entry: a composition exists at
   the same cost.

Words that the prelude units use and DESIGN does not define (`.filter`, `.contains`, `.sortBy`,
`.fold(init, f)` on a level, `.keys`; step S.1g, plan row PRELUDE-words) are that row's work.
`zed/prelude/iteration.zed` also calls `.reverse` on a list, which is not a DESIGN word either;
DESIGN writes the reverse as the composition in section 1; the PRELUDE-words row now lists
those two sites (this row does not edit `iteration.zed`).

## 10. What builds what

- MAP-run (plan row): `fam`, `discard`, the identity `reindex`, the serial `gen` and `fold`,
  `map`, `.where`, lookup, `for`, `><`, `.foldl` / `.foldr`.
- REMAP-run: the general `reindex`, `group`, `as` / `into`, `rekey`, `flatMap`, `tag`,
  truncation.
- FP-ops-run (this row): ranks, the sorted view in key order (L3.4), scans, `.any` / `.all` /
  `.find`, `count` / `min` / `max` / `sum` / product as folds, `split` / `lines` / `concat`,
  `++`, `zip`, `scan`, `.chunkBy`, `sort` / `.orderedValues`, `take`, `drop`, `slice`,
  `takeWhile`, `.first` / `.last`, `.minBy` / `.maxBy`, the reverse of an order (L5.1c).

Built by FP-ops-run piece 1 (2026-11-15): `.any`, `.all`, `.find`; `count`, `sum`, `.reduce`
by `(+)`, `(*)`, `(&&)`, `(||)`, `max`, `min`; `.foldl` / `.foldr` over a level of any keys
(so their use of the sorted view of L3.4 is the key order of the level, walked by entry);
`.first` / `.last`. The rest moved to four rows, each with its failing tests in
`tests/steps/l03_15a_fp_ops_run/cases.rs`: FP-ops-strings (`split`, `lines`, `concat`),
FP-ops-order (`sort`, `.orderedValues`, `take`, `drop`, `slice`, `takeWhile`, `.minBy`,
`.maxBy`, the reverse of an order), FP-ops-concat-zip (`++`, `zip`) and FP-ops-scan (`scan`,
`.chunkBy`).

Built by FP-ops-scan (2026-11-16): `x.scan(op)` by the operators `.reduce` takes, each entry
the fold of its prefix grouped by the canonical tree of DESIGN sec:reduction item 1, so the
last entry is `x >< op` on floats too; `.chunkBy(f)` with the runs of equal `f` value under
their index and the entries keeping their keys. `scanr` (a scan reading the reverse of an
order) waits on FP-ops-order.

Built by FP-ops-concat-zip (2026-11-16): `++` on lists and `a.zip(b)`, so `zipWith` and
`unzip` above are compositions that run. A `zip` the checker cannot show has equal keyspaces on
both sides is refused, with a repair over the ranks both lists hold (rows ZIP-count-facts and
RANGE-literal-keys widen what it can show).

The status of each of these is in the plan rows and in STATUS.md.
