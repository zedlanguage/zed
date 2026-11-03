# Gaps between the compiler's Rust and Zed

This file lists what the Rust compiler relies on that Zed lacks or expresses differently, so
that row S of DESIGN.md (the compiler rewritten in Zed₀) meets no surprises. It was started by
item T13 of docs/plan_dag.md at commit f425b32 and spec commit cb3d910. Step L6.17 reads it.

**Upkeep.** Each step, once its tests pass, adds an entry here for every Rust construct it
relied on that Zed lacks. Line numbers go stale as code is rewritten (T2, T11), so every
citation also names the function. A gap closes when DESIGN.md gains the form it needs; delete
the entry then, in the same commit as the step that closes it.

## What the audit found

The Rust is 32,508 non-blank code lines without comments or tests. No part of it needs a
redesign of the language (inferred from the catalog below), and most constructs rewrite
locally. Ten gaps need a decision, because Zed₀ as specified has no form for them or
the form it has may not meet the cost the compiler needs:

| Gap | Rust construct | Sites | Class | Blocks | Proposed fix |
|---|---|--:|---|---|---|
| 1 | Identity: address-keyed memos, pointer equality, cached digests | 33 | missing | S.3, S.4 | Content digest as a field; `==` shortcut in the runtime |
| 2 | Shared memo and intern tables across pure calls | 52 | workaround | S.3 | Digests from gap 1; state receivers for the rest |
| 3 | Lazy once-only cells and tied recursive types | 27 | workaround | S.3 | Table of definitions keyed by id |
| 4 | Bit operations, float bits | up to 192 | missing | S.2, S.3 | Specify the bit words at L1 |
| 5 | Bytes: spans, binary files, hashing input | 95 | missing | S.2, S.4 | `utf8`, a byte file port, or drop the binary formats |
| 6 | Command line, computed output paths, exit status | 9 | missing | S.5 | `Args` port, `Files` writes, an exit value |
| 7 | Scalar to and from code point | 18 | missing | S.2 | Two L1 words |
| 8 | Abort on a broken invariant, and unproved indexing | 229, ~1193 | missing | S.2 | A word whose type is empty (conflicts with G5 and line 711), or an atom in each codomain |
| 9 | Key range queries on ordered maps | 9 | missing | S.3 | `before` and `after` |
| 10 | File import cycles | 3 cycles, 5 parent/child groups | Rust must change | S.2 | Move definitions in five, merge files in three; no Zed change |

Two more are in the workaround class and matter because of their cost, not their syntax: gap 11
(mutation, which depends on step L6.13 keeping updates in place) and gap 12 (early exit).

**ZED0.md is out of date.** Its section "Gaps found" says there is one, the Cranelift ports.
Gaps 1, 4 to 9 above are further gaps. In particular its Part B lists `bitAnd`, `bitOr`, `bitXor`
and `shl` as provided at L1 (ZED0.md line 48). DESIGN.md does use them (lines 589, 695, 2408), but
they are missing from the words table (line 3343) and from `Prim` (`zed-kernel/term.rs:18`), and
only `shl` has stated semantics (gap 4). The same row writes `%` by `2^32`; the grammar has neither
operator (lines 3087, 3090, 3123), so this is `mod 2 ** 32`. ZED0.md line 47 assigns lexing by code
point to the `String` functions, which provide no word for it (gap 7). Part B says nothing of
bytes or arguments. This item writes only this file, so ZED0.md stands unchanged until step S.1,
which should take its list from here.

**The claim most likely to be wrong** is gap 11's: that primed receivers and `*.` cost O(1) per
update on a compiler state struct. That rests on step L6.13, which is not built, so the claim
is inferred. Everything in the class "workaround" that names L6.13 falls with it.

## Method

A scanner written for this audit (Dart, not committed; this item adds one file) blanked comments
and string contents, removed `#[cfg(test)]` and `#[test]` items, and counted about 165 regular
expressions on the rest of `crates/*/src`, recording file, line and enclosing function. Then
each low-count construct was read at every site and each large one sampled.

- Each statement below is marked: **confirmed** means read in the code or in DESIGN.md at the
  citation; **inferred** means reasoned, and says what would confirm it.
- Counts are confirmed as counts of pattern matches, not exact parses. Three are upper bounds:
  `bitop_call` includes `&` and `|` on `Type`, `closure` a few patterns, `or_pattern` arms
  spanning lines. `let_else` and `slice_pattern` can miss multi-line forms. The first run
  over-counted `>>` in nested generics and `||` as closures; both patterns were corrected and
  sampled before these numbers were taken.
- Same-scope rebinding counts plain `let name` only, not names inside tuples.
- `let_mut` is 871: 826 matches of `let mut`, plus 45 `let` tuple patterns holding a `mut`, each
  counted once however many `mut` names it holds.
- Gap 10 comes from a second scanner (also Dart, not committed), which resolves each `use` and
  each qualified path to the file defining the item, following `pub use`. It finds 8 strongly
  connected components among 76 files. Since neither scanner is in the repository, the counts
  cannot be reproduced from it; committing them is the author's call.
- `crates/zed-cert` has no code (a 5-line stub). `tests/` is not ported and was not audited.

The classes: **missing**, Zed₀ has no form and DESIGN.md needs one. **Workaround**, a form exists
but with a different shape, or its cost depends on a named step. **Mechanical**, a local rewrite.
**Retained**, stays in Rust by DESIGN.md. "Zed₀" means L1–L6, per zed/compiler/ZED0.md.

## What stays in Rust

Confirmed from S.4 and sec:checking_in_zed (DESIGN.md line 1040): compiled programs keep the
Rust runtime's scheduler and allocator, and primitive operations stay built in. So `zed-rt`
(536 code lines) and the `extern "C"` hooks of `zed-native/src/hooks.rs` (27 `extern` matches:
`rt_arg`, `rt_node`, `rt_inc` and others at `addresses`, line 110) stay. The single `unsafe`
function `run` (`zed-native/src/lib.rs:70`, a `transmute` of JIT code) stays too. Its one
`#[repr(C)]` (`Word`, `zed-rt/src/heap.rs:25`) stays.

`zed-native/src/codegen.rs` moves at S.4. It uses 28 distinct Cranelift instruction builders in
72 calls, plus 8 Cranelift type paths: that is the size of the built-in port set, already
planned at S.4.

External crates: `num-bigint` goes, since `int` is unbounded, and `num-integer` and `num-traits`
(`gcd`, `num.rs:34`; `Euclid`, `eval.rs:20`; `ToPrimitive`, `value.rs:15`) go with it. `imbl` goes: `OrdMap` and `Vector`
are a family and a `Seq`. `blake3` and the three `unicode-*` crates need Zed tables or built-ins;
see gaps 4 and 7. `insta` is tests only.

## Gaps that need a decision

### Gap 1. Identity (missing)

Zed forbids it outright: "Identity is never a memory address" (DESIGN.md line 190, confirmed),
and no program reads an address (line 1474). The compiler relies on addresses for speed in
three ways, all confirmed:

- **Memo keys.** `key` (`zedc/store/preimage.rs:572`) casts a term and a scope to addresses, and
  every memo of `Memo` (line 580 on) is keyed by the pair. Two equal terms at different places
  are deliberately different keys.
- **Equality shortcuts.** `Arc::ptr_eq` or `Rc::ptr_eq`, 6 sites: `Text::eq`
  (`zed-kernel/text.rs:136`), `Type::cmp` (`zed-kernel/types.rs:45`), `Row::cmp`
  (`types.rs:253`), `Premises::extend` and `Premises::eq` (`zedc/store/cell.rs:90`, `:152`),
  `Cx::power` (`preimage.rs:1188`).
- **Hand-written equality and order.** 12 `Ord` and 12 `PartialEq` impls (`Type`, `Row`, `Rec`,
  `Bdd`, `Part`, `Expr`, `Text`, `Rope`, `Shown`, `Rat`, `F64`, `Value`, `Premises`), and 2 of
  `Hash`. Zed's `==` and natural order are structural and cannot be replaced by a program.
  `Rec` compares by `id` (types.rs:152), and `Bdd` nodes by an interned number.

This matters beyond style. Terms and types are DAGs with heavy sharing. A structural `==` or
hash walks a DAG as a tree, so it takes exponential time on the depth without a shortcut (the
rule of the memory note on DAG traversal). `Type::digest` and the pointer test are what prevent
that today. Every visited set in a Zed port faces the same problem.

Candidates (nothing can be run, since Zed₀ is not complete; scores are by reasoning):

| Solution | Empirical result | Score | Reasoning |
|---|---|--:|---|
| Content digest field in each node (`Term`, `Type`, `Bdd`), built from children's digests with a strong hash; keys, memos and equality read the digest; runtime `==` also tests pointers first, invisibly | not run | 9 | Deterministic, matches the fact addresses of step L7.6, needs no threaded table, O(1) compare; invisible shortcut is legal since no program can observe it. Costs a hash per node; a false equal needs a hash collision, which content addressing already accepts |
| Number each node by a threaded counter; state receiver owns the arena; keys are ints | not run | 7 | Exact, and is what `Bdd` does now, but every type operation becomes a state method, so all of `Type`'s pure algebra changes shape (gap 2) |
| Key by provenance keypath | not run | 5 | The spec's own identity (line 190), right for "this place" memos like `preimage.rs`, but keypath length grows with depth, so a compare is not O(1) |
| Language guarantee that `==` is O(1) on shared values, by global hash-consing in the runtime | not run | 4 | Cleanest source, but costs every program, and is a schedule-visible cost model promise |
| Add an `identity` word | not run | 0 | Contradicts line 190 and determinism |

Recommendation: the first, with the place-keyed memos of `preimage.rs` using a number assigned
to each term when it is built (`key` needs place, not content). Combine with a runtime pointer
shortcut in compiled `==`, which DESIGN.md should state as an allowed representation fact. The
Rust can adopt digest keys now where equally efficient, which would shrink this gap before S.3.

### Gap 2. Shared tables across pure calls (workaround)

Confirmed: `RefCell` 52 matches, in `Memo` (preimage.rs:580 on) and the `thread_local!` tables
`TUPLES`, `MORPHISMS` (`zed-kernel/types/bdd.rs:65`), `MEMO` (`types/empty.rs:44`), `EMPTY`, `TOP`
(`types.rs:335`), `ROUNDED` (`zedc/store/interval.rs:17`), plus `STATE` (`zed-native/hooks.rs:60`,
retained). Two `AtomicU64` counters issue fresh ids: `Type::rec` (types.rs:375), `Bdd::node`
(bdd.rs:108). Neither has a form: Zed has no global state, and a closure captures values
(line 1333). `@memoized` does not help: it is an assertion on the plan, "never a request that
changes it" (step L18.2), and L18 is above Zed₀.

Workaround. A function that reads its own name is a definedness fix (sec:grammar, Function), so
recursion memoizes within one fix: `define_on_demand` (`eval.rs:1129`) does this today. That
covers `Cx`'s memos during one translation (inferred; confirm by writing `lin_at` in Zed). Tables
that must outlive a call, like `MEMO`, go in a state struct passed by primed receiver, or vanish
with gap 1's digests, which remove `TUPLES` and `MORPHISMS` altogether. The undo logs
(`Cx::forget`, `preimage.rs:871`; `Ck::log`, `check/mod.rs:240`) simplify: with persistent maps,
keep the old value (the same holds for the Rust; a candidate for T11).

`Type`'s `&`, `|`, `!`, `-` write to these tables through operator syntax, which is why the
choice in gap 1 decides this one.

### Gap 3. Lazy cells and tied recursive types (workaround)

Confirmed: `OnceLock` or `OnceCell`, 27 matches. `Rec` (`zed-kernel/types.rs:142`) holds
`body: OnceLock<Type>` and `make: Box<dyn Fn() -> Type>`, computes a recursive type's parts on
first use (`Type::p`, line 392), and ties a cycle through closures. `Group::instance`
(`types/rec.rs:296`), `Cones::free` (`zedc/elab.rs:93`), `Program::main` (`zedc/run.rs:49`),
`Shown` (types.rs:118) and `Text::flat` (`text.rs:24`) cache in place inside a shared value.

Zed values are immutable with no cell, and a function field re-evaluates on each call. Cyclic
data lives in two sanctioned forms, arenas or regions and id-indexed graphs `Id ->? Node`
(line 1399, confirmed), which L6.13 builds. Fix: the second form. A recursive type is `#rec(id)`
with its parts in an indexed definition `parts[id] = …`, evaluated on demand (L6.1, L6.4). `Text` needs no port: `String` ropes are L6.16. Cones become
an indexed definition. Cost: inferred O(1) per read if the definedness table is stored, to be
measured at S.3.

### Gap 4. Bit operations (missing)

Confirmed: line 589 defines `shl(x, k)`: `k : int[0..]`, value `x · 2^k` on the unbounded `int`,
with a width enforced where one is written. Line 695 uses `bitAnd`, `bitOr`, `bitXor` and `shl`,
line 2408 lists them as named functions, and `zed/fences/examples.md:78` uses `shl`. The gap: the
words table (line 3343) lists none of them, `Prim` (`zed-kernel/term.rs:18`) has none, and only
`shl` has semantics.

Rust uses: `<<`, `>>` 42; `&`, `|`, `^` on integers up to 115; `wrapping_*` and `overflowing_*` 14;
`rotate_left` 1 (`mix`, types.rs:79); `count_ones`, `leading_zeros`, `trailing_zeros` 7 (`Ck::resolve`
`check/mod.rs:1224`, `round` `exact.rs:61`, `float.rs:55`); bit masks as
sets (`Carrier::of_mask`, `check/ty.rs:340`). `blake3::Hasher` is used at 6 sites (`address_at`,
`canon/mod.rs:196`, and others).

Fix: add to the L1 row of the words table `shl` as line 589 specifies it, and semantics for
`bitAnd bitOr bitXor bitNot shr popCount leadingZeros trailingZeros` on `int[0..]`, so that a
negative operand is a type error. `bitNot`, `leadingZeros` and `rotl` depend on a width, so each
takes it as an argument. Shift counts stay domain-typed and are never masked (line 589), so a
wrapping shift is written `shl(x, k) mod 2 ** w`. `rotl` and `rotr` are new words.

Wrapping arithmetic is written `(a * b) mod 2 ** 64`. Line 589 already permits computing that in
wrapping `w`-bit arithmetic when the result domain is known statically and spans at most `2^w`
integers (see also line 3691), and step L3.13 builds it, with a test at `mod 2 ** 63`. What remains
is to confirm it for `mix` (`types.rs:77`), where each product is its own expression, since
`bitXor` and `rotl` are not in line 589's list of operators. Also, line 589 lists the
representations as i8…i64, else big-integer, and `int[0..<2 ** 64]` does not fit `i64`, so a hash
would be stored as a big integer. Fix: state that a domain spanning at most `2^w` integers is
stored in one word. Both points are inferred; the test is a scaling run of `mix` at S.3. Carrier masks become sets of atoms. BLAKE3 in Zed
is then ZED0.md's plan; if a stage build shows it too slow, a primitive is allowed by line 1040.

Also float bits, no word: `to_bits`, `from_bits` 13 matches (`Out::value`, `canon/serial.rs:78`;
`W::value`, `zir/binary.rs:122`; `Exact::float`, `num.rs:151`; `exact_sum`, `exact.rs:94`;
`Width::holds`, `store/float.rs:39`). Content addresses hash float bits, so this cannot be avoided.
Fix: L1 words `f64Bits : f64 -> int[0..<2 ** 64]` and its inverse, NaN being canonical first.

### Gap 5. Bytes (missing)

Confirmed: a `String` is scalars (line 152), and `Files` gives text or `#ioError` for a file not
UTF-8 (L1.19). At L1 an output is `Lines`. `bits` and `endian` facets are L7. No word gives a
string's UTF-8.

Rust uses: spans are byte ranges (`Span`, `zedc/lex/mod.rs:21`) and `Lines::new`
(`source.rs:180`) indexes bytes; `.as_bytes()`, `.bytes()` 48; `&[u8]` 21; `from_utf8` 9; byte
literals 20; `to_le_bytes` and `from_le_bytes` 17 (`Out::word`, `canon/serial.rs:31`; `W::n`,
`zir/binary.rs:71`); raw reads and writes (`command_inner`, `run.rs:603`, `:654`; `Disk::get`,
`run.rs:445`).

Fix, three parts. (a) Spans become scalar offsets: mechanical, as ZED0.md says "lex by code
point", but the columns of diagnostics must agree with Rust at S.2, so the differential test
decides. (b) An L1 word `utf8 : String -> [byte]`, and `int` to little-endian bytes as a
library function, which hashing needs. (c) For files, the binary ZIR and wave records
(`zir/binary.rs`, `Record::to_bytes` at `run.rs:476`) either get a `Bytes` file port, or use the text form that
`zir/text.rs` already has. Recommended: the port, since content-addressed caches should not pay
for text parsing; the choice can wait until S.4.

### Gap 6. Command line and outputs (missing)

Confirmed: `main` (`zedc/main.rs:9`) reads `std::env::args`, and `command_inner`
(`run.rs:583`) dispatches on them. No DESIGN.md port gives arguments: `main`'s parameters are
ports, an input is `Lines` or `Files`. A `Lines` output is bound by the driver to a fixed path, so
writing to a path computed at run time (`run.rs:654`, `:657`) has no form. Exit status is fixed
by L1.19 as 0, 1 or 2, by the host; the Rust returns its own status.

Fix: an `Args` input port (L1) as `[String]`, a `Files`-like output `path -> String | Bytes`,
and a status from `main`'s result. Alternative: keep a Rust driver as the stage root that decodes
arguments into port bindings; this needs no spec change but leaves Rust in stage2, against S.
Recommended: the ports.

### Gap 7. Code points and text tables (missing)

Confirmed: there is no character type, and the L1 string words are `len`, `lower`, `upper`, `trim`,
`++`, the `String` and `f64` casts (`Prim`, `term.rs`), and `split`, `lines`, `concat` at L3. Text
is one-element strings ordered by code point (line 368), so comparing `c >= "a"` works, but no
word turns a scalar into its number or back. `\u{…}` decoding (`lex/string.rs:149`, `:292`) needs that, as does
`zir/text.rs:983`. `char` 18, `.chars()`, `.char_indices()` 37.

Fix: L1 words `codePoint : String -> int` and `scalar : int -> String | #invalid`. The rest
(`starts_with`, `strip_prefix`, `split_once` and similar, 86 matches) are ordinary standard library
functions in Zed (step L2.10), needing no spec change. `is_xid_*`, script and NFC data
(`unicode-ident`, `unicode-script`, `unicode-normalization`, in `lex/name.rs` and `source.rs`) are
tables in Zed, or built-ins for now. Substring slices are O(1) in Rust as `&str`; in Zed the cost
is that of `slice` on a rope, inferred O(log n), and 150 range slices exist across all types.
A recursion on `&xs[1..]` would become O(n log n) in total, not O(n); check at S.2.

### Gap 8. Broken invariants and unproved indexing (missing)

Confirmed: `.expect` 150, `unreachable!` 63, `panic!` 3, `assert!` 3, `debug_assert!` 5, `.unwrap()`
5; DESIGN.md has no word that stops with a message. Failure is data, and `@invariant` is L15.
Also about 1,193 index expressions panic in Rust on a bad index, whereas `v[i]` in Zed has
`#notFound` in its type unless the domain proves `i` in range.

Two options, and the choice is the author's:

| Solution | Empirical result | Score | Reasoning |
|---|---|--:|---|
| An L1 word `bug(message)` of empty type, which stops the program and reports the message and its provenance | not run | 7 | Keeps result types small, and the empty type keeps it out of unions. Needs the spec changes listed below |
| An atom `#bug(String)` in the codomain of each function that can reach a broken invariant; indexing is `v[i] else #bug("…")` | not run | 6 | Needs no spec change. Cost: the atom enters the result type of nearly every function, since propagation is declared in the codomain, so signatures and arrows grow and every caller carries it |

With either, indexing that the domain proves in range needs neither. The word `bug` contradicts
DESIGN.md at these places, which the author would have to change (each confirmed):

- G5 (line 21): out-of-bounds indexing and unhandled failure "cannot be written". `bug` is a
  written stop that the compiler does not rule out.
- Line 711: the only run-time tests are those the program writes, and "each one's failure is a
  member of the result type". The failure of `bug` is not.
- Line 3710: "no program writes" the empty type. The type also has no spelling: `!_` appears
  nowhere in DESIGN.md, and a message must print types as a user can write them.

Reachability of such stops is a fact tests can report on. The rule "failure is data" holds for a
program's input; this word would be for faults in the program itself.

`catch_unwind` and `resume_unwind` (`Evaluator::run`, `eval.rs:362`, and `on_stack`) only restore a flag, and
`on_stack` (`eval.rs:290`) exists only to run with a 1 GiB stack (the marker `Stack`). Both vanish.
Depth moves to the runtime: L6.7 tests a `.fold` over a 100,000-node chain, and compiled
recursion on input-sized depth needs a growable stack in the retained runtime (inferred; not in
L6.13). `Drop` for `text::Node`, `Rope` and `Premises` exists to avoid deep recursion in release,
so compiled reference counting must also release iteratively.

### Gap 9. Key range queries (missing)

Confirmed: `.range` on `BTreeMap` or `BTreeSet`, 9 sites: `Tables::uses_in` (`elab.rs:308`),
`Formatter::take` (`format.rs:151`), `same_terms` (`affine.rs:423`), `IntervalSet::snap`
(`interval.rs:347`), `below` and `above` (`interval.rs:476`, `:483`). The substrate supports
O(log n) (L5.8), but the L5 words `slice`, `take` and `drop` are by rank, not by key, and no
word finds the greatest key at or below `k`. `.where(k -> k <= v).last` is O(n) unless the
compiler recognizes it, which no step states.

Fix: L5 words `m.upTo(k)` and `m.from(k)`, each an ordered restriction in O(log n), so that
`.first` and `.last` give neighbors. `BinaryHeap` (`topo`, `elab.rs:1533`; `IntervalSet::cap`,
`interval.rs:266`) is then an ordered set with `.first` and a `patch`.

### Gap 10. File import cycles (Rust must change)

Zed forbids a cycle between files, while recursive types and definitions stay unrestricted within
a unit (line 733). The repairs are to move what both sides use into a unit both import, or to
merge the units (line 1244). The import graph, with re-exports resolved to the defining file, has
8 strongly connected components: 3 cycles between modules and 5 parent/child groups. Each edge
below was read at its citation. Paths are relative to `crates/`, with `src/` dropped.

| Component | Edges | Fix in Rust |
|---|---|---|
| `zed-kernel`: `error`, `family`, `value` | `error.rs:9` `Keypath`, `:44` `Value`; `family.rs:14` `KernelError`, `:15` `Value`; `value.rs:17` `Family` | Merge. `Value` and `Family` (`family.rs:24`) are one recursive type, so they share a unit. `Keypath` (`family.rs:18`) is `Vec<Value>`, `KernelError` holds `Value`, and `Family`'s fallible methods (`union`, `family.rs:206`) return `KernelError`, so moving `Keypath` alone leaves a cycle; all three go in one file |
| `zedc`: `store/interval`, `store/lattice` | `interval.rs:14` `Landmarks`; `lattice.rs:13` `End`, `IntervalSet` | Move `Landmarks` (`lattice.rs:21`) to its own file: it holds only `i64` and `Value`, and its methods use neither `End` nor `IntervalSet` |
| `zedc`: `check`, `elab`, `stage` | `check/mod.rs:44` `Tables`; `elab.rs:31` `check`, `Fit`, `Info`, `:119`, `:124` `stage::free`; `stage.rs:26` `Unit`, `:336` `Def` | Move `Def`, `Test`, `Unit`, `Tables` (`elab.rs:37`, `:51`, `:66`, `:181`) and what `Tables` calls (`topo`, `in_tests`) to a file below all three. None holds a `check` type. `Unit::close` (`elab.rs:76`) stays above `stage` as a function, since it needs `Cones` |
| `zed-kernel`: `types`, `types/bdd` | `types.rs:36` `Form`, `Part`, `:1297` `bdd::Literal`; `types/bdd.rs:39` `Morphism`, `Op`, `Row`, `mix` | Move `Op` and `mix` to a leaf file, and the `Literal` impls of `Row` and `Morphism` with the tables `TUPLES` and `MORPHISMS` (`bdd.rs:65`–`:78`) into `types`. `Bdd<A>` and `Part<A>` are generic in `A`, so no recursive type crosses the two files |
| `zedc`: `canon`, `canon/serial` | `canon/mod.rs:206` `serial::def`; `canon/serial.rs:13` `Def` | Move `Def` and `Facet` (`canon/mod.rs:58`, `:46`) to a leaf file |
| `zedc`: `zir`, `zir/text` | `zir/mod.rs:342`, `:414` and 11 more, `text::spell`, `text::edge`, `text::pattern`; `zir/text.rs:36` the node types, `any_domain`, `kind_name`, `:189` `op_name` | Move the node types and the three naming functions to a leaf file that `validate` (`zir/mod.rs:386`) and `zir/text.rs` both import |
| `zedc`: `lex`, `lex/comment`, `lex/number`, `lex/string` | `lex/mod.rs:17` `Holes`, `:165`, `:194` `comment::comment`, `:204` `number::number`, `:208` `string::string`; `comment.rs:2`, `number.rs:21`, `string.rs:24` `Error`, `ErrorKind`, `Span` and others; `string.rs:24` `lex_from`, `comment` | Move `Span`, `Tok`, `Part`, `Token`, `ErrorKind`, `Error` (`lex/mod.rs:21`–`:107`) to a leaf file, which frees `comment` and `number`. Merge `lex_from` and `string`: `lex_from` (`lex/mod.rs:181`) calls `string::string`, which calls `lex_from` for a hole (`string.rs:99`), and mutual recursion stays within a unit |
| `zedc`: `ast`, `ast/stmts`, `ast/types` | `ast/mod.rs:21`, `:22` the re-exports; `ast/stmts.rs:6` `Builder`, `Expr`, `Param`, `Type` and others; `ast/types.rs:6` `Builder`, `Error`, `Expr` | Merge all three. `ExprKind` holds `Param`, `Type`, `Pattern` and `Stmt` (`ast/mod.rs:80`, `:92`, `:101`, `:107`), while `Param` (`ast/types.rs:65`) and `StmtKind` (`ast/stmts.rs:26`) hold `Expr`, so these are recursive types. `Builder::node` (`ast/mod.rs:347`) and `Builder::block` (`ast/stmts.rs:91`) are mutually recursive too |

A ninth component in the scanner's first run, `lib` with `term`, came from `use super::*` inside
the inline module `term::build` (`term.rs:317`), and is not a cycle. Zed units are files, so all of
this is a Rust refactor, cheap and safe to do now.

## Workarounds that depend on cost

### Gap 11. Mutation (workaround)

Confirmed counts: `&mut self` 431; other `&mut` 572; `let mut` and `let` tuples with `mut` 871; field assignment 144; index
assignment 114; compound assignment 236; `push` 529, `pop` 73, `insert` 206, `remove` 61, `entry` 47;
`iter_mut`, `get_mut`, `or_default` and similar 110; `mem::take`, `replace`, `swap` 50; `FnMut` 27.

Forms, confirmed in DESIGN.md:

- `&mut self` becomes a method with a primed receiver, whose fields are the frame (line 2387),
  called by `c*.m(a)` (line 2395). `Ck` (`check/mod.rs:234`), `Elab`, `Evaluator`, `Gen` port
  this way. It needs L6 (step L6.3), which Zed₀ has.
- A `let mut` outside a loop becomes new names. In a loop, `mutable` and `x'`, or a `foldl`.
- Field and index writes become `with { … }` (L2) and `patch`, or a scatter `hist[i] <- e` (line 437) in a frame.
- `&mut` on a non-receiver argument returns the new value. `each_edge_mut` (`zir/canon.rs:285`)
  and `rename` (`zir/lower.rs:1196`) become maps. A visitor taking `&mut dyn FnMut` (`visit`,
  `zir/lower.rs:951`; `Formula::walk`, `presburger.rs:471`) becomes a fold with an accumulator.
- Open point: whether `*.` reaches a nested receiver such as `self.classes[i]*.m()`. DESIGN.md
  says it "needs a state receiver" and does not define that for a nested path. Fix: define it.

Cost: `blocks` (`product.rs:492`), `weak_topological_order` (`wto.rs:83`) and the union-find of
`Ck` need O(1) writes to dense arrays. In Zed that is reuse in place, by provable last use
(line 1397, step L6.13). If reuse fails, an array update is O(n) or a tree update O(log n), and
the first turns O(n) work into O(n²) silently. `@noalloc` is L18. Fix: at S.1, add a compiler
report of each `patch` or `with` on a threaded state that did not compile in place, and scaling
tests at n and 8n over the ported union-find and worklists.

### Gap 12. Early exit (workaround)

Confirmed: a block exports once and a second `return` is an error (line 174); `if` needs `else`;
`for` has no `break`; `break` exists only in `loop`; no `continue` exists. Counts: `return` 792, of
which 196 inside a loop body; `?` 1015, of which 276 in a loop; `continue` 110; `break` 38; labels 2;
`let … else` 122.

- `?` is the easy case. Declared propagation (line 467) lets an atom flow out through the
  codomain, so most `?` simply vanish once `Result<T, E>` becomes `T | #e(…)` and `Option<T>`
  becomes `T | #none`. Only `Err(String)` needs a chosen atom. **20 nested types** (`Option<Option<…>>`
  at `Part::eval3_pinned`, `bdd.rs:587`, and `witness`, `preimage.rs:2264`; `Result<Option<…>>` such as
  `satisfiable`, `presburger.rs:611`) need distinct atoms, since unions flatten.
- Guard `return`s outside loops (596) become `if`/`else` or `match`. `Elab::call_value` and
  `Ck::apply_one` hold 14 each, so depth grows: split into functions. Mechanical but large.
- A `return` or `?` in a loop becomes `loop` with `break e`, or `where(…).first`. The Rust uses `.any`, `.all`
  172 times and `.find`, `.position` 87 times. These words are undefined: the prelude already calls
  `.all` and `.any` (`zed/prelude/cost.zed:47`, `:48`, `:59`, `:64`; `revision.zed:89`), as does
  line 1007, but no words table lists them and no prelude file defines them. Add them to the words
  table. That they stop early relies on demand (inferred from line 141).
- `continue` becomes `for … where`; the two labels (`Search::retest`, `empty.rs:303`;
  `Search::narrow_tuples`, `:349`) become a helper with `.all`.

### Further points of cost

- **Overflow as refusal.** `Over` in `presburger.rs` is returned when i128 arithmetic overflows,
  and `checked_*` (33) detect it. Zed's `int` is unbounded, so a direct port never refuses and could
  differ from the Rust oracle at S.3, or run far longer. The bound must be ported as an explicit
  test (`MAX_BITS` likewise, `num.rs:19`).
- **`as` casts** (272): most go, but a truncating cast must become `mod 2 ** k`.

## Mechanical rewrites

Confirmed against sec:grammar; counts in the appendix.

| Rust | Count | Zed |
|---|--:|---|
| `Arc`, `Rc`, `Box`, `.clone()`, lifetimes | 548, 37, 76, 1098, 458 | Vanish: values are immutable and shared |
| `format!`, `write!`, `.to_string()` | 490, 215, 105 | Interpolation and `String(…)` arrows; `Display` (42 impls) becomes overloads of `String` |
| `#[derive]` | 223 | Equality, order, update are structural and free; `Default` becomes a written value |
| `impl From` (14), `Deref` (2), `AsRef` (1), `IntoIterator` (1) | 18 | Named functions |
| `impl Not`, `BitAnd`, `BitOr`, `Sub` on `Type`, `Neg` on `End` | 9 | Named `complement`, `meet`, `join`, `minus`: `&` and `|` are type operators only (line 2408); overloading `-` needs its axioms (line 2778) |
| Traits: `Lattice` (8 impls), `Lookup`, `Mark`, `Literal`, `Equations` | 5 traits | `interface` is L10, above Zed₀. Pass a record of functions. `L::bottom()`, dispatched on a return type, becomes a field. Single-parameter cases become overloads |
| `dyn Fn`, `FnMut`, `impl Fn`, `fn` pointers | 37 `dyn` | Function values. `dyn Lookup`, `dyn Read`, `dyn Write` become ports |
| Generics | 67 fns, 38 types | Implicit by inference (line 537), and `type N(X)` at L2 |
| Tuple structs | 20 | `#sym(String)` for a distinction: same-shape structs are one type (line 2774). `Sym`, `Key`, `ContentAddress`, `Card` need this |
| Privacy: `pub`, `pub(crate)`, private fields | 1163 `pub` | `local` hides a declaration in its file; a field cannot be hidden, so an invariant such as `Row`'s is held by convention |
| `if let`, `while let`, `matches!`, `let … else` | 309, 48, 115, 122 | `match`, `is`, `else` |
| Or-patterns | 180 | No grammar form. `is #a \| #b` works for atoms; literal-set types are L10, so strings and ints take `where x in {…}`; arms binding a name in each branch are repeated. An or-pattern in sec:grammar at L2 would be a small addition worth making |
| `x @ pat` | 10 | `x is T` covers type tests; a nested binding needs a second `match` |
| Slice patterns | 43 | Test `.len`, then index |
| Same-scope `let` rebinding | 44 | Rename: rebinding in one scope is an error (line 2385) |
| Integer division: `rem_euclid`, `div_euclid`, and their `checked_` forms | 20, 12, 2 | `mod` and `div`, which are Euclidean (line 589) and give `#divByZero` |
| Truncating `/` and `%` on integers | 16, 22 | `div` and `mod`, since `/` is on float and `rat` only, and truncating variants are library functions (line 589). The results agree when the division is exact (`hull.rs:89`, `num.rs:37`) or the dividend is nonnegative and the divisor positive. Sites where an operand may be negative must be read at S.3: midpoints (`revision.rs:420`, `presburger.rs:1379`), `gcd` (`presburger.rs:839`, `preimage.rs:2533`), parity `k % 2 == 1` (`revision.rs:74`, `:444`), which in Zed is true for an odd negative `k` |
| `saturating_add`, `saturating_mul`, `saturating_sub` | 9, 6, 3 | `saturating_sub` becomes an `if`. The other two guard a machine word and vanish on an unbounded `int`, except for `eval.rs:1385` and `num.rs:61`, where the test against `MAX_BITS` stays as written. In `cost.rs`, costs then no longer stop at the maximum, so a comparison of very large costs can differ from the Rust at S.3 |
| Machine integers (`usize` 760, `i128` 167, `u64` 188, `i64` 206) | | `int` with a domain |
| `Vec`, `HashMap`, `BTreeMap`, sets, `imbl` | 1668, 207, 287, 36 | `[T]`, `K ->? V`, a set is a self-map; keys need a natural order, which excludes NaN-admitting floats |
| `.sort`, `.dedup`, `.retain`, `.truncate`, `.windows`, `peekable` | 27, 12, 9, 17, 7, 13 | `sort`, `.sort(by: le)`, `group`, `where`, `take`, `zip` with `drop`, an index |
| Iterator chains | see appendix | `map`, `where`, `flatMap`, `foldl`, `for`; lazy `impl Iterator` (14) and `from_fn` (2) become families |
| `macro_rules!` | 3 | `rope!` (`types.rs:1129`), `set!` (`check/mod.rs:3691`), `cat!` (`format.rs:516`) become functions |
| `const`, `static`, `const fn` | 58, 13, 1 | Top-level values; rule tables of `fn` (`canon/mod.rs:74`) are records of function values |
| Threads | 1 scope | No parallelism in the compiler: `thread::scope` serves only `on_stack`, and `Send`, `Sync` vanish; no `Mutex` |
| Time, directory listing | 0 | None used |

## Appendix: counts by construct

Non-blank code lines: zed-kernel 6,209; zedc 24,314; zed-native 1,449; zed-rt 536; zed-cert 0;
total 32,508. A site named `X (impl)` is a method signature of `X`, and one named `(item)` is at
item level. A cited line is the first match in that function, and the number after it is the
matches in that function. Paths are relative to `crates/` with `src/` dropped.

| Construct | kernel | zedc | native | rt | total | Largest sites: function `file:first line` (count) |
|---|--:|--:|--:|--:|--:|---|
| `let_mut` | 134 | 693 | 35 | 9 | 871 | blocks `zedc/store/product.rs:501` (21); weak_topological_order `zedc/store/wto.rs:86` (11); Ck::apply_one `zedc/check/mod.rs:3110` (11) |
| `amp_mut` | 215 | 653 | 110 | 25 | 1003 | Ck (impl) `zedc/check/mod.rs:1007` (17); Ck::merge `zedc/check/mod.rs:797` (15); Gen (impl) `zed-native/codegen.rs:136` (11) |
| `amp_mut_self` | 64 | 316 | 36 | 15 | 431 | Ck (impl) `zedc/check/mod.rs:1007` (13); Evaluator (impl) `zed-kernel/eval.rs:827` (7); Ck::merge `zedc/check/mod.rs:797` (6) |
| `compound_assign` | 56 | 166 | 2 | 12 | 236 | Evaluator::eval_node `zed-kernel/eval.rs:573` (10); Doc::broken `zed-kernel/print.rs:480` (7); Doc::write_flat `zed-kernel/print.rs:393` (6) |
| `index_assign` | 12 | 99 | 2 | 1 | 114 | blocks `zedc/store/product.rs:517` (12); Walk::number `zedc/store/iterate.rs:172` (6); weak_topological_order `zedc/store/wto.rs:113` (6) |
| `field_assign` | 29 | 108 | 4 | 3 | 144 | Type::universe `zed-kernel/types.rs:540` (6); Ck::finish `zedc/check/mod.rs:1365` (6); Cell::literal `zedc/store/cell.rs:277` (5) |
| `push` | 92 | 403 | 23 | 11 | 529 | blocks `zedc/store/product.rs:511` (12); Type::show `zed-kernel/types.rs:1199` (11); Cx::summon `zedc/store/preimage.rs:690` (11) |
| `pop` | 23 | 46 | 0 | 4 | 73 | blocks `zedc/store/product.rs:564` (3); raise_region `zedc/zir/lower.rs:1166` (2); Evaluator::discard `zed-kernel/eval.rs:878` (2) |
| `insert` | 68 | 131 | 7 | 0 | 206 | Evaluator::define_on_demand `zed-kernel/eval.rs:1135` (4); Part::go `zed-kernel/types/bdd.rs:572` (4); Search::empty `zed-kernel/types/empty.rs:189` (4) |
| `remove` | 21 | 39 | 1 | 0 | 61 | Search::empty `zed-kernel/types/empty.rs:198` (6); Cx::forget `zedc/store/preimage.rs:875` (4); Row::subst `zedc/store/presburger.rs:879` (2) |
| `entry` | 10 | 36 | 1 | 0 | 47 | blocks `zedc/store/product.rs:510` (2); Evaluator::define_in_rounds `zed-kernel/eval.rs:1099` (2); Elab::new `zedc/elab.rs:387` (2) |
| `refcell` | 16 | 33 | 3 | 0 | 52 | Cx::new `zedc/store/preimage.rs:631` (7); Evaluator::fix_definedness `zed-kernel/eval.rs:1013` (3); Cx (impl) `zedc/store/preimage.rs:835` (2) |
| `cell` | 2 | 2 | 0 | 0 | 4 | (item) `zed-kernel/eval.rs:280` (2); (item) `zedc/store/interval.rs:17` (1); (item) `zedc/store/preimage.rs:622` (1) |
| `borrow_mut` | 18 | 29 | 3 | 0 | 50 | Evaluator::define_on_demand `zed-kernel/eval.rs:1135` (6); relations `zedc/store/preimage.rs:235` (5); Cx::forget `zedc/store/preimage.rs:872` (5) |
| `mem_take` | 14 | 30 | 4 | 2 | 50 | Ck::merge `zedc/check/mod.rs:825` (8); Evaluator::demand `zed-kernel/eval.rs:1171` (4); Ck::finish `zedc/check/mod.rs:1364` (4) |
| `opt_take` | 6 | 7 | 2 | 2 | 17 | Premises::drop `zedc/store/cell.rs:135` (3); Node::drop `zed-kernel/text.rs:71` (2); weak_topological_order `zedc/store/wto.rs:148` (2) |
| `rc` | 16 | 21 | 0 | 0 | 37 | Evaluator::fix_definedness `zed-kernel/eval.rs:996` (4); Evaluator::entry `zed-kernel/eval.rs:1032` (2); Cx::call_prim `zedc/store/preimage.rs:913` (2) |
| `arc` | 148 | 364 | 19 | 17 | 548 | raise_region `zedc/zir/lower.rs:1044` (17); Elab::passes `zedc/elab.rs:455` (8); Elab::call_value `zedc/elab.rs:963` (7) |
| `box` | 15 | 61 | 0 | 0 | 76 | Builder::node `zedc/ast/mod.rs:284` (5); Reader::postfix `zedc/parse/grammar.rs:256` (4); Expr::exact `zed-kernel/types/rec.rs:52` (3) |
| `clone` | 231 | 817 | 28 | 22 | 1098 | rename_first `zedc/canon/binders.rs:264` (28); Lower::term `zedc/zir/lower.rs:501` (25); raise_region `zedc/zir/lower.rs:1051` (20) |
| `ptr_eq` | 3 | 3 | 0 | 0 | 6 | Text::eq `zed-kernel/text.rs:136` (1); Type::cmp `zed-kernel/types.rs:45` (1); Row::cmp `zed-kernel/types.rs:253` (1) |
| `raw_ptr` | 30 | 12 | 14 | 0 | 56 | addresses `zed-native/hooks.rs:110` (14); Part::go `zed-kernel/types/bdd.rs:564` (6); Part::eval3_pinned `zed-kernel/types/bdd.rs:620` (5) |
| `lifetime_param` | 65 | 355 | 38 | 0 | 458 | Ck (impl) `zedc/check/mod.rs:2079` (12); Elab (impl) `zedc/elab.rs:886` (12); Machine (impl) `zedc/zir/memory.rs:558` (7) |
| `trait_decl` | 2 | 3 | 0 | 0 | 5 | (item) `zed-kernel/eval.rs:175` (1); (item) `zed-kernel/types/bdd.rs:58` (1); (item) `zedc/store/iterate.rs:20` (1) |
| `impl_trait_for` | 95 | 55 | 0 | 1 | 151 | (item) `zed-kernel/error.rs:48` (2); (item) `zed-kernel/eval.rs:83` (2); (item) `zed-kernel/family.rs:270` (1) |
| `impl_inherent` | 37 | 94 | 3 | 4 | 138 | (item) `zed-kernel/eval.rs:196` (3); (item) `zed-kernel/family.rs:105` (1); (item) `zed-kernel/num.rs:28` (2) |
| `dyn` | 4 | 32 | 1 | 0 | 37 | Program (impl) `zedc/run.rs:281` (4); command `zedc/testing.rs:240` (2); World::source `zed-kernel/eval.rs:209` (1) |
| `impl_in_sig` | 37 | 55 | 3 | 0 | 95 | Type (impl) `zed-kernel/types.rs:372` (4); Bdd (impl) `zed-kernel/types/bdd.rs:212` (4); Program (impl) `zedc/run.rs:281` (4) |
| `generic_fn` | 27 | 37 | 3 | 0 | 67 | Cx (impl) `zedc/store/preimage.rs:833` (2); Bdd (impl) `zed-kernel/types/bdd.rs:359` (2); Part::restrict `zed-kernel/types/bdd.rs:763` (1) |
| `generic_type` | 9 | 27 | 2 | 0 | 38 | (item) `zed-kernel/eval.rs:158` (1); (item) `zed-kernel/types/bdd.rs:42` (7); (item) `zed-kernel/types/rec.rs:484` (1) |
| `assoc_type` | 13 | 1 | 0 | 0 | 14 | &Type (impl) `zed-kernel/types.rs:1021` (4); Type (impl) `zed-kernel/types.rs:1040` (4); &'a Row (impl) `zed-kernel/types.rs:244` (2) |
| `macro_rules` | 1 | 2 | 0 | 0 | 3 | (item) `zed-kernel/types.rs:1129` (1); (item) `zedc/check/mod.rs:3691` (1); (item) `zedc/format.rs:516` (1) |
| `derive` | 51 | 162 | 3 | 7 | 223 | (item) `zed-kernel/error.rs:12` (1); (item) `zed-kernel/eval.rs:52` (7); (item) `zed-kernel/family.rs:23` (1) |
| `attr_hint` | 0 | 0 | 0 | 1 | 1 | (item) `zed-rt/heap.rs:25` (1) |
| `attr_lint` | 0 | 6 | 3 | 0 | 9 | Ck (impl) `zedc/check/mod.rs:2202` (3); run `zed-native/lib.rs:69` (2); Builder (impl) `zedc/ast/mod.rs:485` (1) |
| `tuple_struct` | 11 | 8 | 0 | 1 | 20 | (item) `zed-kernel/eval.rs:276` (2); (item) `zed-kernel/family.rs:24` (1); (item) `zed-kernel/provenance.rs:25` (1) |
| `struct` | 42 | 146 | 9 | 5 | 202 | (item) `zed-kernel/eval.rs:68` (10); (item) `zed-kernel/family.rs:24` (1); (item) `zed-kernel/num.rs:23` (1) |
| `enum` | 27 | 75 | 1 | 3 | 106 | Ck::derive_into `zedc/check/mod.rs:330` (1) |
| `type_alias` | 7 | 25 | 2 | 0 | 34 | (item) `zed-kernel/eval.rs:91` (3); (item) `zed-kernel/exact.rs:9` (1); (item) `zed-kernel/family.rs:18` (1) |
| `const_item` | 10 | 38 | 1 | 9 | 58 | Word (impl) `zed-rt/heap.rs:36` (9); first_on_cycle `zed-kernel/types/rec.rs:341` (1); Carrier (impl) `zedc/check/ty.rs:296` (1) |
| `static_item` | 9 | 2 | 1 | 1 | 13 | Type::rec `zed-kernel/types.rs:375` (1); Bdd::node `zed-kernel/types/bdd.rs:108` (1); take_sides `zed-rt/rope.rs:105` (1) |
| `const_fn` | 0 | 1 | 0 | 0 | 1 | ax `zedc/axioms.rs:97` (1) |
| `try_op` | 135 | 780 | 78 | 22 | 1015 | Lower::term `zedc/zir/lower.rs:502` (39); Cx::lin_at `zedc/store/preimage.rs:1223` (30); Evaluator::eval_node `zed-kernel/eval.rs:517` (29) |
| `return` | 183 | 577 | 14 | 18 | 792 | Elab::call_value `zedc/elab.rs:949` (14); Ck::apply_one `zedc/check/mod.rs:3135` (14); Type::list `zed-kernel/types.rs:620` (13) |
| `continue` | 31 | 78 | 0 | 1 | 110 | Ck::apply_one `zedc/check/mod.rs:3120` (8); blocks `zedc/store/product.rs:543` (4); Bdd::forced `zed-kernel/types/bdd.rs:249` (4) |
| `break` | 6 | 30 | 2 | 0 | 38 | Parser::m `zedc/parse/mod.rs:279` (3); Evaluator::define_in_rounds `zed-kernel/eval.rs:1090` (2); Evaluator::generations `zed-kernel/eval.rs:1212` (2) |
| `label` | 2 | 0 | 0 | 0 | 2 | Search::retest `zed-kernel/types/empty.rs:303` (1); Search::narrow_tuples `zed-kernel/types/empty.rs:349` (1) |
| `while` | 17 | 68 | 0 | 4 | 89 | blocks `zedc/store/product.rs:549` (3); tokens `zedc/check/ty.rs:1110` (3); Type::pairwise `zed-kernel/types.rs:435` (2) |
| `while_let` | 14 | 31 | 0 | 3 | 48 | blocks `zedc/store/product.rs:549` (3); first_on_cycle `zed-kernel/types/rec.rs:352` (2); Ck::derive_into `zedc/check/mod.rs:338` (2) |
| `for` | 91 | 553 | 38 | 7 | 689 | Ck::apply_one `zedc/check/mod.rs:3112` (13); blocks `zedc/store/product.rs:507` (13); Machine::region `zedc/zir/memory.rs:565` (11) |
| `loop` | 8 | 23 | 0 | 0 | 31 | enumerate_on `zedc/store/preimage.rs:2607` (2); Evaluator::generations `zed-kernel/eval.rs:1210` (1); union_at `zed-kernel/family.rs:246` (1) |
| `if_let` | 60 | 237 | 8 | 4 | 309 | lex_from `zedc/lex/mod.rs:194` (10); rename_first `zedc/canon/binders.rs:259` (8); products `zedc/store/presburger.rs:1505` (6) |
| `let_else` | 17 | 100 | 4 | 1 | 122 | project_each `zedc/store/presburger.rs:1245` (3); Scope::project_part `zedc/store/product.rs:1208` (3); Machine::note `zedc/zir/memory.rs:1129` (2) |
| `matches` | 21 | 86 | 6 | 2 | 115 | Evaluator::prim `zed-kernel/eval.rs:779` (5); prim_data `zed-kernel/eval.rs:1462` (4); node `zedc/zir/mod.rs:521` (3) |
| `match` | 204 | 731 | 28 | 25 | 988 | prim_data `zed-kernel/eval.rs:1402` (11); Machine::node `zedc/zir/memory.rs:652` (11); Ck::apply_one `zedc/check/mod.rs:3131` (9) |
| `or_pattern` | 40 | 134 | 3 | 3 | 180 | Cx::back_prim `zedc/store/preimage.rs:1663` (5); Cx::back_arith `zedc/store/preimage.rs:1830` (5); binary_level `zedc/format.rs:82` (4) |
| `at_binding` | 3 | 7 | 0 | 0 | 10 | Evaluator::eval_node `zed-kernel/eval.rs:544` (1); Evaluator::go_on `zed-kernel/eval.rs:1251` (1); Provenance::origins `zed-kernel/provenance.rs:123` (1) |
| `slice_pattern` | 2 | 40 | 0 | 1 | 43 | Builder::node `zedc/ast/mod.rs:268` (8); command_inner `zedc/run.rs:583` (4); Builder::lambda `zedc/ast/mod.rs:411` (3) |
| `closure` | 226 | 1217 | 71 | 16 | 1530 | Omega::inequalities `zedc/store/presburger.rs:994` (23); Ck::apply_one `zedc/check/mod.rs:3109` (21); command_inner `zedc/run.rs:574` (17) |
| `move_closure` | 7 | 5 | 1 | 0 | 13 | Group::instance `zed-kernel/types/rec.rs:303` (2); component `zed-kernel/types/rec.rs:470` (2); Provenance::preorder `zed-kernel/provenance.rs:98` (1) |
| `fnmut` | 11 | 15 | 1 | 0 | 27 | Bdd (impl) `zed-kernel/types/bdd.rs:362` (2); Part::atoms `zed-kernel/types/bdd.rs:806` (2); map_children `zedc/canon/binders.rs:139` (2) |
| `fn_bound` | 22 | 37 | 3 | 0 | 62 | Program (impl) `zedc/run.rs:281` (4); Cx (impl) `zedc/store/preimage.rs:837` (3); Type (impl) `zed-kernel/types.rs:372` (3) |
| `fn_ptr` | 1 | 5 | 14 | 0 | 20 | addresses `zed-native/hooks.rs:112` (13); Search::find_rep `zed-kernel/types/empty.rs:508` (1); run `zed-native/lib.rs:70` (1) |
| `panic` | 1 | 1 | 1 | 0 | 3 | Provenance::term `zed-kernel/provenance.rs:88` (1); Tables::const_index `zed-native/tables.rs:222` (1); parse_to `zedc/parse/mod.rs:111` (1) |
| `unreachable` | 8 | 50 | 4 | 1 | 63 | Builder::node `zedc/ast/mod.rs:292` (4); Lin::product `zedc/store/presburger.rs:181` (2); Builder::ty `zedc/ast/types.rs:118` (2) |
| `assert` | 3 | 0 | 0 | 0 | 3 | canonical_tree `zed-kernel/exact.rs:148` (1); Group::instance `zed-kernel/types/rec.rs:288` (1) |
| `debug_assert` | 0 | 4 | 1 | 0 | 5 | State::new `zed-native/hooks.rs:43` (1); Walk::set `zedc/store/iterate.rs:198` (1); narrow `zedc/store/iterate.rs:250` (1) |
| `expect` | 33 | 108 | 6 | 3 | 150 | P::value `zedc/zir/text.rs:923` (3); decode `zedc/lex/string.rs:285` (3); Elab::call_declared `zedc/elab.rs:1236` (3) |
| `unwrap` | 0 | 5 | 0 | 0 | 5 | Lines::new `zedc/source.rs:180` (2); backward `zedc/store/revision.rs:367` (2); Ck::apply_many `zedc/check/mod.rs:3398` (1) |
| `unwrap_or` | 15 | 62 | 5 | 0 | 82 | Scope::join `zedc/store/product.rs:807` (2); prim_data `zed-kernel/eval.rs:1474` (2); read_rat `zed-kernel/words.rs:98` (2) |
| `option` | 106 | 265 | 10 | 3 | 384 | Evaluator (impl) `zed-kernel/eval.rs:829` (16); Part::eval3_pinned `zed-kernel/types/bdd.rs:591` (9); Ck (impl) `zedc/check/mod.rs:2207` (8) |
| `result` | 25 | 222 | 36 | 12 | 295 | hull_from `zedc/store/presburger.rs:1349` (4); P::ty `zedc/zir/text.rs:802` (3); Heap::value `zed-rt/heap.rs:281` (3) |
| `nested_option` | 2 | 16 | 1 | 1 | 20 | Omega::inequalities `zedc/store/presburger.rs:985` (2); int_binary `zed-kernel/eval.rs:1349` (1); Part::eval3_pinned `zed-kernel/types/bdd.rs:647` (1) |
| `u8` | 8 | 94 | 15 | 2 | 119 | addresses `zed-native/hooks.rs:110` (14); Program (impl) `zedc/run.rs:280` (4); number `zedc/lex/number.rs:29` (3) |
| `u32` | 29 | 49 | 0 | 1 | 79 | Evaluator (impl) `zed-kernel/eval.rs:829` (8); Cx::lin_at `zedc/store/preimage.rs:1244` (3); Machine::note `zedc/zir/memory.rs:1133` (2) |
| `u64` | 77 | 97 | 2 | 12 | 188 | Parts::hash `zed-kernel/types.rs:340` (7); add_shifted `zed-kernel/exact.rs:11` (5); Bdd (impl) `zed-kernel/types/bdd.rs:154` (4) |
| `u128` | 4 | 0 | 0 | 0 | 4 | add_shifted `zed-kernel/exact.rs:14` (4) |
| `usize` | 107 | 579 | 55 | 19 | 760 | blocks `zedc/store/product.rs:501` (20); topo `zedc/elab.rs:1533` (8); Evaluator (impl) `zed-kernel/eval.rs:831` (7) |
| `i8` | 0 | 6 | 0 | 0 | 6 | at `zedc/store/revision.rs:110` (3); End::signum `zedc/store/interval.rs:103` (2); quotient `zedc/store/revision.rs:320` (1) |
| `i32` | 3 | 3 | 0 | 0 | 6 | show_f64 `zed-kernel/num.rs:197` (2); Width::holds `zedc/store/float.rs:49` (2); exact_f64 `zed-kernel/num.rs:230` (1) |
| `i64` | 14 | 100 | 75 | 17 | 206 | addresses `zed-native/hooks.rs:112` (24); Word (impl) `zed-rt/heap.rs:36` (9); rt_callable `zed-native/hooks.rs:159` (5) |
| `i128` | 0 | 167 | 0 | 0 | 167 | Congruence::meet `zedc/store/lattice.rs:273` (12); at `zedc/store/revision.rs:103` (10); hull_from `zedc/store/presburger.rs:1355` (9) |
| `f32` | 0 | 1 | 0 | 0 | 1 | Width::format `zedc/store/float.rs:33` (1) |
| `f64` | 21 | 17 | 1 | 1 | 40 | round `zed-kernel/exact.rs:56` (5); exact_sum `zed-kernel/exact.rs:94` (5); Width::format `zedc/store/float.rs:30` (3) |
| `as_cast` | 44 | 182 | 33 | 13 | 272 | Congruence::meet `zedc/store/lattice.rs:273` (13); at `zedc/store/revision.rs:116` (11); add_shifted `zed-kernel/exact.rs:12` (9) |
| `wrapping` | 13 | 1 | 0 | 0 | 14 | SplitMix::next `zed-kernel/eval.rs:1284` (3); mix `zed-kernel/types.rs:79` (3); sub `zed-kernel/exact.rs:35` (2) |
| `checked` | 8 | 25 | 0 | 0 | 33 | relaxed_empty `zedc/store/presburger.rs:1149` (5); int_binary `zed-kernel/eval.rs:1352` (4); class_of `zedc/store/preimage.rs:2553` (4) |
| `saturating` | 6 | 12 | 0 | 0 | 18 | Type::list `zed-kernel/types.rs:669` (3); per_device `zedc/cost.rs:119` (3); scalarize `zedc/cost.rs:135` (3) |
| `rotate` | 1 | 0 | 0 | 0 | 1 | mix `zed-kernel/types.rs:79` (1) |
| `bit_count` | 10 | 5 | 0 | 0 | 15 | Rat::bits `zed-kernel/num.rs:112` (2); Ck::apply_one `zedc/check/mod.rs:3139` (2); sized `zed-kernel/eval.rs:1341` (1) |
| `byte_conv` | 0 | 17 | 0 | 0 | 17 | unit_address `zedc/canon/mod.rs:220` (3); key `zedc/query.rs:41` (2); node_key `zedc/zir/canon.rs:136` (2) |
| `float_bits` | 6 | 4 | 1 | 2 | 13 | round `zed-kernel/exact.rs:65` (2); F64::eq `zed-kernel/value.rs:41` (2); exact_sum `zed-kernel/exact.rs:112` (1) |
| `shift` | 30 | 12 | 0 | 0 | 42 | add_shifted `zed-kernel/exact.rs:14` (4); round `zed-kernel/exact.rs:71` (4); Exact::float `zed-kernel/num.rs:163` (4) |
| `bitop_call` | 48 | 64 | 3 | 0 | 115 | Search::tuples `zed-kernel/types/empty.rs:408` (5); mix `zed-kernel/types.rs:79` (4); Ck::apply_one `zedc/check/mod.rs:3143` (3) |
| `bigint` | 30 | 5 | 0 | 0 | 35 | Rat::decimal `zed-kernel/num.rs:58` (3); Rat::new `zed-kernel/num.rs:30` (2); Rat::int `zed-kernel/num.rs:43` (2) |
| `as_bytes` | 7 | 36 | 0 | 5 | 48 | Record::to_bytes `zedc/run.rs:477` (6); Rope::cat `zed-rt/rope.rs:30` (4); checks `zedc/testing.rs:89` (4) |
| `chars` | 2 | 31 | 1 | 3 | 37 | Rope::cat `zed-rt/rope.rs:38` (2); Elab::expr `zedc/elab.rs:729` (2); label `zedc/fence.rs:77` (2) |
| `char_type` | 0 | 18 | 0 | 0 | 18 | escape `zedc/lex/string.rs:149` (2); tokens `zedc/check/ty.rs:1108` (1); label `zedc/fence.rs:77` (1) |
| `str_type` | 51 | 245 | 11 | 1 | 308 | Ck (impl) `zedc/check/mod.rs:1008` (12); Gen (impl) `zed-native/codegen.rs:324` (4); rename `zedc/canon/binders.rs:392` (4) |
| `string_type` | 54 | 366 | 41 | 11 | 472 | region `zedc/zir/mod.rs:392` (5); Ck (impl) `zedc/check/mod.rs:2081` (5); Elab (impl) `zedc/elab.rs:888` (5) |
| `byte_slice` | 1 | 19 | 0 | 1 | 21 | split_lines `zedc/run.rs:403` (2); Record::from_bytes `zedc/run.rs:507` (2); bytes `zed-kernel/types.rs:86` (1) |
| `from_utf8` | 0 | 8 | 0 | 1 | 9 | Record::from_bytes `zedc/run.rs:513` (2); lines `zed-rt/ports.rs:22` (1); split_lines `zedc/run.rs:410` (1) |
| `str_method` | 17 | 69 | 0 | 0 | 86 | Grammar::read `zedc/parse/grammar.rs:90` (12); Formatter::raw `zedc/format.rs:341` (4); read_rat `zed-kernel/words.rs:98` (4) |
| `format` | 43 | 414 | 27 | 6 | 490 | node `zedc/zir/mod.rs:522` (12); command_inner `zedc/run.rs:603` (12); Elab::call_declared `zedc/elab.rs:1146` (10) |
| `write_macro` | 65 | 150 | 0 | 0 | 215 | Expr::fmt `zedc/ast/mod.rs:580` (20); Value::fmt `zed-kernel/value.rs:422` (19); KernelError::fmt `zed-kernel/error.rs:52` (16) |
| `to_string` | 19 | 82 | 4 | 0 | 105 | command_inner `zedc/run.rs:579` (5); Elab::stmt `zedc/elab.rs:571` (4); doc `zed-kernel/print.rs:199` (3) |
| `push_str` | 1 | 6 | 0 | 2 | 9 | Ck::named `zedc/check/mod.rs:1394` (4); Rope::flat `zed-rt/rope.rs:74` (2); Text::write_out `zed-kernel/text.rs:56` (1) |
| `vec` | 273 | 1289 | 82 | 24 | 1668 | Lower::term `zedc/zir/lower.rs:507` (37); blocks `zedc/store/product.rs:492` (35); weak_topological_order `zedc/store/wto.rs:83` (25) |
| `hashmap` | 32 | 98 | 12 | 0 | 142 | Elab::new `zedc/elab.rs:385` (6); Part::eval3_pinned `zed-kernel/types/bdd.rs:595` (5); Part::restrict `zed-kernel/types/bdd.rs:766` (4) |
| `hashset` | 9 | 54 | 2 | 0 | 65 | Ty::union `zedc/check/ty.rs:507` (4); Part::atoms `zed-kernel/types/bdd.rs:809` (2); Ck::derive_into `zedc/check/mod.rs:334` (2) |
| `btreemap` | 44 | 121 | 5 | 0 | 170 | relaxed_empty `zedc/store/presburger.rs:1134` (7); blocks `zedc/store/product.rs:503` (6); Omega::inequalities `zedc/store/presburger.rs:988` (5) |
| `btreeset` | 36 | 81 | 0 | 0 | 117 | Provenance::origins `zed-kernel/provenance.rs:122` (8); products `zedc/store/presburger.rs:1502` (3); Scope::enumerate_exactly `zedc/store/product.rs:1350` (2) |
| `binheap` | 0 | 4 | 0 | 0 | 4 | IntervalSet::cap `zedc/store/interval.rs:268` (2); topo `zedc/elab.rs:1542` (1) |
| `imbl` | 21 | 15 | 0 | 0 | 36 | used `zedc/store/hull.rs:196` (2); walk `zedc/store/product.rs:1656` (2); spaced `zed-kernel/types.rs:1269` (1) |
| `range_query` | 0 | 9 | 0 | 0 | 9 | IntervalSet::snap `zedc/store/interval.rs:354` (2); Tables::uses_in `zedc/elab.rs:319` (1); Formatter::take `zedc/format.rs:155` (1) |
| `sort` | 6 | 21 | 0 | 0 | 27 | clauses `zed-kernel/types.rs:1325` (3); frontier `zedc/cost.rs:178` (2); blocks `zedc/store/product.rs:534` (2) |
| `binary_search` | 2 | 11 | 0 | 1 | 14 | matches `zed-kernel/eval.rs:1323` (1); Bdd::forced `zed-kernel/types/bdd.rs:279` (1); Heap::matches `zed-rt/heap.rs:483` (1) |
| `dedup` | 1 | 11 | 0 | 0 | 12 | blocks `zedc/store/product.rs:535` (2); Bdd::forced `zed-kernel/types/bdd.rs:276` (1); canonicalize `zedc/canon/mod.rs:174` (1) |
| `retain` | 0 | 9 | 0 | 0 | 9 | Ck::apply_one `zedc/check/mod.rs:3319` (1); Ty::diff `zedc/check/ty.rs:699` (1); Elab::passes `zedc/elab.rs:443` (1) |
| `drain` | 2 | 1 | 0 | 0 | 3 | Evaluator::define_on_demand `zed-kernel/eval.rs:1149` (1); Search::empty `zed-kernel/types/empty.rs:205` (1); Cx::forget `zedc/store/preimage.rs:872` (1) |
| `truncate` | 4 | 13 | 0 | 0 | 17 | Parser::m `zedc/parse/mod.rs:263` (4); Evaluator::entry `zed-kernel/eval.rs:1059` (3); Evaluator::leave `zed-kernel/eval.rs:499` (1) |
| `vec_swap` | 1 | 1 | 0 | 0 | 2 | SplitMix::shuffle `zed-kernel/eval.rs:1294` (1) |
| `extend` | 15 | 105 | 3 | 2 | 125 | Ck::merge `zedc/check/mod.rs:835` (4); Lower::node `zedc/zir/lower.rs:425` (3); Search::empty `zed-kernel/types/empty.rs:184` (3) |
| `windows` | 1 | 4 | 2 | 0 | 7 | Value::atom_named `zed-kernel/value.rs:140` (1); Gen::function `zed-native/codegen.rs:157` (1); Gen::params `zed-native/codegen.rs:443` (1) |
| `split_at` | 5 | 6 | 0 | 0 | 11 | show_f64 `zed-kernel/num.rs:210` (2); Builder::function `zedc/ast/stmts.rs:181` (2); prim_data `zed-kernel/eval.rs:1527` (1) |
| `iter` | 164 | 900 | 38 | 14 | 1116 | region `zedc/zir/mod.rs:395` (14); Omega::inequalities `zedc/store/presburger.rs:994` (14); Ck::apply_one `zedc/check/mod.rs:3117` (13) |
| `map` | 69 | 427 | 18 | 8 | 522 | Machine::node `zedc/zir/memory.rs:655` (7); Elab::call_declared `zedc/elab.rs:1179` (7); doc `zed-kernel/print.rs:203` (6) |
| `filter` | 11 | 146 | 3 | 1 | 161 | Omega::inequalities `zedc/store/presburger.rs:1008` (9); Product::reduce_domains `zedc/store/product.rs:302` (6); Ty::union `zedc/check/ty.rs:508` (4) |
| `flat_map` | 9 | 49 | 5 | 0 | 63 | map2 `zedc/store/revision.rs:291` (3); Ck::apply `zedc/check/mod.rs:2995` (3); Ty::vars_in `zedc/check/ty.rs:827` (3) |
| `fold` | 10 | 60 | 1 | 0 | 71 | Scope::narrow `zedc/store/product.rs:919` (6); Cx::lin_at `zedc/store/preimage.rs:1267` (2); Doc::fits `zed-kernel/print.rs:433` (2) |
| `collect` | 74 | 465 | 22 | 8 | 569 | Elab::call_declared `zedc/elab.rs:1180` (9); Omega::inequalities `zedc/store/presburger.rs:994` (9); Machine::node `zedc/zir/memory.rs:655` (6) |
| `any_all` | 38 | 132 | 1 | 1 | 172 | fits_sig `zedc/check/ty.rs:920` (6); Ck::apply_one `zedc/check/mod.rs:3118` (5); Planner::mode `zedc/zir/memory.rs:245` (4) |
| `find` | 8 | 77 | 1 | 1 | 87 | edges `zedc/zir/mod.rs:635` (4); Search::find_rep `zed-kernel/types/empty.rs:518` (3); region `zedc/zir/mod.rs:395` (3) |
| `enumerate` | 17 | 102 | 16 | 3 | 138 | Machine::region `zedc/zir/memory.rs:565` (6); region `zedc/zir/mod.rs:437` (6); Uses::of `zedc/zir/memory.rs:192` (3) |
| `zip` | 33 | 38 | 1 | 2 | 74 | Type::zip `zed-kernel/types.rs:762` (7); Type::list `zed-kernel/types.rs:696` (4); Part::go `zed-kernel/types/bdd.rs:751` (4) |
| `rev` | 7 | 28 | 1 | 1 | 37 | Ck::derive_into `zedc/check/mod.rs:336` (3); Elab::call_declared `zedc/elab.rs:1178` (3); cmp `zed-kernel/exact.rs:44` (2) |
| `peekable` | 0 | 13 | 0 | 0 | 13 | tokens `zedc/parse/grammar.rs:158` (3); name `zedc/lex/name.rs:22` (2); P::value `zedc/zir/text.rs:889` (2) |
| `next` | 6 | 46 | 0 | 0 | 52 | tokens `zedc/parse/grammar.rs:159` (6); P::string `zedc/zir/text.rs:956` (3); decode `zedc/lex/string.rs:280` (2) |
| `skip_take` | 4 | 45 | 0 | 0 | 49 | Cx::scan `zedc/store/preimage.rs:1771` (7); children `zed-kernel/provenance.rs:186` (3); children `zedc/canon/binders.rs:107` (2) |
| `minmax` | 9 | 60 | 0 | 1 | 70 | first_on_cycle `zed-kernel/types/rec.rs:361` (4); map2 `zedc/store/revision.rs:278` (3); backward `zedc/store/revision.rs:366` (3) |
| `unsafe` | 0 | 0 | 2 | 0 | 2 | run `zed-native/lib.rs:70` (2) |
| `extern` | 0 | 0 | 27 | 0 | 27 | addresses `zed-native/hooks.rs:112` (13); rt_arg `zed-native/hooks.rs:128` (1); rt_node `zed-native/hooks.rs:132` (1) |
| `transmute` | 0 | 0 | 1 | 0 | 1 | run `zed-native/lib.rs:70` (1) |
| `thread` | 6 | 1 | 1 | 0 | 8 | on_stack `zed-kernel/eval.rs:294` (2) |
| `once` | 14 | 8 | 0 | 5 | 27 | Type::rec `zed-kernel/types.rs:378` (2); take_sides `zed-rt/rope.rs:105` (2); grammar `zedc/parse/mod.rs:28` (2) |
| `atomic` | 6 | 0 | 0 | 0 | 6 | Type::rec `zed-kernel/types.rs:375` (2); Bdd::node `zed-kernel/types/bdd.rs:108` (2) |
| `env` | 0 | 1 | 0 | 0 | 1 | main `zedc/main.rs:9` (1) |
| `fs` | 0 | 8 | 0 | 0 | 8 | command_inner `zedc/run.rs:603` (5); main `zedc/main.rs:13` (1); Disk::get `zedc/run.rs:445` (1) |
| `process` | 0 | 1 | 0 | 0 | 1 | (item) `zedc/main.rs:6` (1) |
| `io` | 0 | 13 | 0 | 0 | 13 | main `zedc/main.rs:26` (10); Disk::get `zedc/run.rs:450` (1) |
| `print` | 0 | 4 | 0 | 0 | 4 | main `zedc/main.rs:11` (4) |
| `catch_unwind` | 1 | 0 | 0 | 0 | 1 | Evaluator::run `zed-kernel/eval.rs:370` (1) |
| `hash_trait` | 2 | 6 | 0 | 0 | 8 | Text::hash `zed-kernel/text.rs:155` (1); Type::hash `zed-kernel/types.rs:69` (1); address_at `zedc/canon/mod.rs:196` (1) |
| `phantom` | 3 | 0 | 0 | 0 | 3 | on_stack `zed-kernel/eval.rs:292` (2) |

## Entries from T2-eval (`zed-kernel/src/eval.rs`, `exact.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Vec` of an enum as an explicit stack, popped and pushed in a loop | `Machine::run`, `Frame`, `Wait`, `exact::CanonicalTree` | Mutation | A state receiver; a list value updated per step would allocate per frame unless the runtime reuses it |
| Terms borrowed for the run: `Frame<'t>`, `Step<'t>`, `V<'t>` | throughout `eval.rs` | None | Zed shares values, so a term is held without a lifetime |
| `Rc<RefCell<...>>` cells shared by frames | `Definedness::{defined, busy, stalled}`, `Drops::envs` | Mutation, identity | State threaded through the machine, keyed by a fix's id (gaps 1 and 3 of the T13 catalog) |
| `impl Drop for Closure`: environments put on a list so that their release does not recurse | `Drops`, `Closure` | None | Removed: the runtime frees values, and must free a deep chain without recursion itself |
| `std::mem::take`, `std::mem::replace` of a field in place | `Evaluator::run`, the fix frames | Mutation | A state receiver |
| `imbl::HashMap` and `imbl::OrdMap`, persistent maps sharing structure | `preimage::Scope`, `preimage::Sets` | None | Zed's maps are values: an update makes a new map, and the runtime must share its structure to keep the update at `O(log n)` |

## Entries from T2-native (`zed-rt/src/heap.rs`, `zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Vec` of frames as an explicit stack, each frame growing its own `Vec` of results | `Making`, `Reading`, `Matching`, `hooks::term` | Mutation | As for `Machine::run`: a state receiver |
| `slice::Iter` held in a frame across steps, to resume a walk | `Making::rest` | None | An index into the list |
| Reborrowing `&mut` to each sub-pattern through a stack | `hooks::rename` | Mutation | Zed builds the renamed pattern as a new value |
## Entries from T2-eval-repair (`zed-kernel/src/deep.rs`, `value.rs`, `family.rs`, `types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `thread_local!` list of parts waiting to be freed, and a flag for the walk that holds it | `deep::free`, `FREEING`, `PARTS` | Mutation, global state | Removed: the runtime frees values, and must free a deep chain without recursion itself |
| `thread_local!` queue of families to compare, because `==` is called from inside `imbl` where no stack of ours reaches | `deep::settle`, `COMPARING`, `PAIRS` | Mutation, global state | Zed's map comparison takes the element test as a function, so the queue is a state receiver or goes away |
| `impl Drop` on a newtype, with `mem::take` of its `Vec` | `Items`, `Family` | None | Removed, with the first row |
| `slice::Iter` held in a stack frame, a borrow into the value being walked | `walk`, `Copying`, `all_leaves` | None | An index into a shared tuple |
| `Cow<'_, Value>`, a key borrowed unless it needs a copy | `as_key` in `eval.rs` | None | Zed shares values, so a function returns the key or its normalized copy with no borrow |
| `RefCell` to collect from inside a `Fn` closure that `Expr::eval` calls | `Type::contains` | Mutation | The closure returns what it needs, as a value |
| Raw pointers as map keys, `*const Node` and `*const Value` | `Type::contains` | Identity | Keyed by a hash-consed id of the type and the position in the value |
| Hardware counter opened with `perf_event_open` through `perf-event2`, and the thread CPU clock through `rustix` | `zed_tests::scaling::Meter`, `cpu_time` | Foreign library | Test harness only, so a Zed port needs it only if the tests move to Zed: an `@ffi` signature over the two system calls (L7.4) |

## Entries from T2-parse (`zedc/src/parse/mod.rs`, `ast/`, `format.rs`, `lex/`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Vec` of `Copy` frames as an explicit stack, popped and pushed in a loop | `Parser` machine, `Formatter::run`, `ast::show` | Mutation | A state receiver, as for the evaluator's machine |
| `impl Drop` with a work list, on enums and structs | `ast/drop.rs`, `parse::Tree`, `lex::Part` | None | Removed: the runtime frees values, and must free a deep chain without recursion itself |
| `VecDeque` with `push_front`, `pop_back` and `get_mut`, slots taken in place by `Option::take` | `Builder::fill`, `Builder::take` | Mutation | A map keyed by position, or a state receiver over a list |
| `Cow<str>` for pieces of output, some borrowed from the source | `Formatter::pieces` | None | Zed shares strings, so a piece is a plain `String` |
| `macro_rules!` for repeated statements in a `match` | `then!`, `shown!`, `debug_as_shown!` | Macros | A function |
| `OnceLock` for a table computed once | `ast::forms` | Global state | A constant, or a value passed in |
