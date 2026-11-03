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
  T11-preimage removed this from `preimage.rs`: its memos are keyed by numbers a transfer gives
  its terms and scopes (see the T11-preimage entries below).
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
`Shown` (types.rs:118) and `Text::flat` (`text.rs:28`) cache in place inside a shared value. Since T14-rope the native runtime holds its strings as the same `Text` (`zed-rt/src/heap.rs`, `Obj::Str`); `zed-rt`'s own `Rope`, with a second `OnceLock`, is gone.

Zed values are immutable with no cell, and a function field re-evaluates on each call. Cyclic
data lives in two sanctioned forms, arenas or regions and id-indexed graphs `Id ->? Node`
(line 1399, confirmed), which L6.13 builds. Fix: the second form. A recursive type is `#rec(id)`
with its parts in an indexed definition `parts[id] = …`, evaluated on demand (L6.1, L6.4). `Text` needs no port: `String` ropes are L6.16. Cones become
an indexed definition. Cost: inferred O(1) per read if the definedness table is stored, to be
measured at S.3.

### Gap 4. Bit operations (missing)

Confirmed: line 612 defines `shl(x, k)`: `k : int[0..]`, value `x · 2^k` on the unbounded `int`,
with a width enforced where one is written. Line 729 uses `bitAnd`, `bitOr`, `bitXor` and `shl`,
line 2632 lists them as named functions, and `zed/fences/examples.md:78` uses `shl`. The gap, when found: the
words table (line 3723) lists none of them, `Prim` (`zed-kernel/term.rs:18`) has none, and only
`shl` has semantics. Since the 2026-11-03 DESIGN audit, step L1.39a specifies the bit words and
the L1 row of the words table lists them; ledger item BIT-words builds them (docs/plan_dag.md).

Rust uses: `<<`, `>>` 42; `&`, `|`, `^` on integers up to 115; `wrapping_*` and `overflowing_*` 14;
`rotate_left` 1 (`mix`, types.rs:79); `count_ones`, `leading_zeros`, `trailing_zeros` 7 (`Ck::resolve`
`check/mod.rs:1224`, `round` `exact.rs:61`, `float.rs:55`); bit masks as
sets (`Carrier::of_mask`, `check/ty.rs:340`). `blake3::Hasher` is used at 6 sites (`address_at`,
`canon/mod.rs:196`, and others).

Fix: add to the L1 row of the words table `shl` as line 612 specifies it, and semantics for
`bitAnd bitOr bitXor bitNot shr popCount leadingZeros trailingZeros` on `int[0..]`, so that a
negative operand is a type error. `bitNot`, `leadingZeros` and `rotl` depend on a width, so each
takes it as an argument. Shift counts stay domain-typed and are never masked (line 612), so a
wrapping shift is written `shl(x, k) mod 2 ** w`. `rotl` and `rotr` are new words.

Wrapping arithmetic is written `(a * b) mod 2 ** 64`. Line 589 already permits computing that in
wrapping `w`-bit arithmetic when the result domain is known statically and spans at most `2^w`
integers (see also line 4088), and step L3.13 builds it, with a test at `mod 2 ** 63`. What remains
is to confirm it for `mix` (`types.rs:77`), where each product is its own expression, since
`bitXor` and `rotl` are not in line 612's list of operators. Also, line 612 lists the
representations as i8…i64, else big-integer, and `int[0..<2 ** 64]` does not fit `i64`, so a hash
would be stored as a big integer. Fix: state that a domain spanning at most `2^w` integers is
stored in one word. Both points are inferred; the test is a scaling run of `mix` at S.3. Carrier masks become sets of atoms. BLAKE3 in Zed
is then ZED0.md's plan; if a stage build shows it too slow, a primitive is allowed by line 1075.

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
L6.13). `Drop` for `text::Node` and `Premises` exists to avoid deep recursion in release,
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
`interval.rs:266`; reference 14's `Level::merge`, `zed/corpus/ref/src/p14.rs`) is then an ordered set
with `.first` and a `patch`.

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

- **Overflow as refusal.** Since T4 the Omega test, `twovar` and `utvpi` compute in
  `store::int::Int`, unbounded with i128 while a value fits, and no coefficient refuses a
  question; in Zed this is `int`, and `store::int` goes at the port. `checked_*` remain elsewhere.
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
| `saturating_add`, `saturating_mul`, `saturating_sub` | 9, 6, 3 | `saturating_sub` becomes an `if`. The other two guard a machine word and vanish on an unbounded `int`. In `cost.rs`, costs then no longer stop at the maximum, so a comparison of very large costs can differ from the Rust at S.3 |
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
| `const_fn` | 0 | 1 | 0 | 0 | 1 | ax `zedc/axioms.rs:102` (1) |
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
| `at_binding` | 3 | 7 | 0 | 0 | 10 | Evaluator::eval_node `zed-kernel/eval.rs:544` (1); Evaluator::go_on `zed-kernel/eval.rs:1251` (1); Provenance::origins `zed-kernel/provenance.rs:297` (1) |
| `slice_pattern` | 2 | 40 | 0 | 1 | 43 | Builder::node `zedc/ast/mod.rs:268` (8); command_inner `zedc/run.rs:583` (4); Builder::lambda `zedc/ast/mod.rs:411` (3) |
| `closure` | 226 | 1217 | 71 | 16 | 1530 | Omega::inequalities `zedc/store/presburger.rs:994` (23); Ck::apply_one `zedc/check/mod.rs:3109` (21); command_inner `zedc/run.rs:574` (17) |
| `move_closure` | 7 | 5 | 1 | 0 | 13 | Group::instance `zed-kernel/types/rec.rs:303` (2); component `zed-kernel/types/rec.rs:470` (2); Provenance::preorder `zed-kernel/provenance.rs:98` (1; removed by T14-occ) |
| `fnmut` | 11 | 15 | 1 | 0 | 27 | Bdd (impl) `zed-kernel/types/bdd.rs:362` (2); Part::atoms `zed-kernel/types/bdd.rs:806` (2); map_children `zedc/canon/binders.rs:139` (2) |
| `fn_bound` | 22 | 37 | 3 | 0 | 62 | Program (impl) `zedc/run.rs:281` (4); Cx (impl) `zedc/store/preimage.rs:837` (3); Type (impl) `zed-kernel/types.rs:372` (3) |
| `fn_ptr` | 1 | 5 | 14 | 0 | 20 | addresses `zed-native/hooks.rs:112` (13); Search::find_rep `zed-kernel/types/empty.rs:508` (1); run `zed-native/lib.rs:70` (1) |
| `panic` | 1 | 1 | 1 | 0 | 3 | Provenance::term `zed-kernel/provenance.rs:238` (1); Tables::const_index `zed-native/tables.rs:222` (1); parse_to `zedc/parse/mod.rs:111` (1) |
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
| `btreeset` | 36 | 81 | 0 | 0 | 117 | Provenance::origins `zed-kernel/provenance.rs:296` (8); products `zedc/store/presburger.rs:1502` (3); Scope::enumerate_exactly `zedc/store/product.rs:1350` (2) |
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
| `skip_take` | 4 | 45 | 0 | 0 | 49 | Cx::scan `zedc/store/preimage.rs:1771` (7); children `zed-kernel/provenance.rs:186` (3; removed by T14-occ); children `zedc/canon/binders.rs:107` (2) |
| `minmax` | 9 | 60 | 0 | 1 | 70 | first_on_cycle `zed-kernel/types/rec.rs:361` (4); map2 `zedc/store/revision.rs:278` (3); backward `zedc/store/revision.rs:366` (3) |
| `unsafe` | 0 | 0 | 2 | 0 | 2 | run `zed-native/lib.rs:70` (2); since T14-low one in `run` and one in `Jit::drop` |
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
| `impl Drop` on a newtype, with `mem::take` of its `Arc` or map | `Items`, `Family` | None | Removed, with the first row |
| `slice::Iter` held in a stack frame, a borrow into the value being walked | `walk`, `Copying`, `all_leaves` | None | An index into a shared tuple |
| `Cow<'_, Value>`, a key borrowed unless it needs a copy | `as_key` in `eval.rs` | None | Zed shares values, so a function returns the key or its normalized copy with no borrow |
| `RefCell` to collect from inside a `Fn` closure that `Expr::eval` calls | `Type::contains` | Mutation | The closure returns what it needs, as a value |
| Raw pointers as map keys, `*const Node` and `*const Value` | `Type::contains` | Identity | Keyed by a hash-consed id of the type and the position in the value |
| Hardware counter opened with `perf_event_open` through `perf-event2`, and the thread CPU clock through `rustix` | `zed_tests::scaling::Meter`, `cpu_time` | Foreign library | Test harness only, so a Zed port needs it only if the tests move to Zed: an `@ffi` signature over the two system calls (L7.4) |

## Entries from T2-parse (`zedc/src/parse/mod.rs`, `ast/`, `format.rs`, `lex/`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Vec` of `Copy` frames as an explicit stack, popped and pushed in a loop | `Parser` machine, `Formatter::run`, `ast::show`, `preimage::Tx::read_powers` (with a `Count` of factors since CAP-pow32: the value as `Option<u32>` and the parity) | Mutation | A state receiver, as for the evaluator's machine |
| `impl Drop` with a work list, on enums and structs | `ast/drop.rs`, `parse::Tree`, `lex::Part` | None | Removed: the runtime frees values, and must free a deep chain without recursion itself |
| `VecDeque` with `push_front`, `pop_back` and `get_mut`, slots taken in place by `Option::take` | `Builder::fill`, `Builder::take` | Mutation | A map keyed by position, or a state receiver over a list |
| `Cow<str>` for pieces of output, some borrowed from the source | `Formatter::pieces` | None | Zed shares strings, so a piece is a plain `String` |
| `macro_rules!` for repeated statements in a `match` | `then!`, `shown!`, `debug_as_shown!` | Macros | A function |
| `OnceLock` for a table computed once | `ast::forms` | Global state | A constant, or a value passed in |
| A generic struct over a trait with an unsized `Self` (`Parser<I: Input + ?Sized>` on `[char]` and on `Tokens`) | `zedc::parse::engine` | Unsized types | An interface over a value, passed as a parameter |
| `env!("CARGO_MANIFEST_DIR")`, a path fixed when the tool is built | `zed_tools::impl_root` | Build-time environment | A parameter of the tool |

## Entries from L2.1 (`zedc/src/ast/`, `format.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `HashMap<&'a str, Span>` borrowing names from the source text, filled while a list is built | `Builder::once` and its callers (struct fields, display entries, `with` paths, type parameters) | None | A map from name to span over shared strings |
| `let … else { unreachable!() }` on an enum variant that an earlier pass has ruled out | `elab.rs`, `check/mod.rs` (the L2 forms resolution refuses) | Partial match | A total match whose L2 arm returns the refusal, or a narrower type from resolution |

## Entries from L2.2 (`zedc/src/ast/`, `format.rs`, `resolve.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Iterator::peekable` with `next_if`, taking the next node only when it starts at a given token | `Builder::annotated` | Mutation | An index into the list of nodes, passed along a fold |
| `let … else { … return; }` taking the first arm of a slice, the rest of the arms pushed back as a job | `Formatter::run`, `Job::Arms` | Early return | A `match` on the list, empty against first and rest |
| `Box<Type>` and `Box<Expr>` in `Pattern::{Is, Lit}`, so the enum stays small | `ast/types.rs` | None | Removed: Zed values are shared, and size is not the programmer's concern |


## Entries from T4 (`zedc/src/store/utvpi.rs`, `presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A tree held as a ring of `next` and `prev` indices in preorder with a depth per node, relinked in place by index when a subtree is cut out | `utvpi::potential` | None | Removed by UTVPI-GOR: the search keeps no shortest-path tree |
| `VecDeque` used as a FIFO queue, `push_back` and `pop_front`, with a `Vec<bool>` of what it holds | `utvpi::potential` (Kahn's order since UTVPI-GOR) | Mutation | A state receiver over a list and a set, or two lists swapped at each round |
| `Iterator::partition` of borrowed rows into two `Vec<&Row>` | `presburger::search` | None | `partition` over a list of rows, which Zed shares rather than borrows |

## Entries from UTVPI-GOR (`zedc/src/store/utvpi.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec<usize>` of pass numbers written in place as the visited set of each pass, so no set is cleared between passes, with a `Vec<bool>` of the nodes on the search stack | `utvpi::potential` | Mutation | A state receiver over a map from node to pass, or a fresh persistent set per pass at a log factor |
| `Vec` of `(node, next edge)` frames as an explicit stack for a depth-first search, the top frame's edge place advanced through `last_mut` | `utvpi::potential` | Mutation | A state receiver, as for the parser's machine |
| Distances in a `Vec<Int>` lowered in place while the edges are relaxed | `utvpi::potential` | Mutation | A state receiver over a map from node to distance |

## Entries from T14-low (`zed-native/src/lib.rs`, `codegen.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `impl Drop` on a guard holding `ManuallyDrop<JITModule>`, taken once with `ManuallyDrop::take` to call the consuming `free_memory` | `zed_native::Jit` | Foreign library | The JIT is a foreign resource: an `@ffi` handle whose release the runtime calls when its count reaches 0 |
| `unsafe` block in `Drop` to call Cranelift's `free_memory` | `Jit::drop` | Foreign library | Inside the `@ffi` binding |
| `#[expect(lint, reason = ...)]` | `zed_native::run`, `Jit::drop`, test `Counted` | Attributes | None needed: Zed has no lint attributes |
| Cranelift `Switch` (a jump table over block indices) | `codegen::dispatch` | Foreign library | The code generator's own `match` lowering |
| `AtomicUsize` counters shared through `Arc` with a memory provider trait object | test `a_failed_compile_frees_the_jit_memory` | Mutation | Test harness only: the provider returns its counts as a value |

## Entries from T14-value (`zed-kernel/src/value.rs`, `deep.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Arc<[Value]>`, a shared slice with a reference count, and `Arc::default()` for the static empty slice | `Items`, `Atom::fields` | None | Zed values are shared already; the type is a plain tuple |
| `Arc::strong_count` to tell a shared sequence from one held once, and `Arc::get_mut` to move the parts out of one held once | `Items::is_shared`, `Items::pair`, `Items::into_vec` | Identity, mutation | Removed: the runtime reuses a value held once, and the walks key their read sets by a hash-consed id |
| Address of a shared slice (`Arc::as_ptr`, `Arc::ptr_eq`) as a key in a `HashSet` or `HashMap` held only while both values are borrowed | `deep::walk` (`read`), `deep::copy` (`copied`), `deep::all_leaves` (`read`) | Identity | A hash-consed id of the value, as for `Type::contains` |

## Entries from T11-elab (`zedc/src/elab.rs`, `stage.rs`, `query.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Arc<Term>` and `Arc<[Test]>` held so that a let or a staged unit shares a term rather than copying it | `Def.term`, `Unit.tests`, `stage::Entry.known` | None | Zed shares values, so a field holds the term itself |
| `OnceCell` per definition for its reads and its digest, filled when first needed through `&self` | `Cones::reads`, `Cones::digests` | Lazy cells (gap 3) | A map of the reads and digests made when the unit is indexed, or threaded through as a state receiver |
| `Cow<'_, [Arc<str>]>` for a binder's names, borrowed from the term or built for a pattern | `stage::kids` | None | Zed shares lists, so each child carries the list itself |
| `std::slice::from_ref` to see one name as a list of one | `stage::kids` | None | A list of one name |
| A struct borrowing the checker's findings (`&'a Info`) for its lifetime | `Elab` | None | The findings passed as a value, which Zed shares |
| `std::mem::take` of the mixer's report after each split | `Specializer::split` | Mutation | The split returns the report it built, and the mixer is a state receiver |

## Entries from T14-provenance (`zed-kernel/src/provenance.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `BTreeMap::pop_last` as a worklist taken in descending key order, each step adding entries at smaller keys | `Provenance::origins` | Key range queries (gap 9), mutation | `.last` and a `patch` removing that key on an ordered map, in a state receiver; or a fold over the fact indices from `i` down to 0, which visits facts the pass would skip |
| `BTreeMap::entry(k).or_insert_with` as a memo filled during the pass | `Provenance::origins` | Mutation | A state receiver over a map, or the members each fact holds computed for all facts before the pass |

## Entries from T11-preimage (`zedc/src/store/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Terms numbered in an arena (`Vec` of nodes with `u32` children), filled by an explicit stack | `Terms::add` | Mutation | A state receiver over a map from number to node, or the content digest of gap 1, which makes the numbering unneeded |
| Raw pointer `*const Term` as the key of the visited set while the arena is filled | `Terms::id` | Identity | Keyed by the content digest of gap 1; the address lives only during the walk and is never a memo key |
| `std::mem::discriminant` of `Prim` as part of a hash key, since `Prim` has no `Hash` | `Made::Call` | None | `Prim` is an enumeration, so its value is the key |
| `fn(&mut Memo) -> &mut HashMap<K, V>` choosing the table a generic memo helper fills | `Tx::cached`, `Tx::translated` | None | A function over the memo record returning the updated record |
| `std::mem::replace` of the context field around a sub-transfer | `Tx::within`, `Tx::cached` | Mutation | The context passed as an argument and returned with the result |
| `imbl::HashMap` scopes numbered once by `(scope, name, binding)` | `Tx::bind` | None | Zed's maps are values; the numbering is a map from that triple to a number, in a state receiver |
| A trait with a default method, passed as `&mut dyn Search`, implemented by local structs (`First`, `Met`, `Any`) | `branch`, `witness`, `exact_search` | Interfaces (L10) | A record of two functions over a search state, the state returned with the result |

## Entries from T14-heap (`zed-rt/src/heap.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A cell's index and generation packed into one `i64` by shifts and masks | `Word::cell`, `Word::index`, `Word::generation` | Bit operations | A pair of integers in the word, or the bit words of gap 4 |
| A free list of cell indices, a `Vec` popped and pushed, beside the cells the heap mutates in place | `Heap::alloc`, `Heap::free_cell` | Mutation | A state receiver over the cells and the free list |
| `BTreeMap<Value, usize>` that interns the empty tuple and bare atoms across calls | `Heap::uncounted` (`bare`) | Shared tables across pure calls | A map in the heap's state receiver |
| `Option<Value>` in each cell, set at the first read and cleared when the cell is freed (T14-R1) | `Cell::value`, `Heap::value`, `Heap::fresh`, `Heap::free_cell` | Lazy cells (gap 3), Mutation | A map from cell to value in the heap's state receiver, its entry removed when the cell is freed |
| A `match` arm guarded by `if let` on the cell's kept value | `Heap::read` | None | An `is` test before the `match` |
| `Result<(), String>` from `inc`, passed on by `?`; `rt_inc` records it in the run with `get_or_insert` (was an `Option<String>` kept until the next `dec`, changed in T14-heap-rest) | `Heap::inc`, `hooks::rt_inc` | Early exit | `inc` returns the error as a value |
| An `enum` whose variants borrow the heap's cells or table (`Shape<'h>`) while a `match` reads them | `Heap::shape` | None | A value returned by the read |

## Entries from T14-heap-rest (`zed-rt/src/heap.rs`, `zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `return` from inside the arms of a `match` that otherwise yields a value | `Heap::is_in` | Early exit | Each arm yields an `Option` of the answer, or the kind is a separate function |

## Entries from T14-hooks (`zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A thread-local `RefCell<Option<State>>` borrowed once per hook and split into `&Tables` and `&mut Run` | `hooks::with`, `with_args` | Mutation | The run is a state receiver passed to each hook; the tables are an immutable value beside it |
| `std::mem::take` of a buffer, used as a borrowed slice, then cleared and put back | `with_args`, `matched` (`outs`) | Mutation | A state receiver; the runtime reuses a list held once |
| `Vec<Option<_>>` filled at first use, indexed by node or constant | `Run::shapes` (and `Run::ropes`, removed by T14-rope) | Mutation | A map in the run's state, or the shape computed once at compile time for constant names |

## Entries from LR4 (`zedc/src/ast/mod.rs`, `zed-tools/src/fuzz.rs`)

- No new gap. `Builder::make_expr`, arm `"Expr12"`, reads its two children with `let [l, t] = kids[..] else { unreachable!(..) }`, a slice pattern in a `let … else`; both are rows of the appendix (`let_else`, slice patterns) with the rewrite already listed: test the length, then index.

## Entries from T11-fix-rest (`resolve.rs`, `parse/engine.rs`, `zir/text.rs`, `zir/lower.rs`, `zir/canon.rs`, `zed-kernel/src/eval.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `imbl::Vector<usize>`, a persistent vector, so that every use of an overload set shares one list | `resolve::Ref::Bound`, `Found::Bound`, `Bound.ids` | None | Zed lists are shared values already |
| `std::mem::take` of the expected set into the saved stack at a `!`, and `mem::replace` with an empty domain that allocates nothing while the rules hold an edge's facts | `parse::engine` (`saved`), `zir::canon::normal_edge` | Mutation | The parser state and the edge are state receivers; the rules take the facts and return the new ones |
| `Peekable` over an owning iterator, with `next_if` to move each line's parts out | `zir::text::build` | Mutation, iterators | A recursive descent over the list of lines that returns the rest of the list |
| `Cow<'_, [Term]>`, inputs moved into a term when owned and copied when borrowed | `zir::lower::node_term` | None | Zed shares lists, so the term holds the inputs |
| A pair of slices read as one list (`args.0` then `args.1`) | `zir::lower::raise_region` | None | `++` of two shared lists, or the index split the same way |
| A cursor (`next: usize`) into a sorted `Box<[Value]>` held in an `Rc`, and `binary_search` for membership | `eval::Pull`, `Definedness::domain` | Mutation | A fold over the domain's keys, and a sorted set's membership |

## Entries from T11-uses-of (`zedc/src/elab.rs`, `zed-kernel/src/eval.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A hash key over a shared list (`ListKey`) hashed by its first element and length, compared by `Vector::ptr_eq` before its content, so a use finds its group in O(1) | `elab::Tables::new` | Identity (gap 1) | Number each overload set when `resolve` makes it and record the number in the use, so the group is found by an integer key |
| `<[V; 2]>::try_from(Vec)` to move both arguments out of the argument list after its length is checked | `eval::Machine::prim` | None | A tuple or list pattern of two items |
| Join nodes numbered after the items in one `Vec<Vec<usize>>`, told apart by `index < items` | `elab::topo_joined`, `elab::place` | None | A sum type of item and join for each node, or the same numbering |

## Entries from T14-rope (`zed-kernel/src/text.rs`, `zed-rt/src/heap.rs`, `zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| One `Arc` rope node shared by the kernel and the native heap, so a string crosses between them with no copy | `Obj::Str(Text)`, `Heap::value`, `hooks::text` | None | Zed shares values; one runtime holds one string type |
| `OnceLock<Arc<str>>` in each join node, the text written out on the first read through `&self` | `Text::flat`, `Deref for Text` | Lazy cells (gap 3) | `String` ropes in the standard library (L6.16): the text written out by a function, its result kept by the runtime, or no cache |
| Byte and character counts kept in each node and added at a join | `Node::len`, `Node::chars` | None | Two integer fields of the rope node |
| `Mutex<Option<(Text, Text)>>` for a join's parts, taken through `&self` once the text is written out | `Node::parts`, `Deref for Text` | Lazy cells (gap 3) | The rope's written-out form replaces the node in the runtime's cache, or no cache |

## Entries from L3.1 (`zedc/src/ast/`, `format.rs`, `resolve.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A generic enum `RangeEnd<T>` with a method returning `Option<&T>`, used for both expressions and patterns | `ast::RangeEnd`, `ExprKind::Range`, `Pattern::Range` | None | A union of atoms with a payload of the type parameter: `#below(T) \| #through(T) \| #open` |
| A generic method taking `impl FnOnce(&mut Self, usize) -> Result<T, Error>`, so one helper builds the end of a range for both expressions and patterns | `Builder::range_end` | Mutation | The builder is a state receiver; the function argument returns the new builder with the result |
| `match (layer, kids)` on a tuple of an integer and a slice pattern (`&[op]`, `&[_, unordered]`) | `Builder::reduce_tail` | Slice patterns | Test the length, then index (the appendix's row for slice patterns) |
| `unreachable!` arms for the L3 forms that resolution refuses | `elab.rs`, `check/mod.rs` | Partial match | As for L2.1: a total match whose L3 arm returns the refusal, or a narrower type from resolution |

## Entries from T14-occ (`zed-kernel/src/provenance.rs`, `value.rs`, `family.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A global `AtomicU64` handing out blocks of ids to a thread-local `Cell` counter, so that each new family gets a fresh id (lists had one too until T14-occ-id) | `fresh_id` in `family.rs`; `Family::made_from`, `Family::extend` | Identity (gap 1), mutation | A content digest as a field (gap 1), or an id counter threaded as state through the machine |
| `imbl::OrdMap::diff`, which skips subtrees two maps share | `Held::base`, `short_diff` | Identity (gap 1) | A diff that compares entries; it costs the size of the smaller map rather than the change, unless the runtime gives `==` a shortcut on shared nodes |
| `HashMap` keyed by family ids and by the address of a list (`Items::addr`) while the facts are borrowed, filled during the pass | `Held::{sets, seen, done, made}` | Identity, mutation | A state receiver over a map keyed by family ids and list digests (gap 1) |
| A persistent cons list in `Arc` with a cached hash and depth, whose `Eq` first tests `Arc::ptr_eq` | `Position::{child, eq}` | Identity (gap 1) | A list of child indices with the hash as a field; `==` compares the hashes, then the indices |
| `Drop` that unlinks a long cons list in a loop, so that dropping it does not recurse | `Position::drop` | No destructors | The runtime frees long lists without recursion (step L6.13) |

## Entries from T14-rope-len (`zed-kernel/src/text.rs`, `zed-kernel/src/words.rs`, `zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `usize::checked_add` of two byte counts, refused past `usize::MAX` | `Text::join` | Machine integers | With `int` counts the sum never wraps; the refusal stays as an `if` comparing the sum with the largest length the runtime can address |
| `i64::try_from` of a count, with a big integer when it does not fit | `words::word` (`Len`), `hooks::node` (`Len`), `store::cell::Cell::literal` (a string's length; past `i64` the ray from `i64::MAX` up) | Machine integers | Vanishes: `len` returns an `int` |

## Entries from L6.1 (`zedc/src/ast/`, `format.rs`, `resolve.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A stable `sort_by_key` on a key method of an enum, shared by the builder and the formatter | `StmtKind::place`, `Builder::block`, `ast::unit`, `Formatter::stmts` | None | A `sort` by a key function; the prelude's sort is stable |
| `match *self.kids(k) { [name, set] => …, [e] => … }`, slice patterns on a dereferenced slice | `Builder` index keys | Slice patterns | Test the length, then index (the appendix's row for slice patterns) |
| A `HashSet<&str>` borrowed from the statements, so each indexed family is bound once | `Resolver::declare` | Borrowed keys | A set of names; strings are values, so no borrow is needed |
| `unreachable!` arms for the L6 forms that resolution refuses | `elab.rs`, `check/mod.rs` | Partial match | As for L2.1 and L3.1: a total match whose L6 arm returns the refusal, or a narrower type from resolution |

## Entries from OSP-lit (`zedc/src/docs.rs`, `zed-kernel/src/num.rs`, `zedc/src/run.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `slice::partition_point` with a closure, a binary search over the token list | `docs::check` | None | A binary search over a sequence by a predicate, from the L3 library |
| `Option<(usize, Span)>` matched as `Some((n, span)) if *n == next` through `&mut`, then extended in place | `docs::check` | Mutation | A fold over the doc comments whose state is the open block, returned with each step |
| `str::parse::<f64>()` and `str::parse::<f32>()`, correctly rounded by the standard library | `num::literal_f64`, `num::literal_f32` | Missing primitive | A prelude cast `f64(text)` that rounds to nearest with ties to even, as `num::literal_f64` does |
| A sink typed `FnMut(&str, &str) -> Result<(), (String, String)>` for the path and reason of a failed write | `run::commit` | Mutation | A function returning the acknowledgment atom `#ioError(op:, path:, why:)` directly |

## Entries from T11-fix-store (`zedc/src/store/hull.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A builder that takes `mut self` and changes its `imbl::OrdMap`s in place through `get_mut` and `entry(..).or_default()`, which copy only the shared nodes on the path; `contains_key` first, since `remove` and `get_mut` copy that path even for an absent key | `Hull::and`, `Hull::join`, `used` | Mutation | Zed's map updates return new maps; the cost matches only if the runtime updates a map in place at its last use (step L6.13) |

## Entries from T-zone (`zedc/src/store/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `imbl::OrdMap` of bindings, cloned into each arm's scope and shared by structure | `Scope::{bind, unbind, join, close}` | None | A Zed map is a value; cloning is sharing |
| A `u64` counter in the scope that orders bindings | `Scope::bind` | Mutation | The scope is passed and returned, with the counter as a field |
| A worklist `Vec` with a visited `BTreeSet`, then a sort by order and a right fold into nested `Term::Let` | `Scope::close` | None | A `fold` over the worklist with a set in its state, then `sort` and a fold |
| `matches!(**e, Term::Lam(..))` on an `Arc<Term>`, and `Option::then` | `Scope::bind` | None | A pattern test `is Lam` |

## Entries from OSP-order (`zedc/src/store/wto.rs`, `iterate.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::ptr::eq` on two forms as a shortcut to `Equal` before comparing them structurally | `impl Ord for VertexKey` | Identity (gap 1) | The structural comparison alone, or the runtime's `==` shortcut on shared values; the address comparison before it already leaves only nodes of one binding and one address |
| `Ord` written by hand for a struct of three fields, so that the form, a type parameter, is compared last and only on a tie | `VertexKey::cmp` | None | A tuple `(name, address, form)`, which compares left to right (`zed/prelude/iteration.zed`, `solve`) |
| A stack of `&mut Element` walked to rewrite vertex numbers in place in a nested tree | `wto::ordered_by` | Mutation | A map over the tree of elements that returns a renumbered tree, by an explicit stack or by recursion on the nesting depth |

## Entries from ST (`zedc/src/store/product.rs`, `presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `imbl::OrdMap::diff`, which skips subtrees the two maps share, to find the names a join or a reduce must visit | `Scope::join`, `changed`, `Scope::reduce_with` | Missing | Zed's maps are values but have no structural difference; it needs a `diff` word that the runtime answers in time proportional to what differs, or the scope keeps its own list of changed names |
| A cache field whose `PartialEq` always holds, so that comparing scopes ignores it | `Reduced` | None | A field left out of the comparison the port writes for `Scope` |
| `std::mem::take` of the cache at the start of a reduce, put back at the end | `Scope::reduce_with` | Mutation | A state receiver, or the cache returned with the scope |
| A persistent set of conjuncts kept with two persistent indexes in step (by name, and by term and relation for the tighter-bound rule), each update touching all three | `conjuncts::Conjuncts` | None | A Zed record of three persistent maps, updated together by one function; no gap beyond the `diff` row above |
| `imbl::OrdSet::diff` of two relations to find the conjuncts one side added or removed | `Scope::join`, `Scope::due`, `Scope::narrow` | Missing | As for `OrdMap::diff` above |
| `imbl::OrdMap::range` from a key, taken while the first part of the key matches, to drop the cached entries of one conjunct | `Scope::due` | None | An ordered-map range query from a key, which Zed's ordered maps need to offer |
| A snapshot field held as `Option` and swapped with `Option::replace` at each reduce, so the previous snapshot and the new one are both in hand | `Seen`, `Scope::enumerate` | Mutation | A state receiver, or the old snapshot returned with the new scope |
| A persistent union-find of block trees and a block-cut forest (`imbl::OrdMap` from conjunct to block, block to members, name to blocks, and parent links), rerooted and merged in place of a rebuild as conjuncts come and go | `conjuncts::Blocks`, `Conjuncts::and`, `Conjuncts::swap`, `Conjuncts::remove` | None | A Zed record of persistent maps updated by one function; union by size without path compression keeps it a value |
| A map from a set of atoms to the conjuncts taken out of a relation (`BTreeMap<BTreeSet<Atom>, Vec<Arc<Formula>>>`), passed by `&mut` through `and_one` so each new conjunct takes the place of an old one with the same atoms (`Vec::swap_remove`), the rest removed after | `Conjuncts::swap`, `Conjuncts::and_one` | Mutation | A state receiver, or the map returned with the relation from each step of the fold over the new conjuncts |
| `std::mem::take` of the relation out of the scope while the worklist reads its blocks and narrows the names, and putting it back after | `Scope::project` | Workaround | In Zed the relation and the names are separate values of one record; the worklist reads one and returns the other, so nothing is taken out |

## Entries from OSP-diag (`zedc/src/rejection.rs`, `check/read.rs`, `check/ty.rs`, `testing.rs`, `zed-rt/src/heap.rs`, `zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `macro_rules!` that declares the enum of rejection rows, its list of every row and its name function from one table | `rejection::rows!` | No macros | An atom union with a constant list of `(row, name)` pairs; the name function is a lookup in it |
| A cargo feature that adds a field to a struct and a body to a method, off in a release build | `Cell::site`, `Heap::site`, `Heap::allocating`, `Display for Ty` and `Sig` under `printed-types` | No conditional compilation | A build mode of the runtime unit: the test build imports a counting heap, the release build the plain one, both with one interface |
| A thread-local `RefCell` that a test turns on and reads back, filled from inside `Display` | `ty::printed::{start, take, record}`, `hooks::COUNTED`, `zed_native::counted` | Mutation (gap 11), no global state | The printer and the run return what they record beside their result, and the test reads it there |
| `BTreeMap` keyed by `(&'static str, Option<usize>)` to group the live cells | `Heap::survivors` | None | A family keyed by the pair, summed by a reduce |
| A text-level pass over a printed type that tracks parenthesis depth and quotes to cut the `for` clauses | `read::clauses` | None | A fold over the characters with the stack of open groups as its state |
| `<[String; 1]>::try_from(Vec)` to move the one item out, the vector given back otherwise | `Sig::text` | None | A list pattern of one item |

## Entries from ST-deep-stack (`zedc/src/store/presburger/deep.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `impl Drop` with a work list on the enum `Formula`, so a value nested 100,000 deep is freed without recursion | `presburger/deep.rs` | None | Removed: the runtime frees values, and must free a deep chain without recursion itself (as for T2-parse's row) |
| Moving parts out of a value whose type has `Drop` by `mem::take` and `mem::replace` through `&mut` (`into_parts`, `into_negated`, `Con::take`), since Rust forbids moving fields out of such a value by a pattern | `Formula::and`, `or`, `negate`, `Parts::of`, `Conjuncts::and_held` | Workaround | A pattern that binds the parts; with no `Drop` in Zed the workaround goes |
| Hand-written `Clone`, `PartialEq`, `Ord`, `Hash`, `Debug` and `Display` over explicit stacks, giving what the derived forms give | `presburger/deep.rs` | Missing | Structural equality, order, hashing and printing are the runtime's, which must not recurse on depth |
| A generic post-order fold with a context passed down, results kept on one `Vec` and split off per node | `Formula::fold`, used by `map_cons`, `forget`, `holds_as`, `nnf` and `Clone` | None | A recursive function, once the machine keeps frames on the heap; or a state receiver over a list |

## Entries from OSP-drop (`zedc/src/check/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An explicit stack with a visited `HashSet<Span>`, both mutated while walking back from the bound value to where each dropped atom enters | `Ck::entries` | Mutation (gap 11) | A fold over the worklist with the visited set in its state |
| An explicit stack over nested `else` nodes, with an `if let` guard in a match arm to tell an atom default from any other | `named_defaults` (removed by OSP-drop2) | None | A loop over the `else` chain, and a nested `match` on the default in place of the guard |
| `Src::Call` holding a borrowed `&'a Expr` beside the function id, so the walk can reach the call's arguments | `Src`, `Ck::entries` | None | The call node itself as the source, a shared value |

## Entries from TD-refusals (`zedc/src/store/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An `FnMut` closure that prints the constraint once into a captured `Option<Arc<str>>` (`get_or_insert_with`) and is called at each refused question of one projection | `Scope::project_part` (`refuse`) | Mutation (gap 11) | The text is printed before the projection when it may be needed, or each call returns the text with the refusal; printing once per refused part costs the same |
| A struct whose derived `Ord` (field order: constraint, how it was asked, cause) is the order of the warnings, kept in an `imbl::OrdSet` | `Refused`, `Scope::warnings` | None | A record in a set ordered by its fields in that order |

## Entries from ST-join (`zedc/src/store/conjuncts.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `BTreeMap` from block to the conjuncts it loses, with a `Vec` of the blocks in the order first met, filled through `entry(..).or_default()` | `Blocks::remove` | None | A fold over the removed conjuncts into a map of lists and a list of blocks |
| A slice pattern with a guard that changes `self` (`[g] if self.unlink(b, g) => {}`), so the guard both tests and does the unlinking | `Blocks::remove` | Mutation (gap 11) | `unlink` returns the new forest or nothing, and a `match` on that result picks the split |
| The block of a conjunct kept in a local while the forest is merged around it, since looking the conjunct up again compares it whole (`Ord` on `Arc<Formula>`) | `Blocks::place`, `Blocks::split` | Identity (gap 1) | The same local, carried through the fold; with content digests a lookup would cost O(1) and the local would be a choice, not a need |

## Entries from CAP-bits (`zed-kernel/src/num.rs`, `num/bound.rs`, `num/factor.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `u128` products for a 64-bit product modulo a 64-bit number | `factor::mul_mod`, `factor::split` | None | `(a * b) mod m` on unbounded `int`, the operands' ranges `int[0..<2 ** 64]` letting the plan use two words |
| `BigUint::bits`, `trailing_zeros`, `bit`, `<<` and `>>` on big integers, and `u64::leading_zeros` and `trailing_zeros` | `bound::Bound`, `Rat::small_integer`, `valuation`, `factor::factor` | Bit operations on `int` | Library words on `int` (`bits`, `trailing_zeros`, `shl`), as for the counts in the row of `count_ones` above |
| `Cow<'_, Rat>`, an operand borrowed unless it must be rebuilt over more primes | `Rat::aligned`, `Value::as_integer` | None | Zed shares values, so the function returns the operand or the rebuilt one |
| `&dyn Fn(&BigInt, &BigUint) -> bool`, the exact test of a near-tie passed into the rounding | `bound::round`, `Quotient::floor_scaled` | None | A function value |
| `Box<[(u64, BigInt)]>`, the primes and exponents of a number | `Rat::pows` | None | A shared list of pairs |
| `Vec::<u64>::try_reserve_exact`, asking the allocator for a block and freeing it at once, to learn before a build whether its memory exists | `num::room` | Zed has no fallible allocation a program can ask for | A runtime word that reports whether the allocator grants `n` words, failing as an error atom rather than stopping the process |

## Entries from L25.8 (`zedc/src/mutate.rs`, `elab.rs`, `stage.rs`, `testing.rs`, `zed-kernel/src/provenance.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An explicit stack `Vec` of (marked term, term, position) pushed and popped to walk two terms together in preorder | `mutate::sites` | Mutation | A fold over a worklist list with the found mutants as its state, or recursion on the term's depth |
| A copy of the definition walked root to leaf by a reborrowed `&mut Term` (`provenance::child_mut`, which copies a shared `Arc` child first by `Arc::make_mut`), and the one node assigned in place | `mutate::apply` | Mutation | An update of the term at the position's path of child indices, which copies only the nodes on that path of a persistent term |
| `std::mem::discriminant` to compare two terms' variants without their fields | `mutate::sites` | None | A `match` on the pair of terms with one arm per variant and a final arm for a mismatch |
| A lazily filled `Vec<Option<Term>>` of each definition's remixed original, written by index the first time a mutant of that definition is seen | `mutate::run` (`built`) | Mutation | A map from definition to remixed original built before the loop over the mutants, or a state receiver |
| `stage::Remix::mix(&mut self, …)`, a mixer that keeps its memo across calls | `mutate::run` | Shared memo (gap 2) | A state receiver that returns the memo with each mixed term |
| `.expect` on a marked constant's integer and on a position inside its definition | `mutate::sites`, `mutate::apply` | Abort (gap 8) | As gap 8 |
| `text.as_bytes()` scanned for the operator after a span, skipping blanks, parentheses and `//` comments | `mutate::operator_at` | Bytes (gap 5) | A fold over the text's characters from the span's end |
| `Option<(usize, &Arc<Term>)>` passed down to replace one definition while closing a term | `testing::Swap`, `Cones::close_with`, `testing::row`, `testing::wave` | None | An optional pair argument |

## Entries from OSP-drop2 (`zedc/src/check/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Two `HashMap<Span, KType>` fields of `Ck` (`unnamed`, `made`) and a `HashMap<usize, Span>` (`alias`), written as each expression is checked and read by later ones | `Ck::expr`, `Ck::unnamed_of`, `Ck::entries` | Mutation (gap 11) | Maps threaded through the checker's state, as `seen` would be |
| A loop over an array of `(&mut HashMap, Option<KType>)` pairs, to insert or remove one entry in each of two maps | `Ck::expr` | None | Two calls of one helper, or a fold over the pairs |
| Closures that borrow `self` immutably (`u`, `union`, `made`) inside one method | `Ck::unnamed_of` | None | Local functions taking the maps as arguments |

## Entries from S22a (`zedc/src/store/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A persistent treap in `Rc` nodes, each holding its subtree's least and greatest value and a lazy affine tag pushed down on a split, with a priority computed from the piece's ends, shared by every summary built from it | `PaNode`, `Tree`, `split_at`, `join_treap`, `slice_treap`, `apply_tag`, `invert_treap` | Identity (gap 1) | A Zed tree value: an update makes new nodes along one path and shares the rest, which the runtime must keep at `O(log n)`; the priority is a field, so no identity is needed |
| The sticky `ROUNDED` flag saved, cleared and restored around the hull of a term, so a rounding while computing the hull is seen and not reported | `Tx::clip`, `Tx::invert_pa` | Mutation, global state (gap 11) | The hull computation returns whether it rounded with its result; no flag |

## Entries from ENDS-dag (`zedc/src/stage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Raw pointer `*const Term` as the key of the map from part to number while the term is read | `Reader::read`, `Reader::got` | Identity | Keyed by the content digest of gap 1; the address lives only during the reading and is never a memo key or an order |
| An explicit stack `Vec<(&Term, bool)>` read in post-order, results pushed to a `Vec` by number | `Reader::read`, `each_part` | Mutation | A fold over a worklist list with the map from part to result as its state |
| An arena of trie nodes (`Vec<SetNode>`) with a hash table from node to number (hash-consing) and a memo `HashMap<(Set, Set), Set>` of unions, all filled through `&mut self` | `Sets::make`, `Sets::union` | Shared memo (gap 2), Mutation | A state receiver holding the arena, the table and the memo, returned with each set made; or sets made identical by the content digest of gap 1 |
| `u32::leading_zeros` and bit masks to find the highest differing bit of two names | `Sets::join`, `above` | Bit operations (gap 4) | As gap 4 |

## Entries from S22b (`zedc/src/store/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `c - v` computed in `i128` and turned into an end by `End::lower` and `End::upper`, which set the global `ROUNDED` flag when the end leaves `i64` | `reflect` | Machine integers; Mutation, global state | Zed's `int` is unbounded, so `c - v` needs no wider type and no rounding flag |

## Entries from T6 (`zed-kernel/src/types/bes.rs`, `rec.rs`, `empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Vec<u32>` stamps and marks overwritten in place, reset by advancing a counter | `bes::Stamp`, `bes::Scratch` | Mutation | A persistent array per pass, or a map from node to the pass that marked it; the counter trick needs mutable arrays |
| A closure `Box<dyn Fn() -> Option<bool> + Send + Sync>` stored in a recursive type node, computed once through `OnceLock` | `types::Rec::judge`, `rec::Env::judged` | Laziness | A lazy field of the group's instance, forced on first use |
| Explicit work stack of `(node id, &Arc<Node>)` pairs filling a graph allocated ahead | `rec::judge`, `rec::kids` | Mutation | A fold over the body tree that returns the nodes it adds |
| `impl Iterator for Values` holding an odometer `Vec<usize>` advanced in place, and a `BTreeSet` of the tuples given | `types::Values::next` | Mutation, laziness | A lazy stream whose state (box, positions, tuples given) is passed from one value to the next |
| `std::mem::take` of the lists out of one iterator into the next, in `each_value` | `Type::each_value` | Moves | The lists threaded through a fold over the types in order |
| Explicit stacks of `Step::Enter`/`Step::Leave` and of slice iterators, with `Vec<Option<Item>>` taken in place as each node is visited | `print::Printer::walk`, `print::Printer::write` | Mutation | A fold over the graph in post-order returning the texts and the order, with the visited set as a persistent map threaded through it |
| `&dyn Fn(&mut Printer, &A) -> Text` callbacks that borrow the printer mutably, so one diagram walk serves tuple and morphism parts | `print::Printer::part` | Generic closures over mutable state | A function generic over the literal kind, returning the texts and the nodes found instead of writing them into shared state |
| Explicit post-order stack over the expression graph with `HashMap` memos keyed by node id, holding `Option<imbl::OrdSet>` sets merged smaller into larger | `bdd::Part::forced` | Mutation | A fold over the graph in post-order with a persistent map keyed by the node id, returning the two sets |
| A counter of open needs per simulation pair decremented in place, and a worklist of failed pairs | `empty::Simulation::holds` | Mutation | A fold over the failures that returns the new counts as a persistent map |
| `self.cycles` entries written for every type on a walked path (`Vec` path and `BTreeMap` of positions) | `empty::Search::find_cycle` | Mutation | The walk returns the path and the result; the caller folds them into a persistent map |
| A region shrunk to a piece in place, the search run on it, and the region put back; a counter `give_ups` read before and after to learn whether the search showed a value | `empty::Search::refine` | Mutation | The search takes the piece as an argument and returns whether it showed a value with the verdict |
| A global atomic counter giving each diagram node and expression its id at construction | `bdd::NEXT`, `Bdd::node`, `Part::expr` | Global mutable state | Ids from hash-consing in a persistent table threaded through construction, or content digests |
| `Vec<OnceLock<Type>>` members set in two rounds (recursive members, then plain members in post-order) before they are read | `rec::Group::instance`, `rec::eval` | Mutation, laziness | A fold over the plain members in post-order building a persistent map from index to type, after the recursive members |
| A `shut` array of six optional key sets, one per universe, filled in place by a first pass over the types: the keys every cofinite type lists, intersected in place (`retain`) starting from the shortest list | `empty::overlaps` | Mutation | A fold per universe over the cofinite types' lists returning their intersection as a persistent set |
| Union-find with path halving: `parent` links rewritten in place while a root is found | `empty::overlaps` | Mutation | A persistent map from key to the first type holding it, folded over the types, joining a type to the classes of its keys |
| A `Vec<bool>` window of steps marked in place by each negated class, the window doubled | `empty::least_length` (removed in T6 repair 6: `residue_length` picks the length by conditional expectations) | Mutation | A fold over the classes returning the set of held steps in the window, as a persistent bit set |
| A list kept as its length, a `num_bigint::BigUint`, with `%` and `-` on it in the walk | `empty::Rep::List`, `residue_length`, `greedy_length`, `Search::list_member` | None | Zed's `int` is unbounded; the length is a plain `int` and the list a record of it |
| A `BTreeMap<Type, BigUint>` of the rest types met, cleared in place after the length left is cut to its remainder modulo the steps between | `empty::Search::list_member` | Mutation | A loop whose state (type, length left, persistent map of types met) is passed to the next round, the map replaced by an empty one after the cut |
| `Option<Option<KType>>` filled on first use inside an `all` closure (`get_or_insert_with`), so the kernel type of the target is built only when some piece needs it | `zedc` `check/ty.rs` `Ty::sub` | Laziness, mutation | A lazy local bound before the fold, forced on first use |
| Address of a shared slice (`xs.as_ptr().addr()`) with its length as the memo key of one membership test, held while the value is borrowed and never iterated | `types::Type::contains` | Identity | A hash-consed id of the value, as for `deep::walk`; the recorded exception at `Type::contains` |

## Entries from OSP-neglit (`zedc/src/ast/neglit.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `OnceCell<HashSet<&str>>` of the names written bare, shared by every builder of one source and filled on the first rejection through `&self` | `Builder::written_bare`, `ast::with_holes` | Lazy cells (gap 3) | The set made in one pass before building, or threaded through as a state receiver that is filled on first use |
| A `HashSet<&str>` borrowed from the source text | `bare_names` | Borrowed keys | A set of names; strings are values, so no borrow is needed |

## Entries from SCALE-bytes (`zed-alloc-count/src/lib.rs`, `tests/src/scaling.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `#[global_allocator]` and `unsafe impl GlobalAlloc` forwarding to `System` | `zed_alloc_count::Counting` | Foreign library | Test harness only: the Zed runtime's allocator counts the bytes itself, read through an `@ffi` binding |
| `thread_local!` with a `const` `Cell<u64>`, added to through `&self` | `zed_alloc_count::BYTES`, `add`, `allocated` | Mutation | A count kept by the runtime per thread and read as a value |
| `#[expect(unsafe_code, reason = ...)]` and a crate lint table that denies `unsafe_code` instead of forbidding it | `zed-alloc-count` | Attributes | None needed: Zed has no lint attributes |
| `std::thread::scope` with a stack size, returning the closure's value and its thread's count | `scaling::on_a_thread` | None | A task with its own stack, as in T2-eval |

## Entries from R10-stack (`zed-rt/src/stack.rs`, `zed-native/src/lib.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `libc::mmap` with `MAP_NORESERVE` and `mprotect` of a guard page, sized by `libc::sysinfo`; `munmap` in `Drop` | `Stack::new`, `Drop for Stack` | System calls, no destructors | Stays in the Rust runtime (L6.13); a Zed runtime needs a foreign call to map memory and a scope that unmaps it |
| `psm::on_stack`, switching the machine stack for one call | `Stack::run` | Stack switching | Stays in the runtime; a Zed program has no access to the machine stack |
| `catch_unwind` on the new stack and `resume_unwind` on the old one | `Stack::run` | Early exit (gap 12) | Errors are values in Zed; the runtime returns the run's error across the switch |
| A raw pointer `*mut c_void` to the mapping | `Stack::base` | Identity (gap 1) | An address held by the runtime, not by Zed code |

## Entries from ST-arms-quad (`zedc/src/store/presburger.rs`, `preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Rc<Parts>`, a disjunct shared by the level above, a search and the parts a disjunct was settled from, so that no level copies the nest below it | `Parts.ors`, `settle`, `project_parts`, `pick` | None | Zed shares values, so a disjunct is the parts themselves |
| `OnceCell<OrdSet<Atom>>` on `Parts`, the atom set of a disjunct filled the first time it is asked for through `&self`, and used as the visited mark of the walk that fills it | `Parts::atoms` | Lazy cells (gap 3) | The atom sets built bottom up when the parts are made, or a map from a hash-consed id of each part, threaded through as a state receiver |
| `imbl::OrdSet<Atom>`, a persistent set cloned in O(1), so that a disjunct's atom set starts as its largest child's, shared, and the others are inserted | `Parts::atoms` | None | Zed's sets are values that share structure, so the larger set is reused as is |
| `Cell<u64>` on `Parts`, the stamp of the last search that found the parts not to hold, set through `&self` during a walk of shared parts, with stamps from a global `AtomicU64` counter | `Parts::failed`, `Parts::witness`, `fresh_stamp`, `pick` | Mutation, identity, global state | A set of the hash-consed ids of the parts found not to hold, threaded through the search as a state receiver and emptied when the model changes |
| `HashMap<(BTreeMap<Atom, Int>, Rel), usize>`, the index of the bound kept for each left-hand side and comparison, so that a bound written again replaces or is dropped against the one kept, in place | `Linked::meet`, `Linked.by_terms` | Mutation | A map from the terms and comparison to the bound, updated as a value, with the constraint list rebuilt from it |
| An explicit stack of frames borrowing the parts (`Frame<'a>`), with the output vector truncated back to a frame's mark when the part fails | `Parts::witness` | Mutation | A fold over the parts returning the list of held parts or a failure, with the stack as a list value |
| `Option<&Formula>` and `Option<Formula>` filled on first use (`get_or_insert_with`) for the summary of a level | `project_parts` | Lazy cells (gap 3) | The summary built before the loop when any hull has two finite bounds, or a lazy `let` |
| `thread_local!` `Cell<u64>` counting the parts the search tests, read and reset by a test through `parts_tested` | `presburger::TESTED`, `Parts::witness`, `parts_tested` | Mutation, global state | The count returned with the search's answer, or a trace effect the test handles |
| `std::ptr::eq` on two formulas as a shortcut to `Equal` in a hand-written `Ord` and `PartialEq` that otherwise compare as the derived ones, so a lookup that finds the very formula it holds does not walk it | `impl Ord for Formula`, `impl PartialEq for Formula` (`presburger/deep.rs`) | Identity (gap 1) | The runtime's `==` shortcut on shared values, or keys by the content digest of gap 1 |
| `impl Drop` with a work list on `Parts`, taking each nested disjunct no other holder shares by `Rc::try_unwrap`, so a nest 100,000 deep is freed without recursion; and `Parts::of` building nested disjuncts on an explicit stack of frames | `Parts::drop`, `Parts::of` | None | Removed: the runtime frees values without recursion (as for `Formula`), and `of` becomes a fold over the formula |
| A `bottom` flag set on a scope while its names are kept as they were, and the names rebuilt as bottom only for a scope that is shown | `Scope::reduce_case`, `Scope::empty_if_bottom` | None | A record field set by the reduce that returns the scope; the shown scope is mapped to bottom names once |

## Entries from HOLE-oneline (`zedc/src/lex/string.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `match` arm guarded by `if let` on the comment that starts at the position, and `if … && let Some(nl) = …` testing a flag and binding the first line break | `hole_end` | None | An `is` test before the `match`, and an `if` on the flag around a `match` on the break |
| `slice::partition_point` over the sorted line-break positions, the first break in a range | `Holes::first_break` | None | A binary search over a sequence by a predicate, from the L3 library (as `docs::check`) |

## Entries from TD-values (`zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A resumable generator per type as an explicit state machine (`At::Start`, `Tuple`, `Past`) whose step returns `Err((maker, position))` for a value it needs first, driven by an explicit stack | `types::Values::fill`, `Maker::step` | Laziness, mutation | A `gen` per type over the makers' lists, or the same loop as a state receiver holding every maker's list and position |
| `split_at_mut` of the makers, so a maker grows its own list while it reads the lists of the makers before it | `types::Maker::step` | Mutation | The step returns the new value and state, and the loop puts them in the persistent list of makers |
| `std::mem::replace` of the maker's state with `At::Start`, put back on the path that waits | `types::Maker::step` | Mutation | The step returns the next state as a value |

## Entries from LIN-probe (`zedc/src/store/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec<Vec<bool>>` of which disjuncts a point found so far holds, beside the disjunctions; one row taken with `std::mem::take` while its disjunction is tested and put back after, the other rows set in place when a point is found | `probe` | Mutation | A loop whose state is the disjunctions with their flags as one list of records; a point found returns the list with its flags or-ed |

## Entries from CAP-pow32 (`zedc/src/store/revision.rs`, `preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An enum of the solver's `Int`, the kernel's `Arc<Rat>` (an unbuilt prime power) and a parity alone for a count of factors past `u32::MAX`, read only by `is_zero`, `is_odd` and `to_u32` | `revision::Exponent` | None | Zed's `int` is one type, so the exponent is an `int` or a parity; a port must keep the kernel's unbuilt form or `10 ** 10 ** 9` is built |
| `Option<u32>` with `checked_add` and `zip`, a count that is `None` past `u32::MAX` | `preimage::Count` | Fixed-width integers | `Option<u32>`, or an `int` compared with `2 ** 32`, as it is O(1) only while bounded |
| `Op` no longer `Copy`, passed as `&Op` to `tonicity`, `forward` and `backward` | `revision`, `preimage`, `preimage_ref`, `product`, `check` | None | Values are shared in Zed; the reference goes |
