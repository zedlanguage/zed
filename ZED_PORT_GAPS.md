# Gaps between the compiler's Rust and Zed

This file lists what the Rust compiler relies on that Zed lacks or expresses differently, so
that row S of DESIGN.md (the compiler rewritten in Zed₀) meets no surprises. It was started by
item T13 of docs/plan_dag.md at commit f425b32 and spec commit cb3d910. Step L6.17 reads it.

**Upkeep.** Each step, once its tests pass, adds an entry here for every Rust construct it
relied on that Zed lacks. Line numbers go stale as code is rewritten (T2, T11), so every
citation also names the function. A gap closes when DESIGN.md gains the form it needs; delete
the entry then, in the same commit as the step that closes it.

## What the audit found

At the audit the Rust was 32,508 non-blank code lines without comments or tests; on 2026-11-05 it was about 75,800 (zedc 58,129, kernel 14,988, native 1,753, rt 959). Step S.1 recounts. No part of it needs a
redesign of the language (inferred from the catalog below), and most constructs rewrite
locally. Ten gaps need a decision, because Zed₀ as specified has no form for them or
the form it has may not meet the cost the compiler needs:

| Gap | Rust construct | Sites | Class | Blocks | Proposed fix |
|---|---|--:|---|---|---|
| 1 | Identity: address-keyed memos, pointer equality, cached digests | 34 | planned (L6.13a) | S.3, S.4 | Content digest as a field; `==` shortcut in the runtime |
| 2 | Shared memo and intern tables across pure calls | 52 | workaround | S.3 | Digests from gap 1; state receivers for the rest |
| 3 | Lazy once-only cells and tied recursive types | 27 | workaround | S.3 | Table of definitions keyed by id |
| 4 | Bit operations, float bits | up to 192 | built (L1.39a) | S.2, S.3 | The bit words at L1, built by step L1.39a |
| 5 | Bytes: spans, binary files, hashing input | 95 | planned (L1.39c: `utf8`; step L7.3f, row FILE-bytes: byte port) | S.2, S.4 | `utf8`, a byte file port, or drop the binary formats |
| 6 | Command line, computed output paths, exit status | 9 | closed for the command line (built, L1.19a); executables built (L1.36a); computed paths and exit status at step L7.3f (row FILE-bytes) | S.5 | `CommandLine` port; `Files` writes, an exit value |
| 7 | Scalar to and from code point | 18 | built (L1.39c) | S.2 | Four L1 words: `codePoint`, `scalar`, `utf8`, `fromUtf8` |
| 8 | Abort on a broken invariant, and unproved indexing | 229, ~1193 | decided (S.1d: the member) | S.2 | The atom `#bug(message)`, deleted from the type wherever the invariant is proved; `zedc check` lists the rest |
| 9 | Key range queries on ordered maps | 9 | planned (L5.8a: `upTo`, `from`) | S.3 | `before` and `after` |
| 10 | File import cycles | 9 components in `zedc` at S.1f; 4 left in `zed-kernel` and `zed-native` | fixed in `zedc` (S.1f, and the cycles through calls by CYCLE-zedc-moves), `zed-native` (S.1f-rest) and `zed-kernel` (CYCLE-kernel-moves) | S.2 | Move shared definitions to a file below both sides; no Zed change |

Two more are in the workaround class and matter because of their cost, not their syntax: gap 11
(mutation, which depends on step L6.13 keeping updates in place, with the report of copies of
step L6.13b) and gap 12 (early exit, which the quantifiers of step L3.15a cover for searches).

**ZED0.md is current** as of the audit of 2026-11-03: its Part B and "Gaps found" take their
list from this file, and each gap above that the compiler meets before row S is now a step
before its first use (DESIGN.md step S.1 lists them). The bit words are in the words table
and built (gap 4); the content-address row writes `mod 2^32`, as the grammar has no `%`.

**The claim most likely to be wrong** is gap 11's: that primed receivers and `*.` cost O(1) per
update on a compiler state struct. That rests on step L6.13, which is not built, so the claim
is inferred. Everything in the class "workaround" that names L6.13 falls with it.

**The routines the Rust calls** are listed in `zed/compiler/CATALOG.md` (row PORT-catalog,
2026-11-05): 1,369 routines of the standard library and of dependencies, called 50,049 times by
zedc, zed-kernel and zed-native outside unit tests, each with its Zed text, the plan row that
provides it, or `missing` (398 at PORT-catalog, 333 after PORT-catalog-audit, 2026-11-07,
which wrote out as Zed texts the signed truncating division and remainder, the wrapping and
saturating arithmetic, the widening conversions and others, each text exact; 332 after CATALOG-followups, which wrote out `BigInt::div_ceil` and the floor division and remainder for a divisor of either sign). The missing ones
are gaps of the library, not of the language (inferred from their kinds, not checked row by
row). The largest groups: methods of `Option` and `Result`, checked arithmetic and narrowing
conversions (`checked_*`, `TryFrom`), `Ordering` and `cmp`, hashing and formatting, `Cell`,
`RefCell` and `OnceCell`, character classes, and the operating-system calls of `std::fs`,
`std::io`, `std::env` and `std::process`. Rows STD-seq, STD-text and STD-num start from this
list, and step S.1 regenerates it with the tool `catalog`.

Library words the audit found missing, with no plan row adding them (PORT-catalog-audit; each a
`missing` row of the catalog, none invented):

| Rust | Rows | What Zed lacks | Workaround until a word exists |
|---|---|---|---|
| `BigInt::trailing_zeros`, `BigUint::trailing_zeros` | 2 | `trailingZeros` of an integer with no width (L1.39a requires `width:`) | none at linear cost: a loop of `div 2` costs O(bits²) on an unbounded integer |
| `<Discriminant<T> as PartialEq>::eq` | 1 | a test that two values of a union are the same member | a `match` on both, one arm per member |
| `Ord::cmp` of each type, `partial_cmp`, `total_cmp`, `Iterator::cmp` and the `Ordering` methods (`reverse`, `then`, `then_with`, `is_*`) | 32 | a three-way comparison and its value | `a < b`, `a == b` and `by: le` for sorting |
| `Hash::hash` of each type, `Hasher::write*`, `BuildHasher::hash_one`, `DefaultHasher` | 13 | a hash word for any value (row STD-blake3 covers byte sequences only) | the value as its key in a family |
| `iter::repeat`, `iter::repeat_n` | 2 | a sequence of one value repeated, unbounded or `n` times | `xs[i] else d` for padding |
| `TryFrom` narrowing (24), `checked_*` (21) | 45 | a narrowing conversion and checked fixed-width arithmetic as a value-level failure | `if a < 2^w { … }` written out (author question) |

## Method

A scanner written for this audit (not committed) blanked comments
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
- Gap 10 first came from a second scanner (not committed), which found 8 strongly connected
  components among 76 files of `zedc` and `zed-kernel`. Step S.1f replaced it with the
  checked-in tool `imports` (`crates/zed-tools/src/imports.rs`), whose counts gap 10 gives. The
  first scanner is still not in the repository, so the other counts cannot be reproduced from it.
- `crates/zed-cert` has no code (a 5-line stub). `tests/` is not ported and was not audited.

The classes: **missing**, Zed₀ has no form and DESIGN.md needs one. **Workaround**, a form exists
but with a different shape, or its cost depends on a named step. **Mechanical**, a local rewrite.
**Retained**, stays in Rust by DESIGN.md. "Zed₀" is the whole core, as step M0.8 and zed/compiler/ZED0.md define it since 2026-11-05: L1–L18 in full, the language parts of L19–L24 and the MLIR path of L28. Where an entry below was written when Zed₀ meant L1–L6 and says a form is above Zed₀, step S.1 rereads it.

## What stays in Rust

Confirmed from S.4 and sec:checking_in_zed (DESIGN.md line 1040): compiled programs keep the
Rust runtime's scheduler and allocator, and primitive operations stay built in. So `zed-rt`
(536 code lines) and the `extern "C"` hooks of `zed-native/src/hooks.rs` (27 `extern` matches:
`rt_arg`, `rt_node`, `rt_inc` and others at `addresses`, line 110) stay. The single `unsafe`
function `run` (`zed-native/src/lib.rs:70`, a `transmute` of JIT code) stays too. Its one
`#[repr(C)]` (`Word`, `zed-rt/src/heap.rs:25`) stays.

`zed-native/src/codegen.rs` stays in Rust with the Rust-hosted compiler. It uses 28 distinct
Cranelift instruction builders in 72 calls, plus 8 Cranelift type paths. The compiler written in
Zed emits MLIR text through the port of step S.1a (see zed/compiler/MLIR.md, decision 9).

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
  SUB-corpus-slow added one: `Search::cuts` (`zed-kernel/types/empty.rs`, `settles`) keys the
  meet or difference of two types by their nodes' addresses (`Type::node_addr`), because a key
  by contents compared equal types built apart in full and made a test quadratic. A port needs
  the content digest with an equality that skips the full comparison, or interned types.
- **Equality shortcuts.** `Arc::ptr_eq` or `Rc::ptr_eq`, 6 sites: `Text::eq`
  (`zed-kernel/text.rs:136`), `Type::cmp` (`zed-kernel/types.rs:45`), `Row::cmp`
  (`types.rs:253`), `Premises::extend` and `Premises::eq` (`zedc/store/cell.rs:90`, `:152`),
  `Cx::power` (`preimage.rs:1188`).
  T11-unit-share added test-only uses: `run::tests` and `l01_19_whole_file_ports::sharing` assert
  with `Arc::ptr_eq` that a program holds the front end's unit and a record the input's bytes.
  Zed values are shared and have no identity to compare, so a port of these tests keeps only
  their bytes-allocated scaling check.
  T11-ptr-tests added two more, `testing::tests` and `mutate::tests`: the programs `zedc test` and
  `zedc test --mutants` make share the front end's unit. A port keeps neither.
  ERRS-precise added one in a library: `Atoms::zip` (`zed-kernel/types.rs`) walks
  `imbl::OrdMap::diff` of two atom maps, which skips the subtrees the maps share by address, so
  the union that builds a chain's `#errs(E ->? E)` costs the entries that differ, not the
  smaller map. A port needs a diff of two persistent maps that skips shared nodes, from the
  runtime or by the content digests of gap 1.
- **Ids drawn when a node is made** (ADDR-presburger, COMPLEXITY K74). `presburger::Shared<T>`
  (`zedc-presburger/src/presburger/formula.rs`) keeps a `u64` from the global counter
  `fresh_id` beside each compound part of a formula, and `Shared::change` uses `Arc::get_mut`
  (a unique handle) to change a part in place and draw a new id; `Parts` (`presburger.rs`)
  draws its id lazily into a `Cell<u64>` (gap 3). A Zed program has no global counter and no
  test of uniqueness: a port numbers the parts when the formula is built, as the id-indexed
  graphs of gap 3 do, and changes a part by building a new one.
  VERDICT-group-readers added one: `Type::group` (`zed-kernel/types.rs`, `rec::Key::group`)
  names a recursive group by the address of the `rec::Env` its members share, so the walk of
  `decide_groups_read` (`types/empty.rs`) notes each group once in O(1) per member met. A port
  needs a group number issued when the group is built, as `Type::rec` issues ids.
- **Hand-written equality and order.** 12 `Ord` and 12 `PartialEq` impls (`Type`, `Row`, `Rec`,
  `Bdd`, `Part`, `Expr`, `Text`, `Rope`, `Shown`, `Rat`, `F64`, `Value`, `Premises`), and 2 of
  `Hash`. Zed's `==` and natural order are structural and cannot be replaced by a program.
  `Rec` compares by `id` (types.rs:152), and `Bdd` nodes by an interned number. Where two
  digests tie, the order reads the contents as deep as they go, so it cannot use the call
  stack: one loop with a stack of its own (`types/bdd.rs` `order`) orders types, rows,
  morphism types, diagrams and expressions, as the derived order of `Parts` overflowed on
  types tied a few thousand levels down (SHORT-stack-l01_22). A Zed port's structural order
  on deep values needs the same, from the language or written by hand.

This matters beyond style. Terms and types are DAGs with heavy sharing. A structural `==` or
hash walks a DAG as a tree, so it takes exponential time on the depth without a shortcut (the
rule of the memory note on DAG traversal). `Type::digest` and the pointer test are what prevent
that today. Every visited set in a Zed port faces the same problem.

Candidates (nothing can be run, since Zed₀ is not complete; scores are by reasoning):

| Solution | Empirical result | Score | Reasoning |
|---|---|--:|---|
| Content digest field in each node (`Term`, `Type`, `Bdd`), built from children's digests with a strong hash; keys, memos and equality read the digest; runtime `==` also tests pointers first, invisibly | not run | 9 | Deterministic, matches the fact addresses of step L7.6, needs no threaded table, O(1) compare; invisible shortcut is legal since no program can observe it. Costs a hash per node; a false equal needs a hash collision, which content addressing already accepts |
| Number each node by a threaded counter; state receiver owns the arena; keys are ints | not run | 7 | Exact, and is what `Bdd` does now, but every type operation becomes a state method, so all of `Type`'s pure algebra changes shape (gap 2); not taken for `Type`, because its algebra would become state methods; kept as a choice for the machine's own counters at lines 906 and 1379 |
| Key by provenance keypath | adopted for place-keyed memos (L7.6), not for value keys | 5 | The spec's own identity (line 190), right for "this place" memos like `preimage.rs`, but keypath length grows with depth, so a compare is not O(1) |
| Language guarantee that `==` is O(1) on shared values, by global hash-consing in the runtime | not taken: L6.13a keeps a digest per shared object, so `==` is not promised O(1) | 4 | Cleanest source, but costs every program, and is a schedule-visible cost model promise |
| Add an `identity` word | not run | 0 | Contradicts line 190 and determinism |

Recommendation: the first, with the place-keyed memos of `preimage.rs` using a number assigned
to each term when it is built (`key` needs place, not content). Combine with a runtime pointer
shortcut in compiled `==`, which DESIGN.md should state as an allowed representation fact. The
Rust can adopt digest keys now where equally efficient, which would shrink this gap before S.3.

### Gap 2. Shared tables across pure calls (workaround)

Confirmed: `RefCell` 52 matches, in `Memo` (preimage.rs:580 on) and the `thread_local!` tables
`TUPLES`, `MORPHISMS` (`zed-kernel/types/bdd.rs:65`), `MEMO` (`types/empty.rs:44`), `EMPTY`, `TOP`
(`types.rs:335`), `ROUNDED` (`zedc/store/interval.rs:17`), plus `STATE` (`zed-native/hooks.rs:60`,
retained); VERDICT-group-readers added `DECIDING`, `STORES` and `SHARED` (`types/empty.rs`), which
keep the groups being decided and the values each decided group built, for the unit.
Two `AtomicU64` counters issue fresh ids: `Type::rec` (types.rs:375), `Bdd::node`
(bdd.rs:108). Neither has a form: Zed has no global state, and a closure captures values
(line 1333). `@memoized` does not help: it is an assertion on the plan, "never a request that
changes it" (step L18.2).

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
`Shown` (types.rs:118) caches in place inside a shared value; `Text` did the same until WRITE-prefix-scale removed its cache. Since T14-rope the native runtime holds its strings as the same `Text` (`zed-rt/src/heap.rs`, `Obj::Str`); `zed-rt`'s own `Rope`, with a second `OnceLock`, is gone. `OddPart::filter` (`zedc-int/src/int.rs`, SCALE-fix-wide) takes the residues of a base modulo the primes below 1024 in a `OnceCell` the first time a root wider than one word is looked for; in Zed the loop over indices computes them at the first such index and carries them along.
`Row::keys` (`zedc-types/src/ty.rs`, TY-row-class) keeps in a `OnceLock<Keys>` the class and key of each component of a tuple row, found the first time a row is filed, so later filings of the same row read them; at the port this is a field computed with the row, or a memo keyed by row id, whichever the measured cost of computing it for rows never filed allows.

Zed values are immutable with no cell, and a function field re-evaluates on each call. Cyclic
data lives in two sanctioned forms, arenas or regions and id-indexed graphs `Id ->? Node`
(line 1399, confirmed), which L6.13 builds. Fix: the second form. A recursive type is `#rec(id)`
with its parts in an indexed definition `parts[id] = …`, evaluated on demand (L6.1, L6.4). `Text` needs no port: `String` ropes are L6.16. Cones become
an indexed definition. Cost: inferred O(1) per read if the definedness table is stored, to be
measured at S.3.

### Gap 4. Bit operations (built)

Built by step L1.39a (ledger item BIT-words): `bitAnd bitOr bitXor bitNot shl shr popCount
leadingZeros trailingZeros rotl rotr f64Bits` are kernel primitives (`zed_kernel::bits`, `Prim`)
on the unbounded `int`, prelude words of layer L1 with each parameter positional but `width`,
with forward transfer on intervals (`store::interval::bit_word`, COMPLEXITY.md row C25). A
negative operand, or an `x` wider than its width, is a type error at the call with its
derivation; the checker decides it from the operand's text and listed values (row C26), so an
int that only a test narrows is rejected, as `^`'s exponent is. Shift counts are never masked.
Step L1.39f adds the integer machine operations `mulHi bitReverse byteSwap pdep pext funnelShl
funnelShr` on the same domains (`zed_kernel::bits`, row C25). The Rust uses `u128::reverse_bits`,
`swap_bytes`, `isolate_lowest_one` and a `u128` product to compute them on machine operands; in
Zed these are the words themselves, so the step adds no new gap.
What remains for S.2 and S.3: the representation point and `mix` below; `i32` and other
domain-typed ints are L10, so `w: i32 = shl(1, 31)` is decided by the store's transfer, not yet
by the checker. The text below is the audit's, kept as found.

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
wrapping shift is written `shl(x, k) mod 2^w`. `rotl` and `rotr` are new words.

Wrapping arithmetic is written `(a * b) mod 2^64`. Line 589 already permits computing that in
wrapping `w`-bit arithmetic when the result domain is known statically and spans at most `2^w`
integers (see also line 4088), and step L3.13 builds it, with a test at `mod 2^63`. What remains
is to confirm it for `mix` (`types.rs:77`), where each product is its own expression, since
`bitXor` and `rotl` are not in line 612's list of operators. Also, line 612 lists the
representations as i8…i64, else big-integer, and `int[0..<2^64]` does not fit `i64`, so a hash
would be stored as a big integer. Fix: state that a domain spanning at most `2^w` integers is
stored in one word. Both points are inferred; the test is a scaling run of `mix` at S.3. Carrier masks become sets of atoms. BLAKE3 in Zed
is then ZED0.md's plan; if a stage build shows it too slow, a primitive is allowed by line 1075.

Also float bits, no word: `to_bits`, `from_bits` 13 matches (`Out::value`, `canon/serial.rs:78`;
`W::value`, `zir/binary.rs:122`; `Exact::float`, `num.rs:151`; `exact_sum`, `exact.rs:94`;
`Width::holds`, `store/float.rs:39`). Content addresses hash float bits, so this cannot be avoided.
Fix: L1 words `f64Bits : f64 -> int[0..<2^64]` and its inverse, NaN being canonical first.

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
decides. (b) An L1 word `utf8 : String -> [u8]`, and `int` to little-endian bytes as a
library function, which hashing needs. (c) For files, the binary ZIR and wave records
(`zir/binary.rs`, `Record::to_bytes` at `run.rs:476`) either get a `Bytes` file port, or use the text form that
`zir/text.rs` already has. Recommended: the port, since content-addressed caches should not pay
for text parsing; the choice can wait until S.4.

### Gap 6. Command line and outputs (closed for the command line by L1.19a)

Confirmed before step L1.19a: `main` (`zedc/main.rs:9`) read `std::env::args`, and `command_inner`
(`run.rs:583`) dispatched on them. No DESIGN.md port gave arguments: `main`'s parameters are
ports, an input is `Lines` or `Files`. A `Lines` output is bound by the driver to a fixed path, so
writing to a path computed at run time (`run.rs:654`, `:657`) has no form. Exit status is fixed
by L1.19 as 0, 1 or 2, by the host; the Rust returns its own status.

Fix: an `Args` input port (L1) as `[String]`, a `Files`-like output `path -> String | Bytes`,
and a status from `main`'s result. Alternative: keep a Rust driver as the stage root that decodes
arguments into port bindings; this needs no spec change but leaves Rust in stage2, against S.
Recommended: the ports.

Closed for the command line (step L1.19a): an input of type `CommandLine` is the family of the
words after `--`, keyed by position from 1 (`run::arguments`); `main.rs` now reads
`std::env::args_os`, and a word that is not UTF-8 is a usage error. The compiler in Zed reads its
arguments through this port from S.5 on. An executable that binds its ports from its own command
line is built (step L1.36a, `zedc build`). Still open: a write to a path computed at run time and an exit status from `main`'s
result have no step.

### Gap 7. Code points and text tables (code points built; text tables missing)

Built by step L1.39c: `codePoint : String -> int | #notScalar`, `scalar : int -> String |
#notScalar`, `utf8 : String -> (int ->? int)` (keys `1 ..= n`) and `fromUtf8 : (int ->? int) ->
String | #badUtf8` are kernel primitives (`zed_kernel::words`, `Prim`) and prelude words of layer
L1 (COMPLEXITY.md, Kept). So `\u{…}` decoding (`lex/string.rs:149`, `:292`) and
`zir/text.rs:983` can be written in Zed. The implementation uses `char::from_u32`, `str::chars`,
`str::bytes` and `String::from_utf8`; in Zed these are the four words themselves, so the step adds
no new gap. There is still no character type: text is one-element strings ordered by code point
(line 368), and `char` 18, `.chars()`, `.char_indices()` 37 become `codePoint` and `scalar` on
one-element strings.

Missing: the rest (`starts_with`, `strip_prefix`, `split_once` and similar, 86 matches) are
ordinary standard library functions in Zed (step L2.10), needing no spec change. `is_xid_*`,
script and NFC data (`unicode-ident`, `unicode-script`, `unicode-normalization`, in `lex/name.rs`,
`zir/text.rs` and `source.rs`) are tables in Zed, or built-ins for now. Substring slices are O(1) in Rust as
`&str`; in Zed the cost is that of `slice` on a rope, inferred O(log n), and 150 range slices
exist across all types. A recursion on `&xs[1..]` would become O(n log n) in total, not O(n);
check at S.2.

### Gap 8. Broken invariants and unproved indexing (decided: the member `#bug`, step S.1d)

Confirmed: `.expect` 150, `unreachable!` 63, `panic!` 3, `assert!` 3, `debug_assert!` 5, `.unwrap()`
5; DESIGN.md has no word that stops with a message. Failure is data, and `@invariant` is L15.
Also about 1,193 index expressions panic in Rust on a bad index, whereas `v[i]` in Zed has
`#notFound` in its type unless the domain proves `i` in range.

Decided by the author on 2026-11-04: the member. A function that reaches a broken invariant
returns the atom `#bug(message)`, and indexing is `v[i] else #bug("index past end")`. Wherever
the checker proves the index or the invariant, the `else` has nothing to replace and `#bug` is not
in the type; where it does not, `#bug` stays in the type, reaches the callers' types, and
`zedc check` lists the site. Step S.1d builds this; the port (S.3) writes each Rust `expect`,
`unreachable!`, `panic!`, `assert!` and unproved index as such a site.

| Solution | Empirical result | Score | Reasoning |
|---|---|--:|---|
| **Chosen.** An atom `#bug(message)` in the codomain of each function that can reach a broken invariant; indexing is `v[i] else #bug("…")` | not run | 8 | Needs no spec change, and keeps G5 and line 711. The cost first counted against it, that the atom enters the result type of nearly every function, holds only where an invariant is unproved: wherever the checker proves it, the member is deleted. The functions that keep it are the list of proofs still missing, which `zedc check` prints |
| An L1 word `bug(message)` of empty type, which stops the program and reports the message and its provenance | not run | 3 | Keeps result types small, and the empty type keeps it out of unions. But it breaks G5: it is a written stop that the compiler does not rule out, and a program could halt in a way its types do not show. Needs the spec changes listed below |

The word `bug` was rejected because it contradicts DESIGN.md at these places (each confirmed when
the gap was written):

- G5 (line 21): out-of-bounds indexing and unhandled failure "cannot be written". `bug` is a
  written stop that the compiler does not rule out.
- Line 711: the only run-time tests are those the program writes, and "each one's failure is a
  member of the result type". The failure of `bug` is not.
- Line 3710: "no program writes" the empty type. The type had no spelling then; it is now the
  prelude type name `Never` of L1 (author decision A13, 2026-11-09), and every printer writes it
  so (EMPTY-print).

So the rule "failure is data" covers faults in the program itself as well as its input.

Open for S.1d (inferred from DESIGN.md sec:failure, not part of the decision): a `#bug` that arises
as a loose atom is stripped by a caller's `e else d`, so a default such as `x else 0` would also
hide a bug. A prelude family `type Bug = #bug(message: String)`, written in the result types,
would keep it, since family atoms survive `else` and are removed only by `else #bug -> d`. S.1d
chooses between these and tests the choice.

`catch_unwind` and `resume_unwind` (`Evaluator::run`, `eval.rs:362`, and `on_stack`) only restore a flag, and
`on_stack` (`eval.rs:290`) exists only to run with a 1 GiB stack (the marker `Stack`). Both vanish.
Depth moves to the runtime: L6.7 tests a `fix` term over a 100,000-node chain, and compiled
recursion on input-sized depth needs a growable stack in the retained runtime (inferred; not in
L6.13). The preimage transfer (`store/preimage.rs`, PRE-stack-explicit) keeps its frames on the
heap: each analysis is an `async fn` whose recursive calls the loop in `zed-kernel/src/frames.rs` runs from a
`Vec` of suspended state machines; Zed has no `async` or state machines written by the compiler,
so a port writes each analysis's frames as a sum type with an explicit stack (see the entries from
PRE-stack-explicit). `Drop` for `text::Node` and `Premises` exists to avoid deep recursion in release,
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
`interval.rs:266`; Dijkstra's search in `difference_hulls`, `presburger.rs`, and in `Scope::repair` and `Scope::bound_pass`, `product.rs`; reference 14's `Level::merge`, `zed/corpus/ref/src/p14.rs`) is then an ordered set
`.first` and `.last` give neighbors. `BinaryHeap` (`topo`, `elab/topo.rs:10`; `IntervalSet::cap`,
`interval.rs:266`; reference 14's `Level::merge`, `zed/corpus/ref/src/p14.rs`) is then an ordered set
with `.first` and a `patch`.

### Gap 10. File import cycles (Rust must change)

Zed forbids a cycle between files, while recursive types and definitions stay unrestricted within
a unit (DESIGN.md line 797). The repairs are to move what both sides use into a unit both import,
or to merge the units (line 1329). The tool `imports` (`crates/zed-tools/src/imports.rs`, step
S.1f) computes the import graph of a crate's sources: each `use` and each qualified path is
resolved to the file defining the item, `pub use` is followed to the defining file, and a
parent's re-export of a child is an edge from parent to child. It names every strongly connected
component, with a shortest cycle and every import within it. Paths below are relative to
`crates/`, with `src/` dropped.

**`zedc` had no cycle through paths after S.1f** (`imports crates/zedc/src`: 87 files, 291
imports, exit 0, before calls of methods written apart counted). The tool found nine components
when S.1f began, against the six `zedc` components of the first, uncommitted scanner. Each was broken by moving
the shared items to a file below both sides; no file was merged and no re-export hides an edge:

| Component before S.1f | Fix in S.1f |
|---|---|
| `lex`, `lex/comment`, `lex/number`, `lex/string` | `Span`, `Tok`, `Part`, `Token`, `ErrorKind`, `Error` moved to `lex/token.rs`. The mutual recursion of `lex_from` and `string` was already gone: `string` returns at a hole (`string::Stop`) and `lex_from` goes on |
| `ast`, `ast/neglit`, `ast/stmts`, `ast/types` | The data types, which are one recursive type (`Expr`, `ExprKind`, `Stmt`, `Type`, `Param`, `Pattern` and the rest), moved to `ast/node.rs`; `ast/mod.rs` re-exports them, so that edge goes down. `stmts.rs`, `types.rs`, `neglit.rs` and `body.rs` hold only `impl Builder` blocks, and `Bare` moved from `neglit.rs` to `ast/mod.rs` |
| `canon`, `canon/serial` | `Def` and `Facet` moved to `canon/def.rs` |
| `check`, `check/ty`, `check/walk`, `check/widen`, `elab`, `stage` | `class_id` and `var_name` moved to `check/ty.rs`; `Args` (its fields) and `Saved` to `check/mod.rs`, `impl Args` staying in `walk.rs`. `elab.rs` split: `Def`, `Test`, `Unit` to `elab/defs.rs`; `Tables`, `Uses`, the `collect_*` functions and `in_tests` to `elab/tables.rs`; `topo`, `topo_joined`, `cycles` to `elab/topo.rs`; `kernel_type` and its helpers to `elab/kernel_type.rs`. `impl Unit { close, get }` stays in `elab.rs` |
| `mutate`, `testing` | Running one table row or wave (`row`, `wave`, `Swap`) moved to `rows.rs`, which both import |
| `query`, `run`, `unit` | `Front`, `Parsed`, `Diagnostic`, `Step`, `compile`, `write_warnings`, `linear_questions`, `placed`, `step`, `error` and `parse_unit` moved to `front.rs`; `zedc::run::{Diagnostic, Step, linear_questions}` are now `zedc::front::...` |
| `store/interval`, `store/lattice` | `Landmarks` and `Mark` moved to `store/landmarks.rs` |
| `store/presburger`, `presburger/deep`, `presburger/deep/canon` | The formulas (`Atom`, `Lin`, `Con`, `Formula`, `Rel`, `Model`) and `Id` moved to `store/presburger/formula.rs` |
| `zir`, `zir/text` | The validator moved from `zir/mod.rs` to `zir/validate.rs`, which imports `zir/text.rs` |

**Methods written apart are imports since S.1f-rest.** A call of a method whose `impl` block is
in another file than its type (`impl Builder { … }` in `ast/stmts.rs`, `Builder` in
`ast/mod.rs`) is an import of the block's file, since a Zed unit cannot split a definition's
methods across units and the port makes each such block a unit of its own. The tool types the
receiver from parameters, `let`s, fields, return types, patterns (`for`, `match`, `if let`,
closures) and the standard wrappers; when it cannot, the call is an import of every file with a
method of that name written apart from its type that the caller may call, so no cycle is
missed, and the report counts those calls. A receiver of a type parameter's type takes only
trait methods, so it imports nothing.

**The cycles that counting reveals, still open** (S.1f-rest, test
`s_01f_import_graph::no_crate_has_an_import_cycle_but_the_known_ones`, which lists their files).
The tool reports one component of 32 files in `zedc` (90 files, 370 imports, 212 calls not
typed) and one of 12 in `zed-kernel` (28 files, 89 imports, 68 calls not typed; broken since
by CYCLE-kernel-moves, below). The true cycles inside them were found by adding the cross-file
call edges rustc's MIR gives (`--emit=mir`, a scratch check, not committed) to the tool's path
edges; the files beyond them are in the components only through calls the tool did not type
(in `zedc` 23 files through `x.get()` read as `Unit::get` in `elab.rs`; in `zed-kernel`
`num.rs`, `text.rs`, `value.rs` and `bes.rs` through `x.is_empty()` read as `Type::is_empty`
in `types/empty.rs`). The MIR call graph also tells which cycles a move can break: functions
that call each other in a cycle must stay in one unit, and only two such groups cross files.

| True cycle | Edges | Fix (inferred from the MIR call graph, not built) |
|---|---|---|
| `zedc`: `ast/mod`, `body`, `neglit`, `stmts`, `types` | the `impl Builder` blocks call each other's methods | No group of mutually recursive functions crosses these files, so moving methods breaks it: order the `Builder` methods by what they call and put each file's methods below the files that call them |
| `zedc`: `check/mod`, `check/walk` | 56 functions in one group of mutual recursion, 27 in `check/mod.rs` (`fit_declared`, `compare`, `fits_slot`, `bind_pattern`, …) and 29 in `check/walk.rs` (`call`, `expr_of`, `infer`, `scope`, …) | The group must be one unit: move the 27 into `check/walk.rs` (or the 29 into `check/mod.rs`), the rest of each file importing it |
| `zedc`: `elab`, `elab/walk` | `Elab::scope` and the walk's methods | No recursive group crosses them: move the methods `elab/walk.rs` calls below it |
| `zedc`: `store/presburger`, `presburger/deep`, `deep/canon` | `Formula::fold`, `Con::holds`, `canon::Canon`, `Lin::constant`; one recursive group `presburger::witness`, `presburger::holds`, `deep::holds_as` | Move `holds_as` to `presburger.rs` (or `witness` and `holds` to `deep.rs`); the rest by moving the split methods of `Formula`, `Con` and `Lin` to `formula.rs` |

These moves touch the files that ZEDC-split (`zedc` into crates) and the kernel `types` branches
were changing while S.1f-rest ran, so they were left to be made after those merge.

**The four `zedc` rows are done (CYCLE-zedc-moves).** After ZEDC-split the 32-file component
was four cycles of 12 files, one per crate; the other files had been in it only through calls
the tool did not type, which the split into crates removed. Every `zedc` crate now passes the
tool, and `s_01f_import_graph` checks that each has no cycle. The moves:

| Cycle | Moves |
|---|---|
| `zedc-syntax`: `ast/mod`, `body`, `neglit`, `stmts`, `types` | `Builder`, `Level`, `Built`, `Bare` and the steps every form's builder reads (`new`, `span`, `word`, `kids`, `later`, `node`, `take`, `body`, `op`, `range_end`, `once`, `args`, `literal_at`) moved from `ast/mod.rs` to `ast/builder.rs`, below all the others; `target` moved from `stmts.rs` to `types.rs`, which `stmts.rs` already imports. `ast/mod.rs` keeps the entry points, `fill`, `make` and the expression forms, and imports every other file |
| `zedc-check`: `check/mod`, `check/walk` | `check`, `check_with`, `operator` and the 32 methods of `Ck` that re-enter the walk (`apply`, `apply_many`, `apply_one`, `at_index`, `at_key`, `bind_pattern`, `bit_domains`, `check_on`, `compare`, `component`, `components`, `data`, `exponent`, `fit_declared`, `fit_needs`, `fits_slot`, `flow`, `generalize`, `into`, `int_range`, `literal_refused`, `meet`, `merge`, `narrowed`, `need`, `partial`, `payload`, `repaired`, `repairs`, `replay`, `try_outside`, `sum`) moved to `check/walk.rs`, now `pub mod walk`. The paths are `zedc_check::check::walk::{check, check_with, operator}` (and `zedc::check::walk::…`); no re-export from `check/mod.rs`, which would be an edge from it to `walk.rs` |
| `zedc-elab`: `elab`, `elab/walk` | `Mark`, `mutable` and `mark_of` moved to `elab/mark.rs` (paths `zedc::elab::mark::{Mark, mutable, mark_of}`); the walk's state `Elab`, `Bind` and their helpers to `elab/state.rs`; `if_` and `what` to `elab/walk.rs`. `elab.rs` keeps the entry points and imports the three |
| `zedc-presburger`: `presburger`, `presburger/deep`, `deep/canon` | `Names`, `as_is` and the methods of `Factor`, `Atom`, `Lin` and `Con` (arithmetic, `eval`, `holds`, `show`, `Display`) moved from `presburger.rs` to `presburger/formula.rs`, with `Formula::rank` and `Formula::flattens_into` from `deep.rs`, which `canon.rs` calls. No function moved between `presburger.rs` and `deep.rs`: the recursive group `witness`, `holds`, `holds_as` the MIR graph suggested does not exist, as `holds_as` calls only `Con::holds`, so `presburger.rs` imports `deep.rs` and not the reverse |

**The other components the tool found when S.1f-rest began are broken.** `zed-kernel`: `value`,
`family`, `error` and `deep` were one recursive type (`Value`, `Family`, `Part`, `KernelError`
holding `Value`), so `family.rs` and `error.rs` merged into `value.rs`, and `deep.rs` imports it
(the paths `zed_kernel::family` and `zed_kernel::error` are now `zed_kernel::value`). `num` and
`num/bound`: `LiteralRounding`, `TooLarge`, `room` and `bytes_of` moved to `num/room.rs` and
`built` to `num/fast.rs`, which both import. `zed-native`: `codegen`, `exe`, `hooks` and `lib`:
`legalize` moved to `legal.rs`, and a run's outcome and the running of generated code to
`outcome.rs`. `zed-native`, `zed-rt`,
`zed-cert`, `zed-tools` and `zed-alloc-count` have no cycle.

**The `zed-kernel` row is done (CYCLE-kernel-moves).** At its start the tool reported one
component of 12 files (`num`, `text`, `types`, `types/bdd`, `bdd/list`, `types/bes`,
`types/debug`, `types/empty`, `types/print`, `types/rec`, `rec/walk`, `value`; 30 files, 102
imports, 87 calls not typed); it now reports no cycle (33 files, 98 imports, 30 calls not
typed), and `s_01f_import_graph` checks that. Each type moved to the module that owns it, with
no re-export and no copy, and no change in behavior:

| Edge | Move |
|---|---|
| `types` and `bdd` call each other's `Literal` methods and the order of diagrams | `impl Literal for Row` and `for Morphism`, their tables, and the order of two diagrams (`Step`, `order`, `walk`, the private trait `Ordered`) moved from `bdd.rs` to `types.rs`; `Op` moved to `bdd.rs`; `Literal` no longer requires `debug::Queue`, which the `Debug` impls in `debug.rs` require instead |
| `bdd/list` and `bdd` | `bdd/list.rs` is the inline module `list` of `bdd.rs`, as it is one unit with it; the tests of `bdd.rs` moved to `bdd/tests.rs` |
| `types` uses `empty::{Refusal, Verdict}` and `print::Surface` | the three types are defined in `types.rs` (the `pub use` lines are gone; the paths `zed_kernel::types::{Refusal, Verdict, Surface}` are unchanged); `Type::split` moved to `empty.rs` |
| `types` and `rec` | `rec` is an inline module of `types.rs`, holding the definitions (`Expr`, `Def`, `Group`, `Checked`, `Node`, `Shape`, `Env`, `Key`, `Rejection`, and REC-canon's `Canon` and `canon`; paths unchanged) and the module `walk`; the checks of a group and its tables went to `rec/group.rs`, the units and the unfolding (`eval`, `Env::member`, `Type::group_members`) to `rec/unfold.rs`; the stored closure `Rec::judge` is gone: `Type::judged` (`empty.rs`) reads the group's decision through `Key::member_at`, and `judge` and `kids` moved from `rec.rs` to `empty.rs` |
| `num`, `text`, `value`, `bes` and `types` reach `empty.rs` through `x.is_empty()` | not real: the tool did not type the receiver; 21 locals and closure parameters got a written type (for instance `let below: Vec<(u64, BigUint)>` in `num.rs`), which the compiler checks |

The tests of `types.rs` and `empty.rs` moved to `types/tests.rs` and `types/empty/tests.rs`,
and those of `rec.rs` to `rec/group.rs` (`types::rec::group::tests`).

`zed-kernel` and `zedc` read the shared scaling test through `#[path]` (`zed-kernel` `lib.rs:28`, `zedc` `lib.rs:45`); the tool reports such
a module and does not read it, since its file is outside the crate.

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
- A map held across a recursion and undone after it (`Rigid` in `check/ty.rs` `fits_in`, which
  adds the expected type's bounded variables, recurses through `accepts`, then removes them)
  becomes a persistent map passed down, so nothing is undone. The printer's `&mut String`
  (`Ty::write`, `Sig::write`) becomes a fold over text pieces joined once, which keeps it O(n).
- A nested receiver such as `self.classes[i]*.m()` is defined: DESIGN.md (sec:tour_methods,
  the `*.` rule) lets the receiver be any keypath the one-writer rule accepts, entries included.

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
- **Three live variables (LIVE3).** `store::live3` computes in `Int` and `linear::Q` and holds no state; its numbers of three (`[Q; 3]`, `[[Int; 3]; 3]`) are fixed-size tuples in Zed. The 64-bit fast paths added to `Int` (`div_floor`, `mod_floor`, `*`) go with `store::int` at the port.
- **`as` casts** (272): most go, but a truncating cast must become `mod 2^k`.

## Mechanical rewrites

Confirmed against sec:grammar; counts in the appendix.

| Rust | Count | Zed |
|---|--:|---|
| `Arc`, `Rc`, `Box`, `.clone()`, lifetimes | 548, 37, 76, 1098, 458 | Vanish: values are immutable and shared |
| `format!`, `write!`, `.to_string()` | 490, 215, 105 | Interpolation and `String(…)` arrows; `Display` (42 impls) becomes overloads of `String` |
| `#[derive]` | 223 | Equality, order, update are structural and free; `Default` becomes a written value |
| `impl From` (14), `Deref` (2), `AsRef` (1), `IntoIterator` (1) | 18 | Named functions |
| `impl Not`, `BitAnd`, `BitOr`, `Sub` on `Type`, `Neg` on `End` | 9 | Named `complement`, `meet`, `join`, `minus`: `&` and `\|` are type operators only (line 2408); overloading `-` needs its axioms (line 2778) |
| Traits: `Lattice` (8 impls), `Lookup`, `Mark`, `Literal`, `Equations` | 5 traits | `interface` is L10, in Zed₀. Before it, a record of functions. `L::bottom()`, dispatched on a return type, becomes a field. Single-parameter cases become overloads |
| `dyn Fn`, `FnMut`, `impl Fn`, `fn` pointers | 37 `dyn` | Function values. `dyn Lookup`, `dyn Read`, `dyn Write` become ports |
| Generics | 67 fns, 38 types | Implicit by inference (line 537), and `type N(X)` at L2 |
| Tuple structs | 20 | `#sym(String)` for a distinction: same-shape structs are one type (line 2774). `Sym`, `Key`, `ContentAddress`, `Card` need this |
| Privacy: `pub`, `pub(crate)`, private fields | 1163 `pub` | `local` hides a declaration in its file; a field cannot be hidden, so an invariant such as `Row`'s is held by convention. `#[doc(hidden)]` on the entry points exported only for tests (`check::Operands`, `elab::topo`, `store::preimage_ref`) has no Zed form: they are ordinary exports |
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
| `usize` | 107 | 579 | 55 | 19 | 760 | blocks `zedc/store/product.rs:501` (20); topo `zedc/elab/topo.rs:10` (8); Evaluator (impl) `zed-kernel/eval.rs:831` (7) |
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
| `thread_local!` list of parts waiting to be freed, and a flag for the walk that holds it | `deep::free`, `PARTS` (a `deep::Queue` since T2-types) | Mutation, global state | Removed: the runtime frees values, and must free a deep chain without recursion itself |
| `thread_local!` queue of families to compare, because `==` is called from inside `imbl` where no stack of ours reaches | `value::settle`, `Comparisons` (`comparing`, `pairs`) | Mutation, global state | Zed's map comparison takes the element test as a function, so the queue is a state receiver or goes away |
| A `thread_local!` flag that makes `==` on families compare shallowly while `imbl`'s `OrdMap::diff` runs, set and cleared by a drop guard, since `diff` takes no comparison function (PROV-family-entries) | `Family::shallow_diff`, `Comparisons` (`shallow`) | Mutation, global state | Zed's map difference takes the element test as a function, so the flag goes away |
| `impl Drop` on a newtype, with `mem::take` of its `Arc` or map | `Items`, `Family` | None | Removed, with the first row |
| `slice::Iter` held in a stack frame, a borrow into the value being walked | `walk`, `Copying`, `all_leaves` | None | An index into a shared tuple |
| `Cow<'_, Value>`, a key borrowed unless it needs a copy | `as_key` in `eval.rs` | None | Zed shares values, so a function returns the key or its normalized copy with no borrow |
| `RefCell` to collect from inside a `Fn` closure that `Expr::eval` calls | `Type::contains` | Mutation | The closure returns what it needs, as a value |
| Raw pointers as map keys, `*const Node` and `*const Value` | `Type::contains` | Identity | Keyed by a hash-consed id of the type and the position in the value |
| Hardware counter opened with `perf_event_open` through `perf-event2`, and the thread CPU clock through `rustix` | `zed_tests::scaling::Meter`, `cpu_time` | Foreign library | Test harness only, so a Zed port needs it only if the tests move to Zed: an `@ffi` signature over the two system calls (L7.4) |

## Entries from T2-parse (`zedc-syntax/src/parse/mod.rs`, `ast/`, `format.rs`, `lex/`)

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

## Entries from T2-types (`zed-kernel/src/types.rs`, `types/bdd.rs`, `types/rec.rs`, `term.rs`, `deep.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A generic `thread_local!` queue of parts to free, one per module, each an enum of the kinds of part | `deep::Queue`, `deep::free_in`, `Freed` in `types.rs`, `rec.rs`, `term.rs` | Mutation, global state | Removed: the runtime frees values, and must free a deep chain without recursion itself |
| `impl Drop` on a generic struct with a trait bound, freeing through a trait method (`Literal::free`) | `Branch<A>`, `bdd::Expr<A>` | None | Removed, with the first row |
| A `thread_local!` record of the text being made, read by a recursive `show` that returns a placeholder for a missing text, and a drop guard that clears it on a panic | `Type::rope`, `make_rope`, `SHOWING`, `EndShowing`, `Rec::naming` (a recursive type's name, made as an item of the same loop) | Mutation, global state | A fold over the types in postorder that passes the map of texts along |
| `OnceLock::set` from a loop outside the cell's own initializer | `make_rope` | Lazy cells (gap 3) | The map of texts from the row above |

## Entries from T2-types-rest part 3 (`zed-kernel/src/types/debug.rs`, `types/bdd.rs`, `print.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A stack of items to write (`Show<'a>`) holding trait objects (`&dyn fmt::Debug`, `&dyn Queue`, `&dyn Vertex`), so that one loop writes types, rows, morphisms, parts and diagrams of different Rust types | `types/debug.rs` | Trait objects | A sum type of the things written, one case per kind, in a state receiver's list |
| Shared nodes found by a pass with a `HashSet<u64>` of node ids, then numbered in the order written from a `HashMap<u64, Option<usize>>` filled while writing | `debug::Scope` | Identity (gap 1), mutation | The ids as digests (gap 1); the map passed along the fold that writes |
| Post-order walks of a diagram or expression on a `Vec<(&node, bool)>`, with a `HashMap<u64, _>` memo keyed by node id | `Part::eval`, `eval3`, `rebuild` (`substitute_all`, `Part::restrict`), `Bdd::restrict`, atoms, `union_rows` | Identity (gap 1), mutation | A state receiver holding the stack and the memo, keyed by digest |
| A term laid out as a `Vec` of tokens with a second `Vec<usize>` linking each `Start` to its `End`, written and broken by loops over indices with a stack of frames | `print::Doc`, `Doc::render` | Mutation | The tokens as a list; the links as a map from index to index built by a fold; the frames in a state receiver |

## Entries from T2-types-rest-4 (`zed-kernel/src/types/bdd.rs`, `types/debug.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Builds of a diagram from an enum of jobs borrowing the input (`Job::Pair(&Bdd, &Bdd)`, `Job::Node(&A, key)`; `Job::Flip`, `Job::Node(&Branch)`) on a `Vec`, children's results on a second `Vec` popped by the node job, with the memo keyed by node ids as before | `Bdd::apply`, `Bdd::flip` | Identity (gap 1), mutation | A state receiver holding the two lists and the memo, as for `rec` `Node::of` |
| A walk of paths on a `Vec` of steps (`Walk`, `Lo`, `Done(bool)`) sharing two `Vec`s of atoms taken and refused, pushed and popped around each node, the closure called with slices of them | `Bdd::walk`, `Bdd::paths` | Mutation | The atoms taken and refused passed down as lists; a fold that stops at the first `false` |
| `async fn` methods of a struct holding the frame stack (`Connect`, a `frames::Stack`), called through `fn`s returning `Deep` that answer at once (`Stack::ready`) or start a frame (`Stack::call`), so about seven mutually recursive connectives keep their order and run on the heap | `Part::not`, `Part::zip`, `Connect::{not, zip, negate, zipped, same_as_not, condition, choose, choice_of, choice}` | Missing (no coroutines or `async`), as for `types/empty.rs` | Removed: the port's runtime must run deep recursion without overflowing; else an explicit machine of frames |
| A higher-ranked closure bound (`impl for<'m> FnOnce(&'m Connect<'m>) -> Deep<'m, V>`) so the root call borrows a stack made inside `Connect::run` | `Connect::run` | Lifetimes | Removed |
| A complement kept beside an expression in a `OnceLock<Part>`, set once by `get_or_init` after it is made, the complement's own cell set to the expression | `Connect::negate` | Mutation, interior mutability | A memo from expression id to its complement, threaded through the calls |
| Shared types found by one pass with a `HashSet<&Type>` and numbered from a `HashMap<&Type, Option<usize>>`, keyed by the type's value (`Hash` is its digest, `Eq` its comparison), with one counter for the whole text | `debug::shared_types`, `debug::number`, `debug::run` | Identity (gap 1: digests), mutation | A map from digest to number passed along the fold that writes |

## Entries from T2-mid (`zedc-resolve/src/resolve.rs`, `elab.rs`, `canon/`, `stage.rs`, `check/`, `zir/`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An enum of frames borrowing the input (`Job<'t>`, `Walk<'t>`, `Mix<'t>`) on a `Vec`, with a second `Vec` of results that a frame drains the last `k` of (`Vec::drain(len - k..)`) | `canon::binders::Levels::term`, `set_binds`, `stage::ends`, `Mixer::mix`, `zir::Region`'s `Debug` | Mutation | A state receiver holding the two lists, as for the evaluator's machine |
| Children pushed in order, then the pushed range reversed in place (`todo[start..].reverse()`), with a frame's count patched after the push | `canon::binders::Levels::term`, `each_binder`, `serial::Out::write`, `stage::ends`, `Mixer::enter` | Mutation | Build the list of children, then prepend it reversed |
| A machine of `Job`s and `Frame`s on a `Vec`, each frame taking its child's result from one register (`Ret`, read by `take_ty`, `take_arg`, `take_cond`, `take_sig`), large frames boxed to keep the enum small | `check::walk` | Mutation | A state receiver holding the list and the register; a sum type of frames, with no boxing |
| `Rc<Origin>` chains with an `impl Drop` that unwraps each link by `Rc::try_unwrap` in a loop | `check::Origin` | Identity, mutation | Removed: the runtime shares and frees values, and must free a long chain without recursion itself |
| The `check::walk` machine again, with a list frame (`SeqF`) that runs a list of expressions and stops at the first failure when asked, as `collect::<Option<_>>` does; a call frame (`FillF`) holding an `Option<HashMap<&str, usize>>` built at the first named argument (`get_or_insert_with`) | `elab::walk` | Mutation | A state receiver holding the list and the register; a fold over the arguments that stops on the first failure; the name map as a lazily built value |
| `impl Drop for Region` that moves each node's regions out with `mem::take` and frees each region held once (`Arc::into_inner`) from a `Vec`, so no drop recurses | `zir::Region` | Mutation, identity | Removed: the runtime frees values, and must free a deep graph without recursion itself |
| A hand-written `PartialEq` comparing region pairs from a `Vec<(&Region, &Region)>`, skipping a pair that is one shared region (`Arc::ptr_eq`) | `zir::Region` | Identity | Structural equality, which the runtime gives without recursion; the shared-pair shortcut becomes a hash-consed id |
| One `String` path buffer for a walk, cut back to a stored length (`String::truncate`) when the walk leaves a region | `zir::validate`, `zir::text::print` | Mutation | The path passed down as a value, or a list of path parts prepended and dropped |
| A job machine (`Job<'t>`) whose frames borrow the input term for the walk's lifetime (`&'t Term`, `Cow<'t, [Arc<str>]>`), with stacks of values, sources and built regions that a frame drains the last `k` of; a `Closure<'t>` borrows a let-bound lambda's body from the input | `zir::lower::Lower::term` | Mutation | A state receiver holding the stacks; Zed shares terms, so a frame holds the term itself |
| A stack of walks (`Vec<UseWalk<'t>>`), each with its own counts of bound names and its own stack of visits: a walk waits at a lambda whose body's uses are not yet known while that body is walked | `zir::lower::body_uses` | Mutation | A state receiver over a list of walks; the memo of bodies as a map in the receiver, keyed by occurrence id |
| Occurrence ids of a term's subterms from one walk (`Places`: the parts of occurrence `i` are `first[i]`, `first[i] + 1`, …), carried beside each borrowed subterm (`At`) through the lowering's jobs | `zir::lower::Places`, `Places::part` | Identity (gap 1) | The numbering is a fold over the term into a list |
| A raising machine (`Raising<'g>`) of region and node frames on a `Vec`, each holding the terms raised so far and a mark into the shared list of binder names | `zir::lower::raise_from` | Mutation | A state receiver holding the frames and the names |
| A stack of running regions in the counting machine, and a work list of `Part<'p>` (`Drop(Option<usize>)`, `Keep(Option<usize>, Vec<&'p [usize]>)`) borrowing kept paths from the plan | `zir::memory::Machine::region`, `release`, `dec`, `tree` | Mutation | A state receiver holding the regions and the work list; paths shared, not borrowed |
| Open values, patterns and types on a `Vec` while a graph is read or written, each frame counting the parts it has | `zir::text`, `zir::binary` | Mutation | A fold over the parts with a list of open frames in the receiver |
| An open type (`OpenType { t, parts: Vec<&Type>, done: Vec<Option<KType>> }`) per level, and an open pattern (`OpenPattern<'p>`) whose step matches `(frame, finished.take())`, `Option::take` handing one result up | `elab::kernel_type`, `Elab::pattern` | Mutation | A state receiver holding the open list; the handed-up result as a value returned by the step |
| The kernel `Pattern`'s `Clone` and `PartialEq` are written by hand as loops over explicit stacks since T2-types-rest part 1 (`term/walk.rs`, entry under T2-types-rest; they were derived and recursed), and its `Drop`, and `Type`'s, are loops since T2-types | `zed_kernel::term::Pattern` | None (a Rust limit) | Removed: the runtime frees and compares values without recursion |
| A plan as a `Vec` of region plans in preorder, each linked to the region holding it (`up: Option<(usize, usize, usize)>`) and each node to its regions' indices, replacing keys that were the path from the root, O(d^2) bytes in all (T14-paths); a path is a `Display` value (`PathOf`, `NodeAt`) folded up the links when a message is printed, and the machine's checks take their message parts as `&dyn Display` from `format_args!`, so nothing is built for a check that passes | `zir::memory::Plan`, `Machine::sub`, `Machine::check`, `zed_native::tables::Tables::visit` | Missing (no formatter trait) | A list of records with index links; the path a fold up the links; a message part passed as a closure that gives the text |

## Entries from L2.1 (`zedc-syntax/src/ast/`, `format.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `HashMap<&'a str, Span>` borrowing names from the source text, filled while a list is built | `Builder::once` and its callers (struct fields, display entries, `with` paths, type parameters) | None | A map from name to span over shared strings |
| `let … else { unreachable!() }` on an enum variant that an earlier pass has ruled out | `elab.rs`, `check/mod.rs` (the L2 forms resolution refuses) | Partial match | A total match whose L2 arm returns the refusal, or a narrower type from resolution |

## Entries from L2.2 (`zedc-syntax/src/ast/`, `format.rs`, `resolve.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Iterator::peekable` with `next_if`, taking the next node only when it starts at a given token | `Builder::annotated` | Mutation | An index into the list of nodes, passed along a fold |
| `let … else { … return; }` taking the first arm of a slice, the rest of the arms pushed back as a job | `Formatter::run`, `Job::Arms` | Early return | A `match` on the list, empty against first and rest |
| `Box<Type>` and `Box<Expr>` in `Pattern::{Is, Lit}`, so the enum stays small | `ast/types.rs` | None | Removed: Zed values are shared, and size is not the programmer's concern |


## Entries from L2.3 (`zedc/src/unit.rs`, `resolve.rs`, `query.rs`, `run.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `trait Files` with `Dir` and `Memory`, a `&dyn Files` read through a vtable | `unit::load` | None | A function value passed in, `read: (String) -> Option<…>` |
| `Vec`s of met numbers, low links, components and stack places written in place during Tarjan's search, a tuple assigned to three of them at once (`(met[v], low[v], at[v]) = (count, count, stack.len())`), and the explicit path's top counter incremented through `last_mut` (CYCLE-root-order) | `unit::order` | Mutation | A loop with `mutable` maps and stack, or a fold over the search's steps; three assignments for the tuple |
| A breadth-first search's arrays kept across components in a struct passed `&mut`, each entry marked with the component number so none is cleared (CYCLE-root-order) | `unit::Search`, `unit::report` | Mutation | A state receiver over maps from unit to component, or a map made new for each component (its own units only) |
| A labeled `loop` left by `break 'search (u, span)` with a value from inside a nested `for` (CYCLE-root-order) | `unit::report` | Early exit (gap 12) | A recursive function over the queue that returns the closing import |
| `let [c0, _, ..] = *members else { return; }`, a slice pattern testing for two units or more (CYCLE-root-order) | `unit::report` | Slice patterns | Test the length, then index |
| `HashMap<Arc<str>, usize>` index beside a `Vec` of units, both pushed to as units are found | `unit::add`, `Package::index` | Mutation | A map from path to unit built by a fold over the work list |
| `binary_search_by` on a sorted `Vec` of imported units | `Linked::exports` | None | A map from path to resolution |
| `let … else { unreachable!(…) }` for a unit with imports that has text | `unit::cycle_error` | Broken invariants | A type that carries the text with the parsed unit |

## Entries from L2.8 (`zedc/src/pin.rs`, `unit.rs`, `query.rs`, `canon/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A temporary file written beside the target and renamed over it, its permissions copied first, the target's symlink followed | `pin::replace` | Host file system (gap: no atomic rename in the `Files` port) | A `Files` port operation that replaces a file whole, added with PORTABLE-rt |
| `split_inclusive('\n')` with a running byte offset, and `split_once(' ')` twice to read a pin line | `pin::Pins::parse`, `pin::pin_line` | None | `Lines` of the file and a grammar or `split` on its text |
| A `BTreeMap<(String, String), ContentAddress>` read by `range` from a key and `take_while` | `pin::Pins::drop_kind` | None | A sorted map with a range read from a key |
| A memo `Vec<Option<Arc<Address>>>` indexed by unit, filled as units are met | `unit::pin_units`, `unit::unit_address` | Mutation | A map from unit to address built by a fold over the imports |
| Byte offsets of the normalized text mapped back to the raw bytes in one pass over `\r\n` | `pin::raw_offsets` | None | The same pass over the file's bytes |
| `let … else { unreachable!(…) }` for a unit that gains a pin and has text | `Package::pinned`, `Package::write_pins`, `unit::pin_units` | Broken invariants | A type that carries the text with each unit that gains a pin |

## Entries from T4 (`zedc-solvers/src/utvpi.rs`, `presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A tree held as a ring of `next` and `prev` indices in preorder with a depth per node, relinked in place by index when a subtree is cut out | `utvpi::potential` | None | Removed by UTVPI-GOR: the search keeps no shortest-path tree |
| `VecDeque` used as a FIFO queue, `push_back` and `pop_front`, with a `Vec<bool>` of what it holds | `utvpi::potential` (Kahn's order since UTVPI-GOR) | Mutation | A state receiver over a list and a set, or two lists swapped at each round |
| `Iterator::partition` of borrowed rows into two `Vec<&Row>` | `presburger::search` | None | Two `where` calls or a `group` over the list of rows, which Zed shares rather than borrows |

## Entries from UTVPI-GOR (`zedc-solvers/src/utvpi.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec<usize>` of pass numbers written in place as the visited set of each pass, so no set is cleared between passes, with a `Vec<bool>` of the nodes on the search stack | `utvpi::potential` | Mutation | A state receiver over a map from node to pass, or a fresh persistent set per pass at a log factor |
| `Vec` of `(node, next edge)` frames as an explicit stack for a depth-first search, the top frame's edge place advanced through `last_mut` | `utvpi::potential` | Mutation | A state receiver, as for the parser's machine |
| Distances in a `Vec<Int>` lowered in place while the edges are relaxed | `utvpi::potential` | Mutation | A state receiver over a map from node to distance |

## Entries from UTVPI-NEAR (`zedc-solvers/src/negsssp.rs`, `utvpi.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A search held as a struct with an `enum` of where it stands, advanced one unit of work per `step()` call, so that three searches can take turns | `utvpi::GoldbergRadzik::step`, `negsssp::Rounds::step` | Coroutines | A coroutine or generator per search, resumed in turn; without one, the same state machine as a state receiver |
| A caller's `FnMut() -> Result<(), H>` called once per unit of work, its error ending a deep recursion through `?` | `negsssp::potential`, `Solver` | Early exit | An effect handler or an exception that unwinds the recursion; or the coroutine above |
| `PhantomData<fn() -> H>` and `Infallible` to type the stop of a search run alone | `negsssp::Solver`, `potential_alone` | None | Not needed: Zed infers the error type, and a run alone has none |
| `BinaryHeap<Reverse<(Int, usize)>>` with stale entries skipped at the pop instead of a decrease-key | `negsssp::Search`, `bf_dijkstra`, `Rounds`, `Solver::run` | Mutation | A persistent priority queue (a pairing or leftist heap) in a state receiver |
| Labels, stamps and ball membership in `Vec`s written in place and shared by every node of the recursion, each node marked with a fresh stamp so no set is cleared | `negsssp::Solver` | Mutation | A state receiver over maps from vertex to stamp and label |

## Entries from UTVPI-union (`zedc-solvers/src/utvpi.rs`, `negsssp.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The nodes grouped by component with a counting sort into three `Vec<usize>` (start, members, place) filled in place through a cursor array | `utvpi::potential` | Mutation | A group-by into a map from component to its nodes, O(n log n), or the same arrays in a state receiver |
| A `Vec<usize>` of lowered nodes with a `Vec<bool>` of membership, drained by `std::mem::take`, so two searches hand each other only what changed | `utvpi::GoldbergRadzik`, `negsssp::Rounds::take_lowered`, `utvpi::Shared::step` | Mutation | A persistent set of changed nodes passed between the two searches' states |
| Two resumable searches in one struct, each `&mut` field borrowed apart while the other is read | `utvpi::Shared::step` | None | Two coroutines, or two states in one record updated together |

## Entries from UTVPI-both-ways (`zedc-solvers/src/negsssp.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Three buffers of reduced weights reused across steps, the chosen one swapped into place by `std::mem::swap` and the others cleared | `negsssp::Solver::run` | Mutation | The chosen list bound as the next step's value; the others dropped |
| Edges kept in compressed rows (a start offset per vertex into flat target and weight vectors), cleared and refilled each step | `negsssp::Rows`, `Aux`, `Solver::run` | Mutation | An array of rows built once per step by a fold, or a map from vertex to its slice |

## Entries from RACE-constant (`zedc-solvers/src/negsssp.rs`, `utvpi.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Cell<u64>` and `Cell<Option<u64>>` in a `Progress` that the solver writes through `&self` while the caller's closure reads it, both holding shared references | `negsssp::Progress`, `potential`, `Solver::run` | Mutation | The solver passes the units done and its estimate to each tick as values; the tick's caller keeps them in its state |
| A counter captured by `&mut` in the caller's `FnMut` tick, compared with the leader's estimate to skip the pairs' steps | `utvpi::race` | Mutation | The count carried in the race's state receiver, returned by each tick |

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
| The id a sequence or family carries (`Items::id`, `Family::id`, drawn by `fresh_id`, shared by copies) as a key in a `HashSet` or `HashMap`, since ADDR-keys and FAMILY-eq-dag | `value::walk` and `value::maps` (`READ`), `deep::copy` (`copied`), `deep::all_leaves` (`read`) | Identity (gap 1) | A family keyed by value, using L6.13a's hash and equality |
| A thread-local `RefCell<[ReadSet; RELATIONS]>` of pairs read (six relations since MINMAX-tuples), one set per relation indexed by the enum's discriminant (since FAMILY-eq-fast), each an own table by linear probing since FAMILY-eq-cost, emptied (or freed, past 8 times the pairs it held) by the `Drop` of a counted `Scope` when the outermost comparison on the thread ends and kept for the next comparison (FAMILY-eq-reserve), so the comparison `imbl::OrdMap::diff` starts inside another shares it (FAMILY-eq-dag) | `value::Comparisons` (`read`, `scopes`), `Scope` | Mutation (gap 11), no global state | The comparison is one function that threads its read set through its own recursion, including into the comparison of entries |

## Entries from T11-elab (`zedc-elab/src/elab.rs`, `stage.rs`, `query.rs`)

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
| A memo by sequence and family id kept in the evaluator's trace for a run, filled as each fact is made by an explicit stack whose family visits count the values a side stack holds from a mark, `Vec::drain` from that mark when the visit is taken (PROV-oldest-failing) | `Holds::of` | Mutation, identity (gap 1) | A state receiver over the memo, threaded through the run with the facts; the ids are the content digests of gap 1 |

## Entries from T11-preimage (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Terms numbered in an arena (`Vec` of nodes with `u32` children), filled by an explicit stack | `Terms::add` | Mutation | A state receiver over a map from number to node, or the content digest of gap 1, which makes the numbering unneeded |
| The id of a shared subterm (`Shared::id`, drawn by `fresh_id`, shared by copies) as the key of the visited set while the arena is filled; an argument held inline is numbered with no lookup (ADDR-preimage; was `*const Term`) | `Terms::id` in `preimage.rs` and `preimage_ref.rs` | Identity (gap 1) | Keyed by the content digest of gap 1; the id is only looked up, never ordered or printed |
| `std::mem::discriminant` of `Prim` as part of a hash key, since `Prim` has no `Hash` | `Made::Call` | None | `Prim` is an enumeration, so its value is the key |
| `fn(&mut Memo) -> &mut HashMap<K, V>` choosing the table a generic memo helper fills | `Walk::cached`, `Walk::translated` (the type `Table`) | None | A function over the memo record returning the updated record |
| `std::mem::replace` of the context field around a sub-transfer | `Tx::open` and `Tx::shut` around a call, `Walk::made` | Mutation | The context passed as an argument and returned with the result |
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

## Entries from AND-fns (`ast/types.rs`, `check/mod.rs`, `check/read.rs`, `check/ty.rs`, `resolve.rs`)

- No new gap. `Arc::unwrap_or_clone` of a signature is a copy of a shared value, which in Zed is the value itself (gap 1 covers identity). `fits_in` keys a `HashMap<&Arrow, &Arrow>` by the arrows' content (`Hash`, `Eq`), which in Zed is a map keyed by the arrow value; the `entry().or_insert` loop is a fold that keeps the first arrow per key. `Type::and_operands` walks nested intersections with an explicit stack, which in Zed is a fold over the operand tree; `&dyn Fn` in a test is a function value.

## Entries from AND-fns-fit (`check/ty.rs`, `zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap<(usize, Key<'t>), Vec<usize>>` whose key borrows the atom name (`Key::Atom(&'t str)`) from the arrows it indexes | `check::ty::ArrowIndex` | None | A map keyed by a pair of position and a sum type of carrier and name; Zed shares the name |
| `Option::get_or_insert_with` to build the index on the first slot arrow that equals none of the argument's | `check::ty::every_arrow_fits` | Lazy cells (gap 3) | Build the index before the fold when any slot arrow misses the equal map, or fold with the index as an optional accumulator |
| `binary_search` in a sorted posting list, and a merge of two sorted lists by two cursors | `ArrowIndex::first` | Mutation | Sorted-set membership, and a recursive merge of two lists |
| `Iterator::any` and `all` over the candidates, stopping at the first arrow that fits | `ArrowIndex::first`, `every_arrow_fits` | Early exit (gap 12) | The quantifiers of step L3.15a |
| A `thread_local!` `Cell<bool>` that switches `every_arrow_fits` to the all-pairs search in the test module (since AND-fns-rule6, `REFERENCE`, below) | `check::ty::ALL_PAIRS` (cfg(test)) | Global state | Pass the search as a parameter in the test, or test the two functions directly |
| `impl Iterator` returned in an `Option` (`atom_names`) | `zed-kernel::types::Type::atom_names` | Iterators | A list of pairs, or `None` |

## Entries from AND-fns-rule6 (`check/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `thread_local!` `Cell<Reference>` (an enum of none, all pairs, all subsets) that replaces `ALL_PAIRS` and switches `every_arrow_fits` to a reference search in the test module | `check::ty::REFERENCE` (cfg(test)) | Global state | Pass the search as a parameter in the test, or test the functions directly |
| Concatenated posting lists made a set by `sort_unstable` and `dedup`, then filtered by `retain` | `ArrowIndex::candidates` | Mutation | A sorted set built from the lists, then a filter |
| A `HashSet<Key>` of the carriers and atom names a closed result offers, tested for each candidate's result keys | `ArrowIndex::result_keys`, `candidates` | None | A set of the sum type of carrier and name |
| Every nonempty subset of at most 10 arrows as a bit mask `1u32..1 << n` | `check::ty::tests::together` (test only) | Bit operations on a machine word | A fold that builds the list of subsets, or the bit operations of the integer carrier |

## Entries from AND-fns-rule6b (`check/ty.rs`, `check/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An `Option<Option<String>>` field of the comparison state, taken at entry (`Option::take`) so a nested comparison gives no reason, and set on the way out to an error | `check::ty::Cx::why`, `fits_in`, `why_unfit_in` | Mutation | Return the reason with the verdict from `fits_in`, as a sum type of fit, plain refusal and refusal with a reason |
| A struct of two counters bumped in a recursive walk (`Places`), matched with range patterns (`taken: 1..`) | `check::ty::Places::walk`, `refused_cover` | Mutation | A fold that returns the pair of counts; a `match` on the pair |
| `BTreeMap<usize, Vec<(&Ty, Ty)>>` of the parts at each parameter, filled with `entry().or_default().push` | `check::ty::met`, `covered` | Mutation | A table from parameter to a list, built by a fold |
| `std::slice::from_ref` to compare one arrow of the slot alone | `check::ty::fits_in` | None | A list of one |
| A test generator of small types as bit masks of 7 values (`u8`), with `Rng` threaded through plain functions | `check::ty::tests::a_fit_of_small_types_is_a_cover_of_their_values` (test only) | Bit operations on a machine word | The bit operations of the integer carrier, or a set of values |

## Entries from LR4 (`zedc-syntax/src/ast/mod.rs`, `zed-tools/src/fuzz.rs`)

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

## Entries from T11-uses-of (`zedc-elab/src/elab.rs`, `zed-kernel/src/eval.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A hash key over a shared list (`ListKey`) hashed by its first element and length, compared by `Vector::ptr_eq` before its content, so a use finds its group in O(1) | `elab::Tables::new` | Identity (gap 1) | Number each overload set when `resolve` makes it and record the number in the use, so the group is found by an integer key |
| `<[V; 2]>::try_from(Vec)` to move both arguments out of the argument list after its length is checked | `eval::Machine::prim` | None | A tuple or list pattern of two items |
| Join nodes numbered after the items in one `Vec<Vec<usize>>`, told apart by `index < items` | `elab::topo_joined`, `elab::topo::place` | None | A sum type of item and join for each node, or the same numbering |

## Entries from T14-rope (`zed-kernel/src/text.rs`, `zed-rt/src/heap.rs`, `zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| One `Arc` rope node shared by the kernel and the native heap, so a string crosses between them with no copy | `Obj::Str(Text)`, `Heap::value`, `hooks::text` | None | Zed shares values; one runtime holds one string type |
| `OnceLock<Arc<str>>` in each join node, the text written out on the first read through `&self` | `Text::flat`, `Deref for Text` | Lazy cells (gap 3) | `String` ropes in the standard library (L6.16): the text written out by a function, its result kept by the runtime, or no cache |
| Byte and character counts kept in each node and added at a join | `Node::len`, `Node::chars` | None | Two integer fields of the rope node |
| `Mutex<Option<(Text, Text)>>` for a join's parts, taken through `&self` once the text is written out | `Node::parts`, `Deref for Text` | Lazy cells (gap 3) | The rope's written-out form replaces the node in the runtime's cache, or no cache |

The `OnceLock` and `Mutex` rows above were removed by WRITE-prefix-scale, with `Deref for Text`.

## Entries from WRITE-prefix-scale (`zed-kernel/src/text.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A persistent AVL tree of `Arc` nodes, a join rebuilding the path it rebalances (replaced by TEXT-append-O1, below) | `Text::join`, `concat`, `balance` | None | A recursive `enum` with shared parts; the recursion is O(log n) deep |
| An iterator over the blocks with its own stack of `&Text`, capacity the height plus one (since TEXT-append-O1, six times the depth plus nine) | `Chunks`, `Text::chunks`, `compare` | Early exit (gap 12) | A walk over the tree; `compare` stops at the first byte that differs, a `loop` with `break`; depth O(log n) |
| `Cow<str>` returned by `flat`, borrowed for one block and owned for a join | `Text::flat` | None | Returns a `String`; one block is shared, not copied |

## Entries from TEXT-append-O1 (`zed-kernel/src/text.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A persistent 2-3 finger tree, every tree, node and block one `Arc<Tree>` enum, its digits fixed arrays `[Option<Text>; 4]` and its nodes `[Option<Text>; 3]` filled from the front | `Tree`, `Digit`, `push_back`, `push_front`, `concat`, `nodes` | None | A recursive union with shared parts; a digit and a node are tuples or short lists, matched by their length |
| `std::array::from_fn` to fill a digit or node from a slice | `digit`, `node` | None | A tuple or list built from the parts |
| `std::slice::from_ref` to pass one part as a slice | `push_back`, `push_front` | None | A list of one part |

## Entries from L3.1 (`zedc-syntax/src/ast/`, `format.rs`, `resolve.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A generic enum `RangeEnd<T>` with a method returning `Option<&T>`, used for both expressions and patterns | `ast::RangeEnd`, `ExprKind::Range`, `Pattern::Range` | None | A union of atoms with a payload of the type parameter: `#below(T) \| #through(T) \| #open` |
| A generic method taking `impl FnOnce(&mut Self, usize) -> Result<T, Error>`, so one helper builds the end of a range for both expressions and patterns | `Builder::range_end` | Mutation | The builder is a state receiver; the function argument returns the new builder with the result |
| `match (layer, kids)` on a tuple of an integer and a slice pattern (`&[op]`, `&[_, unordered]`) | `Builder::reduce_tail` | Slice patterns | Test the length, then index (the appendix's row for slice patterns) |
| `unreachable!` arms for the L3 forms that resolution refuses | `elab.rs`, `check/mod.rs` | Partial match | As for L2.1: a total match whose L3 arm returns the refusal, or a narrower type from resolution |

## Entries from T14-occ (`zed-kernel/src/provenance.rs`, `value.rs`, `family.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A global `AtomicU64` handing out blocks of ids to a thread-local `Cell` counter, so that each new family gets a fresh id (lists had one until T14-occ-id and again since ADDR-keys, with field lists) | `fresh_id` in `family.rs`; `Family::made_from`, `Family::extend` | Identity (gap 1), mutation | A content digest as a field (gap 1), or an id counter threaded as state through the machine |
| `imbl::OrdMap::diff`, which skips subtrees two maps share | `Held::base`, `short_diff` | Identity (gap 1) | A diff that compares entries; it costs the size of the smaller map rather than the change, unless the runtime gives `==` a shortcut on shared nodes |
| `HashMap` keyed by family ids and by the id of a list (`Items::id`, since ADDR-keys), filled during the pass | `Held::{sets, seen, done, made}` | Identity, mutation | A state receiver over a map keyed by family ids and list digests (gap 1) |
| A persistent cons list in `Arc` with a cached hash and depth, whose `Eq` first tests `Arc::ptr_eq` | `Position::{child, eq}` | Identity (gap 1) | A list of child indices with the hash as a field; `==` compares the hashes, then the indices |
| `Drop` that unlinks a long cons list in a loop, so that dropping it does not recurse | `Position::drop` | No destructors | The runtime frees long lists without recursion (step L6.13) |

## Entries from T14-rope-len (`zed-kernel/src/text.rs`, `zed-kernel/src/words.rs`, `zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `usize::checked_add` of two byte counts, refused past `usize::MAX` | `Text::join` | Machine integers | With `int` counts the sum never wraps; the refusal stays as an `if` comparing the sum with the largest length the runtime can address |
| `i64::try_from` of a count, with a big integer when it does not fit | `words::word` (`Len`), `hooks::node` (`Len`), `store::cell::Cell::literal` (a string's length; past `i64` its exact value as a big integer) | Machine integers | Vanishes: `len` returns an `int` |

## Entries from L6.1 (`zedc-syntax/src/ast/`, `format.rs`, `resolve.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A stable `sort_by_key` on a key method of an enum, shared by the builder and the formatter | `StmtKind::place`, `Builder::block`, `ast::unit`, `Formatter::stmts` | None | A `sort` by a key function; the prelude's sort is stable |
| `match *self.kids(k) { [name, set] => …, [e] => … }`, slice patterns on a dereferenced slice | `Builder` index keys | Slice patterns | Test the length, then index (the appendix's row for slice patterns) |
| A `HashSet<&str>` borrowed from the statements, so each indexed family is bound once | `Resolver::declare` | Borrowed keys | A set of names; strings are values, so no borrow is needed |
| `unreachable!` arms for the L6 forms that resolution refuses | `elab.rs`, `check/mod.rs` | Partial match | As for L2.1 and L3.1: a total match whose L6 arm returns the refusal, or a narrower type from resolution |

## Entries from OSP-lit (`zedc-resolve/src/docs.rs`, `zed-kernel/src/num.rs`, `zedc/src/run.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `slice::partition_point` with a closure, a binary search over the token list | `docs::check` | None | A binary search over a sequence by a predicate, from the L3 library |
| `Option<(usize, Span)>` matched as `Some((n, span)) if *n == next` through `&mut`, then extended in place | `docs::check` | Mutation | A fold over the doc comments whose state is the open block, returned with each step |
| `str::parse::<f64>()` and `str::parse::<f32>()`, correctly rounded by the standard library | `num::literal_f64`, `num::literal_f32` | Missing primitive | A prelude cast `f64(text)` that rounds to nearest with ties to even, as `num::literal_f64` does |
| A sink typed `FnMut(&str, &str) -> Result<(), (String, String)>` for the path and reason of a failed write | `run::commit` | Mutation | A function returning the acknowledgment atom `#ioError(op:, path:, why:)` directly |

## Entries from T11-fix-store (`zedc-presburger/src/hull.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A builder that takes `mut self` and changes its `imbl::OrdMap`s in place through `get_mut` and `entry(..).or_default()`, which copy only the shared nodes on the path; `contains_key` first, since `remove` and `get_mut` copy that path even for an absent key | `Hull::and`, `Hull::join`, `used` | Mutation | Zed's map updates return new maps; the cost matches only if the runtime updates a map in place at its last use (step L6.13) |

## Entries from T-zone (`zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `imbl::OrdMap` of bindings, cloned into each arm's scope and shared by structure | `Scope::{bind, unbind, join, close}` | None | A Zed map is a value; cloning is sharing |
| A `u64` counter in the scope that orders bindings | `Scope::bind` | Mutation | The scope is passed and returned, with the counter as a field |
| A worklist `Vec` with a visited `BTreeSet`, then a sort by order and a right fold into nested `Term::Let` | `Scope::close` | None | A `fold` over the worklist with a set in its state, then `sort` and a fold |
| `matches!(^e, Term::Lam(..))` on an `Arc<Term>`, and `Option::then` | `Scope::bind` | None | A pattern test `is Lam` |

## Entries from OSP-order (`zedc-lattice/src/wto.rs`, `iterate.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::ptr::eq` on two forms, and on two keypaths, as a shortcut to `Equal` before comparing them structurally (`same_or_cmp`) | `impl Ord for VertexKey` | Identity (gap 1) | The structural comparison alone, or the runtime's `==` shortcut on shared values; the address comparison before it already leaves only nodes of one binding and one address, and the form comparison only cells of one node |
| `Ord` written by hand for a struct of three fields, so that the form, a type parameter, is compared last and only on a tie | `VertexKey::cmp` | None | A tuple `(name, address, form)`, which compares left to right (`zed/prelude/iteration.zed`, `solve`) |
| A stack of `&mut Element` walked to rewrite vertex numbers in place in a nested tree | `wto::ordered_by` | Mutation | A map over the tree of elements that returns a renumbered tree, by an explicit stack or by recursion on the nesting depth |

## Entries from ST (`zedc-preimage/src/product.rs`, `presburger.rs`)

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

## Entries from OSP-diag (`zedc-base/src/rejection.rs`, `check/read.rs`, `check/ty.rs`, `testing.rs`, `zed-rt/src/heap.rs`, `zed-native/src/hooks.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `macro_rules!` that declares the enum of rejection rows, its list of every row and its name function from one table | `rejection::rows!` | No macros | An atom union with a constant list of `(row, name)` pairs; the name function is a lookup in it |
| A cargo feature that adds a field to a struct and a body to a method, off in a release build | `Cell::site`, `Heap::site`, `Heap::allocating`, `Display for Ty` and `Sig` under `printed-types` | No conditional compilation | A build mode of the runtime unit: the test build imports a counting heap, the release build the plain one, both with one interface |
| A thread-local `RefCell` that a test turns on and reads back, filled from inside `Display` | `ty::printed::{start, take, record}`, `hooks::COUNTED`, `zed_native::counted` | Mutation (gap 11), no global state | The printer and the run return what they record beside their result, and the test reads it there |
| `BTreeMap` keyed by `(&'static str, Option<usize>)` to group the live cells | `Heap::survivors` | None | A family keyed by the pair, summed by a reduce |
| A text-level pass over a printed type that tracks parenthesis depth and quotes to cut the `for` clauses | `read::clauses` | None | A fold over the characters with the stack of open groups as its state |
| `<[String; 1]>::try_from(Vec)` to move the one item out, the vector given back otherwise | `Sig::text` | None | A list pattern of one item |

## Entries from ST-deep-stack (`zedc-presburger/src/presburger/deep.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `impl Drop` with a work list on the enum `Formula`, so a value nested 100,000 deep is freed without recursion | `presburger/deep.rs` | None | Removed: the runtime frees values, and must free a deep chain without recursion itself (as for T2-parse's row) |
| Moving parts out of a value whose type has `Drop` by `mem::take` and `mem::replace` through `&mut` (`into_parts`, `into_negated`, `Con::take`), since Rust forbids moving fields out of such a value by a pattern | `Formula::and`, `or`, `negate`, `Parts::of`, `Conjuncts::and_held` | Workaround | A pattern that binds the parts; with no `Drop` in Zed the workaround goes |
| Hand-written `Clone`, `PartialEq`, `Ord`, `Hash`, `Debug` and `Display` over explicit stacks, giving what the derived forms give (since ST-formula-share `Clone` is one `Arc::clone`) | `presburger/deep.rs` | Missing | Structural equality, order, hashing and printing are the runtime's, which must not recurse on depth |
| A generic post-order fold with a context passed down, results kept on one `Vec` and split off per node | `Formula::fold`, used by `map_cons`, `forget`, `nnf` and `Hash` (since ST-formula-share `holds_as` and `Clone` no longer use it) | None | A recursive function, once the machine keeps frames on the heap; or a state receiver over a list |

## Entries from ST-formula-share (`zedc-presburger/src/presburger.rs`, `presburger/deep.rs`, `preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Arc` children on the enum `Formula` (`Not(Arc<Formula>)`, `And` and `Or` of `Arc<Vec<Formula>>`), so a clone is O(1) and a part held in several places is one node; `Arc` and not `Rc` because `Formula` must be `Send` | `presburger.rs`, `presburger/deep.rs`, `conjuncts.rs`, tests | None | Zed shares values, so a part is one value however many places hold it |
| `Arc::strong_count` to tell a node held in several places from one held once, and `Arc::get_mut` to move parts out of, or sort in place, a node held once, copying one level otherwise | `Formula::is_shared`, `into_parts`, `into_negated`, `take_kids`, `Drop`, `nnf` | Mutation (gap 11) | The runtime's own reference counts reuse a value held once; the code builds new values |
| `deep::Id`, an owned clone of a node whose `Eq` and `Hash` are the `Arc` address (`Arc::as_ptr`), as the key of the memos that read a shared node once | `Formula::fold`, `holds_as`, `walk`, `Ord`, `Parts::of`, `unbounded` | Shared tables across pure calls (gap 2) | A memo keyed by the value's identity, if the runtime gives one; otherwise by hash-consing the formula |
| A `u64` hash folded bottom up per node with `DefaultHasher`, then written once, so a formula hashes alike however its parts are shared | `impl Hash for Formula` | None | The runtime's structural hash, which must read a shared value once |
| `Rc<Parts>` memo tables (`HashMap<Id, Vec<Rc<Parts>>>` for disjunctions and `HashMap<Id, Rc<Parts>>` for disjuncts) filled while the frames of an explicit stack are made | `Parts::of` | Mutation (gap 11) | A fold over the formula with the tables in its state |

## Entries from ST-formula-wide (`zedc-presburger/src/presburger.rs`, `presburger/deep.rs`, `preimage.rs`, `conjuncts.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A closure `impl Fn(usize) -> bool` that says which operands to keep whole, passed to `and_keeping` and `or_keeping` | `Formula::and_keeping`, `or_keeping`, `rebuild`, `nnf`, `preimage::Tx::formula_at` | None | A function value parameter |
| A `HashMap` memo keyed by a raw `*const Parts` address with the base constraints and symbols, holding an `Rc` of the key so the address is not reused, threaded by `&mut` through a recursive function | `project_parts` (`Below`) | Shared tables across pure calls (gap 2), mutation (gap 11) | A memo keyed by the value's identity, if the runtime gives one, in the state of a fold |
| A `HashSet<*const Vec<Formula>>` of visited shared conjunctions, with the formulas held in a `Vec` so their addresses stay live, on an explicit stack | `Conjuncts::and_held` | Mutation (gap 11) | A fold over the worklist with the visited set in its state |
| A visited `HashSet<Id>` built in one walk to find the parts reached through two or more parents | `deep::Id::reached_twice`, `Id::among`, `Formula::chooses` | Mutation (gap 11) | A fold with the set in its state |
| Two stacks of `slice::Iter` over borrowed parts, each level tagged with the number of the entry it was entered with, read in step; a `HashSet<(Id, Id)>` of pairs found equal and a `Vec<Option<(Id, Id)>>` of open entries, `take`n when an entry ends | `deep::Side`, `deep::Level`, `Formula::cmp` | Mutation (gap 11), identity (gap 1) | A fold over the two sides' worklists with the set of equal pairs in its state, the pairs keyed by node identity |

## Entries from ST-formula-shift (`zedc-presburger/src/presburger/deep.rs`, `presburger/deep/canon.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An intern table for one call: a `Vec<Sym>` of symbols and a `HashMap<Sym, usize>` from each symbol to its number, so equal symbols get one number and equality is a comparison of numbers | `deep::canon::Canon::intern` | Mutation (gap 11), shared tables (gap 2, here within one call only) | A state receiver holding the map from symbol to number and the list, threaded through the parse; or the content digest of gap 1 with an exact check |
| A memo `HashMap<Id, Option<usize>>` from each shared part to the root of its parse, and a visited `HashSet<Id>` of the shared parts entered | `Canon::value`, `Formula::cmp` | Identity (gap 1), mutation (gap 11) | The memo and the set in the state of the fold, keyed by node identity |
| A cursor into a lazily expanded parse tree: one `Vec` of entries per level, each with a cursor `(usize, usize)` into the level above, expanded on demand from the top | `deep::canon::Finger::grow`, `Finger::cut` | Mutation (gap 11) | A list of levels held in a state receiver, each level a list with its cursor |
| Unbounded counts of repeats (`num_bigint::BigUint`), since a run can be longer than 2^64 | `Sym::Run`, `Canon::cmp_seqs`, `Finger::cut` | None (`int` is unbounded) | `int` |
| Bit operations on symbol numbers for deterministic coin tossing (`^`, `trailing_zeros`, `>>`, `& 1`) | `Canon::chunk` | Bit operations (gap 4, built) | The bit words of L1.39a |

## Entries from BDD-atom-order (`zed-kernel/src/types/print.rs`, `types/bdd.rs`, `types/bdd/list.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An iterator over nested segments with its own stack of frames, each a `slice::Iter` into a segment list or a group's elements, resumed across `next` calls | `print::Pieces`, `Frame` | Mutation (gap 11) | A state receiver holding a list of (list, index) frames, as for `Machine::run` |
| The text of a decision list written into one `Vec<Seg>` from the first block on, with a `Vec` of the segments that close each block begun, popped onto the end | `Printer::list` | Mutation (gap 11) | A list builder in a state receiver; a list value appended per block would copy the prefix unless the runtime reuses it |
| Ranks of nodes by height, each level's signatures sorted by `sort_unstable` and numbered (AHU) | `Printer::canon` | None | A sort of a list of (signature, node) values, then a fold that numbers equal runs |
| A `#[cfg(test)]` `thread_local!` salt mixed into the type digests, so tests can permute the atom order | `types::SALT`, `mix` | Not ported | Tests only; the port's digests would take the salt as an argument of the digest function |

## Entries from ST-formula-k2-rec (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A stack of boxed closures `Box<dyn FnOnce(&mut Memo)>`, each removing one memo entry, run by `Vec::pop_if` as the reading stack falls | `preimage::Memo::held`, `Tx::cached`, `Tx::through` | Mutation (gap 11) | A list of (height, table, key) values in the translator's state; the drop is a fold that removes each key from its table |

## Entries from ST-formula-k2 (`zedc-presburger/src/presburger.rs`, `preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A builder struct changed through `&mut self` one operand at a time (`Joining`: the parts, a `BTreeMap` from each term and comparison to its place, the count of parts added), with `mark` and `close` around an inner operand of a chain, popping its one part back off the `Vec` | `presburger::Joining`, `Formula::and_keeping`, `or_keeping`, `preimage::Tx::chain` | Mutation (gap 11) | A fold over the chain's operands with the joining in its state, `close` a step of that fold |
| An enum declared inside a function (`Step`: an operand to read, or the end of an inner `&&`), the frames of an explicit stack | `preimage::Tx::chain` | None | A sum type private to the unit |

## Entries from OSP-drop (`zedc-check/src/check/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An explicit stack with a visited `HashSet<Span>`, both mutated while walking back from the bound value to where each dropped atom enters | `Ck::entries` | Mutation (gap 11) | A fold over the worklist with the visited set in its state |
| An explicit stack over nested `else` nodes, with an `if let` guard in a match arm to tell an atom default from any other | `named_defaults` (removed by OSP-drop2) | None | A loop over the `else` chain, and a nested `match` on the default in place of the guard |
| `Src::Call` holding a borrowed `&'a Expr` beside the function id, so the walk can reach the call's arguments | `Src`, `Ck::entries` | None | The call node itself as the source, a shared value |

## Entries from TD-refusals (`zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An `FnMut` closure that prints the constraint once into a captured `Option<Arc<str>>` (`get_or_insert_with`) and is called at each refused question of one projection | `Scope::project_part` (`refuse`) | Mutation (gap 11) | The text is printed before the projection when it may be needed, or each call returns the text with the refusal; printing once per refused part costs the same |
| A struct whose derived `Ord` (field order: constraint, how it was asked, cause) is the order of the warnings, kept in an `imbl::OrdSet` | `Refused`, `Scope::warnings` | None | A record in a set ordered by its fields in that order |

## Entries from ST-join (`zedc-presburger/src/conjuncts.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `BTreeMap` from block to the conjuncts it loses, with a `Vec` of the blocks in the order first met, filled through `entry(..).or_default()` | `Blocks::remove` | None | A fold over the removed conjuncts into a map of lists and a list of blocks |
| A slice pattern with a guard that changes `self` (`[g] if self.unlink(b, g) => {}`), so the guard both tests and does the unlinking | `Blocks::remove` | Mutation (gap 11) | `unlink` returns the new forest or nothing, and a `match` on that result picks the split |
| The block of a conjunct kept in a local while the forest is merged around it, since looking the conjunct up again compares it whole (`Ord` on `Arc<Formula>`) | `Blocks::place`, `Blocks::split` | Identity (gap 1) | The same local, carried through the fold; with content digests a lookup would cost O(1) and the local would be a choice, not a need |

## Entries from CAP-bits (`zed-kernel/src/num.rs`, `num/bound.rs`, `num/factor.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `u128` products for a 64-bit product modulo a 64-bit number | `factor::mul_mod`, `factor::split` | None | `(a * b) mod m` on unbounded `int`, the operands' ranges `int[0..<2^64]` letting the plan use two words |
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

## Entries from OSP-drop2 (`zedc-check/src/check/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Two `HashMap<Span, KType>` fields of `Ck` (`unnamed`, `made`) and a `HashMap<usize, Span>` (`alias`), written as each expression is checked and read by later ones | `Ck::expr`, `Ck::unnamed_of`, `Ck::entries` | Mutation (gap 11) | Maps threaded through the checker's state, as `seen` would be |
| A loop over an array of `(&mut HashMap, Option<KType>)` pairs, to insert or remove one entry in each of two maps | `Ck::expr` | None | Two calls of one helper, or a fold over the pairs |
| Closures that borrow `self` immutably (`u`, `union`, `made`) inside one method | `Ck::unnamed_of` | None | Local functions taking the maps as arguments |

## Entries from S22a (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A persistent treap in `Rc` nodes, each holding its subtree's least and greatest value and a lazy affine tag pushed down on a split, with a priority computed from the piece's ends, shared by every summary built from it | `PaNode`, `Tree`, `split_at`, `join_treap`, `slice_treap`, `apply_tag`, `invert_treap` | Identity (gap 1) | A Zed tree value: an update makes new nodes along one path and shares the rest, which the runtime must keep at `O(log n)`; the priority is a field, so no identity is needed |
| The sticky `ROUNDED` flag saved, cleared and restored around the hull of a term, so a rounding while computing the hull is seen and not reported | `Tx::clip`, `Tx::invert_pa` | Mutation, global state (gap 11) | The hull computation returns whether it rounded with its result; no flag |

## Entries from ENDS-dag (`zedc-stage/src/stage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A reference `Part<'t>(&'t Term)` compared and hashed by `std::ptr::eq` and `std::ptr::hash` as the key of the map from part to number while the term is read; it holds the borrow of the term (was `*const Term` until ADDR-stage) | `Reader::read`, `Reader::got`, `reading` | Identity (gap 1), lifetimes | Keyed by the content digest of gap 1, or by the id each shared term node carries (ledger TERM-id; `Shared::id` from ADDR-preimage); the identity lives only during the reading and is never an order |
| An explicit stack `Vec<(&Term, bool)>` read in post-order, results pushed to a `Vec` by number | `Reader::read`, `each_part` | Mutation | A fold over a worklist list with the map from part to result as its state |
| An arena of trie nodes (`Vec<SetNode>`) with a hash table from node to number (hash-consing) and a memo `HashMap<(Set, Set), Set>` of unions, all filled through `&mut self` | `Sets::make`, `Sets::union` | Shared memo (gap 2), Mutation | A state receiver holding the arena, the table and the memo, returned with each set made; or sets made identical by the content digest of gap 1 |
| `u32::leading_zeros` and bit masks to find the highest differing bit of two names | `Sets::join`, `above` | Bit operations (gap 4) | As gap 4 |

## Entries from S22b (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `c - v` computed in `i128` and turned into an end by `End::lower` and `End::upper`, which set the global `ROUNDED` flag when the end leaves `i64` | `reflect` | Machine integers; Mutation, global state | Zed's `int` is unbounded, so `c - v` needs no wider type and no rounding flag |

## Entries from S22-WIDE (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `i128::MIN` and `i128::MAX` as sentinels for the infinities among the summary's values, matched in patterns (`NEG \| POS if mul > 0`), with `checked_mul` and `checked_add` returning `None` to give the summary up when a finite value would reach a sentinel | `NEG`, `POS`, `finite`, `value_at`, `map_vals`, `make_node` | Machine integers | Zed's `int` is unbounded: the values are `int`, the infinities a tagged variant (`#negInf`, `#fin(int)`, `#posInf`), and no give-up is needed, at a cost in the bits of each value per node |
| An `End` turned into a machine integer by `to_i128` with `expect`, after `in_range` checked every end | `small`, `key` | Machine integers; Abort on a broken invariant (gap 8) | With `int` ends no conversion is needed |
| The priority of a piece mixed from both 64-bit halves of its `i128` end by `as u64` casts, `>>`, `^`, `wrapping_add` and `rotate_left` | `prio_of` | Bit operations (gap 4) | As gap 4, or a hash of the end's content digest (gap 1) |
| A closure `impl FnOnce(i128) -> Option<i128>` passed to a free function that applies it to a finite end or returns the given infinity | `solve` | None | A function argument |

## Entries from T6 (`zed-kernel/src/types/bes.rs`, `rec.rs`, `empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Vec<u32>` stamps and marks overwritten in place, reset by advancing a counter | `bes::Stamp`, `bes::Scratch` | Mutation | A persistent array per pass, or a map from node to the pass that marked it; the counter trick needs mutable arrays |
| Each member's emptiness as its group decides it, computed once for the instance through `OnceLock` and read through the member's key (until CYCLE-kernel-moves a closure `Box<dyn Fn() -> Option<bool> + Send + Sync>` stored in each recursive node, `types::Rec::judge`) | `Type::judged` (`types/empty.rs`), `rec::Key::member_at`, `rec::Env::judged` | Laziness | An indexed definition `parts[id] = …`, evaluated on demand (gap 3) |
| Explicit work stack of `(node id, &Arc<Node>)` pairs filling a graph allocated ahead | `empty::judge`, `empty::kids` (in `rec.rs` until CYCLE-kernel-moves) | Mutation | A fold over the body tree that returns the nodes it adds |
| `impl Iterator for Values` holding an odometer `Vec<usize>` advanced in place, and a `BTreeSet` of the tuples given | `types::Values::next` | Mutation, laziness | A lazy stream whose state (box, positions, tuples given) is passed from one value to the next |
| `std::mem::take` of the lists out of one iterator into the next, in `each_value` | `Type::each_value` | Moves | The lists threaded through a fold over the types in order |
| Explicit stacks of `Step::Enter`/`Step::Leave` and of slice iterators, with `Vec<Option<Item>>` taken in place as each node is visited | `print::Printer::walk`, `print::Printer::write` | Mutation | A fold over the graph in post-order returning the texts and the order, with the visited set as a persistent map threaded through it |
| `&dyn Fn(&mut Printer, &A) -> Text` callbacks that borrow the printer mutably, so one diagram walk serves tuple and morphism parts | `print::Printer::part` | Generic closures over mutable state | A function generic over the literal kind, returning the texts and the nodes found instead of writing them into shared state |
| Explicit post-order stack over the expression graph with `HashMap` memos keyed by node id, holding `Option<imbl::OrdSet>` sets merged smaller into larger | `bdd::Part::forced` | Mutation | A fold over the graph in post-order with a persistent map keyed by the node id, returning the two sets |
| A counter of open needs per simulation pair decremented in place, and a worklist of failed pairs | `empty::Simulation::holds` | Mutation | A fold over the failures that returns the new counts as a persistent map |
| `self.cycles` entries written for every type on a walked path (`Vec` path and `BTreeMap` of positions) | `empty::Search::find_cycle` | Mutation | The walk returns the path and the result; the caller folds them into a persistent map |
| A region shrunk to a piece in place, the search run on it, and the region put back; a counter `give_ups` read before and after to learn whether the search showed a value | `empty::Search::refine` | Mutation | The search takes the piece as an argument and returns whether it showed a value with the verdict |
| A global atomic counter giving each diagram node and expression its id at construction | `bdd::NEXT`, `Bdd::node`, `Part::expr` | Global mutable state | Ids from hash-consing in a persistent table threaded through construction, or content digests |
| A process-wide `Mutex<HashMap<u64, Vec<Group>>>` of accepted definition lists by digest, the first equal list kept, and a global `AtomicU64` numbering each list (INST-bucket) | `rec::GROUPS`, the counter `NEXT` in `Group::new` | Global mutable state, shared tables across pure calls (gap 2) | A persistent map from definition list to its number, threaded through the checker, or the definitions' content digest confirmed by equality as the number |
| A process-wide `Mutex<HashMap<(u64, Vec<Type>), Vec<Type>>>` memo of instances, filled through `entry`: an occupied slot returns its members, a vacant one builds them while the lock is held and inserts them (INST-bucket) | `rec::INSTANCES`, `Group::instance` | Global mutable state, mutation | A memo table threaded as a state receiver, or hash-consing of instances in a persistent table |
| `Vec<OnceLock<Type>>` members set in two rounds (recursive members, then plain members in post-order) before they are read | `rec::Group::instance`, `rec::eval` | Mutation, laziness | A fold over the plain members in post-order building a persistent map from index to type, after the recursive members |
| A `shut` array of six optional key sets, one per universe, filled in place by a first pass over the types: the keys every cofinite type lists, intersected in place (`retain`) starting from the shortest list | `empty::overlaps` | Mutation | A fold per universe over the cofinite types' lists returning their intersection as a persistent set |
| Union-find with path halving: `parent` links rewritten in place while a root is found | `empty::overlaps` | Mutation | A persistent map from key to the first type holding it, folded over the types, joining a type to the classes of its keys |
| A `Vec<bool>` window of steps marked in place by each negated class, the window doubled | `empty::least_length` (removed in T6 repair 6: `residue_length` picks the length by conditional expectations) | Mutation | A fold over the classes returning the set of held steps in the window, as a persistent bit set |
| A list kept as its length, a `num_bigint::BigUint`, with `%` and `-` on it in the walk | `empty::Rep::List`, `residue_length`, `greedy_length`, `Search::list_member` | None | Zed's `int` is unbounded; the length is a plain `int` and the list a record of it |
| A `BTreeMap<Type, BigUint>` of the rest types met, cleared in place after the length left is cut to its remainder modulo the steps between | `empty::Search::list_member` | Mutation | A loop whose state (type, length left, persistent map of types met) is passed to the next round, the map replaced by an empty one after the cut |
| `Option<Option<KType>>` filled on first use inside an `all` closure (`get_or_insert_with`), so the kernel type of the target is built only when some piece needs it | `zedc` `check/ty.rs` `Ty::sub` | Laziness, mutation | A plain `let` before the fold, the plan choosing when it runs (DESIGN sec:semantics) |
| The id of a sequence (`Items::id`) with a type as the memo key of one membership test, never iterated (ADDR-keys) | `types::Type::contains` | Identity (gap 1) | A family keyed by value, using L6.13a's hash and equality |

## Entries from OSP-neglit (`zedc-syntax/src/ast/neglit.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `OnceCell<HashSet<&str>>` of the names written bare, shared by every builder of one source and filled on the first rejection through `&self` | `Builder::written_bare`, `ast::with_holes` | Lazy cells (gap 3) | The set made in one pass before building, or threaded through as a state receiver that is filled on first use |
| A `HashSet<&str>` borrowed from the source text | `bare_names` | Borrowed keys | A set of names; strings are values, so no borrow is needed |

## Entries from SCALE-bytes (`zed-alloc-count/src/lib.rs`, `tests/src/scaling.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `#[global_allocator]` and `unsafe impl GlobalAlloc` forwarding to `System` | `zed_alloc_count::Counting` | Foreign library | Test harness only: the Zed runtime's allocator counts the bytes itself, read through an `@ffi` binding |
| `thread_local!` with a `const` `Cell<u64>`, added to through `&self` | `zed_alloc_count::OWN`, `allocated` (`BYTES` and `add` until SCALE-threads) | Mutation | A count kept by the runtime per thread and read as a value |
| `#[expect(unsafe_code, reason = ...)]` and a crate lint table that denies `unsafe_code` instead of forbidding it | `zed-alloc-count` | Attributes | None needed: Zed has no lint attributes |
| `std::thread::scope` with a stack size, returning the closure's value and its thread's count | `scaling::on_a_thread` | None | A task with its own stack, as in T2-eval |

## Entries from SCALE-threads (`zed-alloc-count/src/lib.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `#[unsafe(no_mangle)] extern "C" fn pthread_create` in place of the C library's, found again by `libc::dlsym(RTLD_NEXT, ...)`, so a new thread gets the count of the thread that started it | `zed_alloc_count::pthread_create`, `create`, `start` | Foreign library | None needed: the Zed runtime starts its tasks itself and gives each its parent's count |
| `Arc<Count>` chain of `AtomicU64` counts, one per thread, each holding its parent's, and a `thread_local!` raw pointer to this thread's | `zed_alloc_count::Count`, `COUNT`, `count` | Shared tables across pure calls (gap 2) | A count per task that adds to its parent's, kept by the runtime |

## Entries from R10-stack (`zed-rt/src/stack.rs`, `zed-native/src/lib.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `libc::mmap` with `MAP_NORESERVE` and `mprotect` of a guard page, sized by `libc::sysinfo`; `munmap` in `Drop` | `Stack::new`, `Drop for Stack` | System calls, no destructors | Stays in the Rust runtime (L6.13); a Zed runtime needs a foreign call to map memory and a scope that unmaps it |
| `psm::on_stack`, switching the machine stack for one call | `Stack::run` | Stack switching | Stays in the runtime; a Zed program has no access to the machine stack |
| `catch_unwind` on the new stack and `resume_unwind` on the old one | `Stack::run` | Early exit (gap 12) | Errors are values in Zed; the runtime returns the run's error across the switch |
| A raw pointer `*mut c_void` to the mapping | `Stack::base` | Identity (gap 1) | An address held by the runtime, not by Zed code |
| `std::process::Command` with `pre_exec` calling `libc::setrlimit(RLIMIT_AS, …)`, running the test binary again as a child (R10-stack-notes) | test `stack::tests::a_limited_address_space_refuses_the_reservation` | Missing (process limits) | A test-harness facility, not the language |

## Entries from ST-arms-quad (`zedc-presburger/src/presburger.rs`, `preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Rc<Parts>`, a disjunct shared by the level above, a search and the parts a disjunct was settled from, so that no level copies the nest below it | `Parts.ors`, `settle`, `project_parts`, `pick` | None | Zed shares values, so a disjunct is the parts themselves |
| `OnceCell<OrdSet<Atom>>` on `Parts`, the atom set of a disjunct filled the first time it is asked for through `&self`, and used as the visited mark of the walk that fills it | `Parts::atoms` | Lazy cells (gap 3) | The atom sets built bottom up when the parts are made, or a map from a hash-consed id of each part, threaded through as a state receiver |
| `imbl::OrdSet<Atom>`, a persistent set cloned in O(1), so that a disjunct's atom set starts as its largest child's, shared, and the others are inserted | `Parts::atoms` | None | Zed's sets are values that share structure, so the larger set is reused as is |
| `Cell<u64>` on `Parts`, the stamp of the last search that found the parts not to hold, set through `&self` during a walk of shared parts, with stamps from a global `AtomicU64` counter | `Parts::failed`, `Parts::witness`, `fresh_stamp`, `pick` | Mutation, identity, global state | A set of the hash-consed ids of the parts found not to hold, threaded through the search as a state receiver and emptied when the model changes |
| `HashMap<(BTreeMap<Atom, Int>, Rel), usize>`, the index of the bound kept for each left-hand side and comparison, so that a bound written again replaces or is dropped against the one kept, in place | `Linked::meet`, `Linked.by_terms` | Mutation | A map from the terms and comparison to the bound, updated as a value, with the constraint list rebuilt from it |
| An explicit stack of frames borrowing the parts (`Frame<'a>`), with the output vector truncated back to a frame's mark when the part fails | `Parts::witness` | Mutation | A fold over the parts returning the list of held parts or a failure, with the stack as a list value |
| `Option<&Formula>` and `Option<Formula>` filled on first use (`get_or_insert_with`) for the summary of a level | `project_parts` | Lazy cells (gap 3) | The summary built before the loop when any hull has two finite bounds, or a plain `let` |
| `thread_local!` `Cell<u64>` counting the parts the search tests, read and reset by a test through `parts_tested` | `presburger::TESTED`, `Parts::witness`, `parts_tested` | Mutation, global state | The count returned with the search's answer, or a trace effect the test handles |
| `thread_local!` `Cell<u64>` counting the parts of derivations built and the boxes `@exact` searches take, read and reset by a test through `derivation_steps` and `exact_steps` (L1.39b) | `check::DERIVED`, `built`, `Reason::note`, `Ck::said`, `Ck::also`, `Ck::derive_into`; `preimage::EXACT`, `branch` | Mutation, global state | The count returned with the check's or the search's answer, or a trace effect the test handles |
| A closure that words a note only when it is used, `impl FnOnce() -> String` | `Ck::also` and its three callers | None | A Zed lambda; the note is computed when it is called |
| A lifetime on a value that borrows the unit's text (`Origin<'a>`, `Why<'a>`, `Saved<'a>`) | `check::Origin`, `Why::{Untracked, Typed}` | None | Zed shares values, so the declared type is held without a lifetime |
| `std::ptr::eq` on two formulas as a shortcut to `Equal` in a hand-written `Ord` and `PartialEq` that otherwise compare as the derived ones, so a lookup that finds the very formula it holds does not walk it | `impl Ord for Formula`, `impl PartialEq for Formula` (`presburger/deep.rs`) | Identity (gap 1) | The runtime's `==` shortcut on shared values, or keys by the content digest of gap 1 |
| `impl Drop` with a work list on `Parts`, taking each nested disjunct no other holder shares by `Rc::try_unwrap`, so a nest 100,000 deep is freed without recursion; and `Parts::of` building nested disjuncts on an explicit stack of frames | `Parts::drop`, `Parts::of` | None | Removed: the runtime frees values without recursion (as for `Formula`), and `of` becomes a fold over the formula |
| A `bottom` flag set on a scope while its names are kept as they were, and the names rebuilt as bottom only for a scope that is shown | `Scope::reduce_case`, `Scope::empty_if_bottom` | None | A record field set by the reduce that returns the scope; the shown scope is mapped to bottom names once |

## Entries from HOLE-oneline (`zedc-syntax/src/lex/string.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `match` arm guarded by `if let` on the comment that starts at the position, and `if … && let Some(nl) = …` testing a flag and binding the first line break | `hole_end` | None | An `is` test before the `match`, and an `if` on the flag around a `match` on the break |
| `slice::partition_point` over the sorted line-break positions, the first break in a range | `Holes::first_break` | None | A binary search over a sequence by a predicate, from the L3 library (as `docs::check`) |

## Entries from TD-values (`zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A resumable generator per type as an explicit state machine (`At::Start`, `Tuple`, `Past`) whose step returns `Err((maker, position))` for a value it needs first, driven by an explicit stack | `types::Values::fill`, `Maker::step` | Laziness, mutation | A `gen` per type over the makers' lists, or the same loop as a state receiver holding every maker's list and position |
| `split_at_mut` of the makers, so a maker grows its own list while it reads the lists of the makers before it | `types::Maker::step` | Mutation | The step returns the new value and state, and the loop puts them in the persistent list of makers |
| `split_at_mut` of the basis, so one row is reduced by an earlier row in place (LLL size reduction, and the unimodular completion) | `store::live3::reduce`, `store::live3::complete` | Mutation | The step builds the reduced row from the two rows and puts it in the persistent list of rows |
| `std::mem::replace` of the maker's state with `At::Start`, put back on the path that waits | `types::Maker::step` | Mutation | The step returns the next state as a value |

## Entries from LIN-probe (`zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec<Vec<bool>>` of which disjuncts a point found so far holds, beside the disjunctions; one row taken with `std::mem::take` while its disjunction is tested and put back after, the other rows set in place when a point is found | `probe` | Mutation | A loop whose state is the disjunctions with their flags as one list of records; a point found returns the list with its flags or-ed |

## Entries from CAP-pow32 (`zedc-lattice/src/revision.rs`, `preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An enum of the solver's `Int`, the kernel's `Arc<Rat>` (an unbuilt prime power) and a parity alone for a count of factors past `u32::MAX`, read only by `is_zero`, `is_odd` and `to_u32` | `revision::Exponent` | None | Zed's `int` is one type, so the exponent is an `int` or a parity; a port must keep the kernel's unbuilt form or `10^10^9` is built |
| `Option<u32>` with `checked_add` and `zip`, a count that is `None` past `u32::MAX` | `preimage::Count` | Fixed-width integers | `Option<u32>`, or an `int` compared with `2^32`, as it is O(1) only while bounded |
| `Op` no longer `Copy`, passed as `&Op` to `tonicity`, `forward` and `backward` | `revision`, `preimage`, `preimage_ref`, `product`, `check` | None | Values are shared in Zed; the reference goes |

## Entries from CANON-stable (`zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A struct of dense `Vec<usize>` and `Vec<Vec<usize>>` arrays written by index in a loop (color, position in class, counts, the stack of refining colors), and the `placed` and `taken` marks of the breadth-first order | `presburger::Refine`, `presburger::canonical` | Mutation (gap 11) | A state receiver whose arrays are reused in place by provable last use (L6.13); a copy per write would make the O((n+m) log n) refinement quadratic |
| `Vec::swap_remove` with the moved element's position fixed by hand, and `mem::take` of a scratch vector | `Refine::split`, `Refine::run` | Mutation (gap 11) | The same writes as a `patch` on the threaded state |

## Entries from T6-ratlit (`zed-kernel/src/num.rs`, `types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `u128` product reduced modulo the Mersenne prime `2^61 - 1` by a mask and a shift | `num::mul_mod` | Bit operations (gap 4) | `(a * b) mod (2^61 - 1)` on `int`, the operands' ranges `int[0..<2^61]` letting the plan use two words |
| `[2, 5].map` with a closure that splits each prime off two captured coefficients through `std::mem::take` and reassigns them | `Rat::literal_text` | Mutation | A fold over the two primes with the coefficients as its state |

## Entries from S22e-quad (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A persistent segment tree in `Rc` nodes over class indices, each leaf range holding a `Pa`, with a lazy affine tag pushed down on a splice | `ByClass`, `Cls`, `cls_affine`, `cls_halves`, `cls_splice` | Identity (gap 1) | A Zed tree value, as the treap of S22a: a splice makes new nodes along `O(log n)` paths and shares the rest |
| The memo tables a run computes without reading its class moved out with `std::mem::take` and moved back for the next class | `Kept`, `Run::keep`, `Run::restore` | Mutation | The tables are a value passed from one class's run to the next and returned with each result |
| `u128` saturating multiply and add to bound values and coefficients over every class against `i64::MAX` | `Bound::holds`, `ByClass::affine` | Machine integers | Zed's `int` is unbounded; the check compares with the `i64` limit directly and needs no saturation |

## Entries from S22e-wide (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A Fenwick tree in a `Vec<i64>` changed in place by closures over `&mut`, stepped with `isolate_lowest_one` | `covers` | Mutation | A Zed value threaded through the sweep's fold, or a persistent counting tree over the classes, `O(log G)` per step either way; the step is `bitAnd(i, 0 - i)` on bit words (L1.39a) |

## Entries from TD-ends (`zedc-int/src/int.rs`, `interval.rs`, `affine.rs`, `presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Num`, an enum of one `i64` word or a boxed `BigInt`, normalized so a value that fits is always the word; arithmetic on `&Num` widens to `i128` and back | `store::int::Num`, `interval::End::Fin` | Machine integers | Vanishes: an end is an `int`, which the runtime already holds as a word or a big integer |
| `Num`'s third form, a value outside `i128` kept as boxed `(sum of c_i * core_i + d) / den`, each core a product of powers of integers and of floor roots of kept values (`Word::Kept`), with `PartialEq`, `Ord` and `Hash` written by value (hash by value inside `i128`, by sign outside it; consistent, since a value inside `i128` has one form and equal values outside it have one sign) since a kept value and a written out `BigInt` may be equal; ordering by signed interval approximations at doubling precision, terms collected by core and folded by base | `store::int::{Kept, Atom, Core, Approx, collect, fold, balance, approx_cmp, root_approx, root_power_cmp, least_root, OddPart, odd_root_mod_pow2, coprime_base, exponents_over, strip, is_perfect_power}` | Zed's `int` has no kept form | Needs kept values in the runtime's integers (ledger CAP-bits proposes a kept power for `zed-kernel` num), or a Zed record of the terms and cores with these comparisons written in Zed |
| The approximation of a kept root held in an `Arc<Mutex<Option<(u64, Approx)>>>` beside the root, shared by every copy of the atom, refined through `&self` and left out of the atom's order and equality (`Memo`) | `store::int::{Memo, Atom::approx}` | Lazy cells (gap 3) | A memo of root approximations keyed by the root's form, kept by the runtime, or the approximation passed along with the value |
| `Int`, the same with an `i128` word, for the Presburger solver | `store::int::Int`, `presburger.rs` | Machine integers | Vanishes: an `int` |
| `BigInt` from `num-bigint` behind both | `store::int` | External crate | Goes with `num-bigint` (see the external crates above) |
| `u64` residues multiplied in `u128` and reduced (`pow_mod`), and big integers reduced modulo a power of 2 by a bit mask (`odd_root_mod_pow2`, `pow_mod_pow2`, `inverse_mod_pow2`) | `store::int::{pow_mod, odd_root_mod_pow2, pow_mod_pow2, inverse_mod_pow2}` | Machine integers; bit operations on `int` | `int` products and `%` (the runtime keeps them in a word while they fit), and a mask as `x % 2^k` unless Zed gains bit operations on `int` |
| The S22a summary's pieces as `i128` values with the ends of `i64` standing for the infinities, entered only when every finite end lies strictly inside `i64` (`in_i64`, `small`; since S22-WIDE `in_range`, the ends strictly inside `i128` and the infinities `i128::MIN` and `i128::MAX`), and nodes copied whole with `..(^node).clone()` now that an end is not `Copy` | `store::preimage::{in_range, small, key, input, apply_tag}` | Machine integers; struct update syntax | Vanishes: ends are `int` and the summary holds them as they are |

## Entries from TD-cong (`zedc-lattice/src/lattice.rs`, `canon/domain.rs`, `canon/serial.rs`, `store/affine.rs`, `store/int.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Congruence` no longer `Copy`, since its modulus and residue are `Num`: `.clone()` where a class is kept and matched again, and patterns on `Class { modulus, .. }` with a guard `modulus.is_zero()` in place of the literal pattern `modulus: 0` | `lattice::Congruence`, `canon::domain`, `store::{preimage, preimage_ref, product, revision}` | None (literal patterns on a boxed integer) | Vanishes: a class is a record of two `int` values, shared, and an `int` literal pattern matches at any size |
| The extended Euclid and CRT on `&Num` references with `Num` temporaries | `lattice::inverse`, `Congruence::meet` | Machine integers | Vanishes: `int` arithmetic |
| A serialization tag chosen by whether both values fit in `i64` (tag 1 and two words, else tag 2 and two decimal texts) | `canon::serial` | Machine integers | One tag; the runtime writes an `int` in its own form |
| An exponent held as `Exponent::Num(Num)` or `Exponent::Past { odd }`, read through `num() -> Option<&Num>` | `revision::Exponent`, `Num::{pow_by, floor_root_by, ceil_root_by}` | Machine integers | An `int` exponent, with the parity form kept only where a count is not built |

## Entries from F44-memo (`tests/src/scaling.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::thread::scope` and `Builder::spawn_scoped` with a stack size, joined at once, so each run starts with empty thread-local memos | `scaling::alone` by `scaling::counted_on_a_thread` | Shared tables across pure calls (gap 2) | None needed: a Zed memo is a value threaded through the run, so a run that starts from an empty one is fresh |
| `stacker::remaining_stack` to give the run's thread what is left of the caller's stack | `scaling::alone` | Foreign library | The runtime's own stack size for a task |
| `std::panic::resume_unwind` to carry a run's panic into the caller | `scaling::counted_on_a_thread` (so `alone`, `on_a_thread` and `deep::on_main_sized_stack`) | Early exit (gap 12) | A failed run is a failure value returned to the caller |
| `AtomicUsize::fetch_add` and `Mutex` in place of `Cell` and `RefCell` in test closures, because a run on another thread needs `Sync` | `l01_22` (with `deep_types.rs`), `l01_23` (with `x13.rs`), `l01_36`, `l25_08` scaling tests, and the unit tests `a_comparison_runs_each_size_as_often_as_the_meter_says` and `each_run_starts_with_empty_thread_memos` | Mutation (gap 11) | A state receiver holding the counter or the cache of built inputs |

## Entries from L1.17a (`zed-kernel/src/num.rs`, `num/bound.rs`, `words.rs`, `eval.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `thread_local!` cells, a flag and a slot for the first refusal, set by an infallible `Ord` and read after each primitive | `num::WATCHED`, `num::REFUSED`, `Machine::prim` | Mutation, identity | The order returns its refusal as a value (`try_cmp`) and the family's key order is a fallible function of the run |
| A guard struct whose `Drop` restores the outer flag and record when a run ends, on every exit path | `num::Watch`, `Evaluator::run` | Mutation | The run passes its own state; nothing to restore |
| `Vec::try_reserve_exact` to ask the allocator for a block and free it at once | `num::room`, `num::given` (from CAP-bits) | Missing (no allocator query) | A runtime primitive that answers whether a block of a size can be given |
| `Cow<'a, BigUint>` for a coefficient borrowed from a number or built as a product | `bound::Product`, `num::times` | None | Zed shares values, so the field holds the number itself |
| `Cow<'a, Rat>` in `Exact`, a wide number borrowed and a small one or a float built, so ordering numbers of two kinds copies no digits | `num::Exact`, `Value::exact`, `words::word` | None | Zed shares values, so the place holds the number itself |
| `rustix::process::setrlimit(Resource::As, …)` in a test child process | `tests/.../memory_check.rs` | Missing (process limits) | A test-harness facility, not the language |
| A `fmt::Write` sink that counts bytes, so `Display` and `Debug` give a leaf's length with nothing written | `words::Count`, `words::written` | Missing (no formatter trait) | A length function per printed kind, or printing into a counting port |
| `String::try_reserve_exact` that keeps the reserved block and writes into it | `words::print` | Missing (no allocator query) | The runtime primitive above, returning the block |
| A `HashMap` memo keyed by a sequence's id and a family's id, and a map keyed by a field list's id (`Fields::id`) and its length (ADDR-keys) | `words::room_to_print` | Identity (gap 1) | A family keyed by value, using L6.13a's hash and equality |

## Entries from BIT-kept-ends (`zedc-int/src/int.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `match` arm guarded by `if let … && let …` on a divisor that is a kept power of 2 and on the dividend's shift by its exponent (`Kept::shr`, `None` when no term has that power as a factor) | `Num::div_floor` | None | An `is` test and the shift before the `match`, falling through to it when either is absent |
| A struct declared inside a function, `Part<'a>`, whose odd atoms borrow the exponents of the kept form | `Kept::trailing_zeros` | None | A record of the function's own module; the exponents are shared values, not borrows |

## Entries from TYPE-forms (`zedc-check/src/check/mod.rs`, `resolve.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap` of the clauses' variables, each entry saved on entering a clause and restored on leaving it, and a stack of open function types whose bound maps are filled in place by the uses below them | `check::Denote`, `resolve::Resolver::type_var` | Mutation | The clause map passed down as a persistent map argument, and each denotation returning, with its type, the bounds of the variables it uses keyed by the depth of their clause, merged at each function type |
| A `HashMap<&str, Vec<usize>>` of the argument positions of each bounded variable, keyed by borrowed names and emptied by `remove` as each variable is read | `check::Checker::apply_one` | Mutation | A persistent map folded over the arguments, looked up per variable |
| A flag on each open function type, set while its parameters are read, so a use records whether a parameter holds its variable (`Sig::held`) | `check::Denote::{open_params, close_params}` | Mutation | Each denotation returns, with the bounds of its uses, the set of those in parameters, merged at each function type |
| A comparison context whose maps of rigid variables and of functions met are filled as each comparison of function types opens and emptied by a list of the names it made as it closes (`Cx::fresh`, `Cx::forget`), and a counter of names made | `check::ty::Cx`, `fits_in` | Mutation | The maps passed down as persistent map arguments, so closing needs no undo; the counter is a state receiver, or the depth and position of the comparison as the name |

## Entries from LIN-probe-refute (`zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The breadth-first order of the parts built from a `seen: Vec<bool>` written by index, an `order` queue read through a moving `head` index, and a `done: BTreeSet<&Atom>` of atoms whose parts were queued | `bounds_refute` | Mutation (gap 11) | A fold over the queue with `seen`, `order` and `done` in its state, kept in place by provable last use (L6.13); a copy per write would make the O(n log n) reading quadratic |
| An `AtomBounds` map passed by `&mut` through `narrow`, `narrow_ge`, `narrow_or` and `narrow_to`, with the reading stopped at the first part left without a point by a short-circuiting `.all` | `bounds_refute`, `narrow`, `narrow_ge`, `narrow_or`, `narrow_to` | Mutation (gap 11), early exit (gap 12) | Each function returns the new map or nothing, and the reading is a fold that stops on nothing |
| `enum Unit<'a>`, a constraint or a disjunction borrowed from the formula | `Unit`, `bounds_refute` | None | Values are shared in Zed; the borrow goes and `Unit` is a union of the two |
| The implied bounds `implied: Near` kept across the rounds of `probe` and passed as `&mut Near` to `learn`, which adds the bounds it proves | `probe`, `learn` | Mutation (gap 11) | `learn` returns the bounds it adds, and the loop of `probe` carries `implied` in its state |

## Entries from JIT-reloc (`zed-native/src/lib.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `cfg!(target_arch = "x86_64")` choosing a code generator flag | `zed_native::run_in` | Missing (compile-time target query) | A constant of the build's target, read from the build description |
| `libc::mmap` of a `PROT_NONE` reservation, `mprotect` of pieces of it, `munmap` in `Drop` | test `placement::FarApart` | System calls, no destructors | Test harness only: a foreign call to map memory and a scope that unmaps it |
| `unsafe impl Send` for a struct holding a raw pointer to memory it alone owns | test `placement::FarApart` | Foreign library | Inside the `@ffi` binding, which owns the mapping as a handle |
| `Box<dyn JITMemoryProvider + Send>` passed in to choose where the JIT puts code | `zed_native::run_in` | Foreign library | A parameter of the `@ffi` binding to the code generator |

## Entries from BODY-display (`zedc-syntax/src/ast/body.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `OnceCell<Vec<usize>>` of each node's parent, filled on the first rejection through `&self` by one walk from the root | `Builder::parents`, `Builder::body_of` | Lazy cells (gap 3) | The parent passed down while building, or the map made in one pass before building and threaded through as a state receiver |

## Entries from T6-kinds (`zedc-types/src/ty.rs`, `parse/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `retain` over the tuple shapes whose closure also pushes, into a `rest: Vec<KType>` it borrows mutably, the part of a shape that the kind-wide part holds in part | `Ty::diff` | Mutation (gap 11) | A fold over the shapes whose state is the kept shapes and the parts for the set |
| A loop over both orders of the two sides that writes `out.set` and pushes to `met` in place | `Ty::meet` | Mutation (gap 11) | A fold over the shapes with the set and the kept shapes in its state, kept in place by provable last use (L6.13) |
| `Option<&'static str>` for a parse error's message, pointing at a constant | `parse::Error.message`, `parse::DOTS` | None | A `String` constant; values are shared |

## Entries from WIDE-copies (`zed-kernel/src/num.rs`, `value.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A closure `signed(x, y)` choosing `x - y` or `x + y` by a captured `bool`, so one body serves `add` and `sub` | `Rat::sum` | None | A local function of the flag, or the operator passed as a value |
| `BigUint::iter_u64_digits().rev()` folded into a `u128` remainder | `num::rem` | Missing (no word view of an `int`) | A runtime primitive giving an `int`'s words, or `mod` by a word as a primitive |
| `BigUint::from_slice` of a block of `u64` words split into reversed `u32` pairs | `num::rem` | Missing (no word view of an `int`) | The same primitive, building an `int` from a slice of its words |
| `Result<bool, TooLarge>` with `?` through `divides_by`, `magnitude_order` and `exact_div` | `Rat::divides_by`, `Rat::div_euclid`, `Rat::rem_euclid` | Early exit (gap 12) | A failure value returned and matched at each call |

## Entries from PRINT-tyvars (`zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Scope` of `HashMap<Arc<str>, Vec<Option<Arc<str>>>>` (the printed name of each variable, innermost last), a `HashSet` of names in use and a counter, held as `&mut Scope` across the recursion of the printer, pushed by `Scope::open` at each signature and popped by `Scope::close` after it | `Ty::write`, `Sig::write`, `Scope::open`, `Scope::close` | Mutation (gap 11): a map held across a recursion and undone after it | A persistent map from variable to printed name and a set of names in use, passed down into each signature, so nothing is undone; the counter is returned with the text, so a fresh name is still tried once in the whole type |

## Entries from ADDR-cell (`zedc-lattice/src/cell.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A premise-set node's id, drawn by `zed_kernel::family::fresh_id` (made `pub` for it) and shared by copies, as the key of a `HashSet` of the parts a walk has read and as the "one shared set" test in `extend` and `==` | `Premises::{one, extend, set, eq}`, `Node::id` | Identity (gap 1) | A family keyed by value, using L6.13a's hash and equality |

## Entries from ADDR-memory (`zedc-zir/src/zir/memory.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec<Option<Region>>` indexed by occurrence id, an entry filled the first time its occurrence runs (`get_or_insert_with`), and a `HashMap<&str, (usize, &RegionPlan)>` from a region's path to the occurrence id of its first node and its plan, built by one walk of the plan | `zir::memory::Machine::alone`, `Machine::places`, `memory::run` | Mutation (gap 11), lazy cells (gap 3) | A map from occurrence id to region in the machine's state receiver, updated in place by provable last use (L6.13); the path map is a fold over the plan |

## Entries from ADDR-preimage (`zed-kernel/src/term.rs`, `zedc-preimage/src/preimage.rs`, `preimage_ref.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Shared`, a newtype over `Arc<Held>` where `Held` is an `Id` from `fresh_id` with the `Term`; a copy keeps the id and `Shared::make_mut` takes a new one when it changes the term; `Deref`, `AsRef`, `From<Term>`, and a `PartialEq` that is true at once on equal ids | every `Arc<Term>` child of `Term` (`Lam`, `App`, `Let`, `If`, `Match`, `Push`), `term::{lam, app, let_, if_}`, `provenance::child_mut` | Identity (gap 1) | A content digest field in each term node (gap 1), which serves as the id and makes equal terms built apart share it |
| A `HashMap<u64, Tid>` keyed by `Shared::id` while one term is numbered | `Terms::add`, `Terms::id` | Identity (gap 1), mutation | A state receiver over a map keyed by the term's digest |

## Entries from PERF-portable (`tests/src/scaling.rs`, `zed-alloc-count/src/os.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `#[cfg(target_os = ...)]` on items, statements and dependencies, one body per system | `scaling::Meter::new`, `no_counter`, `cpu_time`, `zed_alloc_count::os`, `allocated`, `count` | Attributes | A runtime binding per target, chosen by the build |
| `libc::proc_pid_rusage` into a zeroed `MaybeUninit<rusage_info_v4>`; `windows_sys` `QueryProcessCycleTime` and `GetThreadTimes` | `zed_alloc_count::os` | Foreign library | Test harness only: read through an `@ffi` binding |
| `Box<dyn FnMut() -> u64>` counters in a const-generic array, the first that moves taken | `scaling::Meter`, `first_that_moves` | Mutation | A list of counter functions, each read as a value |
| One process-wide `static AtomicU64` of bytes off Linux | `zed_alloc_count::ALL` | Shared tables across pure calls (gap 2) | A count kept by the runtime and read as a value |

## Entries from LIT-adopt (`zedc-check/src/check/mod.rs`, `walk.rs`, `elab/walk.rs`, `store/preimage.rs`, `store/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec` stack of open tuples, each with borrowed slices of what it holds and a `Vec` of the results pushed in place until the tuple closes (`OpenTuple` in `adopted`: the parts, the components and the expected components; in `parts` and `tuple_seen`, a tuple of the items and the parts or types so far) | `check::adopted`, `parts`, `Ck::tuple_seen` | Mutation (gap 11) | A fold over the parts with the stack as a persistent list; each closed tuple is a value built once |
| A stack of pairs of borrowed sides of `==` (`Side<'a>`, a tuple of references, with a `Vec<&Ty>` of the side's types, one per tuple shape) and an iterator borrowing a tuple's components across its shapes (`fn sides(...) -> Option<impl Iterator<Item = Side<'a>>>`) | `Ck::equal`, `sides` | None | Shared values in place of borrows; the components as a list mapped once |
| `HashMap<Span, (Option<Ty>, Src)>` written in place at each expression, with `None` for a tuple whose type is rebuilt from its components on demand | `Ck::seen`, `walk::resume` (`Frame::Seen`) | Mutation (gap 11) | A persistent map threaded through the walk as a state receiver; a type held by a shared reference needs no `None` case, since a share costs O(1) (gap 1) |
| `let … else` and `if let … && let …` chains, one on a slice pattern (`if let [t] = ts && let Some(k) = …`), choosing the follow shape of a `match`, a comparison of an int-typed operand, and the class a literal operand of `==` follows | `store::preimage::follow_own`, `store::product::plain_comparison`, `Ck::follow` | None | An `is` test on the term's shape, then a `match` |
| A `Vec` stack rebuilding a condition through `&&`, `\|\|`, `!` and `if`, with a nested `fn kids` in place of a closure, whose borrow the compiler could not tie to the term | `store::product::plain_test` | Mutation (gap 11) | A fold over the condition's tree with the rebuilt children as values |

## Entries from FOOTPRINT-peak (`zedc-base/src/cost.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Two per-device accumulators updated in place through `&mut out[d]` and `&mut kept[d]` in one loop over the regions | `per_device` | Mutation (gap 11) | `zed/prelude/cost.zed` `peak`: a fold over the device's regions with a pair (peak, retained so far) as its value |
| `saturating_add` on the retained bytes and the peak | `per_device` | Machine integers (see the mechanical rewrites) | Vanishes on an unbounded `int`; the peak then does not stop at the maximum |

## Entries from NARROW-if (`zedc-check/src/check/arms.rs`, `store/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Rc<Vec<..>>` of a test's fresh names, shared by the node where it holds and the one where it fails | `Arms::test`, `Node::Assume` | None | A list value; values are shared |
| `scopes: Vec<Option<Scope>>` filled on first read and kept, written through `&mut self` | `Arms::compute`, `Arms::scope_or_root` | Mutation (gap 11) | A map from node to scope in the walk's state, updated in place by provable last use (L6.13) |
| `if let Node::Assume { fresh, .. } = &nodes[n] && !p.bottom` (a let chain) | `Arms::compute` | None | `if nodes[n] is #assume(..) && !p.bottom`, narrowing by `is` |
| A `bottom` flag that `Scope::get` reads before the names, so a scope no state reaches keeps its names unchanged | `Scope::assume_case`, `Scope::get` | None | A field of the scope struct read first by `get` |
| `chains: Vec<Option<Chains>>`, each node's two persistent maps from a name to the nearest node that changed it and that reads it, filled on first read through `&mut self` | `Arms::settle_chains`, `Arms::deciding` | Mutation (gap 11) | A persistent map value per node in the walk's state, updated in place by provable last use (L6.13); maps are shared values |
| `narrows: Vec<Option<Vec<Arc<str>>>>`, the names each test changed, from `OrdMap::diff` of the scope it was narrowed from and its own | `Arms::compute` (through `Ck::compute`) | Mutation (gap 11) | A list per node in the walk's state; the diff as `Scope::join` uses it |
| `enum Kind { Narrowed, Read }` choosing a field of `Chains` in a `match` | `Arms::deciding` | None | Removed by repair 7: `deciding` reads the changed-name chain, `Carried` the read chain |
| `OrdMap::diff` of a join's two maps, to find the names the two sides map differently | `Arms::settle_chains` | None | A diff over two persistent maps, as `Scope::join` uses |
| `HashSet<(usize, Arc<str>, bool)>` visited set (a local `type At`) and an explicit stack in the chain walk | `Arms::deciding` | Mutation (gap 11) | A set value in the loop state, with a `gen` loop in place of the stack |
| `let ... else { return false }` on two `Option`s in a tuple | `Arms::explains` | None | A `match` on the pair, `(some(a), some(t)) -> …, _ -> false` |
| `Carried`, a breadth-first search kept in `HashMap<usize, Carried>` and resumed by later lookups: a `VecDeque` FIFO of names, a `HashMap` from each name reached to the test that reached it, and parent pointers followed back by `while let Some(Some(..))` | `Arms::deciding`, `Carried::path`, `Carried::expand` | Mutation (gap 11) | A search state value per carrying test in the walk's state, updated in place by provable last use (L6.13); the queue a list consumed from the front |
| A closure `push_names` that borrows `self.nodes` and the chain lookup (disjoint field captures) while `self.carried` is borrowed mutably, and takes the stack as `&mut Vec` | `Arms::deciding` (repair 8) | Mutation (gap 11) | A local function returning the entries to push, appended to the stack in the loop state |
| `Iterator::reduce` folding a path's tests into one `&&` term, each failing outcome wrapped in `!`; `BTreeMap::entry(..).or_insert_with` for the first product of each name | `Arms::explains` (repair 8) | None | A `fold` over the list of sides; a map insert that keeps an existing key |

## Entries from BIT-axioms (`zedc-base/src/axioms.rs`, `tests/steps/m0_11_prelude_axioms_and_limits/`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Two new `Law` variants, one holding a `Const` and one a `&'static str`, in a `const` table of `Axiom` | `axioms::Law::SelfInverse`, `PowerOfTwo`, `AXIOMS` | None | Atoms with a payload, `#selfInverse(0)` and `#powerOfTwo("*")`, as `zed/prelude/axioms.zed` already writes them |
| An operator's table on 0..<2^w built once into a `Vec<usize>`, then read by index for each tuple | `check_word` (test) | None | A list built by `map` over a range and read by index; the reads are O(1) on a persistent vector |
| `<[Term; 2]>::try_from(Vec<Term>)` to take the two arguments of a binary operator by value | `call` (test) | None | A list pattern `[a, b]` in a `match` |
| `num_bigint::BigInt` for 2^63, 2^64 and 2^128 corner values | `word_corners`, `shift_values` (test) | None | `int` is unbounded: the literals `2^64` and so on |

## Entries from TERM-id (`zedc-stage/src/stage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap<u64, usize>` keyed by `Shared::id` while one term is read, a part held inline having no key | `stage::Reader::ids`, `Reader::read`, `Part::held` | Identity (gap 1), mutation | A state receiver over a map keyed by the term's digest |
| A closure over a mutable iterator (`move \|\| parts.next()`) passed as `&mut impl FnMut() -> Needs`, so a callee takes the next part's answer only when it is a lambda | `stage::Reader::needs_of`, `Reader::callee` | Mutation | The list of the parts' answers passed as a value, each case taking its head |

## Entries from STAGE-dag (`zedc-stage/src/stage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A memo `HashMap<u64, Summary>` keyed by `Shared::id`, and one `HashMap<Set, Set>` of each set's names less the words, filled through `&mut self` while a term is read and cleared before the next | `Frees::summary`, `Frees::nonwords`, `Mixer::mix_top` | Identity (gap 1), Shared memo (gap 2) | A state receiver over maps keyed by the term's digest |
| An arena of Patricia-map nodes (`Vec<MapNode>`) with a hash table from node to number (hash-consing) and memos `HashMap<(Map, Set), Map>` of restrictions and `HashMap<Map, bool>` of whether every binding is build-stage | `Maps::make`, `Maps::restrict`, `Maps::all_known` | Shared memo (gap 2), Mutation (gap 11) | As `Sets` (TERM-id and earlier entries): the arena and memos on a threaded state |
| A memo `HashMap<(u64, Map), (Shared, Summary)>` from a node's id and the bindings of its names to the node it mixed to, read before a part is mixed and filled by a `Store` job after | `Mixer::enter`, `Mixer::mix` | Identity (gap 1), Shared memo (gap 2) | A state receiver over a map keyed by the digest and the bindings' map |
| Interning tables `BTreeMap<Value, Binding>` and `HashMap<(u64, Map), Binding>` filled through `&mut self`, giving a known binding the number of an earlier one equal to it (by value, or by node id and the bindings it reads) | `Mixer::number` | Identity (gap 1), Shared memo (gap 2) | A family keyed by the value (values are ordered keys in Zed), and one keyed by the digest and the bindings' map, threaded as state |
| An explicit work stack `Vec<Mix<'t>>` of jobs that borrow parts of the term (`&'t Term`, `&'t Shared`) and an answer stack `Vec<Out>`, in place of recursion, so a deep term does not grow the thread's stack | `Mixer::mix`, `Mixer::enter`, `Frees::summary` | Lifetimes, Mutation (gap 11) | Recursion, once Zed's stack can grow on the heap; else the same jobs as a list on the threaded state, each holding the part itself |
| `Cow<'t, [Arc<str>]>` for the names a part binds, borrowed from the term or built for a pattern | `subs`, `Mixer::sites` | Lifetimes, ownership | A list of names; values are immutable, so no borrow is needed |
| `Arc::unwrap_or_clone` to move a term out of a node that nothing else holds | `inline` | Identity (gap 1), ownership | No gap: a value is read, never moved; the runtime may reuse a node it holds alone |
| The scope's map of names to bindings kept in `Scope::top` and put back from the entry's `prev` on `pop` | `Mixer::push`, `Scope::pop`, `Scope::truncate` | Mutation (gap 11) | The map passed down as a value; leaving a binder returns to the caller's map |
| A stub's table of answers, `Mutex<BTreeMap<Value, Option<Value>>>` in an `Arc<Stub>` shared by every run and every stub that reads the function, filled through `&self` while the evaluator runs (repair 3) | `Stub::table`, `Stub::answer`, `fill`, `Port::get` | Shared memo (gap 2), Mutation (gap 11) | A family from argument tuple to answer, threaded as state through the runs: each run returns the answers it found, and the next run starts from the table so grown |
| A log of the calls a run made, and the first answer it lacked, written through `&self` from inside `Lookup::get` (`Mutex<Vec<(Probe, Answer)>>`, `Mutex<Option<(Arc<Stub>, Value)>>`), so a pure evaluation reports what it read through the `Lookup` trait object it was given; and `Lookup::refuses`, a default trait method the evaluator asks before it compares a key (repair 3) | `Run::log`, `Run::need`, `Port::get`, `Port::refuses`, `Mixer::eval`, `zed_kernel::eval::Lookup::refuses` | Mutation (gap 11), traits (`interface` is L10; `dyn Lookup` becomes a port, catalog above) | The run returns the list of the calls it made, or the answer it lacked, beside its value; the port is a record of the table and a function from key to whether the key is refused |
| A trie of the questions a part asked, `Vec<Node>` with `Node::Ask(Probe, BTreeMap<Answer, usize>)` edges by arena index and `Node::Leaf` holding the mixed node, reached from a `HashMap<(u64, Map), usize>` by the part's id and bindings, extended in place when a place answers differently (repair 3) | `Mixer::trie`, `Mixer::memo`, `Mixer::recall`, `Mixer::remember` | Identity (gap 1), Shared memo (gap 2), Mutation (gap 11) | A family from a part's digest and bindings' map to a tree of questions, each node a family from answer to subtree, rebuilt along the path it extends and threaded as state |

## Entries from NAME-ties (`zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A substitution counter `now` bumped in place and read as `std::cmp::Reverse(now)` in a sort key | `Equalities::subst`, `Equalities::put` | Mutation (gap 11) | The counter threaded through the state receiver; `Reverse` as a key that sorts descending |
| `Option::take` and `get_or_insert` on the kept first tie | `Omega::loosen`, `Omega::run` | Mutation (gap 11) | The kept tie as a field of the threaded state, read and cleared by one `patch` |
| `return` from inside nested loops on the first point of a splinter, and after the first refused batch, in a function that calls itself on a splinter split again | `splinters` | Early exit (gap 12) | A fold over the batches that stops on a point or a refusal |
| `Vec<(usize, Vec<(usize, usize)>)>` of batches with their live counts, each batch built by `push` in a loop | `Omega::gray`, `Omega::run` | Mutation (gap 11) | An array of batches built by append on the threaded state, each batch a map over the eliminated variables |
| A `String` built by `push_str` while a `&str` cursor moves past each `#` | `Renamed::back_text` | Mutation (gap 11) | A fold over the pieces of the text split at `#`, each piece mapped and joined |
| A depth-first walk with an explicit `Vec` stack and `return` on the first disjunction or negation | `Formula::chooses` | Early exit (gap 12) | A recursive `any` over the children |
| Union and find over a `Vec<usize>` of parents with path halving written in place, by a closure that captures the parents and a `HashMap` from atom to index filled by `entry`; a `Vec<bool>` of roots seen, set by `std::mem::replace` | `alone` | Mutation (gap 11) | The parent array and the roots seen on the threaded state, updated by `patch` at each step of the find |
| `return None` from inside the loop over the roots on a root seen twice, and `?` on the search for a disjunct with no disjunction of its own | `alone` | Early exit (gap 12) | A fold over the roots that stops on the first repeat; an `Option` chain over the disjunctions |
| A nest of disjunctions read on an explicit `Vec` stack of slices, the least key kept in an `Option` with a tie flag, and `?` on an empty disjunction | `by_color` | Mutation (gap 11), Early exit (gap 12) | A recursive fold over the nest, with the least key and the tie as its accumulator |
| `filter_map` to `(disjunct, shown)` pairs, `unzip` into two vectors, and `zip` with `find` on a pattern over a pair of references | `settle_as_sets`, `alone` | Library: DESIGN.md names no `filter_map` or `unzip` | An array of records `{d, shown}` filtered once; the flag read by field |
| `format!("#{k:0width$}")`, a width given by a variable | `Renamed::of` | Formatting (no width argument in Zed's string interpolation) | A `pad_left` of the decimal text to the width |
| `let ... else` returns on a settling with no point and on no choice by color | `settle_tied` | Early exit (gap 12) | A match on each result |
| A vector of each disjunct's settled parts, filled before the asking loop and emptied by `Option::take` as each is read | `project_parts` (`pre`) | Mutation (gap 11) | The settled parts zipped with the disjuncts, read once by a map; no take needed |

## Entries from ITEM-order (`zedc-syntax/src/ast/mod.rs`, `run.rs`, `elab.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `for` loop over the items that pushes each built statement to one `Vec` and each error to another, inside the `with_holes` closure | `ast::unit_all_errors` | Mutation (gap 11) | A fold over the items into a pair of lists, statements and errors |
| Tarjan's search over a `Vec` of (node, next dependency) frames, with `index`, `low` and `on_stack` updated in place by node | `elab::topo::cycles` | Mutation (gap 11) | A fold over the nodes with persistent maps for `index` and `low` and a list for the stack, or the same loop once Zed has mutable arrays |

## Entries from L1.19a (`zedc/src/run.rs`, `main.rs`, `check/mod.rs`, `testing.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::env::args_os` and `OsStr::to_str`, the words as bytes decoded to UTF-8 one by one | `main`, `run::words` | Bytes (gap 5) | None needed: the host decodes the command line and the program reads the `CommandLine` port, a family of `String`s; the usage error is the host's |
| `Iterator::position` for the first `--`, then slices `&args[..i]` and `&args[i + 1..]` | `run::words` | Library: DESIGN.md names no `position` on a family | A fold that finds the first key whose value is `"--"`, then two key ranges of the family |
| `.collect::<Result<Vec<_>, String>>()` stopping at the first word that is not UTF-8 | `run::words` | Early exit (gap 12) | A fold that keeps the first failure |
| `split('\n')`, `Vec::pop` of a last empty piece, `strip_suffix('\r')` | `testing::given_args` | Mutation (gap 11) | The L3 word `lines`, which splits a `String` as a `Lines` input is |
| A `match` on `&words.command[..]` slice patterns with `*cmd == "run"` | `run::command_inner` | None: Zed's `match` on tuples | The same match on the list of words |

## Entries from L1.19b (`zedc/src/run.rs`, `zed-native/src/exe.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Program::address: OnceLock<ContentAddress>`, the address taken at the first wave and kept in the program | `Program::address` | Lazy cells (gap 3) | The address computed once when the program is loaded and held as a field, or a lazy cell once Zed has one |
| A `blake3::Hasher` updated in place with a tag, an address, a length and the ports' text | `Ports::address` | Identity (gap 1) and Mutation (gap 11) | The hash built-in of gap 1 over the concatenated bytes |
| `let mut first = true`, cleared at the end of each pass of the loop over the record's entries, so a `program` entry is accepted only first | `Record::from_bytes` | Mutation (gap 11) | A fold over the entries with the entry's index, or a match on the head of the list of entries |
| `split_first_chunk::<32>()` reading the address out of the executable's data | `exe::Program::decode` | Bytes (gap 5) | A slice of the first 32 bytes of the data, once Zed has bytes |

## Entries from L1.19c (`zedc/src/run.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::env::vars_os` and `OsStr::to_str`, the variables as bytes decoded to UTF-8 at each read | `run::command`, `run::executable`, `Environment::get` | Bytes (gap 5) | None needed: the host takes the variables and the program reads the port, a lookup of `Utf8String`s |
| `BTreeMap<OsString, OsString>` built from an iterator | `Environment::new` | None: a Zed family keyed by name | The family of the variables, built by the host |
| `OnceLock<String>` set by the first read of a value that is not UTF-8, read when the run stops | `Environment::get`, `run::stopped` | Lazy cells (gap 3) and Mutation (gap 11) | The read gives a usage-error atom that the run's driver tests for, in place of a flag beside the lookup |
| `Arc<dyn Lookup>` chosen per port by a closure (`run::local`) | `run::local` | Traits (dynamic dispatch) | A match on the port's kind giving one of two lookups of one type |

## Entries from ISSUE1-else-atoms (`zedc-resolve/src/resolve.rs`, `zedc-check/src/check/mod.rs`, `check/walk.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Resolution::handles` and `Resolution::aliases`, `Vec`s the resolver pushes to as it walks each `else` and `is` and declares each `s = name` | `resolve::Resolver::expr`, `resolve::Resolver::declare` | Mutation | The walk returns its handled sites with its other results, joined at each node |
| A `HashMap<usize, KType>` of each parameter's handled atoms, each entry joined in place (`*e = &*e \| &a`) | `check::handled` | Mutation | A fold over the sites into a persistent map, joining the entry's value |
| A union-find over binders as two `Vec<usize>` (`root`, `size`) updated in place, with path halving | `check::handled` | Mutation | A persistent union-find, or a fold over the aliases into a map from binder to class kept by a library type with O(α) find |
| `Origin::ty: Option<(Ty, 'static str)>`, the type of a note formatted with its text only when a message renders it | `check::Origin`, `Ck::origin_ty`, the note renderer | None | A note holds its type as a value and the renderer formats it; laziness is the same |
| `Ck::outside: HashMap<Span, KType>` and `Ck::widened: HashSet<usize>`, written as each expression is checked and as each parameter is bound (`param_ty` now takes `&mut self`) | `Ck::outside_of`, `Ck::param_ty`, `Ck::handled_sig` | Mutation (gap 11) | Maps threaded through the checker's state, as `unnamed` would be |
| Closures that borrow `self` immutably (`o`, `union`, `made`, `may`, `bare`) inside one method | `Ck::outside_of`, `Ck::first_taking` | None | Local functions taking the maps as arguments |
| A slice pattern `let [first, rest @ ..] = &sig.arrows[..] else { .. }` and `if let .. && ..` chains | `Ck::first_taking`, the `TypeKind::And` reader | None | `match` on a list with a head and tail pattern |
| An `if let` guard in a match arm, `(ExprKind::Call { callee, .. }, _) if let Some((sig, receiver)) = self.called(callee)` | `Ck::outside_of` | None | A nested `match` on `called` inside the `Call` arm, falling to the arm for any other expression |
| `Ck::tried: HashMap<Span, Option<KType>>`, joined in place through the `Entry` API (`Entry::Occupied(mut o)`, `v.take().zip(k)`) and taken by `remove` when the call's expression is seen | `Ck::tried_at`, `Ck::try_outside`, `Ck::outside_of` | Mutation (gap 11) | A map threaded through the checker's state; the join is a fold of `Option` values |
| A trial: `mark` the undo log, apply with `trying` set, read the error count, `undo` to the mark, and put back `applied`, taken out by `Option::take` | `Ck::try_outside` | Mutation | The checker's state passed as a persistent value; the trial applies to a copy that is dropped, with no undo log |
| `Ck::refused` and `Ck::need_passed`, `Vec`s of the atoms a need replayed at a call refuses, pushed by `apply`, drained by `meet` and `pass_needs` and truncated after each call | `Ck::apply`, `Ck::meet`, `Ck::pass_needs`, `Ck::replay`, `Ck::check_on` | Mutation | The replay returns its refused atoms with its result, and the call that gave the lambda folds them into its own result |
| `Ck::need_args: Option<Vec<bool>>`, set by `meet` and taken by `apply` with `Option::take` | `Ck::meet`, `Ck::apply` | Mutation | An argument of `apply` |
| `Info::passes: HashMap<Span, Vec<(Span, KType)>>`, an entry merged in place (`*old = &*old \| k`) and logged for undo | `Ck::pass_at` | Mutation | A persistent map updated by value; the undo log is not needed once the state is a value |

## Entries from CHK-cost (`zedc-types/src/ty.rs`, `mod.rs`, `zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `thread_local!` constant kernel types (the scalars and universes), built once per thread and cloned out | `zed_kernel::types::{SCALARS, UNIVERSES}`, `check::ty` `ATOMS` | Missing (thread-local state) | Top-level constants, built once at load and shared, since values are immutable |
| A field `facts: Facts` wrapping a `OnceLock<VarFacts>` filled on first use, whose `Clone` resets it and whose `PartialEq` and `Hash` ignore it | `check::ty::{Sig, Facts, VarFacts}` | Mutation (interior mutability) | A lazy field of the record, computed on first read; Zed has no way to fill a field after construction, so the port computes the facts when the signature is built, which costs the same walk once |
| `Arc`-shared rows that carry their facts beside the fields | `check::ty::Row` | None | Values are shared in Zed; the facts are a field computed at construction |
| `imbl::OrdSet` persistent sets of class variables and of other names, merged small into large, a variable inserted only when absent so that shared nodes are not copied | `check::ty::VarFacts::{held, merge, add}` | Missing (persistent sets in the standard library) | A persistent ordered set from the standard library catalog (L2.11), with the same merge of the smaller into the larger |
| An explicit stack of borrowed references (`enum Item<'a> { Ty(&'a Ty), Sig(&'a Sig) }`) for a preorder walk that stops early | `check::ty::Sig::first_seen` | None | A recursive walk over the shared values; Zed has no borrowed references to distinguish, and an early stop is a return from the fold |
| The name of a type variable kept on its union-find class (`Class::name`, set in place when the function ends) and written into the signatures once, when the checker finishes | `check::Ck::{generalize, is_class, names, shown, finished}` | Mutation (union-find classes changed in place) | The union-find becomes a persistent map from class to its record, threaded through the checker; the names are a second map read at the end |
| A `Mode` argument (`Replace`, `Rename`, `Outside`) that switches `Ty::replace_in` between substitution, which leaves the own variables of an inner signature alone, renaming, which renames them too, and substitution outside the functions a type holds | `check::ty::{Ty, Sig, Need}::replace_in` | None | Three functions over one fold that takes the treatment of an inner signature as a function argument |
| Two more `OnceLock`s in `Facts`: the settled signature (`Sig::settle`) and the hash (`Sig::digest`), each made on first use from those of the functions it holds; `Hash` for `Sig` writes the digest | `check::ty::{Facts, Sig::settle, Sig::digest}` | Mutation (interior mutability) | Lazy fields of the record; the port computes the digest at construction, as `Row` does, and settles at the end in one fold that shares results by value |
| A method on `self: &Arc<Sig>` that returns the shared `Arc` itself when nothing changes | `check::ty::Sig::settle` | None | Values are shared in Zed; returning the argument unchanged is the default |
| A resolver passed as `&dyn Fn(&str) -> Option<Ty>` (`Solve`) into the comparisons and held in `Cx` | `check::ty::{Solve, Cx, sub_with, subtype_with, fits_sig_with}`, `check::Ck::stale` | None | A function value passed as an argument |

## Entries from L1.37a (`zed-kernel/src/address.rs`, `types/bdd.rs`, `zedc-base/src/address.rs`, `zir/canon.rs`, `zir/lower.rs`, `query.rs`, `elab.rs`, `cost.rs`, `store/product.rs`, `tests/src/oracle.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A cargo feature, `short-addresses`, read as `cfg!(feature = …)` in a `const` that masks every digest and address | `zed_kernel::address::SHORT`, `short64`, `short256`, `ContentAddress::hashed` | Missing (compile-time build option) | A unit parameter of the kernel, a `Bool` given at the import, read by the two masking functions |
| A `HashMap<ContentAddress, BTreeMap<Shape, usize>>` from key to the nodes of that key ordered by shape, entered with `entry` so one search finds or inserts | `Lower::add`, `Frame::seen` | Mutation (gap 11) | A map from key to an ordered map from shape to node, updated with `patch` in a state receiver |
| A hand-written `impl Ord for Shape` comparing the shells' bytes and then the regions from an explicit `Vec` stack of region pairs, stopping at the first difference, with `Arc::ptr_eq` to skip a region the two share | `canon::Shape` | Mutation (gap 11), Early exit (gap 12), Identity (gap 1) | An order given as a fold over a work list; without identity each shared region is compared, which costs its size again |
| A `HashMap<u64, bool>` filled in postorder for whether each node's chain of `lo` edges reaches `true`, read by a closure that borrows it | `Bdd::reaching` | Mutation (gap 11), Identity (gap 1: node ids) | A fold over the postorder into a persistent map keyed by node digest, confirmed by contents |
| A key as `Box<[u8]>` of the encoded inputs, compared in full on a hash-map hit | `query::Key` | Bytes (gap 5) | A key as a tuple of the inputs, compared by `==` |
| A `OnceCell<u64>` per definition for its number, given once through `&self` | `Cones::number`, `Db::cone` | Lazy cells (gap 3) | A table of numbers built once per unit, before the cones are read |
| `min_by_key` on a tuple of the cost and borrowed slices of the plan | `cost::pick`, `cost::order` | none | `minBy` on the same tuple; slices are lists |
| Each nest's sides and each level sorted in place by `sort_by_key` and `sort_by`, and ids written into a `Vec` by position | `store::product::Tree::of` | Mutation (gap 11) | `sort` of each level into a new list, ids by `zip` with the positions |

## Entries from STACK-self-limit (`tests/steps/m0_09_kernel_evaluator/binary.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `rustix::process::setrlimit(Resource::Stack, …)` on the test process, so the child it runs inherits an 8 MiB stack | `limit_stack` in the `zedc_binary` test | Missing (process limits) | A test-harness facility, not the language |

## Entries from GRAMMAR-read-cost (`zedc-syntax/src/parse/grammar.rs`, `parse/engine.rs`, `zed-tools/src/check.rs`, `fuzz.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Box<[Expr; 2]>`, a boxed array of two expressions read as the sequence `sep e`, and the pattern `let [sep, x] = &^items` | `Expr::Sep`, `Reader::postfix`, `check::inner` | None | A pair `(sep, e)`, with a list of its two items made where a loop needs one |
| A frame holding a slice `&'g [Expr]` borrowed from the grammar, and `std::slice::from_ref` to see one expression as a list of one | `engine::Frame::Loop`, `Frame::Sep`, `engine::iteration`, `fuzz::Gen::repeat` | None | Zed shares values, so the frame holds the list itself; a list of one |
| `Iterator::try_for_each` to stop at the first item whose derivation fails | `fuzz::Gen::repeat` | None | A fold that carries the first failure |

## Entries from ZIR-family-key (`zedc-zir/src/zir/text.rs`, `zir/binary.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A literal's entries rewritten in place to their keys (`*k = k.key()` through `&mut`), sorted in place by `sort_unstable_by`, and a repeat found by `windows(2).find` | `zir::text::family` | Mutation (gap 11), Early exit (gap 12) | `sort` of the entries mapped to their keys into a new list, then `zip` with its `drop(1)` and a search for the first equal pair |

## Entries from CHK-held-cascade (`zedc-types/src/ty.rs`, `mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `impl Drop for RowData` that moves the components out with `std::mem::take` and frees the rows and signatures no other type holds (`Arc::into_inner`) on a stack of its own, so freeing a type a million tuples deep does not recurse | `check::ty::RowData::drop` | Missing (user-defined destructors) | None in the program: the runtime frees shared values, and its release of a deep value must itself keep its own stack (an L1.34 memory concern) |
| A printer that pushes borrowed parts (`enum Print<'a> { Text, Ty, Sig, Vars, Bounds }`) onto an explicit `Vec` stack and pops them in order | `check::ty::{write_parts, between, Ty::parts, Sig::parts, Shape::parts}` | None | A recursive fold that returns the text; Zed has no borrowed references to distinguish, and the depth is the runtime's stack handling |
| A visited set of row addresses (`HashSet<*const RowData>` from `Arc::as_ptr`) so that a walk enters a shared row once | `check::ty::Ty::vars_in` | Identity (gap 1) | The row's digest as the key, confirmed by contents, or the row's own variable set (`RowData::vars`) read in place of the walk |
| A per-row `VarFacts` of persistent sets made when the row is built, read to keep whole a row that holds none of the variables replaced | `check::ty::{RowData::vars, Row::holds_any, Ty::var_facts}` | None | A field of the row record computed at construction, as `Row`'s other facts are |

## Entries from T2-types-rest (`zed-kernel/src/term.rs`, `term/walk.rs`, `types/rec.rs`, `types/rec/walk.rs`, `types/empty.rs`, `frames.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Hand-written `Clone`, `PartialEq` and `Debug` over explicit stacks, writing the text the derived `Debug` wrote, on one line under `{:#?}` too | `term/walk.rs` (`Term`, `Pattern`), `types/rec/walk.rs` (`rec::Expr`, `Node`, `Shape`) | Missing | Removed: structural copy, equality and printing are the runtime's, which must not recurse on depth (as for `presburger/deep.rs`) |
| Equality over a stack of pairs with a `HashSet<(u64, u64)>` of pairs of shared subterms already queued, so a DAG is compared once per distinct pair | `term/walk.rs` `Comparing` | Identity (gap 1: `Shared` ids) | Structural `==` of the runtime, which needs the same visited set on shared values |
| A thread-local placeholder `Arc` swapped into a shared field during `Drop`, so a subterm held several times by one node is released from the queue, not inside the drop of its last holder | `term.rs` `free_shared`, `HOLE`, `Freed::Shared` | Missing (the runtime frees values) | Removed |
| A private trait (`Tree`) whose method returns `impl DoubleEndedIterator` (a slice chained with an array of `Option`s), so one generic loop compares and one prints two tree types | `types/rec/walk.rs` `Tree`, `equal`, `show`, `Expr::kids`, `Shape::kids` | None | A function from a value to the list of its parts, passed to one walk |
| Post-order builds with an enum of steps borrowing the input (`Visit`, `Build`; `Eval`, `Component`, `Build`) on a `Vec` and a second `Vec` of results split off per node | `rec` `Node::of`, `eval`, `Show::rope`, `Expr::clone` | Mutation (gap 11) | A state receiver holding the two lists, as for `canon::binders::Levels::term` |
| `async fn` methods run by a hand-written executor (`frames::Stack`, `Deep`): each call that may recurse is a boxed future on the heap, polled from a loop, so the compiler writes the resume points of about thirty mutually recursive methods | `types/empty.rs` `Searching` (frames of their own: `empty`, `decide`, `rep`, `member_known`, `tuples`, `morphisms`) | Missing (no coroutines or `async`) | Removed: the port's runtime must not recurse on depth; without that, a state machine with one frame variant per resume point |
| The search's state in a `RefCell`, moved in with `mem::take` for a run and back after it, borrowed one statement at a time and never across an `await` | `types/empty.rs` `Search::run`, `Searching::s` | Mutation, interior mutability | A state receiver threaded through the calls |
| One `frames.rs` in the kernel, used by the emptiness search and by `zedc`'s preimage analysis (`zedc/src/store/frames.rs` removed at this merge) | `zed-kernel/src/frames.rs`, `zedc-preimage/src/preimage.rs` | None | One module in the port too |
| Pairs to compare kept on a `Vec` (`Simulation::todo`) and drained after the pair is registered, failures spread once every pair is made | `types/empty.rs` `Simulation::pair`, `holds`, `compare` | Mutation (gap 11) | A fold over a list of pairs in a state receiver |
| An explicit stack of index ranges for the halving split, with an enum (`Each`) holding a `&mut Option<usize>` the search writes its answer to | `types/empty.rs` `split_classes`, `Each` | Mutation | A fold returning the answer |

## Entries from REC-id-order (`zed-kernel/src/types.rs`, `types/rec.rs`, `types/bdd.rs`, `types/print.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An order over a key holding an `Arc` to a shared environment, decided at once by `Arc::ptr_eq` when both keys hold one environment or one group, else by contents | `rec::Key::order`, `Checked::order` | Identity (gap 1) | The content digest and an `==` shortcut of the runtime; without them, the comparison of contents alone, O(size of the definitions) per tie |
| An order that pushes the pairs of nested types it leaves undecided into a caller's `Vec` of borrowed pairs, so the caller's loop compares them without recursion | `rec::Key::order`, `bdd::types` | none (a list of pairs returned) | Return the pairs as a list |

## Entries from L1.36a (`zed-native/src/exe.rs`, `link.rs`, `hooks.rs`, `lib.rs`, `zedc/src/run.rs`, `main.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `#[unsafe(no_mangle)] pub extern "C" fn`, so a linked executable finds each hook and `zed_main` by its symbol | the 13 `rt_*` hooks, `exe::zed_main` | Foreign library | The runtime stays in Rust (What stays in Rust); the compiler in Zed names the same symbols in the code it emits |
| C's `main(argc, argv)` read through raw pointers (`CStr::from_ptr`, `slice::from_raw_parts`) in an `unsafe` block, and standard output flushed by hand because Rust's `main` does not return | `exe::zed_main` | Foreign library | Inside the runtime, which stays in Rust |
| A crate built as both `rlib` and `staticlib`, and a binary target whose source lives in another crate (`autobins = false`) | `crates/zed-native/Cargo.toml`, `crates/zedc/Cargo.toml` | none | Cargo only; the compiler in Zed is one package |
| `std::process::Command` running the system linker and reading its status and standard error | `link::build` | Command line (gap 6) | A process port, which no step plans; until then the Rust driver links |
| `OpenOptions::create_new` for the object file, removed after the link | `link::build` | Command line (gap 6): computed output paths | A `Files` write to a computed path (step L7.3f) |
| `std::env::var_os` for `CC` and `ZED_RUNTIME`, `current_exe` for the default library | `link::Toolchain::from_env` | Command line (gap 6) | An environment input port, which no step plans |
| A struct of options parsed once and shared by `zedc run` and an executable, its methods taking `&mut dyn Read`/`Write` | `run::Options`, `run::Ports::run`, `run::executable` | none | A record and functions over the `Lines` ports |
| A block allocated at a file's length (`repeat_n(0, n).collect::<Arc<[u8]>>()`), written through `Arc::get_mut` by `Read::read` into its unfilled tail, so the file is read with no copy (T11-ptr-tests) | `run::read_file`, `run::read_shared` | Mutation | The `Lines` port reads the file itself; a Zed program is given the bytes as a value and never fills a buffer |
| A length-prefixed byte layout (`u64::to_le_bytes`, `split_first_chunk`, `split_at_checked`) | `exe::data`, `exe::Program::decode` | Bytes (gap 5) | Bytes words of step L7.3f |

## Entries from CHK-need-uses (`zedc-check/src/check/mod.rs`, `check/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `match` arm guarded by `if let` on the class of a variable piece, `Piece::Var(_) if let Some(k) = self.class_of(&p)` | `Ck::component` | None | An `is` test on `class_of` inside the `Var` arm, falling to the unknown when it has none |
| The variables a type holds that are no class and that `binds` leaves unbound, inserted into the caller's `&mut BTreeMap` of binds for one replacement and removed after it, so the map is as it was | `check::bound` (and `Ck::meet`, which passes the caller's binds on) | Mutation (gap 11) | A persistent map: the binds with the added variables as a new map, the caller's map unchanged, at the same `log` cost per variable |
| Whether a signature holds a variable the binds bind, read from the smaller of the binds and the signature's variable sets | `check::ty::holds_bound` | None | The same test over the smaller collection, as `Row::holds_any` does |
| A `bool` field of the shared row, set at construction from the components' own and their rows' fields | `check::ty::Row` (`fixed`) | None | A field computed at construction, as the row's other facts |
| A `HashMap<(NeedKind, bool), Ty>` per class from a use's kind to its result, kept beside the list of uses, with the two swapped together and the smaller merged into the larger by `entry(..).or_insert` | `Ck::need`, `Ck::merge` (`Class::known`) | Mutation (gap 11) | A persistent map in the class record, merged smaller into larger with the first value kept |

## Entries from PRE-stack-explicit (`zedc/src/store/frames.rs`, `store/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `async fn` and `async move` blocks as frames: the compiler writes each analysis's resume points and saved locals as a state machine, and `.await` on a recursive call suspends the caller | every analysis of `Walk` (`close`, `mentions`, `reads_mod`, `constant`, `fwd`, `clip`, `summon`, `back`, `scan`, `pa`, `by_class`, `lin`, `formula` and their helpers) | Missing (no `async`, no state machines written by the compiler) | Each analysis's frames written as a sum type, one variant per resume point holding the locals live there, and a loop over an explicit stack of them, as `presburger.rs` does by hand |
| `Pin<Box<dyn Future<Output = ()>>>` as a frame, so that frames of different analyses share one `Vec` | `frames::Frame`, `Stack::run` | Missing (no trait objects, no pinning) | One sum type over the frames of all analyses that call each other, kept in one list |
| A poll loop with `Waker::noop` and `Context`, and a `Future` implemented by hand for `Deep` | `Stack::run`, `Deep::poll` | Missing | The loop of the explicit stack itself: pop a frame, step it, push what it calls |
| `Rc<Cell<Option<V>>>` where a frame leaves its answer for its caller | `frames::frame`, `Deep` | Mutation (gap 11), identity | The callee's answer passed to the caller's frame when the callee is popped |
| `Cell<ManuallyDrop<Option<Frame>>>`, the slot where a suspending call leaves its callee for the loop; `ManuallyDrop` gives `Stack` no destructor, so that it may be borrowed for the lifetime its own frames hold | `Stack::next` | Mutation, ownership | The step function returns the frame to push as its result |
| `RefCell<&mut Tx>` borrowed by `Walk::with` between two suspension points, and `&'m self` shared by every frame | `Walk::with`, `Walk::tr`, every analysis of `Walk` | Mutation (gap 11), shared tables (gap 2) | The tables threaded through the step function as a state record, as gap 2 proposes |

## Entries from CITE-check (`zed-tools/src/cite.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::process::Command` running `git ls-files -z` and reading its standard output and exit status | `cite::run` | Command line and exit status (gap 6): Zed has no port that runs another program | An input port of the tracked paths, or a port that runs a program and gives its output and exit status |
| `std::fs::read` of a path built at run time, with `ErrorKind::NotFound` told apart from other errors, and `String::from_utf8` to skip a file that is not text | `cite::run` | Computed paths and bytes (gaps 5 and 6) | The byte file port of step L7.3f and `fromUtf8` |

## Entries from ROW-made-cost (`zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `imbl::OrdSet::diff`, which steps over the nodes two sets share, run a step at a time in turn with the insertions of the smaller set into the larger, stopping when either ends | `check::ty::merge` | Missing | As for `OrdSet::diff` above: Zed's sets are values but have no structural difference; the port needs a `diff` word that the runtime answers in time proportional to the unshared part, and a lazy sequence to step it in turn with the insertions |

## Entries from TEST-rows-rule6 (`zedc-elab/src/elab/walk.rs`, `testing.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::mem::replace` of each argument that passes atoms with a variable, in place in the `Vec` of arguments, while its term moves into a `let` | `Elab::row_call` | Mutation (gap 11) | A map over the arguments zipped with their spans giving each argument or its variable, and a filter giving the `let`s |
| `let ... else { continue }` over the statements to keep the functions | `testing::checks` | None | A `match` in a fold over the statements, or a filter on the function form |

## Entries from NATIVE-lib-pick (`zed-native/src/link.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The `object` crate reading an executable's symbol table and an archive's symbol index through `ReadCache` (reads of the file on demand), and Rust's mangled symbol names, whose hash tells two builds of a crate apart | `link::runtime_of`, `link::build_symbol`, `link::holds` | Foreign library; Bytes (gap 5) | The linking driver stays in Rust until a process port exists (as for `std::process::Command` above); a Zed version reads the two tables as bytes once Bytes words exist (step L7.3f) |

## Entries from NATIVE-build-id (`zed-native/src/link.rs`, `zed-native/build.rs`)

`link::build_symbol` above is now `link::build_id`, which reads a section by its name in place of the symbol table; the row above holds for it.

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `#[used]` static placed in a named section (`#[unsafe(link_section)]`) holding `const { TypeId::of::<Build>() }`, the compiler's identity of a type, which it derives from the crate's hash | `link::BUILD`, `link::Build` | Foreign library (the object file's layout); no compile-time identity of a build | The compiler of a Zed runtime writes its build's identity into the object file itself, as a constant it knows; nothing in Zed source names a section |
| A build script writing a Rust literal into `OUT_DIR` for `include!`, from an environment variable Cargo sets (`CARGO_ENCODED_RUSTFLAGS`) | `build.rs`, `link::BUILD` | None at the language level: a property of the build tool | The Zed build tool passes the compiler's flags to the build's identity directly |
| `object::build::elf::Builder` removing the symbol table of a copy of `zedc`, as `strip` does | `build_binary::a_stripped_zedc_builds` (test) | Foreign library; Bytes (gap 5) | A test runs the platform's `strip`, from the full suite (tests/full), or rewrites the ELF file as bytes once Bytes words exist |

## Entries from PRIM-hidden-names (`zed-kernel/src/print.rs`, `term.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Cow<'static, str>`, a primitive's fixed text borrowed, or `#err(..)` built when the message has the atom's name | `Prim::written_with` | None | Zed shares strings, so it returns a plain `String` |
| `while let … && …` (a let chain) gathering an index chain `t[0][1]…` into one list | `print::doc` | None | a loop with `match` and `is` |
| An exhaustive `match` giving each `Prim` variant a fixed number | `Prim::code` | None | a `match` on the atom of each primitive |

## Entries from OMEGA-cycle-growth (`zedc-presburger/src/presburger.rs`)

- No new gap. `Omega::cycles` reads a row of one or two unit terms with a `match` on slice patterns with guards (`[t] if t.1.is_positive()`, `[s, t] if s.1 == -&t.1`), a row of the appendix (slice patterns) with the rewrite already listed: test the length, then index.

## Entries from LOWER-legalize (`zedc-zir/src/zir/legalize.rs`, `zed-native/src/lib.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Arc::unwrap_or_clone` to move a region out of its node when it is held once, copying it only when shared | `legalize::legalize` | Identity (gap 1: the reference count) | A region is a value; the pass returns the new region and the old one is no longer read, which step L6.13 keeps in place |
| `mem::take` of a region's and a node's fields, and a `vec::IntoIter` of nodes kept in each frame of a heap stack and advanced in place | `Frame::new`, `Frame::finish`, `Frame::inline`, `Frame::region` | Mutation (gap 11) | A fold over the nodes with the frame as its state; the stack a list of frames |
| A `const fn` set built by `1 << x as u8` over an enum's discriminants, read by a mask | `Expansions::of`, `Expansions::contains`, `memory::EXPANSIONS`, `zed_native::EXPANSIONS` | Bit operations (gap 4, built) | A set of atoms (`{#derived, #gt, #ge}`) and `in`, a constant at the top level |
| A `Vec<u64>` bit set of node numbers, grown and set in place as the walk swaps a node, then held in an `Arc` the native tables share | `Swapped::insert`, `Swapped::contains`, `legalize::legalize`, `Tables::new` | Mutation (gap 11); Identity (gap 1: the reference count) | The pass returns the set of swapped numbers as a value beside the region; the tables read it, shared as every value is |
| A counter `next` threaded through a heap-stack walk by `&mut` to number nodes in preorder | `legalize::legalize`, `Tables::visit`, `lower::Written` in `raise_from` | Mutation (gap 11) | The counter is part of the fold's state, each node's number the state on entering it |

## Entries from CONST-wide-addr (`zed-kernel/src/num.rs`, `zedc-zir/src/zir/binary.rs`, `canon/serial.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Cow<'_, BigUint>`, a side of a rational borrowed when it has no kept powers, built otherwise | `Rat::built_parts` | None | Zed shares numbers, so it returns the side as a plain value |
| `BigUint::iter_u64_digits`, the 64-bit limbs of a magnitude least significant first, and `BigUint::from_bytes_le` to read them back | `W::magnitude`, `R::magnitude` in `zir/binary.rs`, `Out::magnitude` in `canon/serial.rs` | Missing | A primitive giving an exact integer's limbs as a `U8String`, and its inverse |

## Entries from REPLACE-shared-rows (`zedc-types/src/ty.rs`, `zedc-check/src/check/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A memo keyed by the address of a shared row (`HashMap<*const RowData, Row>`), valid because the input holds every row for the whole walk | `check::ty::Replacer`, `Subst` and `Settle` (the `Rebuild` policies of `rebuild`), `once` | Gap 1 (identity) | The row's content digest as the key, which costs a hash of the outer level per row, or the identity the runtime gives (L6.13a) |
| A memo keyed by the address of a signature (`HashMap<*const Sig, Arc<Sig>>`) | `Replacer::known_held` | Gap 1 | As above, with the signature's digest (`Facts`) |
| A set of row addresses as the visited set of a walk (`HashSet<*const ()>`, `Row::addr`) | `Ck::data`, `Ty::vars_outside` (`Vars::outside`) | Gap 1 | As above |
| A stack of memo frames, pushed when the walk enters a signature that hides variables and popped when it leaves, with a counting map of the hidden variables | `Replacer::known_held`, `made_held`, `Replacer::hidden`, `Replacer::memos` | Expressible | A list of maps threaded as state, and a map from variable to count; no new form |
| Closures that change captured state, passed as `impl FnMut` to `Ty::map_payloads` and `Need::map_tys`, so a walk's memo, or the stack of results it draws from, is shared by its calls | `check::ty` | Workaround (gap 2) | Thread the memo as an argument and result through the map, or a state receiver |

## Entries from FLOAT-minmax (`zed-kernel/src/eval.rs`, `zedc-base/src/axioms.rs`, `zed-native/src/codegen.rs`)

- No new gap. `ieee_min_max` is `if`s on `f64` comparisons and `is_sign_negative`, which Zed writes with `min` and `max` on `f64` themselves; the manual `PartialEq` on `Const` compares `to_bits`, the float bits word of gap 4 (built). Cranelift `fmin`/`fmax` is the back end's own instruction.

## Entries from SLABS-count (`zedc-solvers/src/live3.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A cargo feature that adds a statement to a method, off in a release build | `Lin2::minus` under `counts` | No conditional compilation | A build mode of the unit, as for `printed-types`: the test build counts, the release build does not, both with one interface |
| A `thread_local!` `Cell<u64>` that a method increments and a test reads before and after a call | `live3::counts::MINUS`, `live3::counts::minus` | Mutation (gap 11), global state | `solve2` returns the count of its subtractions beside its result, and the test reads it there |

## Entries from INCR-script (`tests/steps/l01_30_queries/reuse.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Edits whose texts are `&'a str` slices of the script, so a script of n bytes is read without copying its texts | `Edit`, `Step`, `parse` | None | Zed shares values; a slice is a range of the script's string |
| `str::match_indices` to find a text and check it occurs once, and `split_inclusive('\n')` to read lines with their ends | `parse`, `apply` | Library: DESIGN.md uses `split`, and names no word that finds every place of a substring | A stdlib word (catalog of step L2.11) that lists the places of a substring, and `split("\n")` |
| `#[should_panic(expected = …)]`, a test that passes when its body stops with a given message | `a_replace_of_text_the_file_lacks_stops_the_script`, `a_replace_without_its_with_stops_the_script` | Missing (test harness) | A test-harness facility, not the language: a row whose expected outcome is the failure's message |

## Entries from LAYOUT-measure (`zed-alloc-count/src/lib.rs`, `tests/src/layout.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `thread_local!` `Cell` of the running measurement, read and written by the global allocator on each allocation and free | `TRACKED`, `track`, `Counting` | Mutation, global state; Missing (no allocator hook) | The runtime's allocator reports bytes to a measurement the test harness holds; Zed code does not replace the allocator |
| A drop guard that puts the outer measurement back when the closure returns or unwinds | `live`, `Restore` | Missing (no destructors, no unwinding) | A failure returns through `live`, which restores the state on both paths |
| Measuring a structure by the bytes its `drop` frees | `bytes_of` | Missing (no explicit drop) | The runtime's count of freed cells when the value's last reference goes |

## Entries from DART-SCALE (`zedc-types/src/ty.rs`, `check/mod.rs`)

- No new gap. `Ty::shapes` now returns a borrowed `Option<&[Shape]>` (`Option::as_deref`) where it returned a copy; Zed shares values, so at the port it returns the list itself, and the copy that made the pattern quadratic (COMPLEXITY.md F100) does not arise. The other changes are in test code (`partition_point`, a `Mutex` around a held `Db`).

## Entries from RUNG2-mod-symbol (`zedc-preimage/src/preimage.rs`, `presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `while let … && …` (a let chain) popping the pairs a truncation undoes from the end of a list | `preimage::Tr::truncate` | None | a loop with `match` and `is` |
| A `HashMap` keyed by a pair of linear forms, `(Lin, Lin)`, so `a div n` and `a mod n` share one quotient and remainder | `preimage::Tr::div_mod_by_term` | None | a family keyed by the pair, the linear forms compared by content |

## Entries from RUNG2-definedness (`zedc-preimage/src/preimage.rs`, `divisors.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Hash-consed canonical treaps of divisors: nodes in a `Vec` addressed by `u32` numbers, found by `(divisor, left, right)` in a `HashMap` before they are made, priorities a fixed hash of the divisor (`BuildHasherDefault<DefaultHasher>::hash_one`), unions memoized by the pair of numbers, and ordered searches from a bound by recursion | `divisors::Sets`, `preimage::Defined::{meet, with_divisor, arm, shown_nonzero}` | Identity (gap 1); Mutation (the node table and memos) | A map from the content of a node to the node, its digest the key; the table and memos threaded as state, or a runtime intern table |
| Structural numbering of formulas: a memo by `presburger::Id` and one by shape (`enum Shape { Con, Not, And, Or }` of child numbers), filled on an explicit stack | `preimage::FormulaNumbers`, used by `Walk::shared_call_key` | Identity (gap 1); Mutation | The formula's digest as the key, confirmed by contents |
| `RefCell` and `Cell` captured by a closure passed to `map_cons`, to collect a failure and a substitution while the formula is rebuilt | `preimage::Defined::instance` | Mutation | A fold that returns the rebuilt formula with the failure flag |
| `if matches!(p, IntDiv \| Mod) && let n = … && ….is_none()` (a let chain in an `if`) | `Walk::defined_at` | None | `if` on `p` then a `match` on the constant |
| A struct update, `Defined { rest, ..Defined::top() }` | `Defined::failed`, `Walk::defined_at` | None | a record built with the named field and the others from `top` |

## Entries from RAT-asks-rest (`zedc-syntax/src/lex`, `ast`, `check/mod.rs`, `mutate.rs`, `zir/binary.rs`, `zir/canon.rs`, `zir/lower.rs`, `canon/serial.rs`, `zed-kernel/src/text.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Arc<String>` for a literal's digits, shared by the token and the syntax tree, and `Rc<String>` for the checker's literal text, shared by its clones | `lex::Digits`, `check::Lit::text` | None | Zed shares values, so the field holds the text itself |
| `fmt::from_fn`, a closure that writes a message, measured by a counting `fmt::Write` and then written into memory asked first | `check::menu`, `check::no_one_carrier`, `check::quoting` | Missing (no formatter trait) | The length function per printed kind named for `words::written`, then one write into the block |
| Functions generic over `W: fmt::Write`, writing a list of forms to a counter, a reserved `String` or a plain one | `check::write_forms`, `check::or_forms` | Missing (no formatter trait) | One function over the text builder the port has |
| `Cow<'_, str>` from `Text::try_flat`, a one-piece string borrowed and a joined one copied into memory asked first | `Text::try_flat`, `words` casts | None | Zed shares values; the copy is a runtime primitive returning the block or a refusal |
| An `Option<TooLarge>` field holding the first refusal while an infallible writer or the lowering goes on, read once at the end | `zir::binary::W`, `canon::serial::Out`, `zir::lower::Lower` | Mutation | The writer returns the refusal through each call, as Zed has no mutable field |

## Entries from ATOM-nested-sq (`zedc-types/src/ty.rs`, `mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A payload shape as a newtype over `Arc<ShapeData>` with `Deref` to its fields, so it is copied in constant time and read as before, and made only by `Shape::new`, which computes its facts | `check::ty::Shape` | Identity (gap 1); `Deref` has no Zed form | A record with the facts as fields, built by one function; Zed shares values, so a copy is free, and fields are read by name |
| `impl Drop for ShapeData` that moves its components out and frees them with the rows' explicit stack (`drop_types`, `Arc::into_inner` on each shape no other type holds) | `check::ty::{ShapeData::drop, drop_types}` | Missing (user-defined destructors) | As for `RowData::drop`: the runtime frees shared values, on a stack of its own |
| A visited set of shape addresses (`HashSet<*const ShapeData>` from `Arc::as_ptr`, `Shape::as_ptr`) so a walk enters a shared shape once | `check::ty::Ty::{vars_in, vars_outside}`, `check::Ck::data`; and a memo of what a rebuilding walk made of each shape (`Made::shapes`, `Memo`) | Identity (gap 1) | As for rows: the shape's digest as the key, confirmed by contents, or its kept facts read in place of the walk |

## Entries from ATOM-payload-open (`zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An explicit stack of a borrowing enum (`Walk<'a>`: a type, a row or a shape) whose newly pushed items are reversed in place (`stack[from..].reverse()`) so they pop in the order a recursive walk visits them | `check::ty::Ty::vars_outside`, `Sig::first_seen` | Mutation | A fold over a list used as a stack, items prepended in visit order; the borrowed references are shared values |
| A visited set of row and shape addresses (`HashSet<*const ()>` from `Row::addr`, `Shape::as_ptr`) local to one walk | `check::ty::Sig::first_seen` | Identity (gap 1) | As for ATOM-nested-sq: the node's digest as the key, confirmed by contents |

## Entries from TY-subst-stacks (`zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A trait with one hook per node kind (`Rebuild`: `known_ty`, `known_row`, `made_row`, `known_shape`, `made_shape`, `known_held`, `made_held`, `binding`), implemented by three local structs and passed as `&mut impl Rebuild` to one walk | `rebuild`, `rebuild_ty`, `rebuild_held`, `rebuild_tys`; `Replacer`, `Subst`, `Settle` | Interfaces (L10) | A record of functions over the walk's state, the state returned with each result |
| An explicit stack of a borrowing enum of steps and done steps (`Step<'a>`), its new items reversed in place, with one result stack per node kind (`Rebuilt`) drained by `split_off` and `drain` when a done step is popped | `rebuild` | Mutation | A fold over a list used as a stack, items prepended in visit order, the results a list per kind threaded as state |
| `Cow<'_, Ty>` for a binding that is either borrowed from the map or made | `Rebuild::binding` | Expressible | A shared value; the copy is free |
| Moving fields out of a shared node in drop: `Arc::into_inner` of a signature destructured by fields, `OnceLock::take` of its settled form and `Option::take` of a row's or shape's held and unchecked signatures, so the explicit drop stack owns them | `drop_types`, `Drop for RowData`, `Drop for ShapeData`, `Need::into_tys` | Mutation; no destructors | No code: the runtime frees the type, and its free must not recurse in the depth of the data, as for the drops of K39 |

## Entries from ORACLE-cones (`tests/src/oracle.rs`, `tests/steps/l01_37_oracle/scaling.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `BTreeMap::range` from a prefix with `take_while(starts_with)`, to find the keys that begin with a text | `counterexamples` | Library: DESIGN.md names no ordered-map range word | A stdlib word (catalog of step L2.11) that walks an ordered map from a key |

## Entries from HOOKS-term-dag (`zed-native/src/hooks.rs`, `zedc-zir/src/zir/memory.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap` memo filled during a walk, keyed by a cell's word (`i64`) or number (`usize`), whose values are terms that share their bodies through `Arc` | `Lets::closures`, `hooks::term`, `term_of`, `Machine::term` | Mutation; Identity (Gap 1) for the key | A map `Int ->? Term` threaded through the walk's state receiver; the key is the cell's number, which the runtime would expose as an identity |

## Entries from README-fences (`tests/src/readme.rs`, `tests/steps/l01_07_fences/readme/`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An index loop over the line's bytes that finds the first `//` outside a string literal, a `Peekable<Chars>` scan of tags and entities, and `str::find` over the HTML of cells | `comment`, `text_of`, `cells` | None | A fold over the string's code points with the state in the accumulator |
| `let … else { continue }` to skip a fence with no entry | `the_enabled_readme_fences_run_with_their_stated_results` | None | A `match` on the lookup's `#notFound` |
## Entries from DIAG-suppress (`zedc/src/suppress.rs`, `zedc/src/run.rs`, `zedc/src/unit.rs`)
| `u128` products reduced modulo `2^61 - 1` for the prefix hashes of a text, and the hash of a span from two prefixes | `Content::new`, `Content::hash` | None | `(a * b) mod (2^61 - 1)` on `int`, the operands' ranges `int[0..<2^61]` letting the plan use two words (as `num::mul_mod`) |
| An incremental `blake3::Hasher`, finalized once for the occurrence key and again after the count is added | `addresses` | Library | A hash word over a byte sequence built by appending, from the stdlib catalog of step L2.11; the key and the address as two hashes of two sequences |
| `slice::partition_point` over the top-level statements in source order | `enclosing` | None | A binary search over a sequence by a predicate, from the L3 library (as `docs::check`) |
| A `HashMap<ContentAddress, bool>` whose flags are set as warnings match, then read for the addresses that matched nothing | `Suppress::hides`, `unmatched`, `refused` | Mutation | A fold over the warnings that returns the set of matched addresses beside the printed ones; the unmatched are the named set minus it |
| `vec![String::new(); n]` filled by index, so problems placed per file come out in their first order | `Package::report` | Mutation | Each problem keyed by its index in a map, read back in key order |
| `Option::get_or_insert_with` on a cloned `Option<Vec<u8>>` that makes the per-arrow carrier vector on the first class piece of a path, then masks entries in place (`m[j] &= …`) | `check::Ck::apply_many` (`ClassAt`) | Lazy cells (gap 3); Mutation | A path state that starts with `None` and is rebuilt as a new vector by one map over the arrows at each class piece |

## Entries from GROUP-oracle (`tests/steps/l01_23_subtyping/group_oracle.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A table of `u32` over every pair of pool values, written in place, with three values above the pool's numbers as markers (unknown, divergent, on the path) | `Machine`, `Machine::app` | Mutation; Workaround (no mutable array in place) | A persistent map from the pair to an atom `#unknown`, `#diverges`, `#onPath` or a value number, threaded through the rounds; the markers become atoms, so no number is reserved |
| A pool whose values are numbered in order of insertion, with a `HashMap` from a value's canonical text to its number for deduplication | `Pool::add`, `Pool::seen`, `import` | Gap 2 (shared tables) | A map from text to number threaded as state, as gap 2 proposes |
| Closures inside the pool written as a small enum of body forms applied by a loop that replaces the closure and argument in place for calls in tail position | `Body`, `Machine::app` | None | A `match` on the body atom in a loop over `(c, x)` |
## Entries from XMARK-rows (`zedc/src/testing.rs`, `check/mod.rs`, `resolve.rs`)
- No new gap. `no_arrow_at_carrier` is a search over the operator's arrows for one whose parameter type meets the operand's, a fold with early exit that Zed writes as `any` over the arrows; the menus are lists of notes built once per refusal; `mark_failure` is a `match` on an optional row.
## Entries from TIME-report (`zedc-base/src/work.rs`, `main.rs`, `testing.rs`)
| A `thread_local!` `RefCell` holding the recorder, which every stage mark reads and writes without the stages passing it | `work::RECORDER`, `with`, `stage`, `unit`, `cached` | Mutation, global state (gap 2) | A recorder threaded as a state receiver through the stages, or the runtime's own counters read by the compiler's driver at each stage |
| A counter given as a boxed `FnMut` closure that reads a hardware counter and the global allocator | `work::Counter`, `main.rs` `counter` | Missing (no foreign counters, no allocator hook); mutation inside a closure | The runtime offers instructions and bytes as one foreign read; the port's driver passes it in, as the Rust driver does |
| `perf_event_open` through `perf-event2`, and the global allocator of `zed-alloc-count` | `main.rs` `counter` | Missing (foreign calls) | Stays in Rust: the measurement belongs to the runtime the port runs on |
| A flag set by the closure a query computes with, to tell a computed row from a cached one | `testing::counted_row` | Mutation of a captured variable | The query returns whether it computed, with its answer |
## Entries from NUM-subquad (`zed-kernel/src/num/fast.rs`, `num.rs`)
| Number-theoretic transforms over `Vec<u64>` updated in place, with `u128` products, `wrapping_mul` and Shoup's precomputed quotients for the products modulo three 64-bit primes | `Field::convolve`, `forward`, `inverse`, `shoup` | Bit operations (gap 4), Machine integers, Mutation (gap 11) | These are the arithmetic of `int` itself, which belongs to the runtime (row "What stays in Rust"); a Zed port would write them on `int[0..<2^64]` words with gap 4's bit words and an array updated in place |
| The half gcd's leaf steps on `i128` residues and matrix entries, chosen because they provably stay below `2^120` | `half_leaf` | Machine integers | Unbounded `int`, the ranges letting the plan use two words |
| Leaf sizes that differ between the unit tests and the build (`#[cfg(test)]` constants), so the unit tests reach the transforms at small sizes | `MUL_LEAF`, `GCD_LEAF` | No conditional compilation | A parameter of the routine, or a build mode of the unit, as in the entry from SLABS-count |
| Leaf sizes and cost constants set from timings of the Rust code, crossovers between methods with identical results (author decision 2026-11-06) | `MUL_LEAF`, `DIV_LEAF`, `RECIP_LEAF`, `GCD_LEAF`, `PRINT_LEAF`, `TRANSFORM_COST`, `SPARSE_WORD`, `SPARSE_STEP` | None | Measure each again on the Zed code by the procedure in COMPLEXITY.md section "Crossovers", compare with the curves recorded there, and explain the anomalies listed there; a method never slower than the other is used alone |
| A divisor borrowed or owned (`Cow<'a, BigUint>`) beside its reciprocal, built once and used for every block | `Divisor` | None | Zed shares values; the divisor is a value and the reciprocal a field beside it |

## Entries from BIGINT-fast-mul (`zed-kernel/src/num/fast.rs`, `num.rs`, `zedc-int/src/int.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Re-measure: the leaf and cost constants of the product's three-way choice, set from timings of the Rust code on 2026-11-07 (load 16 to 41), results identical | `MUL_LEAF` (512), `TOOM_COST` (10.4), `TOOM_POWER`, `TRANSFORM_COST` (12) | None | Measure each again on the Zed code by the procedure in COMPLEXITY.md section "Crossovers", BIGINT-fast-mul; compare with the grid there; explain the bimodal time at 3072 by 3072 words; at the port num-bigint's product is replaced by Zed's own, so `TOOM_COST` is measured against that one, and dropped if one method is never slower |
| A cost of num-bigint's product as `f64` with `powf` | `toom_cost` | Floating point in cost decisions | A rational or integer approximation of `s^0.465` (for example a table by the bit length of `s`), since only the choice depends on it |
| Pairs of transform points taken as `[u64; 2]` by `as_chunks_mut::<2>()` and destructured, butterflies on `&mut [u64; 2]` | `lazy_butterfly`, `Field::forward`, `Field::inverse` | Mutation (gap 11), Machine integers | An array updated in place by index pairs, as for the other stages |
| Garner's constants and inverses modulo the primes computed by `const fn` at compile time | `GARNER`, `inv_mod` | None | Constants found by partial evaluation of the same function (no separate constant evaluator) |
| A factor borrowed or owned (`Cow<BigUint>`) through the squarings of a power | `pow` | None | Zed shares values; the base is a value rebound at each squaring |

## Entries from CAST-menu-check and CAST-menu-rest (`zedc-check/src/check/mod.rs`)
- No new gap. The carriers of an argument are a `u8` mask with one bit per carrier, and the disjointness test runs over a `u16` with one bit per mask value; Zed writes both as sets of a four-member enum (bit operations, gap 1 where the masks are packed). The literal refusals of an application are pushed to a `Vec` on the checker and split off after it (mutation, gap 2), which the port writes as a list the application returns. A trial of a repair saves the checker's state, applies and undoes (as F6 and the CAST-menu entry).

## Entries from ORACLE-chain (`tests/src/oracle.rs`, `zedc-elab/src/elab.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `OnceCell` per definition holding its reads, filled on the first call | `Cones::reads`, `Cones::reach` | Lazy cells (gap 3) | The reads of every definition computed once when the cones are built, as one map from position to reads |
| A visited set kept as a vector of walk numbers, one per definition, set in place by `std::mem::replace` so all walks share it without clearing | `Runs::run` | Mutation | A set of the positions met, new for each walk; each walk is over one run's cone, so the cost stays that of the walk |
| `Vec<Known>` and `Vec<Option<String>>` written by index as definitions are run or marked, and a `loop` whose `break` gives the first stop | `Runs::outcomes`, `Runs::reads_a_stop`, `Runs::values` | Mutation | Maps from position to state and to outcome threaded through a fold over the unit's order; the doubling of the prefixes as a recursive function returning the stop |

## Entries from VERDICT-group-share (`zed-kernel/src/types/empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::mem::take` and `std::mem::replace` of the search's list of missing values read, around a nested build and each retry, and a `BTreeMap` from a type to the kept failures waiting on it, updated in place | `Searching::rep`, `Searching::retry`, `Search::forget_failures` | Mutation | A nested build returns the types it read with its value; the waiting map is search state threaded through the builds, as the other `Search` fields |

## Entries from VERDICT-group-roots (`zed-kernel/src/types/empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec<(usize, Refusal)>` of causes pushed in place by the search as it meets forks and give-ups, and a `Vec<Option<Refusal>>` marked by index in a walk over the readers with an explicit stack | `Search::give_up`, the fork in `Searching::tuples_on`, `Search::causes` | Mutation | The causes are search state threaded through the decisions, as the other `Search` fields; the walk is a fold over the readers with a persistent map as its visited set |
| `std::slice::from_ref` to pass one root as a list of roots without a copy | `Search::solve` | None | A one-element list |

## Entries from DIAG-addr-rest (`zedc/src/suppress.rs`, `unit.rs`, `testing.rs`, `run.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec<Option<Reported>>` written by index from each file's group and unwrapped in problem order | `Package::reported` | Mutation (gap 11) | The groups' results merged by problem index, as a sorted list or a map from index |
| An enum `Accepted` whose variant `Refused` carries the rejection that `run::program` gave | `testing::checks`, `testing::command` | None | A union with a payload |

## Entries from DIAG-addr-root (`zedc/src/place.rs`, `unit.rs`, `suppress.rs`, `run.rs`)

These replace the DIAG-suppress-rest rows (that section is now empty and removed) on `InFile::of` and `InFile::from_resolved` and the DIAG-addr-rest rows on `InFile::under` and the `HashMap` in `Package::report_on_disk`, whose code is gone.

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::fs::canonicalize` of the file, then `rustix::fs::openat` of its directory with `O_PATH`, of each `..` above it from the one below, and `rustix::fs::statat` of `zed.manifest` in each, so no probe repeats the whole path | `Place::of` | Library (host file system); `O_PATH` is Linux only (PORTABLE-rt) | `realpath`, `openDir`, `parentOf` and `statIn` words of the `Files` port (step L1.19), each directory a handle the walk folds over |
| An enum `Place` with variants `Unit { root, name }` and `Loose(PathBuf)` | `Place::of`, `InFile::at`, `package_report`, `run::load_file` | None | A union with two payloads |
| The parts of a path, or of a unit name split at `/`, fed to one BLAKE3 hasher under a tag, each followed by a zero byte | `InFile::{at, named, hashed}` | None | A fold of the parts into the hash state |

## Entries from K30-rest (`zedc-zir/src/zir/canon.rs`, `canon/serial.rs`, `store/int.rs`, `zed-kernel/src/words.rs`, `text.rs`, `zed-native/src/exe.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Vec::try_reserve_exact` and `num::room` (an allocation asked of the allocator and freed at once) before each growth or copy, an `Err` naming the bytes when the system refuses | `zir::binary::W::put`, `canon::serial::Out::put`, `Num::built`, `words::reserved`, `Text::try_shared`, `exe::data` | Missing (no allocation that reports failure) | The runtime's allocation returns a failure value the routine passes up; the asks become that failure |
| A `Display` impl that reads the formatter's width, precision, fill and alignment and writes the blocks of a finger tree | `impl Display for Text` | None | A `show` with a padding record over the text's blocks |
| `Arc<String>` shared between a token and the syntax tree | `lex::Part::Text`, `ast::StrPart::Text` | None | Zed values are shared |
| A table numbering finished regions by their contents, read by a derived order of node shapes | `canon::Regions`, `Shape` | Gap 2 (shared tables) | A map from contents to number threaded through the lowering |

## Entries from LOAD-chain (`zedc-preimage/src/preimage.rs`, `front.rs`)
| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An undo log of boxed `FnOnce(&mut Memo)` closures, each removing one memo entry a body made, run after the body; the scopes made since a mark cut off the end of their `Vec` | `Fresh`, `Walk::made`, `Tx::bind`, `Tx::drop_fresh` | Mutation (gap 11), Shared tables (gap 2) | The memo threaded as state, with the entries a body made kept in a map of their own and dropped as one value, or the tables as values taken before the body and the scope's part restored after |
| A trait over memo keys (`Key`, implemented for `At` and `(At, D)`) giving the term and scope an entry is keyed by | `Key`, `Walk::cached`, `Walk::made`, `Walk::translated` | Interfaces (L10) | A function giving the place passed beside the table, as `Table` is |
| A struct borrowing the given terms for its lifetime (`Scoped<'t>`), built once and asked once per body | `Scoped`, `front::linear_questions` | None | A value threaded through the fold over the functions, returned with each relation |

## Entries from LOAD-chain-share (`zedc-preimage/src/preimage.rs`, `presburger/extend.rs`, `front.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap<Id, Known>` from a shared conjunction, keyed by the part it is, to its answers and an `Rc<Model>` point shared with the conjunctions that extend it | `extend::Extending`, `Extending::answers`, `Extending::extend` | Shared tables (gap 2), Mutation (gap 11) | A map from the part's identity threaded through the fold over the questions, as `Id` sets are |
| The memo's translation tables moved out with `std::mem::take` after a body and moved back before the next (`Option<(bool, Translations)>`) | `Memo::take_translations`, `Memo::put_translations`, `Scoped::relation` | Mutation (gap 11) | The tables returned with each relation and passed to the next |
| An index `HashMap<Arc<str>, Vec<Rc<Logged>>>` from a name to the kept call entries whose arguments hold it, pruned with `retain` to the names a body reads | `Scoped::by_name`, `Scoped::relation` | Shared tables (gap 2), Mutation (gap 11) | A map from name to entries rebuilt by a filter over the next body's inputs |

## Entries from LOAD-chain-aux (`zedc-preimage/src/preimage.rs`, `presburger/extend.rs`, `front.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| One translation state (`Tr`) kept in `Scoped` for every body of a scope, its auxiliary numbers and definitions growing, replaced when `products` changes | `Scoped::tr`, `Scoped::relation`, `Scoped::def` | Mutation (gap 11) | The state returned with each relation and passed to the next |
| A point as an `imbl::OrdMap<Atom, Int>` that each extension adds the values of new atoms to, sharing the callee's point | `extend::Known::point`, `Extending::extend`, `extend::met` | None | Zed's maps are values; the runtime shares their structure, so an update stays `O(log n)` |
| A borrowed closure `&dyn Fn(u32) -> Formula` giving the definition of an auxiliary variable | `Extending::defined`, `extend::reached`, `front::linear_questions` | None | A function value passed beside the formula |
| An enum `What` of what an auxiliary variable stands for, written by a function that renumbers its auxiliary atoms, and `Display` | `preimage::What`, `What::written`, `Scoped::written` | Interfaces (L10) for `Display` | A union with a function writing it |

## Entries from LOAD-chain-args (`zedc-preimage/src/preimage.rs`, `front.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A map keyed by a body's address (`HashMap<*const Term, Frame>`), the body being shared by the function's definition and its uses | `Scoped::frames`, `Scoped::relation`, `Scoped::coordinates` | Pointer identity (no Zed equivalent) | A key the elaborator gives each function body, or the function's name in its unit |
| A type alias `Frame = Vec<(Arc<str>, i64)>` | `preimage::Frame` | None | A type definition naming a list of records |
| A closure returning `Option` and using `?` on each step of reading an argument | `Scoped::coordinates` (`through`) | None | A function whose body chains `else` on each failure (`#none`) |
| An optional borrowed closure `Option<&dyn Fn(&Lin) -> Lin>` passed to a writer | `What::written`, `Scoped::written` | None | An optional function value |

## Entries from LOAD-chain-sep (`zedc-presburger/src/presburger.rs`, `presburger/extend.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A memo `HashMap<Id, Option<Summary>>` keyed by a definition's `Arc` identity, filled by an explicit stack with a `HashSet<Id>` of open entries | `extend::Summaries`, `Summaries::summary`, `Summaries::make` | Identity (gap 1), Shared tables (gap 2), Mutation (gap 11) | A map from the definition's content digest threaded through the fold over the questions |
| A two-state enum `Made { Done(Option<Summary>), First(Formula) }` telling the stack loop to finish an entry or descend first | `extend::Made`, `Summaries::summary` | None | A union of two records |
| A let chain `if let Some(..) = .. && let Ok(b) = ..` choosing the summaries before the fallback | `extend::decide_defined` | None | Nested matches, or `else` on `#none` |
| A struct with methods `push`, `combine`, `dark_is_real` over one bound of a variable, used in Fourier-Motzkin elimination | `presburger::Side1`, `presburger::shadow` | None | A record type with functions over it |

## Entries from LOAD-chain-affine (`zedc-preimage/src/preimage.rs`, `zedc-presburger/src/presburger/extend.rs`, `zedc/src/front.rs`)

The LOAD-chain-args entries for `Frame` and `Scoped::coordinates` no longer apply: both are removed.

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A map keyed by a lambda's body and scope ids, `HashMap<At, (Vec<Lin>, u32)>`, with an undo list of its keys (`claimed`) | `Tr::claims`, `Tr::claimed`, `Walk::binding` | Mutation (gap 11) | A map value returned with each binding, the undo a kept earlier value |
| Union-find over parameter indices with path halving, `Vec<usize>` parents mutated in place, and a `Vec<HashSet<usize>>` of each class's functions merged smaller into larger | `preimage::identity_classes` | Mutation (gap 11) | A persistent map from index to parent, or a union-find in the stdlib catalog of step L2.11 |
| A nested `fn find(parent: &mut [usize], ..)` inside a function | `identity_classes` | None | A local function over the map value |
| An explicit stack of `(Formula, bool)` for a post-order walk, the bool marking the second visit | `Extending::defined` | None | A list value used as a stack |
| `usize` sizes compared to choose the largest decided part | `extend::Known::size`, `Extending::extend` | None | `int` |
| A loop over the kept parts that sets an `Option` and leaves at the first part whose point extends or that holds nowhere | `Extending::extend` | Mutation (gap 11), Early exit (gap 12) | A search over the list of parts returning the first answer it finds |

## Entries from LOAD-affine-cone (`zedc-preimage/src/preimage.rs`, `zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An explicit stack of `&Formula` with a `HashSet<u32>` visited set over auxiliary numbers, pushing each definition reached once and leaving early with `return None` | `preimage::projected` | Mutation (gap 11), Early exit (gap 12) | A fold over a work list carrying the visited set, ending in `#none` |
| A memo table of `Arc<[Con]>` keyed by `CallKey`, with an undo log entry `Logged::Projection` | `Memo::projections`, `Walk::projection` | Mutation (gap 11) | A map value threaded through the translation, the undo a kept earlier value |

## Entries from LOAD-call-summary (`zedc-presburger/src/presburger/extend.rs`, `zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A memo `HashMap<Id, Option<Face>>` filled by an explicit stack of `Formula` (shared nodes), a conjunction popped once its kept parts have faces, the map itself the visited set | `extend::Faces::make` | Mutation (gap 11) | A map value threaded through a fold over a work list |
| A local `#[derive(PartialEq, Eq, Hash)] struct Congruence` and `enum Says` used as `HashSet` keys to keep each congruence once | `extend::congruences_once` | None | A record and a union type as keys of a set from the stdlib catalog of step L2.11 |
| A per-scope `HashMap<Id, HashSet<Atom>>` of the atoms each bound conjunction's caller binds, extended in place at each binding | `preimage::Tr::bound`, `Scoped::interface` | Mutation (gap 11) | A map value returned with each translation, the undo a kept earlier value |
| Closures `&dyn Fn(u32) -> Formula` and `&dyn Fn(&Formula) -> Option<Vec<Atom>>` (`Interface`) passed as parameters | `Extending::defined_with` | None | Function values |

## Entries from L1.36b (`zed-native/src/link.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `blake3::Hasher` from `new_derive_key`, fed each part of a link's key after its length (`usize::to_le_bytes`), and one fed a whole file by `update_reader` | `link::Identity::key`, `Identity::of` | Library; Bytes (gap 5) | A hash word over a byte sequence from the stdlib catalog of step L2.11, over the bytes of a `Files` read |
| `std::process::Command` running the C compiler driver with `--version` and `-Wl,--version` and keeping its standard output as bytes | `link::Identity::of` | Command line (gap 6) | The process port the linker needs too; until then the Rust driver links |
| `object::File::parse` over a `ReadCache` of the output and `Object::build_id`, to read the key an executable records in its GNU build-ID note | `link::recorded` | Foreign library; Bytes (gap 5) | An ELF note read from the bytes of a `Files` read once Bytes works, or the record kept beside the executable |
| An `Option` built with `?` from each fallible step, every failure meaning "no record" | `link::recorded` | None | An `else` chain ending in `#none` |

## Entries from NAME-at-print-warnings (`zed-kernel/src/print.rs`, `zedc-presburger/src/presburger.rs`, `presburger/deep.rs`, `elab.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A plain function pointer `fn(&str) -> &str` held in the printer's state (`Option<fn(..)>`) and passed down the `show` of each formula part, whose result borrows from its argument (a prefix of the name) | `print::written`, `Pieces::name`; `Formula::written`, `Factor::show`, `Atom::show`, `Lin::show`, `Con::show`; `elab::written_name` | None | A function value passed as an argument; the written name is the string's `slice` before `@`, shared and not borrowed |

## Entries from ST-exact-enum (`zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `if … && let …` (a let chain) taking a constraint off the due set and reading its free names | `product::Scope::enumerate_exactly` | None | a `match` on the lookup inside the `if` |
| An or-pattern in an irrefutable `let`, naming the key of each item of a persistent map's difference | `product::Scope::enumerate_exactly` | Or-patterns (row above) | a `match` with one arm per kind of change |

## Entries from NARROW-hub-settle (`zedc-check/src/check/arms.rs`, `zedc-preimage/src/product.rs`, `zedc-presburger/src/conjuncts.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `RefCell<HashMap>` memo filled by a `&self` method, so a lookup under a shared borrow of the arms keeps its answers | `Arms::found`, `Arms::lookup` | Mutation (gap 2) | `lookup` takes and returns the memo as a state receiver; every lookup runs inside `deciding`, which holds the arms mutably but reads a node's names (`push_names`) while it looks each one up, hence the cell |
| Skew-binary jump pointers in two `Vec<usize>` indexed by node and pushed as nodes are added (Myers 1983) | `Arms::add`, `Arms::depth`, `Arms::jump`, `Arms::step` | Mutation | Two maps from node to depth and jump target, grown with the node list; the arithmetic is plain `int` |
| A scope settled in place on a clone (`let mut s = self.clone(); s.settle(..)`) to answer a read through `&self` | `Scope::settled` | Mutation | `settle` returns the settled scope; the clone is the persistent maps' sharing, which Zed values have |

## Entries from DECIDE-disj-chain (`zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `HashMap::entry(..).or_default()` accumulators per atom, updated in place (an owner set to `None` when a second disjunction holds the atom; bounds, rows and a `bad` flag pushed per row) | `absorb` | Mutation (gap 11) | A fold over the rows that returns the map |
| `enum Side<'a>`, a bound side kept as a small state machine (`Empty`, `Shared`, `Mixed`) changed in place by `add(&mut self, ..)`, borrowing the terms and constant of a row | `Side::add`, `absorb` | Mutation (gap 11); lifetimes vanish | `add` returns the new side; the terms are shared values |
| A `struct Bounds<'a>` with `#[derive(Default)]` declared inside the function that uses it | `absorb` | None | A record type declared `local` in the file |
| Closures `held_by` and `serves` that borrow the function's maps, with `?` and early `return None` inside `serves` | `absorb` | None (early exit is gap 12) | Local functions taking the maps as arguments; the early exits as `if` or a fold with an `Option` |
| `Vec::retain` whose closure advances a captured counter to read a `Vec<bool>` of removed positions | `absorb` | Mutation (gap 11) | `where` over the disjunctions zipped with their positions |
| `Option::is_none_or`, `Option::is_some_and` | `repair`, `settle` | None | A `match`, or `x is #none or ..` |

## Entries from DISJ-diff-fast and DISJ-incremental (`zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `thread_local!` `Cell<bool>` (`OLD_PATH`) set around a second run of a question, read deep in the solver to choose the old path | `old_path`, `or_old`, `project_each`, `settle`, `pick`, `decide_inner`, `project_parts` | No global mutable state | A `path` argument, or a field of the solver's context, passed down from the public entry points |
| `macro_rules! put` that inserts a row or keeps the tighter of two rows on one form, mutating a `Vec` and a `HashMap` of the enclosing function | `shadow` | Mutation (gap 11); no macros | A local function over the rows and the map that returns both |
| Per-atom counts in a `HashMap` updated in place (`Deg`: lower, upper, equalities, unit equalities and their terms) as rows are added and removed | `shadow` | Mutation (gap 11) | A map threaded through a fold, or the solver's mutable-cell port if it has one by then |
| An explicit stack of ranges with their projected rows (`Vec<(usize, usize, Option<Vec<Con>>)>`) for the divide and conquer over disjuncts | `by_halves` | None | A `loop` over a list used as a stack, or plain recursion once Zed's lowering manages the stack |
| `std::mem::replace` and `std::mem::take` to move a value out of a slot it is replaced in | `project_each`, `settle` | Mutation (gap 11) | The new value built from the old and bound to a new name |
| `retain` on the map of bounds by linear form, joining each disjunct's bounds into the disjunction's | `disjunction_hulls` | Mutation (gap 11) | `where` over the bounds, or a fold that builds the joined map |

## Entries from DISJ-three-atom-empty (`zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An optional log of eliminations passed as `Option<&mut Vec<_>>` and reborrowed with `as_deref_mut` at each elimination | `shadow_logged`, `point_of` | Mutation (gap 11); references | `shadow` returns the eliminations with the rows left, and `shadow`'s callers that do not read them drop them |
| A closure that pushes a row onto a captured `Vec`, solves, and pops it again | `tighten` (`at_end`) | Mutation (gap 11) | The rows with the one row added, built for each end (two per symbol) |
| `Vec::dedup_by` after a sort, keeping the first row of each linear form | `shadow` (the trial) | Mutation (gap 11) | A fold over the sorted rows that keeps a row when its form differs from the last kept |

## Entries from DISJ-dpll (`zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An `FnMut` closure passed to `by_halves` that captures the disjunctions by `&mut` and a `removed` flag, removes disjuncts with `Vec::retain`, and returns rows that `by_halves` adds to the projections still to run | `drop_jointly_empty` | Mutation (gap 11); closures capturing by mutable reference | `by_halves` as a fold whose leaf takes and returns its state (the disjunctions left and the flag) with the rows to add |
| `Err(())` returned from the leaf as an early exit, read as "no point" by the caller | `drop_jointly_empty` | Error as control flow | The fold's state carries "no point", and the fold stops on it |
| `std::slice::from_ref` to pass one disjunction as a slice of one | `drop_jointly_empty` | References | A list of one |

## Entries from LINK-obj-leftover (`zed-native/src/link.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::fs::File::lock` and `try_lock` (`flock`) on an open directory, released by the kernel when the process ends | `link::Scratch::new`, `link::sweep` | Foreign library (`flock`); file system port | A file-system port operation that takes an advisory lock and reports "held by another" |
| A `Drop` impl that removes the build's working directory on every exit, unwinding included | `link::Scratch` | No destructors | The build's own `finally`-like cleanup in the process port's scope, as for other temporary files |
| A `static AtomicU64` counter with `std::process::id()` to name a fresh directory | `link::Scratch::new` | No global mutable state; process id | A counter in the build's state and the process port's id |
| `MetadataExt::dev` and `ino` compared after `symlink_metadata` and `File::metadata`, to check a name still names the locked directory | `link::names` | File identity from the OS (gap 5, Bytes and foreign calls) | A file-system port call returning a file's identity |
| `std::fs::rename` of the linked executable over the output | `link::build` | File system port | The port's atomic replace |

## Entries from LINK-key-deps (`zed-native/src/link.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::collections::HashSet<(u64, u64)>` of (device, inode) from `MetadataExt::dev` and `ino`, to hash each file once | `link::Inputs::of` | File identity from the OS (gap 5, Bytes and foreign calls) | A file-system port call returning a file's identity, kept in a Zed set |
| `FileExt::write_all_at` on a file opened read-write, and `object::ReadCache` over `&mut File`, to patch the build-ID note in place | `link::write_build_id` | File system port (positioned writes); foreign crate | Port calls for a positioned read and write; an ELF note reader in Zed |
| `blake3::Hasher::update_reader` over a `File`, and `blake3::derive_key` contexts | `link::hash_file`, `link::Inputs::of`, `link::Identity::key` | Foreign library (BLAKE3) | The BLAKE3 the kernel's content addresses use, behind the same port |
| `Command::env` and `env_remove` per variable, and `std::env::var_os` | `link::driver_env`, `Toolchain::driver` | Process port (environment) | The process port's environment map, passed to the spawn |
| `OsStr::as_encoded_bytes` and `OsStr::from_bytes` (`OsStrExt`) to read paths from the linker's list and the record | `link::dependencies`, `link::Record::read`, `Record::to_bytes` | Bytes as paths (gap 5) | Paths as byte strings in the file-system port |

## Entries from S22-order (`zedc-preimage/src/preimage.rs` tests, `zedc/src/lib.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `&dyn Any` with `downcast_ref::<T>()` and `is::<T>()`, to compare a memo entry of any table by its type | test `rechecked`, `shown_any` | Reflection | One comparison function per memo table, passed with the table |
| `#[path]` on a module, to share one test file between crates | `zedc` `lib.rs` (`mod scaling`), as `zed-kernel` | Modules | A shared test unit imported by each crate's tests |

## Entries from RUNTIME-build-src (`zed-native/build.rs`, `zed-native/src/sources.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A build script hashing the source files of its crate and of the workspace crates it depends on, found by reading `Cargo.toml` files line by line, listing directories (`std::fs::read_dir`, `canonicalize`) and searching Rust files for `include!`, `include_str!`, `include_bytes!` and `#[path]`; it prints `cargo::rerun-if-changed` for each file and directory read | `build.rs`, `sources::of` | None at the language level: Cargo's crate hash leaves out the sources' contents; Library (host file system) | The Zed build tool knows the content address of every unit it compiles (sec:ir) and writes the runtime's identity from those addresses; no file walk or manifest reading is needed |
| `#[path]` on a module, to compile one file both in a build script and in the crate | `build.rs` (`mod sources`), `lib.rs` (`pub mod sources`) | Modules | Gone with the build script, as above |

## Entries from IS-chain-quad (`zedc-check/src/check/mod.rs`, `zedc-check/src/check/walk.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `VecDeque` joined by moving the shorter onto the longer: `append` onto the back, or `pop_back` and `push_front` onto the front, so an item moves at most log2 n times in a tree of joins | `check::joined`, the `Facts` and `Saved` of `CondAnd2` | Mutation (gap 11) | A persistent sequence with O(log n) concatenation (a finger tree or rope of facts), or a list consumed and rebuilt in place by provable last use; `Saved` is restored in reverse order, so the sequence needs a walk from its back |
| A narrowing left applied to the checker's environment across frames (`Held`: the `Saved` that restores it, handed from the frame of a condition to the frame that reads it) | `CondAnd1`, `CondAnd2`, `CondNot`, `Logic1`, `If1`, `Ck::narrow_side`, `Ck::release` | Mutation (gap 11) | The environment a value in the walk's state, the condition's result carrying the environment it leaves, read by the next frame in place of the outer one |

## Entries from LIST-parity-quad (`zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A tree of restrictions by halves kept in a `Vec<Option<Part<Row>>>`, each built on first use through `&mut self` while the iterator runs | `RowIndex::half`, `RowIndex::holds` | Mutation | The tree in the iterator's state receiver, each node a lazy value; or all `2c` restrictions built before the first value, which costs the same order |
| Per column and depth, a `BTreeMap<Value, Vec<usize>>` filled with `entry().or_default().push` | `Keyed::add`, `Keyed::at` | Mutation | A table from column, depth and value to a list, built by a fold over the tuple types |

## Entries from S22-chain-cost (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Peekable` over a `Vec`'s owning iterator, with `next_if` taking the next leaf only when its range lies inside the node being built | `cls_build` | Mutation, iterators | A recursive build over the list of leaves that returns the rest of the list |
| A `&mut Vec` passed down a recursion that pushes the leaf pairs of two trees walked together | `cls_zip` | Mutation | A fold that returns the list, or the two walks' leaf lists merged by their ranges |
| `if … && let Split::Exact(..) = …` (a let chain) taking a second split's answer only when it is exact | `preimage_in` | None | `match` with an `is` test |

## Entries from NARROW-hub-rest (`zedc-presburger/src/conjuncts.rs`, `zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Box<StarIndex>`, the star indexes of a conjunction behind one pointer, so a `Scope` moved on the checker's stack stays small (an unboxed index made `check::walk`'s frame 0x1278 bytes against 0xbe8, and `follow::following_tests_scale` overflowed) | `Conjuncts::index` | None | Removed: Zed values are shared, and size is not the programmer's concern |
| The relation cloned to forget a name on the copy, and its stars compared with the original's by `OrdMap::diff`, before the scope settles and forgets in place | `Scope::bind` | Mutation | `forget` returns the new relation; the clone is the persistent maps' sharing, which Zed values have |

## Entries from NARROW-hub-related (`zedc-presburger/src/conjuncts.rs`, `zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A hub's map of near names updated in place through `OrdMap::get_mut`, its size before and each pair's presence before kept in `BTreeMap`s, so that the leaves are rechecked only for net changes | `Conjuncts::refree` | Mutation | A fold over the changed conjuncts that returns the new map and the two maps of what was before |

## Entries from LIST-parity-tail (`zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A stack of runs, each a meet and its length, merged with `Vec::pop_if` while the top run is no longer than the new one, as a binary counter | `list_boxes` (in `Type::boxes` before LIST-xor-finite) | Mutation | A list of runs returned from each step of the fold, merged by a recursive step on its head |
| A `HashMap<Vec<usize>, usize>` numbering each set of rows (a region) on first sight, seeded with the empty set as 0 | `RowIndex::new` | Mutation (gap 2: an intern table) | A fold over the keys with the map in its state, or the sets sorted and numbered by their rank |

## Entries from LIST-parity-keys (`zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An explicit stack of `enum Step { Meet, Tuple(n) }` with a results `Vec` that `Tuple(n)` takes the last `n` of by `split_off` | `meet_types` | Mutation | A recursive meet over the columns, its depth bounded by the type's depth, or a fold over a work list returning the results list |
| A `HashMap<Place, BTreeMap<Value, usize>>` filled on first read by `entry().or_insert_with` inside an `FnMut` closure passed to `spine` | `RowIndex::holds`, `spine` | Mutation (gap 2: a memo table), closures capturing mutable state | `spine` returns the places it reads, the regions are made for the new places and threaded back in the index state |
| A `HashMap<Vec<usize>, usize>` numbering each set of types (a region) on first sight, and `HashSet`s of types seen | `place_regions` | Mutation (gap 2: an intern table) | A fold over the sorted keys with the map in its state |
| `Option<Firsts>` filled on first use by `get_or_insert_with` in a class; a `Vec` of block deltas sorted and merged in place by `dedup_by` | `RowIndex::holds`, `Blocks::eval` | Mutation | The class's firsts made when the class is made; the deltas grouped by a sorted fold |

## Entries from LIST-xor-finite (`zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Two passes over an expression by an explicit stack of `enum Step { Read, Combine }`, with `HashMap`s keyed by (expression or diagram, id, sign) holding each operand's finiteness and its boxes, filled once each | `part_boxes` | Mutation (gap 2: memo tables) | A fold over the operands in post order, the two maps in its state; or a recursive function over the expression with the maps threaded through |
| `imbl::OrdSet<Row>` boxes shared between an operand and the expressions that read it, a union adding the smaller set to the larger | `part_boxes` | Persistent sets (none in the Zed prelude yet) | A persistent ordered set in the library (L2.11), or a sorted list merged smaller into larger at the cost of the larger's copy |
| `enum Made { Diagram, Same, Union, Meet }` recording how each operand's boxes were made, read by a second explicit stack to build the column-wise join of an operand only when a meet needs it, memoized in a `HashMap` | `join_of` | Mutation (gap 2: a memo table) | A lazy join stored beside the boxes when they are made, or a recursive join with the memo threaded through |
| A `BTreeMap<Row, bool>` of whether each box has only finite columns, filled by `entry().or_insert_with` | `part_boxes` | Mutation (gap 2: a memo table) | The flag computed once when the box is made and kept beside it |
| A graph of a part's nodes in topological order (`Vec<Vertex>`, `enum Vertex { List, Not, Or(Vec), And(Vec) }`), built from an explicit stack with a visited `HashMap`, then merged in place with `std::mem::take` of operand lists, the largest list kept and the others appended | `Graph::new`, `Graph::merged` | Mutation (gap 2), explicit stacks | A fold over the operands in post order building a list of nodes; merging as a second fold that returns new operand lists, the smaller appended to the larger |
| Per class, a `Base` of node values and counts kept in an `Option` filled with `get_or_insert_with`; per candidate, overlay `HashMap`s of changed values and count changes and a `BTreeSet` of nodes to read again, popped lowest first | `RowIndex::holds`, `Graph::base`, `Graph::apply` | Mutation (gap 2: memo tables, work sets) | The base computed when the class is made and kept beside it; the evaluation as a loop over an ordered set in its state, the two maps threaded through |
| A `HashSet<Vec<usize>>` of the tuples tried, by their components' numbers, `insert` returning whether the tuple is new | `Maker::tried` | Mutation (gap 2: a set in the iterator's state) | A persistent hash set in the iterator's state (L2.11) |
| A table numbering each value made, a `BTreeMap<Value, usize>` for scalars and bare atoms and a `HashMap<Vec<usize>, usize>` for tuples by their components' numbers, filled by `entry().or_insert` | `Numbers`, `Maker::new`, `Maker::step` | Mutation (gap 2: a table in the iterator's state) | The table in the iterator's state, threaded through each step |
| A hand-written `Ord` that tries `==` (which skips shared nodes of two `imbl::OrdSet`s) before the ordered walk | `impl Ord for Lits` | Persistent sets (none in the Zed prelude yet) | Equality of the library's persistent set (L2.11) checked first, by node identity |

## Entries from CHAIN-zip-size (`zed-kernel/src/types/bdd.rs` with its module `xor`, `bdd/set.rs`, `bdd/list.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Thread-local tables that hash-cons treap nodes, list cells and exclusive ors by the ids of their children, the ids taken from one global `AtomicU64` | `set::make`, `list::cell`, `xor::node`, `NEXT` | Shared tables across pure calls (gap 2) | A state struct of the three tables passed by primed receiver, ids issued from a counter in it; or keys by digest (gap 1) |
| `OnceLock` fields of a shared cell filled on first use: the atoms of a list's blocks, the first node of each value, the complement of an exclusive or set both ways | `Cell::atoms`, `Bdd::view`, `xor::xor2` | Mutation of shared data | Lazy values computed when the cell is made, or a memo table keyed by cell id in the state struct |
| Treap walks that keep `Vec<&Arc<Set>>` stacks of the path and rebuild it bottom up; an `Iterator` struct holding its own stack | `set::split`, `set::insert`, `set::remove`, `set::Iter`, `xor::node` | Mutation, iterators | A fold over the path list returned by a loop; the iterator as a recursive list builder |
| A slice pattern binding the last two elements of a `Vec` mutably inside a let chain | `Bdd::assemble` | Mutation | Take the last two elements off the list, rebuild them, and put them back |
| A blanket `impl<A: Literal> set::Atom for A`: the treap module states the four operations it needs of an atom (its table of set nodes to look up and insert, the same table to remove a dropped node, its digest, freeing a node) as a trait of its own, so it imports nothing of the diagrams (KERNEL-bdd-cycle) | `set::Atom`, `impl set::Atom for A` in `bdd.rs` | Interfaces (L10) | A record of the four functions passed to the set functions, or an interface of the set unit that the diagram unit implements |

## Entries from NARROW-notes-name (`zedc-check/src/check/arms.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The breadth-first search of a carrying test kept in a `HashMap` and resumed in place: `Carried::others` expands the queue to the depth of a name and records each other way a name is reached at its depth (`also`) | `Carried::expand`, `Carried::others` | Mutation | A search state returned by each step, the map of searches threaded through `Arms::deciding` |

## Entries from NARROW-eager-scope (`zedc-presburger/src/conjuncts.rs`, `zedc-preimage/src/product.rs`, `zedc-check/src/check/arms.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The class index of stars (`classes`, `class_of`, `class_at`) updated in place in `flush` by `enclass` and `unclass` | `Conjuncts::enclass`, `Conjuncts::unclass` | Mutation | A fold over the changed stars that returns the three maps |
| The search of a carrying test drained to the end in place, recording for each name the tests that read it and for each test the names it was reached from | `Carried::drain`, `Carried::expand` (read by `Carried::around` and `Arms::longer`) | Mutation | The search state returned by each step, as for `Carried::others` |

## Entries from EMPTY-nonstrict-unsound (`zed-kernel/src/types/empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `BTreeSet` round of types popped one at a time (`pop_first`) from the search's state, refilled by `std::mem::take` of `again`, and read by drains started inside the decisions it runs | `Searching::drain`, `Search::round` | Mutation | The round is search state threaded through each decision, as the other `Search` fields; a nested drain returns the round it leaves |

## Entries from S22-transfer-rem (`zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An `Option<Rc<HashMap>>` field of the run filled on the first call and shared by every later call (the cuts of each input and modulus) | `Tx::classes_of`, `Run::cut_table` | Mutation, shared ownership | A value computed once when the run starts, or a lazy binding of the run |
| A `HashMap` keyed by a pair of a term and an `Option` of an input and modulus, memoizing the summaries by class | `Memo::by_class`, `Walk::by_class` | Mutation | A memo keyed by the same tuple, as the other memos of the walk |

## Entries from ZEDC-split (`crates/zedc/src/lib.rs`, `store/mod.rs`, `crates/zedc-presburger`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A module of another crate republished at its old path (`pub use zedc_check::check;`), so callers keep writing `zedc::check` after the compiler is split into crates | `zedc` `lib.rs`, `store/mod.rs` | Missing (a re-export is a definition of one name, DESIGN.md sec:units) | Not needed in the port: each unit imports the unit that defines what it uses; the Rust paths are kept only so the split changes no caller |
| A cargo feature, `two-at-a-time`, that keeps a `thread_local!` switch and the joins it selects in the build of `zedc-presburger`, so the unit tests of another crate (`zedc-preimage`) can set it; before the split it was `#[cfg(test)]` in the same crate | `presburger::TWO_AT_A_TIME`, `and_keeping`, `or_keeping` | No conditional compilation; global state (gap 2) | A build mode of the unit, as for `printed-types`, or the join order passed as a parameter in the test |

## Entries from TABLE-life (`zed-kernel/src/types/bdd.rs`, `bdd/set.rs`, `bdd/list.rs`, `bdd.rs` module `xor`, `types/rec.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Tables of `Weak` references, each entry removed by the node's `Drop` on a pointer match, through `try_with` and `try_borrow_mut` of the thread's table | `set::make`, `list::cell`, `xor::node`, `Drop for Set`, `Drop for Cell`, `Drop for Pair`, `Literal::untable`, `rec::GROUPS`, `rec::INSTANCES` | Shared tables across pure calls (gap 2), identity (gap 1); Zed has no weak reference or finalizer | A per-unit state struct of the tables, dropped whole at the end of a unit, so no entry needs to leave on its own |
| A `Mutex<Weak<Expr>>` beside a `OnceLock<Part>` so that an expression and its complement hold each other one way only | `Expr::back`, `Expr::link`, `Expr::known` | Lazy cells and tied recursive types (gap 3) | The complement in the unit's memo table keyed by expression id, both ways |
| A weak table of rows, each row removed by `Drop for RowNode` on a pointer match (since ATOM-intern the generic `Shared<K>`, below) | `Row::new`, `ROWS`, `Drop for RowNode` | Shared tables across pure calls (gap 2), identity (gap 1); Zed has no weak reference or finalizer | A row table in the unit's state struct, dropped whole at the end of a unit |
| The form an expression was the complement of, kept so a freed source is made again alike | `Expr::source`, `Source`, `Connect::negate` | Lazy cells (gap 3) | Not needed when the unit's memo table keeps both sides for the unit |

## Entries from TABLE-short-scan (`zed-kernel/src/types/bucket.rs`, `types.rs` `Shared`, `types/bdd/set.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A treap of `Weak` references in a `Vec` of slots with `u32` links, each node keeping its slot so its `Drop` takes its entry out by slot and a pointer match; a lookup passes closures that borrow the thread's table once per step and compares outside the borrow, restarting on a version count | `bucket::find`, `Bucket`, `Shared::new`, `Drop for Shared`, `set::make`, `Drop for Set` | Shared tables across pure calls (gap 2), identity (gap 1); Zed has no weak reference or finalizer | An ordered map from key to node in the unit's state struct, dropped whole at the end of a unit, as for the TABLE-life entries above |

## Entries from CHAIN-restrict-memo, CHOICE-both-chains, XOR-cross-thread (`zed-kernel/src/types/bdd.rs`, `bdd/list.rs`, `bdd/set.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A walk down a list that pushes `(&Arc<Cell>, bool)` onto a `Vec` until a memo hit, then pops it to build the result bottom up, writing each suffix into a `HashMap` memo passed as `&mut` | `Bdd::restrict` | Mutation | A loop that collects the cells down to the memo hit into a list, then a fold over it that returns the result and the memo |
| An enum variant holding a borrowed `&Bdd` (`Operands::Chain`) so a chain is looked up in place, not listed | `Part::operands`, `choice_of`, `xor::pair` | Borrowed references in data | The variant holds the list value itself; values are shared, not copied |
| Two sets compared by `Arc` id first, then walked side by side from a `Vec` stack of node pairs, so equal sets made on two threads are found equal | `set::same`, `xor::opposite` | Identity (gap 1), mutation | Not needed if the port keeps one table per unit and checks on one thread; otherwise a recursive comparison of the two trees, stopping where the nodes are one |

## Entries from CHAIN-deep-atom (`zed-kernel/src/types/bdd/list.rs`, `types/bdd.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A list's blocks kept in a treap by position whose cells are hash-consed by `(left id, block id, right id)` through one `HashMap::entry` walk that upgrades a `Weak` or inserts one | `list::cell`, `Drop for Cell` | Shared tables across pure calls (gap 2), identity (gap 1) | The cell table in the unit's state struct, as for TABLE-life; the treap itself is a plain recursive value |
| The restriction of a list driven by a `Vec` stack of `(cell, value, Stage)`, where the enum `Stage` holds the block left and the left child's piece between the visits of a cell, results written into a `HashMap` memo passed as `&mut` (replaces the CHAIN-restrict-memo row's walk) | `Bdd::restrict`, `Stage` | Mutation | A recursive function over the treap returning the piece and the memo; the stack is the call stack, deep only as the treap, `O(log m)` |
| A `Hasher` written for the memo's `u64` keys (splitmix64's finalizer), given to `HashMap` through `BuildHasherDefault` | `list::KeyHasher`, `list::Memo` | Interfaces (L10) | The memo map takes its hash function as a parameter, or keys by id in an array map |
| An own set of pairs of ids for comparison (FAMILY-eq-cost, replacing `HashSet` with the hasher `PairHasher` of FAMILY-eq-reserve): a `Vec<(u64, u64)>` of a power of two slots at most half full, `(0, 0)` the empty slot, linear probing from a home slot given by one 128-bit multiply per id with its two halves folded by exclusive or, deletion by backward shift, `#[cold]` growth by doubling; the dispatch `step` and its common arms `plain_step` marked `#[inline(always)]`, the rare `min_max_step` `#[cold] #[inline(never)]` | `value::ReadSet` (`home`, `insert`, `remove`, `grow`, `clear`), `step`, `plain_step`, `min_max_step` | Mutation (gap 11), `u128` product, no inlining or cold hints | A set of pairs in the standard library with a hash parameter, or this table as an array updated in place; the product is a widening multiply of two `u64`; inlining is the backend's choice, with no hint in the source |
| The atoms of a rebuilt cell taken from the cell it replaces, changed by the edit's atoms, written into the new cell's `OnceLock` when the old one has made them | `list::carry`, `list::replace` | Mutation of shared data, lazy cells (gap 3) | The atoms computed when the cell is made, from the replaced cell's, in the cell constructor |

## Entries from S22-linear-rem (`crates/zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap` from the form of a term and its scope to an auxiliary variable, with a `Vec` of its keys in the order made, popped back to a mark to undo a scope | `Tr::cases`, `Tr::cased`, `Tr::truncate`, `Walk::lin_by_class` | Mutation, undo by hand | A persistent map carried down the translation, so leaving a scope drops its entries with no undo |

## Entries from S22-case-cuts (`crates/zedc-preimage/src/preimage.rs`)

- No new gap. `neighbor_cuts` merges two sorted lists by index; `lin_by_class` finds the cuts inside a piece with `slice::partition_point` (as `docs::check`) and tests ends with `Option::is_some_and` and `Option::is_none_or` (as `repair`).

## Entries from PA-let-block (`crates/zedc-preimage/src/preimage.rs`, `product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A graph of `Arc` nodes, each with a `OnceLock` holding its sum once a test reads it, and an id from a global `AtomicU64` counter for the visited set | `LetPa`, `LetNode`, `LetPa::force`, `LetPa::sum`, `LET_IDS` | Lazy cells (gap 3), global state (gap 2), shared ownership | The summaries in a table of the walk keyed by binding order, each sum memoized in the table; the binding order is the id |
| A `Drop` that empties a chain of nodes on an explicit stack with `Arc::try_unwrap`, so a deep chain does not overflow | `Drop for LetNode` | No finalizers; ownership | Not needed: the table is dropped whole with the walk |
| A cache field whose `PartialEq` always says equal, so two scopes compare by their names and not by the summaries | `Summary` in `Binding` | Identity, mutation | The summary table outside the compared scope |
| A cache rebuilt from the names with its own differing entries, so the persistent maps keep shared nodes and `diff` skips them by pointer | `Scope::seen_fresh` | Identity (gap 1): `imbl` diff compares node pointers | A version number per name, compared instead of the nodes |

## Entries from REC-cycle (`zed-kernel/src/types.rs`, `types/rec.rs`, `types/empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A thread-local unit of work, `RefCell<Unit>`, listing by `Weak` the instances whose recursive members it made, ended by `Type::forget_emptiness` and by its `Drop` at thread exit, and the thread's number, which keys `INSTANCES` | `rec::unfold::{Unit, UNIT, thread, THREADS, end_unit}`, `Env::register`, `Env::forget` (in `rec.rs` until CYCLE-kernel-moves) | Shared tables across pure calls (gap 2); Zed has no weak reference or finalizer | The unit's state struct holds the instances and their members, and is dropped whole at the end of the unit, so no cycle needs breaking |
| A recursive type's unfolding and an instance's recursive members in `Mutex<Option<Type>>` cells, cleared at the end of a unit and made again when next read | `Rec::body`, `Rec::unfolding`, `Rec::forget_unfolding`, `Env::members`, `Env::member` | Lazy cells and tied recursive types (gap 3) | The unfolding in the unit's memo table keyed by member id |
| A guard that lends the parts of a node or of a fresh unfolding (`PartsRef`), and an append-only arena of chunks that holds the unfoldings a walk borrows from (`Held`) | `Type::p`, `Type::p_held`, `Held::put`, `classes`, `overlaps`, `Walk::enter` | References into values (Rust lifetimes); a Zed value is not freed while a binding names it | Not needed: the walk binds the unfoldings it reads |
| An instance named by a counter, never reused, instead of its address | `Env::id`, `ENVS`, `Key::group`, `Type::group` | Identity (gap 1) | The instance's index in the unit's table |

## Entries from PA-let-check (`crates/zedc-check/src/check/walk.rs`, `arms.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A memo of `Rc<Summarized>` per binder in a `HashMap`, filled on an explicit stack with an `entered` set | `Arms::summaries`, `Ck::summarized` | Shared ownership, mutation of the checker state | A table of summaries keyed by binder, filled in dependency order with the binders |

## Entries from ATOM-intern (`zed-kernel/src/types.rs`, `types/bdd.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A generic node `Shared<K>` kept in a weak `thread_local!` table chosen by a trait method that returns a `&'static LocalKey` (`Tabled::live`), one table per key type, each node removing its entry in a generic `Drop` | `Shared`, `Shared::new`, `Tabled`, `ROWS`, `ARROWS`, `Row`, `Morphism` | Shared tables across pure calls (gap 2), identity (gap 1), global state; Zed has no weak reference, finalizer or thread-local | One table per key type in the unit's state struct, dropped whole at the end of a unit, as for TABLE-life |

## Entries from PA-let-stack (`crates/zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `async fn` methods of a struct holding a `frames::Stack`, called through `fn`s returning `Deep` that answer a leaf at once (`Stack::ready`) or start a frame (`Stack::call`), so the walk of the arms and the forward transfer keep their nesting on the heap in plain-recursion order | `Run::forward`, `Run::forward_at`, `Run::walk`, `Run::walk_at` | No `async` or compiler-written state machines (as for PRE-stack-explicit) | Each walk's frames as a sum type with an explicit stack |
| The scope of the current arm as the top of a `RefCell<Vec<Scope>>` over a `RefCell<&mut Scope>` of the caller, and the arms gathered in a `RefCell<Vec<Arm>>`, shared by all frames | `Run::scope`, `Run::inner`, `Run::outer`, `Run::out` | Mutation shared by frames (gap 1) | State threaded through the frame loop: a list of scopes and a list of arms |

## Entries from S22-hole-summaries (`crates/zedc-preimage/src/preimage.rs`)

- No new gap. `Walk::pa_select` joins stretches with a let chain `if let Some(last) = slices.last_mut() && ..` (as `extend::decide_defined`) and mutates the last slice in place through `last_mut`, a `match` on the list's end at the port; `no_input_between` uses `slice::partition_point` (as `docs::check`) and `Option::is_none_or` (as `repair`).
- `preimage::CLASS_READS`, read and reset by a test through `class_domain_reads`, is a `thread_local!` `Cell<u64>` counter, the gap of row `preimage::EXACT` above (the count returned with the answer at the port); `meets` uses `partition_point` as `no_input_between`.

## Entries from S22-fwd-holes (`crates/zedc-preimage/src/shared_ints.rs`, `preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A shared node (`Rc<Node>`) whose pieces are filled in once when first read (`OnceCell`), and whose recipe is taken out at that time (`RefCell<Option<Made>>`) | `shared_ints::Ints`, `Ints::set`, `Ints::list` | Mutation of a shared value, a cache filled in place (as `Rec` and `Shown`) | A persistent node that holds its recipe, listed by the reader into a table keyed by the node, or the pieces carried with the value once listed |
| Keys made from addresses: `Rc::as_ptr` of an input's domain and `Ints::id`, the address of a node, with the entry holding the node so that the address is not reused; `Rc::ptr_eq` as a fast path of equality | `preimage::SharedInts`, `Tx::input_ints`, `Tx::forward_ints`, `Ints::join`, `impl PartialEq for Ints` | Identity of values (as the `ptr_eq` rows above) | Numbered nodes: each set made gets a number from the run, and the tables are keyed by numbers |
| `impl Drop for Node` with a work list that unwraps each node held once (`Rc::try_unwrap`), so that dropping a chain of `k` levels does not recurse | `shared_ints::Node` | None | Removed: the runtime frees values, and must free a long chain without recursion itself (as `check::Origin`) |
| `thread_local!` empty set shared by every value with no integer; `thread_local!` `Cell<u64>` counter `FORWARD_PIECES`, read and reset by a test through `forward_pieces` | `Ints::empty`, `preimage::count_forward` | Thread-local state (the gap of `preimage::EXACT` and `CLASS_READS` above) | A constant empty set; the count returned with the answer |
| `std::mem::Discriminant<Op>` in a key | `preimage::OpKey` | None | The operator's tag as a value of an enumeration without payload |

## Entries from TY-sub-stack (`crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `async fn`s awaited in their caller's frame, with a new heap frame (`Stack::call`, `Deep`) at each function or tuple compared, so the comparison of function types keeps its nesting on the heap in plain-recursion order with its short-circuits | `Comparing::sub_in`, `Comparing::fits`, `Comparing::rows`, `accepts`, `fits_in`, `every_arrow_fits`, `arrow_fits`, `result_within`, `covered`, `part_of`, `met`, `meet_within`, `refused_cover` | No `async` or compiler-written state machines (as for PRE-stack-explicit and PA-let-stack) | The frames as a sum type with an explicit stack |
| The comparison's state (`Cx`: names made, rigid variables, functions read as variables) in a `RefCell` shared by all frames, borrowed one statement at a time and never across an `await` | `Comparing::cx`, `Cx::open` | Mutation shared by frames (gap 1) | State threaded through the frame loop |
| `macro_rules! comparing` that moves a `&mut Cx` into a `RefCell`, runs a body on a new stack and moves it back | `Ty::sub`, `Ty::sub_with`, `Ty::diff_in`, `fits_sig`, `fits_sig_with`, `why_unfit_in`, `within` and the test `index_keeps` | No macros | A function taking the body as a closure over the comparison |

## Entries from PA-let-narrow (`crates/zedc-check/src/check/walk.rs`, `mod.rs`, `crates/zedc-preimage/src/preimage.rs`, `product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The inputs of a summary in a persistent `imbl::OrdMap`, merged by `union`, which puts the smaller map into the larger and shares the rest | `Summarized::inputs`, `Ck::summarize_value` | Shared structure of persistent maps; Zed's maps are values, but a union that costs the smaller side is not specified | A map union of cost `O(m log n)` for the smaller side `m`, or a table of inputs keyed by binder |
| The type of each parameter at each binder bound under a narrowing, in a `HashMap` keyed by `(binder, parameter)`, and a counter of narrowings in place | `Ck::narrowed_at`, `Ck::unnarrowed`, `Ck::narrowings`, `Ck::param_type` | Mutation of the checker state | A field of each binder's record, written when it is bound |

## Entries from PA-let-multi (`crates/zedc-check/src/check/walk.rs`, `crates/zedc-preimage/src/preimage.rs`, `product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The domain of each input passed as a borrowed closure, `&dyn Fn(&Arc<str>) -> Option<&IntervalSet>`, with two lifetimes (`Dom<'f, 'd>`) | `Sep::add`, `Sep::add_pa`, `Sep::take_bounds`, `LetPa::sum`, `LetPa::form` | Borrowed trait objects and lifetimes; Zed passes a function value | A function argument, or the map of inputs itself |
| A running total kept beside a persistent map and updated as entries are put in and taken out, with counts of infinite ends | `Sep::tot`, `Tot::put`, `Sep::shift` (was `Sep::bounds_over`) | None beyond a record field updated with the map | The same record |

## Entries from PA-let-narrow-many (`crates/zedc-check/src/check/images.rs`, `walk.rs`, `mod.rs`, `arms.rs`, `crates/zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A persistent treap of `Rc` nodes, each holding the sum of its subtree, updated by split and join that copy one path | `images::Tree`, `images::set`, `split`, `without`, `join` | Shared immutable nodes and reference counts; Zed's values are immutable, but a tree with a monoid sum per node is not in the standard library | A persistent ordered map with a sum per subtree (a finger tree or a weight-balanced tree with a monoid annotation) |
| The keys where two persistent maps differ, by `imbl`'s `diff`, which skips subtrees the two share by pointer | `images::updated`, `LetPa::changed_since` | Pointer equality of shared subtrees; Zed has no identity on values | A diff of persistent maps that compares shared nodes by identity in the runtime, or a log of the keys changed since a version |
| A priority from the bytes of a name, FNV-1a mixed by splitmix64, with wrapping arithmetic | `images::prio` | Wrapping `u64` multiplication | `u64` words with wrapping operations (step L7.4c) |

## Entries from LOAD-disj-residue (`crates/zedc-presburger/src/presburger/extend.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An explicit stack of `enum Step { Split, And(usize, Vec<Formula>), Or(usize) }` whose results go on a second `Vec` and are taken back with `split_off` | `extend::project` | Mutation (gap 11) | A fold over a work list returning the stack of results, or recursion where the port has deep stacks |
| Union-find over atom indices in a `Vec<usize>` with path halving in place (`root(&mut up, a)`) | `extend::split`, `Face::of` | Mutation (gap 11) | A persistent map from index to parent, or the union-find of the stdlib catalog of step L2.11 |
| `Formula::into_parts()` and `Formula::Con(ref c) => c.clone()`, since `Formula` implements `Drop` and its parts cannot be moved out by a pattern | `extend::projected`, `extend::split` | Moves out of `Drop` types; Zed values are shared | A plain `match` binding the parts |
| A `HashSet<Atom>` per part merged small into large inside a fold that also inserts into a captured set, and `HashMap::entry(..).or_insert(..)` counters per atom | `extend::joined`, `extend::split` | Mutation (gap 11) | A fold returning the set or map with the result |
| A local `#[derive(PartialEq, Eq, Hash)] struct Congruence` turned into a `Con` key with a placeholder atom `Atom::Product(Aux(u32::MAX), Aux(u32::MAX))` | `Congruence::key`, `extend::clause_key` | None | A record or union value used as the key directly |
| `Model` (`HashMap<Atom, Int>`) filled in place by `solved` before a check | `extend::solved`, `extend::met` | Mutation (gap 11) | `solved` returns the extended map |

## Entries from LOAD-bound-holes (`crates/zedc-presburger/src/presburger/extend.rs`, `extend/holes.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A persistent treap of `Option<Arc<Node>>` whose `split` and `join` copy the path they walk, shared between faces by `Arc` clone | `holes::Holes`, `holes::split`, `holes::join` | None (Zed values are shared and immutable) | A persistent ordered map from the stdlib catalog of step L2.11, or the same treap as a recursive union value |
| A union-find with offsets in a `Vec<(Int, usize, Int)>` (each atom equal to `s` times its parent plus `d`), each path compressed in place by `find(&mut up, i)` | `extend::unit_classes` | Mutation (gap 11) | A persistent map from index to `(s, parent, d)` returned by `find`, or the union-find of the stdlib catalog of step L2.11 |

## Entries from LOAD-holes-mod (`crates/zedc-presburger/src/presburger/extend.rs`, `extend/residues.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `BTreeMap<Atom, Line>` of per-class bounds, holes and residues filled through `entry(..).or_insert_with` and `&mut Line`, the holes swapped out by `std::mem::replace` and the residues by `std::mem::take` | `residues::Lines::line`, `Lines::cut`, `Lines::keep`, `residues::read` | Mutation (gap 11) | A fold over the conjuncts returning a persistent map from class root to its line |
| A work list over the top-level equalities with a `HashMap<&Atom, Vec<usize>>` index and a `Vec` of unknown-atom counts decremented in place | `extend::fixed` | Mutation (gap 11) | A fold over a work list carrying the map of fixed values and the counts as persistent maps |
| A `HashSet` of residue keys filled inside a `filter` closure (`kept_in.insert`) | `extend::clauses_once` | Mutation (gap 11); a closure capturing state by `&mut` | A fold over the clauses carrying the set of keys seen |

## Entries from LOAD-extend-refuses (`crates/zedc-presburger/src/presburger/extend.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Union-find over atoms in a `HashMap<Atom, (Int, Option<Atom>, Int)>` (`a == k·b + c`) with path compression through `&mut self` | `Bound::bind`, `Bound::resolve`, `Bound::back` | Mutation (gap 11) | A persistent map from atom to its binding, threaded through `of` and returned, or the union-find of the stdlib catalog of step L2.11 |
| An iterative post-order walk over the divisions' owners on a `Vec` of `(usize, btree_map::Iter<Atom, Int>)` frames, with a `Vec<bool>` visited set | `Bound::merge_divisions` | Mutation (gap 11); a borrowed iterator kept in a stack frame | A fold over a work list carrying the visited set, or plain recursion once Zed's lowering manages the stack (PRE-stack decision (b)) |
| `HashMap::entry` on the `(Lin, Int)` key of a division, binding the second quotient and remainder on `Entry::Occupied` | `Bound::merge_divisions` | Mutation (gap 11) | A map lookup and an insert returning the new map |
| `Point` (`HashMap<Atom, Int>`) filled in place with the replaced atoms' values | `Bound::back`, `extend::point` | Mutation (gap 11) | `back` returns the extended map |

## Entries from TY-write-stack (`crates/zedc-check/src/check/mod.rs`, `crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A post-order walk of a written type on a `Vec` of steps (`enum Step<'a>` borrowing the type's nodes) and a `Vec` of values, the parts of each node taken off the value stack with `split_off`, `drain` and `truncate` | `Denote::ty`, `Denote::enter`, `Denote::make`, `and` | Borrowed references with a lifetime in a sum type; mutation of growable vectors (gap 11) | A fold over the type with the step stack as a list value, or plain recursion once Zed's lowering manages the stack (PRE-stack decision (b)) |
| `impl Drop for Sig` that moves its fields out with `std::mem::take` and drops the `Arc`s whose count is 1 in a loop (`Arc::into_inner`) | `Drop for Sig`, `Sig::take_parts`, `drop_types` | No destructors and no reference counts in Zed's surface; the drop of a deep value is the runtime's | The runtime frees nested values without recursion; nothing at the port |
| Values worked out at first use in `OnceLock`s, filled for the held signatures first by a post-order walk with an explicit stack and a `HashSet` of `*const Sig` as the visited set | `Sig::facts`, `Sig::digest`, `Sig::held_without` | Interior mutation of a shared value; identity by pointer | A memo keyed by the signature's identity in the runtime, or the facts made when the signature is built |

## Entries from PA-walk-multi (`crates/zedc-preimage/src/product.rs`, `images.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A cache of the last read of each summary, shared by the copies of a scope through `Arc<Mutex<HashMap<..>>>`, written from a `&self` method | `product::Reads`, `Scope::holds` | Interior mutability behind a shared reference; Zed has none, and a scope is a value | The walk's state threaded explicitly: `holds` takes and returns the map of reads, or the walk keeps it beside the scope it passes down |
| `images.rs` moved from `zedc-check` to `zedc-preimage`, its nodes `Arc` rather than `Rc` since a `Scope` is `Send + Sync`, and `Read<S>` generic over what the caller keeps beside the tree | `images::Read`, `images::Node` | Atomic reference counts and a generic struct; the PA-let-narrow-many entries above still apply | As above: a persistent ordered map with a sum per subtree; a record type with a type parameter |

## Entries from LOAD-call-relation (`crates/zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A struct borrowing `&Tr` that holds memo maps (`HashMap<Atom, Option<Lin>>`, the representatives by `(Lin, i128)`) filled through `&mut self` methods | `preimage::Normal` | Borrowed references in a record; mutation (gap 11) | A record of map values threaded through the writing of the rows, `Tr` passed alongside |
| A post-order walk on a `Vec<(Atom, bool)>` stack, the bool marking the second visit, with a `HashSet<Atom>` of open atoms to cut a binding that reaches itself | `Normal::atom` | Mutation (gap 11) | A fold over a work list carrying the memo and the open set, or plain recursion once Zed's lowering manages the stack (PRE-stack decision (b)) |
| A walk over auxiliary numbers on a `Vec<Lin>` work list with a `HashSet<u32>` visited set, leaving early with `?` on a definition of another kind | `preimage::value_projected` | Mutation (gap 11), Early exit (gap 12) | A fold over a work list ending in `#none` |
| A `&mut HashMap<u32, u32>` passed down a recursive writer so each pair is made once per call | `Tr::instance` | Mutation (gap 11) | The map returned with the written term |
| A `Projection` record of `Arc<[Con]>`, `Option<Lin>` and `Arc<HashMap<u32, (Lin, i128)>>`, cloned out of the memo by reference count | `Projection`, `Walk::projection`, `Walk::value_projection` | Shared ownership by reference count | A plain record value; Zed values are shared |

## Entries from GROUP-same (`crates/zed-kernel/src/types/rec.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap<(u64, u32), Arc<Node>>` from a digest and a probe number to the first node of each shape, filled while the tree is built, its `Entry` held across the building of the node and filled from the `Vacant` entry; the probe loop runs on over the shapes of one digest | `Numbering`, `Node::of` | Mutation; identity of a node shared by reference count (gap 1) | The table as a map in the state receiver of the post-order build; the class is a number held in the node, so no identity is needed beyond it |

## Entries from HEAP-fresh-dag (`zed-rt/src/heap.rs`, `zedc-zir/src/zir/memory.rs`, `zed-kernel/src/value.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap` memo filled during an explicit-stack walk of a value, keyed by `SharedParts<'v>` (the sequence's id and, for an atom, a borrowed `&str` name and the field names' id), whose values are cell words or numbers | `Heap::fresh`, `Machine::tree` | Mutation; Identity (Gap 1) for the sequence id | A map from the sequence's identity to the cell threaded through the walk's state; the identity is what the runtime exposes for a shared sequence |
| `Arc::strong_count` to tell a sequence held once from a shared one (`Items::is_shared`, read by `Value::shared_parts`) | `Value::shared_parts` | Identity (Gap 1) | The runtime's reference count of the sequence, or a memo entry for every sequence at a constant cost |

## Entries from ST-holes-many (`crates/zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A labeled `'round: loop` around a Dijkstra search on a `BinaryHeap<Reverse<..>>`, restarted with `continue 'round` from inside the heap loop when a cycle of weight 0 is tied, and left with `return` on a negative cycle (moved here from `Scope::repair`) | `product::put_in`, called by `Scope::repair` and `Scope::raise` | Mutation (gap 11), Early exit (gap 12) | A recursive function per round over a persistent heap, its result a sum of "put in", "tie these edges and go again" and "negative cycle" |
| A `BTreeMap` of bounds filled at first read through a closure taking it as `&mut`, so the search reads each name's ends once | `Scope::bound_pass` (`read`, `label`) | Mutation (gap 11) | The map threaded through the search's fold and returned with each read |

## Entries from PREIMAGE-and-chain (`crates/zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `hash_map::Entry` matched as occupied or vacant, inserting into a second `HashSet<Tid>` (`Terms::shared`) on the occupied side while numbering a term | `Terms::id` | Mutation (gap 11) | A lookup in the map of seen terms, then either the set with the term added or the map with the new number, both returned |
| A local `enum Step` work list (operand, memo read, close at a `Mark`) popped in a `while let` loop inside an `async fn`, a closure giving each inner node's steps | `Walk::chain` | Mutation (gap 11), Early exit (gap 12) | A fold over the work list in a state receiver, ending in `#none` at the first operand with no formula |

## Entries from PREIMAGE-ref-tests (`zedc-preimage/src/lib.rs`, `zedc/src/store/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A cargo feature, `preimage-ref`, that adds a whole module and its re-export, off in a release build; every package that builds the zedc and zedc-preimage dylibs asks for it, so their copies are not rebuilt | `zedc_preimage::preimage_ref`, `zedc::store::preimage_ref` under `#[cfg(feature = "preimage-ref")]` | No conditional compilation | A unit of its own that only the test units import, so the release build does not hold it; no build mode needed |

## Entries from EMPTY-overlap-chain (`crates/zed-kernel/src/types/empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap<u64, Known>` memo keyed by a part node's id, filled during an explicit-stack walk whose entries carry a "children done" flag, each node's components held as an `Rc<[usize]>` shared with its `!` parent | `Choices::decide` | Mutation (gap 11); Identity (gap 1) for the node id | A map from the node's identity threaded through the walk's fold; the components as an immutable shared sequence |
| A `HashMap<usize, Pick>` of the choices along a decision list, each `Pick` holding a `HashSet` of refused cells, updated in place block by block and read hypothetically before each update (`Picks::fits`) | `Choices::list`, `Picks::fix` | Mutation (gap 11) | Persistent maps threaded through the fold over the blocks |
| A `&dyn Fn(&Row) -> (usize, usize)` closure over the region's index, read for every atom | `Choices::at`, `Searching::one_pass` | none | A function value |

## Entries from EMPTY-overlap-fast (`crates/zed-kernel/src/types/empty.rs`, `types/bdd.rs`, `types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A top-down walk on an explicit stack of `(node, wanted value)` that fills a `HashMap` of visited node ids and a `Vec<Option<Choice>>` of the choice per component in place, left with `Err(component)` through `?` | `Choices::witness`, `Choices::extract`, `Choices::complete` | Mutation (gap 11), early exit (gap 12) | A fold over the walk's work list threading a persistent map and a persistent sequence, its result a sum of the choices and the refused component |
| `Option<Option<Vec<Type>>>`: none when the pass does not apply, `Some(None)` when it proves the box empty, `Some(Some(row))` with a value | `Searching::one_pass_row` and the tuple candidate loop of `Searching::rep` | None | A sum of three named cases |
| `sort_by_key` with `std::cmp::Reverse` on a tuple key, and type aliases for tuples (`Point`, `MeetPoint`, `Block`) | `by_x_descending`, `lists`, `list_parity`, `parities`, `meet` | None | A sort taking a comparison function; records with named fields |
| A refusal message built by `format!` with `return` from inside a `match` arm, the other arms giving a `&'static str` turned into a `String` after it | `Refusal::message` | Early exit (gap 12) | Each arm gives the text; the one with the component builds it by interpolation |
| Two diagrams compared by the ids of their first cells, fields of an `Arc` | `Connect::same_as_not` | Identity (gap 1) | The node's identity from the hash-consing table |

## Entries from PREIMAGE-or-chain (`crates/zedc-preimage/src/preimage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `#[cfg(test)]` `thread_local!` `Cell<bool>` that turns off the reading of `if g { true } else { b }` as `g \|\| b`, read by a function that is `false` outside tests | `OR_IF_AS_IF`, `or_if_as_if` | Not ported | Tests only; the port's test would pass the reading as a parameter of the walk |

## Entries from ST-eqs-cubic (`crates/zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `?` on `Option` from inside a `for` loop and after calls, leaving with `None` when a conjunct is not of the route's form or a projection refuses, so the caller takes the whole projection | `Scope::project_by_pendants`, `Scope::pendant`, `one_disjunction` | Early exit (gap 12) | A fold over the conjuncts whose result is an option, matched once after it |
| A `BTreeMap` entry met in place (`*d = d.meet(..)` through `entry().or_insert_with`), and a counter map filled by `*count.entry(n).or_default() += 1` | `Scope::project_by_pendants` (`forms`, `count`) | Mutation (gap 11) | A fold building a persistent map, each step returning the map with the entry replaced |

## Entries from PA-letpre-linear (`crates/zedc-preimage/src/preimage.rs`, `images.rs`, `product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A trait object `Arc<dyn SummaryRead>` in `LetIn`, so that `preimage.rs` reads the tree of `images.rs` without importing it, and an `Rc<[Arc<dyn SummaryRead>]>` of them in the transfer's context | `preimage::SummaryRead`, `LetIn::read`, `Cx::reads`, `images::TermRead` | Trait objects and reference counts | A record of functions (`vars`, `ints`, `total`, `visit`) or the read passed as a value of a known type once the two modules may share it |
| `images::Tree<L>` and `Read<S, P, L>` generic over the leaf through a trait `Sum` (`zero`, `plus`), with a default type parameter | `images::Sum`, `images::Tree`, `images::updated`, `images::fresh`, `images::visit` | A trait with an associated constructor; default type parameters | A persistent ordered map parameterized by a monoid record (`zero`, `plus`) |
| A walk of the tree pruned by a `&dyn Fn` predicate on the subtree sums that calls a `&mut dyn FnMut` callback, which records an early end in a captured `Option<Option<Res>>` and stops the walk by returning `false` | `images::visit`, `Tx::invert_read` | Mutation of captured state (gap 11), Early exit (gap 12) | A fold over the tree carrying the box and an ending value, pruning by the sums |
| A second cache of the reads of each summary beside the first, `Arc<Mutex<HashMap<u64, ..>>>` written from `&self` | `product::Reads`, `Scope::term_read` | Interior mutability behind a shared reference, as PA-walk-multi's | As PA-walk-multi's: the map of reads threaded through the walk |
| A flag in the run (`Run::marked`) set the first time the landmarks are read, to add the ends of the reads' inputs lazily through `&mut self` | `Tx::marks` | Mutation (gap 11) | The landmarks computed on demand and returned with the run's state |
| A cache flag whose `PartialEq` always holds, as `Reduced`'s, set when a scope no state reaches has emptied its names, so that its copies are shown without emptying them again | `product::Emptied`, `Scope::empty_if_bottom` | None | A field left out of the comparison the port writes for `Scope`, as `Reduced` |

## Entries from LIST-box-overlap (`zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `imbl::OrdSet::diff` advanced in turn with an iterator over the smaller set inside a `loop`, the first to finish used, its `DiffItem::Add` items collected into a `Vec` | `Lits::union` | Persistent sets (none in the Zed prelude yet) | The library's persistent set (L2.11) with a diff that skips shared nodes; the two walks as two lazy sequences stepped together |
| Per column, a `HashMap<u64, Vec<usize>>` grouping boxes by a wrapping sum of hashes, groups as `Vec<Vec<usize>>`, a box's row copied with `to_vec` and one column replaced; a `HashMap<Vec<Type>, Option<Type>>` of unions filled by `entry().or_insert_with_key` | `merge_boxes`, `union_column` | Mutation (gap 2: memo tables, work sets) | A fold over the columns with the grouping map in its state; the union memo threaded through `finite_order` |
| A first pass over the graph's nodes keeping per node a representative and a polarity in a `Vec<(usize, bool)>`, with `HashMap`s keyed by a list's blocks and by an exclusive or's two operands, rewriting nodes in place; a reachability pass marking a `Vec<bool>` from the last node down | `Graph::parities`, `Graph::merged` | Mutation (gap 2) | A fold over the nodes in topological order producing a new node list |
| `Overlay` of changed values and count changes in `HashMap`s, kept per class in a `HashMap<Vec<(usize, bool)>, Option<Overlay>>` filled the second time a key recurs, and a `HashMap<Vec<(usize, bool)>, bool>` of results; a `Vec<usize>` of per-row change counts sorting the changed rows | `RowIndex::holds`, `Class`, `Graph::apply` | Mutation (gap 2: memo tables) | The memo maps in the class's state, threaded through the checks |

## Entries from STAGE-stub-fast (`crates/zed-kernel/src/eval.rs`, `crates/zedc-stage/src/stage.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Two more default methods on the `Lookup` trait, `calls` (whether a port is called rather than read) and `function` (the key value of a function argument, from its body), asked by the evaluator through the trait object | `zed_kernel::eval::Lookup::calls`, `Lookup::function`, `Machine::call_port`, `Port::calls`, `Port::function` | Traits (`interface` is L10; `dyn Lookup` becomes a port, catalog above) | Two more fields of the port's record, with the default values given where the record is built |
| An `AtomicBool` in the run, set from `&self` inside `Lookup::get` when a call took a function argument, read once after the run | `Run::function`, `Port::get`, `Mixer::eval` | Mutation (gap 11) | The run returns, beside its value and its list of calls, whether a call took a function argument |
| An `Arc<BTreeMap<Arc<str>, Arc<Stub>>>` of every stub of a run, shared by each port so a token argument resolves to its stub | `Port::ports`, `Port::with`, `run_with` | None | A map value passed to each port's record |

## Entries from EMPTY-morphism-diff-cost (`crates/zed-kernel/src/types.rs`, `crates/zed-kernel/src/types/bdd/set.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A per-thread `HashMap` with `BuildHasherDefault<KeyHasher>` (the digest as the hash), each bucket a `Vec<Weak<Set>>`; a set removes itself from its bucket when dropped | `bdd::set::SetTable`, `Slot`, `make`, `Drop for Set`, `Tables::new` | Weak references and drop hooks (as in K66 and K70) | A hash map keyed by digest in the per-thread store, entries removed when the set is freed |
| Pointer identity of a thread-local `Type` read through `LocalKey::with(\|k\| Arc::ptr_eq(..))` to recognize the empty and top types | `Type::zip_at_once`, `Morphism::cmp` | Identity (equality shortcuts) and thread-locals | A tag on the node for the empty and top types, compared as values |

## Entries from MINMAX-stack (`crates/zedc-check/src/check/mod.rs`, `walk.rs`, `crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A post-order walk of a type on a `Vec` of steps (`enum Step` owning the types) and a `Vec` of results, the joined components of each type taken off with `split_off`, and a `HashMap<Ty, Ty>` of the types already joined, keyed by the type's value through its cached digest | `one_shape_per_length` | Mutation of growable vectors and of a map (gap 11); hashing by a cached digest (gap 1) | A fold with the step stack and the map as values, or plain recursion once Zed's lowering manages the stack (PRE-stack decision (b)); the map keyed by the type's content digest |
| `Sig::word: Option<Arc<str>>`, the prelude word a signature is, included in its digest, so the checker tells `min` from `+` of the same arrows wherever the function value goes | `Sig`, `word_sig`, `Ck::apply` | None | A field of the signature's record |

## Entries from MINMAX-sig-word (`crates/zedc-check/src/check/walk.rs`, `crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A new variant of the enum `NeedKind` with named fields (`Order { what, word, other, first }`), matched with `..` rest patterns in `tys`, `every_ty`, `into_tys` and `map_tys` | `ty.rs`, `Ck::meet` | None: Zed has sums of records and record patterns with a rest | A member of the need sum |
| A fixed-size array `[bool; 2]` updated by index inside a loop over `[(a, b), (b, a)].into_iter().enumerate()` | `Ck::min_max_tuples` | Mutation of an array element (gap 11) | A pair of booleans returned by a fold over the two sides |
| A closure capturing another closure (`only` calls `rest`) | `Ck::min_max_tuples` | None | Two local functions |
| A `HashMap<(Arc<str>, bool, Span), usize>` field indexing a `Vec` of uses, kept in step with it by `std::mem::take` and a swap at a class merge, and an `if let ... && let Some(&i) = map.get(..)` let chain | `Class::orders`, `Ck::need`, `Ck::merge` | None: a keyed morphism of positions, rebuilt by a fold at the merge | A morphism from (word, side, site) to the use's position |
| An `Option<(usize, OrderKey)>` field naming the class and key of the use whose result a class is, cleared at a merge and at resolve, read by an `if let Some(..) = ...clone() && ...` let chain | `Class::order_of`, `Ck::order_given` | None: an optional field, rebuilt in the class record | The record field `orderOf` of type `?(i64, OrderKey)` |

## Entries from EMPTY-morphism-next (`crates/zed-kernel/src/types.rs`, `crates/zed-kernel/src/types/empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `HashMap`/`HashSet` keyed by `Type` with `BuildHasherDefault<KeyHasher>`, in `Search` fields and in thread-locals built in a `const` block (`const { RefCell::new(..) }`) | `empty.rs` `ByType`, `TypeSet`, `MEMO`, `VERDICTS`, `DECIDING`, `SHARED`, `Search`; `types.rs` `Equal` in `order` | Interfaces (L10) and thread-locals, as in the `list::KeyHasher` entry | A family keyed by the type's digest in the per-thread store, the hash function given as a parameter |
| A memo keyed by the operands' node addresses that holds the operands, so no address is reused while the entry lives | `Searching::cut` (`cuts`), as `settles` before it | Identity (node addresses) | A key by node id in the per-thread store |

## Entries from CLASS-atoms (`crates/zedc-resolve/src/resolve.rs`, `crates/zedc-check/src/check/mod.rs`, `walk.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Resolver::flow`: a walk of an expression on a `Vec<&Expr>` stack, pushing each recorded use onto `Resolution::flows` | `flow`, `declare` | Mutation of growable vectors (gap 11) | A fold over the expression with the stack and the list of uses as values, or plain recursion once Zed's lowering manages the stack (PRE-stack decision (b)) |
| `check::handled`: an iterative Tarjan over edges in compressed rows (`from`, `to` index vectors), with `index`, `low`, `on_stack` vectors and an explicit call stack of `(node, next edge)` | `handled` | Mutation of growable vectors in place (gap 11); indexes as node names | Arrays built once by a fold, the component walk as a fold whose state holds the stacks; the same O(B + R + E) |
| `Resolver::else_regions: HashMap<Span, usize>`, one region per `else` found by its span | `else_region` | Hashing by a span (gap 1) | A map keyed by the span's two offsets |

## Entries from TEXT-cmp-fast (`crates/zed-kernel/src/text.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The iterator over the blocks as a private `enum` of two states: one block held as `Option<&str>` and given once by `Option::take`, or a tree's walk on its own `Vec<&Text>` stack | `Chunks`, `Walk`, `Text::chunks` | References into values (Rust lifetimes) and early exit (gap 12), as the WRITE-prefix-scale row above | A list of the blocks produced lazily, one block a list of one; the walk as before |
| Two blocks compared as byte slices, `<[u8] as Ord>::cmp` (one `memcmp` and the lengths) | `compare`, `Text::as_flat` | None | `compare` of two strings of one block is the prelude's string order on the two values; no walk is built |

## Entries from ROW-eq-deep (`crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A node's address (`Arc::as_ptr` cast to `*const ()`) as a key of a `HashMap` with a written `Hasher` (`AddressHasher`), sound only while both operands are borrowed | `Same::root`, `Same::assumed`, `AddressHasher` | Identity (equality shortcuts) | A node id given when the node is made, or the interned node's own key |
| `Arc::strong_count` read to tell a shared node from one with a single owner, so only shared nodes are recorded, less the references the rows and shapes on the path keep to a function (`Above`) | `Same::alike_rows`, `Same::alike_shapes`, `Same::shared_sigs`, `Above` | Identity and reference counts | A sharing flag set when a node gains a second owner, or record every node and accept the table's cost |
| A union-find in one `HashMap` from address to (parent, size) mutated in place (union by size, path halving), an explicit stack of borrowed pairs `Vec<(&Ty, &Ty)>`, and an `Option<Same>` made at the first pair that is not one node (`Lazy`) | `Same`, `Lazy` | Mutation (gap 11) and borrowed references | A persistent union-find or an array threaded through the loop's state, and a list as the stack |

## Entries from NUM-print-fast (`crates/zed-kernel/src/num/fast.rs`, `crates/zedc-int/src/int.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Re-measure: two crossovers to num-bigint's printing, set from timings of the Rust code on 2026-11-08, digits identical | `PRINT_HANDOFF` (496 words, flat from 248 to 992; load 23 to 28), `PRINT_WHOLE` (60,000 words, ratio 1.01 at 58,134 and 0.93 at 62,287; load 6 to 5) | None | Measure each again on the Zed code against Zed's own printing, by the procedure in COMPLEXITY.md section "Crossovers" (K81 has the curves); a cheaper Newton step or powers built as `5^K` shifted would lower `PRINT_WHOLE`; drop a crossover where one method is never slower |
| Leaf sizes that differ between the unit tests and the build (`#[cfg(test)]` constants set to 1), so the unit tests split small numbers | `PRINT_HANDOFF`, `PRINT_WHOLE` | No conditional compilation | A parameter of the routine, or a build mode of the unit, as in the entries from SLABS-count and NUM-subquad |
| Each level's power and reciprocal transformed once per prime and kept as `[Vec<u64>; 3]` spectra, reused by every division at that level; cyclic products on these spectra | `Level`, `Printer`, `cyclic_product`, `Field::spectrum`, `Field::cyclic` | Machine integers, Mutation (gap 11) | The arithmetic of `int` itself, which belongs to the runtime (row "What stays in Rust"), as for the transforms of NUM-subquad; a level is a record of the power and its spectra |
| The digits appended by a recursion to one `String` reserved once from a bound on the digits (`String::with_capacity`, `&mut String`) | `to_decimal`, `Printer::write` | Mutation (gap 11) | A text built by joining the halves' texts (a rope, as `Text`), or a buffer threaded through the recursion |
| Explicit `drop` of an operand once its last use is past, to lower the peak heap | `to_decimal`, `Printer::write` | None | The last use frees the value; no statement needed |

## Entries from VARIANT-sync (`tests/src/fences.rs`, `tests/steps/l01_07_fences/variants.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A slice pattern with `else` (`let [live] = live[..] else { … continue }`) to require exactly one live ✗ line | `disagreements` | None | A `match` on the sequence's length |
| A `Vec<bool>` of used changes set by index as fixtures agree, and a `HashSet` of agreed places filled in the loop | `disagreements` | Mutation | A fold over the fixtures whose accumulator holds the used changes and agreed places as sets |

## Entries from NARROW-hub-seed-edges (`zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The edges that can lower a seed gathered into a `Vec<Edge>`, then the least bound per seed kept in a `BTreeMap` updated in place, then the labels and the heap updated in place for each seed lowered | `Scope::bound_pass` | Mutation of growable vectors and maps (gap 11) | A fold over the edges into a map from seed to least bound, then a fold over that map that returns the labels, the names moved and the starting heap |

## Entries from KEY-written-addr (`crates/zedc-preimage/src/address.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A node's id, `Shared::id`, as the key of `HashMap`s that hold each shared part's height and free names, and its canonical form for each binding of its free names; a pair of ids as the key of the parts compared equal | `Canon::info`, `Canon::arms`, `Canon::done`, `order` | Identity (gap 1) | A node id given when the node is made, as gap 1 decides; the maps as persistent maps keyed by it |
| Two walks on explicit stacks of enums that borrow the term (`Read`, `Step`, `Pair`), with the results of the parts on a second stack drained at each exit | `Canon::read`, `Canon::canonical`, `order` | References into values (Rust lifetimes) and mutation (gap 11) | A fold over the term with the stacks as lists threaded through the loop's state; the borrowed parts as the values themselves |
| A digest built one 64-bit word at a time with wrapping multiplication and shifts (splitmix64's finalizer) | `Digest` | None: the prelude's 64-bit words wrap (gap 4, built) | The same words with `u64` wrapping operators |
| `Ord` written by hand for a key type (digest, then a walk of the two terms), so a persistent map orders its keys by it | `impl Ord for Address` | None | A comparison function the map takes, or the key's `compare` member |

## Entries from C2-chain (`crates/zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap<usize, Option<(Model, Option<HashMap<Atom, IntervalSet>>)>>` (since C2-chain-general `HashMap<usize, Option<HashMap<Atom, Ends>>>`) filled for a part the first time one of its factors is reached, through `entry` with a fallible computation in the `Vacant` arm (`?` returns a refusal from inside the match) | `products` | Lazy cells (gap 3), Mutation (gap 11) | Each part's point and hulls computed for all parts that hold a factor before the loop over factors, as a fold over the parts that stops at the first refusal |
| (Removed by C2-chain-general: `products` reads the bounds from the map and no longer computes a hull in an arm.) `Option::insert` into a local declared before the match, so that an arm can return a reference to a hull computed in that arm alongside references into the map | `products` | Lazy cells (gap 3) | The arms return the hull by value; the map's hulls are shared values in Zed, so no copy is made |

## Entries from CHK-need-bound (`crates/zedc-check/src/check/walk.rs`, `check/mod.rs`, `crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A newtype `Width(Value)` with a written `Hash` that hashes only a machine int and a derived `PartialEq`, so a key holding a value that is not `Hash` can be hashed | `ty::Width`, `IntDomain` | None: Zed hashes by value | The record field of type `?int`, hashed with the rest |
| A `HashMap<usize, Need>` from a parameter's binder to its one need, replaced when a smaller domain comes (`surface_cmp` of two widths), and drained by `remove` when the function's signature is made | `Ck::floors`, `floor_on`, `floors_into` | Mutation (gap 11) | A morphism from binder to need in the walk's state, folded over the uses and read once at the signature |
| A singly linked list of call links shared by `Arc` (`Via { at, text, next: Option<Arc<Via>> }`), walked by a `while let` into a `Vec` of notes inside a closure that runs only when an error is reported | `Ck::floors_at` | None: shared immutable lists | A list of links; the notes a map over it, made in the error branch |
| A `loop` over names bound to names with a visited `HashSet<usize>`, left by `return` | `Ck::open_param` | Early exit (gap 12), mutation (gap 11) | A recursive function over the binding facts with the visited set as an argument |

## Entries from RUNG2-carrier (`crates/zedc-types/src/ty.rs`, `zedc-elab/src/elab.rs`, `zedc-stage/src/defs.rs`, `zedc/src/front.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Option::is_some_and` on a lookup (`HashMap::get`, slice `get`) | `Sig::int_params`, `front::linear_questions` | None | a `match` on the lookup, the missing case `false` |
| A struct update, `Unit { int_params, ..Unit::default() }` | `elab::lower` | None | a record built with the named field and the others from the default |
| `return` from the closure passed to `work::stage`, to skip a function | `front::linear_questions` | None | an `if` around the closure's body |

## Entries from C2-chain-general (`crates/zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `Cow<'_, Con>`: a top-level constraint borrowed, or the negation of `t >= 0` built as `-t - 1 >= 0` and owned | `as_row`, `conjunct_bounds`, `part_bounds` | None: Zed values are shared | A function returning `?Con`, the constraint itself or the new one |
| A lookup passed as `impl Fn(&Atom) -> Option<&'a Ends>`, so that one function reads either one map or a local map that falls back to another | `row_bounds` | None: Zed has closures | A function argument `(Atom) -> ?Ends` |
| A `HashMap<Atom, Ends>` tightened in place by `entry(..).or_insert_with(..)` and two passes over the rows | `conjunct_bounds`, `meet_bound` | Mutation (gap 11) | A fold over the rows building a new map per pass |
| A `HashMap<Id, Option<HashMap<Atom, Ends>>>` memo of each shared disjunct, cloned out on each read | `disjunction_bounds` | Identity (gap 1), Shared tables (gap 2) | A memo keyed by the disjunct's structural key; the maps are shared values, so no copy |
| `Iterator::partition` of references into two `Vec<&Con>` | `part_bounds` | None | `partition` over a list |
| A `thread_local!` `Cell<u64>` counter of solver questions, read and reset by a public function for tests | `SIDES`, `hull_side`, `hull_sides_asked` | Mutation (gap 11), no thread-local state | The count returned with the result by `products`, or kept by the test harness's own instrumentation |
| Kahn's work list: a struct of `Vec`s (`at`, `late`, `left`, `queued`, `gone`, `valued`) updated in place by a method, a `Vec` (`ready`) used as a stack, and a closure reading rows by index | `propagate` (`Found::give`) | Mutation (gap 11) | A fold over the work list threading a record of persistent maps |
| Union-find with path halving, `parent[i] = parent[parent[i]]` in place | `clusters` (and `products`, as before) | Mutation (gap 11) | A persistent union-find (Conchon and Filliâtre 2007), O(log n) per step |
| One `Rc<Formula>` per cluster shared by every atom of the cluster in a map | `clusters`, `PartBounds::local` | None: Zed values are shared | A map from each atom to the cluster's formula |
| A `FnMut` closure that sets a captured `bool` (`loose`) while it computes a side | `products` (`side`) | Mutation (gap 11) | The side returned with a flag, folded with `or` |
| A label per node `Vec<Option<(Int, Option<usize>)>>` (distance and nearest factor, `None` where two are nearest) and a stage per node `Vec<u8>`, both updated in place while a `BinaryHeap` of `Reverse` pairs is drained, so a node is expanded at most twice | `Differences::search` | Mutation (gap 11) | A fold over a persistent priority queue threading persistent maps of labels and stages |

## Entries from PRES-mod-conjuncts (`zedc-preimage/src/preimage.rs`, `zedc-presburger/src/presburger.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `HashMap<BTreeMap<Atom, Int>, Int>` keyed by a term's variable part, updated in place through `entry().or_insert_with` to keep the nearest bound shown | `preimage::Shown::{above, below}` | Mutation | A map threaded through the fold over the chain's operands, each step returning the updated map |
| A closure capturing `self` and `p` that returns `Option<[Tid; 2]>` from a `match`, and a work list with a `HashSet` of visited nodes popped in a `while let` | `Walk::defined_chain` | Mutation | A recursive descent over the chain returning the operands and the visited set |
| `solve(..).ok()??`, two `?` on a `Result<Option<_>>` | `presburger::own_repair` | None | A `match` on the result |

## Entries from ATOM-payload-sub (`crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A memo `RefCell<HashMap<KType, KType>>` filled inside a `&self` method | `Forms::cut` | Mutation (gap 11) | `cut` takes and returns the memo with the result, or the forms are built in one pass that threads it |
| Atom names that start with a NUL (`"\0fn 3"`), names no program writes, as marks in a normal form | `mark`, `fields_mark`, `Forms::number_marks` | None | the same strings; the kernel needs no change |

## Entries from ENV-bounded-partial (`crates/zedc-types/src/ty.rs`, `crates/zedc-check/src/check/mod.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A closure taking `&dyn Fn(&Ty, &KType) -> bool`, called with two predicates | `Ck::taking` | Function values | a function with a function-typed parameter |
| `bool::then_some` building the `Option` of a struct of borrowed parts | `Sig::morphism` | None | `if … { … } else { #notFound }` |
| An enum of borrowed parts (`Morphism<'a>`) that lives only while printing | `Sig::morphism`, `Morphism::parts` | Lifetimes | a union of the two shapes, holding the types by value |

## Entries from ST-holes-moves (`crates/zedc-preimage/src/holes.rs`, `product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A union-find with offsets in two `Vec`s, `find` pointing every name of the path at the root in place | `holes::merge` (`find`) | Mutation (gap 11) | A persistent map from name to parent and offset, threaded through the merge's fold |
| Tarjan's search over the components with an explicit call stack of `(name, next edge)` pairs, its counters and stack in `Vec`s changed in place | `holes::components` | Mutation (gap 11) | A fold over the names with the index, low link and stack as persistent values, or a recursive function once the Zed lowering manages the stack |
| An ordered `BTreeMap` of pieces keyed by raw output and input, cut and flattened in place, with an offset added in O(1) | `holes::Map` (`insert`, `flatten`, `cap`, `snap`) | Mutation (gap 11) | A persistent ordered map returned by each step, the offset a field of the value |
| A Dijkstra search on a `BinaryHeap<Reverse<..>>` and a breadth-first search on a `VecDeque`, both filling `Vec`s of labels | `holes::Run::paths`, `holes::Run::hull` | Mutation (gap 11) | A recursive function over a persistent heap or queue, the labels a persistent map |
| `return Err(Stop::..)` and `?` out of the loops over components and cycles | `holes::Run::component`, `holes::greatest` | Early exit (gap 12) | A result value checked at each step of the fold |
| `self.raise(..)` changing the scope's potential, inside `Iterator::all`, which stops at the first `false` | `Scope::by_holes`, `Scope::project` | Mutation (gap 11), Early exit (gap 12) | A recursive function over the names that returns the new potential and stops on the first failed raise |

## Entries from ATOM-payload-unify (`crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| An `impl Iterator` built by `std::iter::from_fn` over a `BinaryHeap<Reverse<(usize, usize, usize)>>` it owns, a k-way merge | `Choices::merged` | Iterators, Mutation (gap 11) | a function that returns the merged list, or a heap threaded through a loop |
| `BTreeMap::entry` matched on `Occupied` and `Vacant` to claim a bucket once | `Comparing::search` | Mutation (gap 11) | a lookup, then an insert into the map returned |
| An enum constructor passed as a function (`point.map_or(k, ShapeKey::Point)`) | `Choices::new` | None | `if p is #some(v) { #Point(v) } else { k }` |
| A `#[cfg(test)]` `thread_local!` `Cell<bool>` that switches a search to the full scan | `SCAN_ALL`, `Comparing::search` | No test-only state | a parameter of the search, or a test build of the module |

## Entries from MSG-audit-front (`crates/zedc/src/main.rs`, `crates/zedc-base/src/rejection.rs`, `tests/src/lib.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::panic::set_hook` with a payload read by `downcast_ref::<&str>` and `downcast_ref::<String>` | `main.rs` `bug_report` | No panic hook and no dynamic downcast | a broken invariant is the member `#bug(message)` (author, S.1d); the driver prints `rejection::bug` for it |
| `macro_rules!` that expand to string literals inside `concat!` (`not_yet!`, `import_not_yet!`) | `tests/src/lib.rs` and the step tests | No macros | the texts are made by `rejection::not_yet` at run time, or written out |

## Entries from TY-diff-meet (`crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `HashMap::entry(..).or_default().push(..)` grouping tuples by length and arrangement, and `BTreeMap::entry(..).or_default().push(..)` filing them by key | `by_pattern`, `near_pairs` | Mutation (gap 11) | a fold that returns the map with the index added to the key's list |
| A `BTreeMap` keyed by `Vec<(&ShapeKey, Option<&Value>)>`, keys that borrow from the tuples' keys for the length of the call | `near_pairs` | None | keys of shared values; no lifetimes are written |
| `out[*l].extend(..)` into a `Vec<Vec<usize>>` made at its full length, then `sort_unstable` of each list in place | `near_pairs` | Mutation (gap 11) | a map from each left index to its sorted list, built by the fold |
| `std::mem::take(&mut out.tuples)` and a `Ty { tuples: .., ..bare.clone() }` per row, with an `Option<(&Ty, &Whole, &Arc<Filed>)>` passed down | `Comparing::diff`, `sub_near` | Mutation (gap 11) | the record with its tuples replaced, and an optional record argument |
| A `#[cfg(test)]` `thread_local!` `Cell<bool>` that switches the lookup to every pair of one length | `NEAR_ALL`, `near_pairs` | No test-only state | a parameter of the lookup, or a test build of the module |

## Entries from GROUP-admit (`tests/steps/l01_23_subtyping/admission_sweep.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `BTreeMap::entry` with `Entry::Vacant`/`Entry::Occupied` and `get_mut`, counting false rejections per arm in place | `sweep` | Mutation (gap 11) | a fold over the seeds that returns the map with the arm's record replaced |
| Destructuring assignment `(r.size, r.seed, r.group) = (n, seed, group)` into fields of a borrowed record | `sweep` | Mutation (gap 11) | a new record in the fold |
| A `&mut usize` counter threaded through a recursive walk to find the subterm at a preorder place | `replaced` | Mutation (gap 11) | the walk returns the place left with the new term |
| A closure argument `impl Fn(&[T]) -> bool` for the property shrinking keeps | `shrink` | None | a function parameter |

## Entries from SURFACE-cycle (`crates/zed-kernel/src/types/print.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `std::mem::replace(&mut entered[i], true)` as the test and the mark of a visited set in one step, and `Vec<Option<usize>>` heights written in place as the explicit stack leaves each node | `types/print.rs` `Printer::heights` (SURFACE-cycle) | Mutation (gap 11) | a persistent set of entered nodes and a map of heights threaded through the loop's state |
| A `Vec<Option<Option<usize>>>` memo (not reached, reached with no name, reached with a name) and a `waiting` flag per node, filled from a path popped in place | `types/print.rs` `Printer::same_names` (SURFACE-cycle) | Mutation (gap 11) | a map from node to `#none | #name(usize)` threaded through the fold, absence for not reached |

## Entries from FINITE-type (`crates/zed-kernel/src/types.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashSet<&Type>` of the one-valued types filled by `insert` in a `for` loop over `finite_order`, read by a closure | `Type::values_listed` | Mutation (gap 11) | a fold over the order building a persistent set of the one-valued types |

## Entries from T2-ty (`zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `async fn` methods on a struct holding a `frames::Stack` and a `&RefCell<HashMap<K, V>>` memo, generic over the key and answer (`Pairs<'m, K, V>`), one `impl` per operation, each call that is not answered at once or from the memo on a heap frame (`Pairs::kept`) | `Ty::meet`, `Ty::meets`, `Ty::contains`, `Pairs::{meet, meets, contains, kept}` | Missing (no coroutines or `async`), interior mutability, as for `types/empty.rs` | Removed: the port's runtime must run deep recursion without overflowing; the memo a map threaded through the calls |
| A second `&RefCell<HashMap<(*const Ty, usize), Visits>>` passed down the `async` frames of `Pairs::contains`, keyed by a node's address and a length, whose entries change state (scanned so many times, then filed) and hold the rows of one length as an `Rc<[usize]>` shared with each scan | `Pairs::contains`, `Pairs::tried`, `Holders`, `Visits`, `Tried` | Mutation (gap 11); Identity (gap 1) for the address; interior mutability | The filings are a map threaded through the walk with the memo; the rows a persistent vector shared by value |
| Memo keys made of raw addresses, `(*const Ty, *const Ty)` and `(*const Ty, *const Value)`, sound only while both operands are borrowed | `Pairs` | Identity (gap 1) | Keys by digest or node id |
| A stack of items to write (`Dbg<'a>`) holding `&dyn fmt::Debug` for the leaves, so one loop writes types, rows, shapes, signatures and needs | `write_debug`, `debug_list`, `debug_map`, `debug_ty`, `debug_sig`, `debug_need` | Trait objects | A sum type of the things written, one case per kind, in a state receiver's list |

## Entries from TRIVIAL-models-study (`tests/steps/l22_08_vacuity/trivial.rs`, a prototype that L22.8 moves into the checker)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| Counts of live cubes per choice, per variable of a constraint and per constraint, the variables of each constraint kept ordered by those counts in an array with bin starts and positions (swapped in place), removed-value flags, a list of removed cubes and a trail of removals with their reasons, all updated in place and undone by popping the trail and the list | `Engine::remove`, `Engine::kill`, `Engine::lower`, `Engine::raise`, `Engine::undo_to`, `search` | Mutation (gap 11) | a persistent map of the domains and counts per choice, kept on the search's stack, so undoing is dropping the frame; the ordered array becomes a persistent map from count to the set of variables with it |
| An iterative depth-first search over explicit frames that returns once two models are listed or a choice leads to no model | `search` | Early exit (gap 12) | a fold over the frames whose state carries the end reached, with the stop as its result |
| A union-find with parities over #a, #b and a clause's binders (`Parities`, `Symbols`): parent and parity vectors and a `HashMap` from binder to node, updated in place with path compression; for a clause with one open field, a base union-find of the comparisons that do not reach the field and, per choice of the field, a local one keyed by the base roots | `Theory::clause_holds`, `Theory::clause_fails_for`, called by `Engine::check_clause` | Mutation (gap 11) | a persistent map from node to parent and parity threaded through the comparisons, or the union-find of the library once it has one |
| A `HashMap` from field and value to the reason it was removed, built once to write the explanation | `explain` | Mutation (gap 11) | a map built by one fold over the trail |

## Entries from GROUP-refusal and REFUSE-group-site (`crates/zed-kernel/src/types.rs`, `types/empty.rs`, `empty/refused.rs`, `bes.rs`; `crates/zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `OnceLock<Judgment>` on the group's `Env`, now holding the answers, the refused flags and the kept system (`rec::Why`) instead of `Vec<Option<bool>>` | `rec::Env::judged`, `judge`, `group_verdicts` | Lazy cells (gap 3) | a lazy field of the group record, as the other judged values are |
| `Bes::set` of every leaf node to `Top` after the first `decide`, and in `recheck` to `Bot` then `Top`, on one system | `judge`, `Why::recheck` | Mutation (gap 11) | two systems that share every node but the leaves, or `decide` given the leaves' kind as an argument |
| A breadth-first walk that pushes onto the `Vec` it reads by index, a `HashSet` or `HashMap` `Entry::Vacant` as its visited set, and a `VecDeque` queue | `refused_site`, `Why::recheck`, `first_member` | Mutation (gap 11) | a fold over levels with a persistent set of the nodes seen |
| A `Mutex<HashMap<Vec<usize>, Rechecked>>` on `Why` (`Rechecked = HashMap<u32, [Answer; 2]>`), filled by each re-check with the answers of the members it reaches and read by later re-checks as leaves (GROUP-refusal-reach), and a `Vec<bool>` of the nodes that reach a refused node, filled by a walk over the parents | `Why::new`, `Why::recheck` | Lazy cells (gap 3), mutation (gap 11) | a lazy map from the set of members given `\| #end` to the answers of one re-check, and the reaching set as a fold over the parents |
| Union-find with path halving over a `Vec<usize>` | `refused::connected` | Mutation (gap 11) | the same structure in a mutable array, or a count of parts by a walk with a visited set |
| `tuples.truncate(branching)` to drop the tuples of a cycle that is not refused, and the struct update `Refusal { component, tuples, ..r }` | `bes.rs` `refusal` | Mutation (gap 11) | a list built per cycle and appended only when the cycle is refused; a record with two fields replaced |
| The records `Judgment`, `Why` and `Recheck` defined in `types.rs` (module `rec`), with `impl Why` split between `types/empty.rs` (`new`) and `types/empty/refused.rs` (`recheck`); `GroupSite` defined in `types.rs` beside `Refusal` | `rec::Env::judged`, `judge`, `Why::new`, `Why::recheck`, `Type::refusal_site` | File import cycles (gap 10) | the records in the unit of the group's instance, which keeps them; `new` a function of the decider's unit and `recheck` one of the message unit, each importing the records, so the units form no cycle (`s_01f_import_graph`) |
| A walk closure that `return`s `None` from inside its loop when a cut walk meets a member kept refused, then is called again with no cuts (GROUP-refusal-reach) | `Why::recheck` (`walk`) | Early exit (gap 12) | A fold over the queue whose result says whether a kept refused member was met, and the second walk taken on that result |
| `Iterator::find` with a closure that also records the first repair the re-check leaves to the search in a captured `Option` (`get_or_insert`) (GROUP-refusal-reach) | `refused_site` | Mutation (gap 11) | A recursive function over the repairs that returns the first decided one, else the first searched one |

## Entries from LOAD-mod-chain (`crates/zedc-presburger/src/presburger/extend/residues.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `Vec` of `((&Atom, Int, &Atom, Int), &Con)` pairs, the terms of each two-term row with the first coefficient made positive, sorted by key and split into runs of equal keys by `slice::chunk_by` | `residues::read` | Mutation of a growable vector (gap 11); borrowed references in a tuple | A fold over the rows into a persistent ordered map from the key to the list of its rows, read in key order |

## Entries from BUCKET-cmp-cost (`crates/zed-kernel/src/types.rs`, `crates/zed-kernel/src/types/hash.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `imbl::OrdSet::ptr_eq` and `imbl::OrdMap::ptr_eq`, two persistent collections on one root compared equal before any entry is read | `Lits::cmp`, `atom_names` | Identity (gap 1) | an equality of persistent collections that answers at once for one shared root, in the runtime (the `==` shortcut of gap 1) |
| `imbl::OrdMap::get_min`, the first entry of an ordered map read by one descent before range iterators are made | `atom_names` | none: a library call | the first entry of an ordered persistent map |
| Arithmetic on `u8` by `wrapping_add` and `wrapping_mul`, and `>>` and `^` to fold a `u64` into a byte | `mix_byte`, `fold`, `spread` | Bit words (BIT-words) | the bit words and arithmetic modulo 2^8 |

## Entries from EMPTY-normalize-subst (`zedc-types/src/ty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `BTreeMap::retain` whose closure also filters each payload list in place and pushes the names it drops onto a captured `Vec` | `rebuild`, `Step::TyDone` | Mutation (gap 11) | a fold over the payload map that builds the kept map and the union of the dropped names' atoms together |

## Entries from EMPTY-bottom-arm (`zedc-check/src/check/walk.rs`, `zedc-preimage/src/product.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A worklist over arm nodes with a `HashSet` of nodes seen, both updated in place, returning at the first node some state reaches | `Ck::no_state_reaches` | Mutation (gap 11), early exit (gap 12) | a fold over the nodes in order with a persistent set of those seen, whose state carries the first reached node as its result |
| A loop over the cases of a test that returns the first case some state reaches (`cases` with `any`) | `Scope::reaches`, `Scope::cases` | Early exit (gap 12) | a fold over the cases whose state carries the first reached case |

## Entries from MSG-line-quote-cost (`crates/zedc/src/front.rs`, the diagnostic renderer)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| The display width of each character from the crate `unicode-width` (`UnicodeWidthChar::width`: 2 for wide East Asian characters, 0 for combining marks), a tab shown as four columns | `shown` | Code points and text tables (gap 7) | A width table in Zed, as for the other `unicode-*` tables, or a built-in for now; `codePoint` gives the key |
| A `HashMap` from a source line to the numbers of its steps, built in one pass so each line is quoted once, at its first step | `Display for Diagnostic` | Mutation (gap 11) | A map built by one fold over the steps |
| A `BinaryHeap<Reverse<(usize, usize)>>` of rows of underlines by their first free column, and the rows as `Vec`s pushed in place (interval partitioning) | `underlines` | Mutation (gap 11) | A persistent priority queue (a pairing or leftist heap) and a persistent list of rows threaded through a fold over the spans |

## Entries from KERNEL-div-newton (`crates/zed-kernel/src/num/fast.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A divisor's transforms built once and kept in a struct (`Divisor`, `Level`, `By::Reciprocal(Box<Level>, Roots)`), each block of the dividend divided through them while a closure (`put`) writes the quotient's words into a buffer in place | `Divisor::new`, `Divisor::blocks`, `Divisor::div_rem`, `Divisor::rem` | Mutation (gap 11) | a record of the spectra, and a fold over the blocks whose state is the remainder so far and the quotient's blocks, joined once |
| Residues and remainders in `Vec<u64>` written in place (`fold_words`, `sub_around`, `unfold`, `add_around`, the corrections of `Level::div_rem`) | `remainder`, `unfold`, `Level::div_rem`, `newton` | Mutation (gap 11) | arrays built by one fold each, the carries in its state |
| Re-measure: two crossovers to num-bigint's division and the cost of the reciprocal, set from timings of the Rust code on 2026-11-09 (load 15 to 17), results identical | `DIV_LEAF` (64 words, below the measured crossing near 8192), `RECIP_LEAF`, `newton_cost`, `sparse_div_cost` | None | Measure each again on the Zed code by the procedure in COMPLEXITY.md section "Crossovers" (DIV-crossover-model); at the port num-bigint's division is replaced by Zed's own |

## Entries from LIT-bare (`zedc-check/src/check/mod.rs`, `check/walk.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `bool` field of the checker (`Ck.rough`) set before one call and cleared after it, read deep inside that call | `Ck::repaired`, `Ck::fewest`, `Ck::apply` | Mutation (gap 11) | a parameter of `adopted` passed down the calls of a tried repair |

## Entries from EMPTY-arg-needs (`zedc-check/src/check/walk.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| `BTreeMap::entry(v).or_insert_with(Ty::empty)`, an insert in place only where the key is absent | `Ck::apply_one`, an argument of type `Never` | Mutation (gap 11) | a persistent map's insert-if-absent that gives the new map |

## Entries from GROUP-cycle-dup (`crates/zed-kernel/src/types/empty.rs`)

| Rust construct | Sites | Gap | At the port |
|---|---|---|---|
| A `HashMap` keyed by `(usize, Made<'a>)`, an enum whose `Atom` variant borrows the atom's name as `&'a str` from the group's bodies, filled through `Entry::Vacant` | `system` | Mutation (gap 11) | a persistent map keyed by the definition and the node's kind and children, the name held by value or by its interned number |
| An explicit stack of `Step::Visit` and `Step::Make(node, k)` with `k` patched in place (`todo[at - 1]`) when a nested union's arms are read into its parent, and `Vec::split_off` of the last `k` finished nodes | `system` | Mutation (gap 11) | a fold over the parts in post-order that returns each part's node, a union returning the set of its arms' nodes |
| Nodes added to the `Bes` as `Bot` placeholders and set to their kind and children once the whole group is read, by draining the map of made nodes | `system` | Mutation (gap 11) | the nodes built after the map is complete, in one pass over it |
