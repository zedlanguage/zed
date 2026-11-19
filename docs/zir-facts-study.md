# Facts carried in ZIR: study STUDY-zir-facts-carried

Author requests P200 (2026-11-14: "Check the checker/partial-evaluation plan against the tweet
reply; read Girard, "The phantom of transparency"; draw design lessons") and P202 (2026-11-14:
"store all derived facts in the IR, which could allow a pedantic consumer of the IR re-confirm
the facts before they trust the code -- but also allow there to be a "stripped form" of IR that
is minimal, and doesn't include anything that is not needed at runtime"), recorded in DESIGN
sec:kernel, "Facts carried, and the stripped form".

The question: for each fact the checker or `mix` derives, does ZIR, its text and binary forms,
the native back end and the runtime receive it, or work it out again? And what does each cost?

## Answer in short

- The checker's facts (types, intervals, congruences, finite sets, may-block) do not reach ZIR
  at all. Lowering takes a kernel term, not the checked program
  (`crates/zedc-zir/src/zir/lower.rs:291`, called from `crates/zed-native/src/link.rs:290`), and
  writes `_` on every value edge (`lower.rs:44`: "Edges carry `_` and no facts but hints").
  So nothing after lowering can read them, and the one reader that would, the native back
  end's NaN test, always answers "may be NaN" and tests at run time. Row **ZIR-checker-facts**.
- Cost is not derived yet (step L18.1 is open). Row **ZIR-cost-facts**, after L18.1.
- The memory plan (release counts, aliasing) is derived from the graph and worked out again at
  every start of an executable. Measured: start is 1.80 times the decode alone. Row
  **EXE-plan-carried**.
- The evidence of `fold` and `fix` and the witness of `reindex` are carried by both forms, but
  nothing after lowering reads them. The fact address is carried by structure: its static half
  is a node's position, which both forms keep; its dynamic half is data and exists only at run
  time.
- Every fact ZIR holds today survives the text and binary forms; a test proves it, with a
  negative control for each fact kind. The stripped form now exists, runs as the full form does,
  and is refused by the full readers and by the re-check (tests listed below).

## The facts, one by one

"Carried" means the fact is on the graph and kept by the text and binary forms. Line numbers are
from the tree at origin/main 7f34b01a9 plus this study's change.

| Fact | Where derived | Where read after lowering | Carried or recomputed | Row |
|---|---|---|---|---|
| Type of each value | checker, `crates/zedc-check/src/check/walk.rs`, `check/mod.rs` | native NaN test `crates/zed-native/src/tables.rs:198-206`, used at `codegen.rs:1003` | **dropped at lowering**: `lower.rs:44`, `lower.rs:291` takes a term; every edge is `_`, so `may_be_nan` returns true and a NaN test runs that a float edge known NaN-free would skip | ZIR-checker-facts |
| Interval, congruence, finite set (the domain) | lattice store `crates/zedc-lattice/src/cell.rs:348` (`Cell`), `:477` (`Store`); checker `check/coprime.rs`, `check/limits.rs` | none | **dropped at lowering** (as above). The graph has the form for them (`ValueEdge{ty, domain, facets}`, text `int in [0..=10] class 1 mod 4 set {5}`) and both forms keep it (test below) | ZIR-checker-facts |
| May block | `crates/zedc-check/src/check/blocking.rs:183` (`facts`) | none; a port operation blocks as it runs | **dropped at lowering**; the runtime needs no flag, but a consumer cannot re-check it | ZIR-checker-facts |
| Cost, work and depth bounds | not derived (L18.1 open; `crates/zedc-base/src/cost.rs` holds the cost model only) | none | **not derived** | ZIR-cost-facts |
| Release counts, aliasing (memory plan) | `crates/zedc-zir/src/zir/memory.rs:256` (`plan`), O(occurrences + edges) | `memory::run`; the native back end through `Program.plan` | **recomputed at every start**: `crates/zed-native/src/exe.rs:211-214` decodes the graph, then runs `legalized_sites`, `legalize` and `plan` | EXE-plan-carried |
| Evidence of `fold` and `fix` (`associative`, `commutative`, `idempotent`, `monotone`, `finiteHeight`) | elaboration `crates/zedc-elab/src/elab/walk.rs:2443`, `walk/fp_ops.rs:104`; key names `crates/zed-kernel/src/term.rs:697-700` | none (the evaluator and the back end ignore it) | **carried**, unread. Its readers are the parallel strategies of L24.1 and the vectorizer of L24.2, which already wait on the study STUDY-codegen-checker-opts | none |
| Witness of `reindex` | the checker's injectivity discharge (`Witness::Residue`, `Witness::Catalog`, `term.rs:659`) | none | **carried**, unread; the evaluator checks the collision rule on every run whatever the witness (`term.rs:655-657`). That check is the duplicate-key test of building the family (`crates/zed-kernel/src/eval.rs:3986`, `Family::from_leaves`), which the build does to place the entries in any case, so trusting the witness would save no work today (inferred from reading the build, not measured) | none |
| Fact address | static half: the node's position, `crates/zed-kernel/src/provenance.rs:24-30`, `:175-183`; dynamic half: the keypath, made by the run | provenance, `Evaluator::with_provenance` | **carried by structure**: positions follow the graph's preorder, which stripping keeps (the stripped graph has the same nodes in the same order, so `legalized_sites` numbers them alike). The keypath is data and is made at run time by design | none |
| Hints (binder names, `name`, `units`) | lowering, from the source's names | messages | **carried** by the lowered graph's text and binary forms; dropped by `canon` (`crates/zedc-zir/src/zir/canon.rs:126`) on purpose, since a content address must not depend on names | none |

One fault was found and fixed in this run: elaboration wrote the evidence key `assoc`, while the
kernel documents and reads `associative` (`term.rs:697-700`). Fixed at `walk.rs:2443`,
`walk/fp_ops.rs:104` and the unit test at `crates/zedc-preimage/src/address.rs:1391`.

## What this run built (P202)

- **The stripped form** (`crates/zedc-zir/src/zir/strip.rs`). `strip` keeps the regions, nodes,
  inputs, results, operations and constants, and whether each edge is a value or a port's state;
  it writes `_` on each value edge and empties each evidence record. Two things stay: a region
  argument fed by a constant capture keeps the constant's type, which the validator requires and
  the constant gives, so it is no derived fact; and a `reindex` keeps its witness, since the
  graph has no form for an unknown witness. Stripping a graph is linear in its size as the binary
  form counts it: a region shared by several nodes is stripped once for each set of constants
  its users capture, so sharing is kept, and the walk keeps its frames on the heap.
- **Its forms.** Text: first line `zir 1 stripped` (`strip::print_stripped`, read by
  `text::parse_form`). Binary: first bytes `ZIRs` (`strip::encode_stripped`, read by
  `binary::decode_form`). The full readers `text::parse` and `binary::decode` refuse a stripped
  module with a message naming its first line or first bytes.
- **The re-check** (`strip::recheck`). A stripped module is refused (`STRIPPED_REFUSED`); a full
  one is validated. It does not yet prove the facts on the edges again, because the checker does
  not yet store any there; ZIR-checker-facts adds that.
- **Executables** (`crates/zed-native/src/exe.rs`) now store the stripped form, and the start
  reads either form with `decode_form`.

Tests, in `tests/steps/l01_31_zir/stripped.rs` and its benchmarks in
`tests/steps/l01_31_zir/bench/stripped.rs`:

- `every_fact_survives_the_text_and_binary_forms`: a graph holding every fact kind the graph can
  hold (an interval, a congruence, a finite set, a hint, a facet, `fold` and `fix` evidence, a
  witness, a typed constant capture) prints, reads back from the text and from the binary form,
  and lists the same facts. The negative control removes each fact kind from the text in turn
  (nine edits) and checks that the fact list then differs.
- `the_stripped_form_keeps_no_fact_and_runs_as_the_full_form`: on that graph, a lowered sum
  fold, a lowered comparison, and a nest of six `if`s, the stripped graph keeps no fact but the
  witness, validates, has as many lines, strips to itself, and gives the same value as the full
  graph under the kernel evaluator (raised), the counting machine and the native back end, from
  both its text and its binary form; its bytes are no more than the full form's.
- `the_recheck_refuses_a_stripped_module`.
- `a_shared_region_is_stripped_once_for_each_set_of_constants_its_users_capture`.
- `stripping_keeps_sharing_so_a_graph_strips_in_the_time_of_its_size`: a graph of 64 regions
  whose tree has 2^64 leaves, and a nest 20 000 deep on a small stack.
- Benchmarks: T(8n)/T(n) = 7.998 for a nest of `if`s and 7.997 for the shared graph (sizes
  12 500 and 100 000; limit 10.5).

## Costs measured

Over the lowered graphs of the 115 corpus units (via the cranelift corpus test harness, 50
repetitions each, on the shared 32-core machine, load not controlled):

| Measure | Full | Stripped |
|---|---|---|
| Binary bytes, all 115 graphs | 79 387 | 76 243 (0.960) |
| Binary bytes, largest graph | 2 081 | 1 826 (0.877) |

The lowered graphs carry no checker facts yet, so the stripped form saves only the hints and the
evidence: 4 percent. Once ZIR-checker-facts stores a type and a domain on every edge, the full
form grows and the stripped form does not; that row measures the new ratio.

| Start of an executable, per repetition | Decode only | Decode, legalize, plan | Ratio |
|---|---|---|---|
| All 115 graphs | 1 264 574 ns | 2 272 820 ns | 1.80 |
| Largest graph | 29 023 ns | 56 632 ns | 1.95 |

So working the memory plan out again costs as much as reading the graph itself. Carrying it
(EXE-plan-carried) saves up to that much, less the time to read the carried plan; the row
measures both.

## Prior work

The sources are recorded with quotes in the spec's `verification/bib.md`, section "Facts
carried in ZIR, and the stripped form".

- **Abstraction-carrying code** (Albert, Arenas, Puebla and Hermenegildo 2010): the producer
  ships the fixpoint of its analysis with the code, and the consumer checks it in one pass
  instead of computing it. Their reduced certificate keeps "only ... information that the
  checker is unable to reproduce without iterating", 3.35 times smaller with no increase in
  checking time. This is the rule for choosing what the full form must carry for a fast
  re-check: a fact found by a fixpoint (an interval of a loop, a `fix`'s bound) must be carried;
  a fact one forward pass gives from its inputs (the type of a primitive's output, the memory
  plan) may be carried for speed but can be re-derived by the checker.
- **Typed assembly language** (Morrisett, Walker, Crary and Glew 1999): types are kept through
  every pass down to machine code so "untrusted and potentially malicious code" can be "checked
  for safety before execution". This is the full form's purpose in P202. Their account of
  Necula's proof-carrying code, the same idea with proofs in a general logic, is quoted there;
  Necula 1997 itself was located but not read.
- **RVSDG** (Reissmann, Meyer, Bahmann and Själander 2020), the IR family ZIR belongs to: an
  edge is "value typed" or "state typed", and "a richer type system permits further
  distinction". ZIR's value edges add a domain and facets to that type; the graph shape is
  unchanged, so carrying the facts needs no new node or region.

## Recommendations and the rows filed

1. **ZIR-checker-facts.** Lower from the checked program, so that each value edge gets the
   checker's type, the store's domain (interval, congruence, finite set) and a facet for
   may-block; make `recheck` prove each stored fact again in one forward pass from its node's
   inputs, as abstraction-carrying code checks a certificate, carrying in full only the facts a
   fixpoint found. Then `may_be_nan` reads a real type and skips the run-time NaN test on a float
   edge known NaN-free. Direct consumer: ZIR-cost-facts, which stores the cost bounds beside
   these facts. L24.2, whose vectorization reads intervals and types from the edges, reaches it
   through S.4 and L24.1, so it is not a direct need of L24.2.
2. **ZIR-cost-facts.** Once L18.1 derives `f::cost` and `f::depth`, store each node's bound on
   the graph, keep it in the full form, drop it in the stripped one, and re-check it. Consumer:
   L24.1, whose strategy catalog chooses a schedule from cost bounds per region.
3. **EXE-plan-carried.** Store the memory plan (release counts, aliasing) in the executable's
   data, in both forms, since running reads it; read it at start instead of planning; a
   re-check plans again and compares. Measure start time before and after on the corpus.
   DESIGN sec:kernel says no runtime works a fact out again, and the executable does, so this is
   a fault against the spec: it joins L1.41-join-zed-native.

No row for the evidence, the witness, the fact address or the hints, for the reasons in the
table.

## The two studies this one unblocks

- **STUDY-linking** needs only STUDY-zir-facts-carried, so with this row done its needs are
  met.
- **STUDY-codegen-checker-opts** does not list this row in its needs; it needs L23.4 only. It
  asks which facts the checker "proves and carries in ZIR"; the table above is that answer for
  today (none of the checker's own facts are carried; fold evidence is), and rows
  ZIR-checker-facts and ZIR-cost-facts say when they will be. Its needs are unchanged: it still
  waits for L23.4.
