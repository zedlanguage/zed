# Code generation passes against the checker's facts (STUDY-codegen-checker-opts)

The record of plan row STUDY-codegen-checker-opts (author, 2026-11-16, P293; its need L23.4
waived by the author's order of 2026-11-21). It answers, for each optimization pass of LLVM, GCC
and Cranelift: which analysis the pass needs and what that analysis costs; which fact the Zed
checker already proves that replaces the analysis, where the fact is derived and where ZIR
carries it; what then becomes exact or free; what must still be computed; and the expected gain.
It ends with the order of steps for parallel code generation (section 6) and the plan rows filed
for L24.1, L24.2, L24.3 and L29.1 (section 7).

Each claim is marked **[C]** (confirmed: a file:line at the stated tag, or a command and its
output) or **[I]** (inferred: what would confirm it is named). The "fact that replaces it",
"exact or free" and "expected gain" columns are design inferences [I] unless a row says what was
measured.

## 1. Sources

| Source | Version | How read |
|---|---|---|
| LLVM | llvm-project tag `llvmorg-22.1.8` (commit ca7933e47d3a); installed `opt` and `llc` 22.1.8 | sparse clone in the study's scratch directory (outside every repository); `opt -print-pipeline-passes`, `-debug-pass-manager`, `llc -debug-pass=Structure` |
| GCC | tag `releases/gcc-16.2.0` (commit 78d4ac73dd39); installed `gcc` 16.2.1 | sparse clone; `gcc -O2 -fdump-passes`, `-O3` |
| Cranelift | wasmtime tag `v51.0.0` (commit 32656dc4873f) | sparse clone of `cranelift/codegen/src/` |
| Zed | zed-impl `f9fe90a5a` | this tree; docs/zir-facts-study.md for where facts are carried |
| Claims checked | LWN, "Cranelift code generation comes to Rust" (D. Alden, 2024-03-15, lwn.net/Articles/964735); H. Xu, F. Kjolstad, *Copy-and-Patch Compilation* (OOPSLA 2021, doi:10.1145/3485513, arXiv 2011.13127); A. Engelke, T. Schwarz, *Compile-Time Analysis of Compiler Frameworks for Query Compilation* (CGO 2024); cranelift/README.md:62-68 at v51.0.0; Rust Project Goals 2026, "Improve cg_clif performance" (goals.rust-lang.org/2026/improve-cg_clif-performance.html); C. Fallin on the Cranelift Zulip, 2022-05-26 and 2022-10-10 | fetched 2026-11-20 |

Paths in the LLVM tables are relative to `llvm/lib/`; **PBP** is
`Passes/PassBuilderPipelines.cpp`. GCC paths are relative to `gcc/` with `passes.def` lines and
`params.opt` lines; Cranelift paths are relative to `cranelift/codegen/src/`.

## 2. The claims checked

| Claim (Gemini, pasted by the author) | Verdict | Evidence |
|---|---|---|
| LLVM runs about 100 passes | **Holds only for pass instances in the default pipeline.** O2: 108 instances, 76 distinct names; O3: 111 and 79. `opt -print-passes` lists 533 passes (18 header lines besides); one O3 run on a 4-function module executed 434 passes, 267 analyses | [C] `opt -passes='default<O2>' -print-pipeline-passes`, adaptors, `require`, `invalidate` and `verify` removed, recounted by this study: 108/76 and 111/79; `opt -print-passes`: 533 indented entries, 18 headers |
| GCC runs 370+ passes | **Holds only for pass instances.** `passes.def` has 386 `NEXT_PASS` entries, 394 on x86-64 (i386-passes.def adds 8); 297 distinct pass classes; at -O2 281 instances are on, about 189 distinct passes | [C] `gcc -O2 -fdump-passes`: 394 lines, 281 ON, 113 OFF; -O3: 288 ON, 106 OFF; `grep -c NEXT_PASS passes.def` = 386. The likely origin is LWN 964735: "LLVM lists 96 optimization passes in its documentation, while GCC has 372." |
| Cranelift code is 10–15% slower than LLVM's | **Holds for one measurement only.** cranelift/README.md:62-68: "~14% slower than WAVM (LLVM)", from the copy-and-patch paper's Fig. 22 (WebAssembly, PolyBenchC); Fallin 2022: "maybe ~10% slower (eyeballing the gap)". Other sources disagree: LWN, "approximately twice as slow on some benchmarks"; CGO 2024, "a similar run-time performance to unoptimized LLVM" | [C] the quoted pages. [I] Gemini may have read the Rust goal's "10-15%", which is a compile-time speedup |
| Cranelift compiles up to 7 times faster | **Not confirmed: no source says 7x.** The 2020 WebAssembly study: "approximately an order of magnitude" (about 10x); CGO 2024: 20–35% faster than unoptimized LLVM; LWN, Cranelift building itself: 20% less wall time, 40% less CPU time; Rust goals 2026: 5% faster with `-Cdebug-info=none`, "between negligible and ~30%" | [C] the quoted pages; two searches found no 7x figure |

## 3. The checker's facts: where derived, where ZIR carries them

The codes below are used in the pass tables.

| Code | Fact | Where derived (zed-impl f9fe90a5a) | Where ZIR carries it | Status |
|---|---|---|---|---|
| D | Domain: interval, finite set | `crates/zedc-lattice/src/interval.rs:160` (`IntervalSet`), `cell.rs:348` (`Cell`), `:477` (`Store`) [C] | the form exists, `ValueEdge{ty, domain, facets}` at `crates/zedc-zir/src/zir/mod.rs:104` [C]; lowering writes `_` on every edge (`zir/lower.rs:44`) [C] | **not carried**: row ZIR-checker-facts |
| M | Congruence (`x ≡ r mod m`) | `crates/zedc-lattice/src/lattice.rs:92` (`Congruence`); `zedc-presburger/src/modular.rs` [C] | as D | **not carried**: ZIR-checker-facts |
| P | Presburger-proved independence and injectivity of keys | `crates/zedc-presburger/src/presburger.rs:286` (`satisfiable`); `crates/zedc-check/src/check/walk/remap.rs:754` (`injective`) [C] | `Witness` on `reindex`, `crates/zed-kernel/src/term.rs:665` [C] | **carried, unread** (docs/zir-facts-study.md) |
| E | Purity and port effects | ports are typed; a port operation is ordered by a state edge per port (`zir/lower.rs:514`, `:522`, `:810`, `:1257`) [C]; may-block, `crates/zedc-check/src/check/blocking.rs:183` [C] | `Edge::State(port)` (`zir/mod.rs`, enum `Edge`) [C]: a node with no state edge touches no port, so purity is read off the graph; may-block is dropped | **carried** (effects), **not carried** (may-block): ZIR-checker-facts |
| A | No aliasing: DESIGN line 62, "Every value has one writer and is readable only once complete" (sec:generations, sec:memory, sec:ports), so no two names share a mutable cell | by the language; the in-place reuse that could alias is the memory plan's, `crates/zedc-zir/src/zir/memory.rs:257` (`plan`) [C] | recomputed at every start, `crates/zed-native/src/exe.rs:212-214` [C], at 1.80 times the decode time (docs/zir-facts-study.md) | **recomputed**: EXE-plan-carried |
| R | Release counts (last use, in-place update) | `zir/memory.rs:257` [C] | as A | **recomputed**: EXE-plan-carried |
| W | Cost, work and depth bounds (`f::cost`, `f::depth`) | **not derived yet**: L18.1 is open; `crates/zedc-base/src/cost.rs` holds the scalarization only [C] | none | **not derived**: ZIR-cost-facts after L18.1 |
| L | Algebraic laws (associative, commutative, idempotent, monotone, finite height) and their grades | `crates/zedc-elab/src/elab/walk.rs:2444`, `walk/fp_ops.rs:104`; grades `term.rs:677` (`Grade`) [C] | evidence keys on `fold` and `fix` [C] | **carried, unread** |
| T | The canonical float tree (DESIGN sec:reduction item 1: blocks of the binary representation of n, largest first, combined left to right; depth ⌊log₂ n⌋ + popcount(n) − 1) | it is the meaning of `fold` on floats, not a fact: `crates/zed-kernel/src/exact.rs:5`, `:82`; checker note `crates/zedc-check/src/check/walk.rs:5184` [C] | the `fold` node itself; the policy (`tree`, `compensated`, `unordered`) | **carried by the node**; no native lowering of `fold` exists (`grep` of `crates/zed-native/src` finds none) [C] |
| N | NaN-freedom of a float value | from the type and domain (D) | `may_be_nan` reads the edge, `crates/zed-native/src/tables.rs:199`, used at `codegen.rs:1009` [C] | **not carried**, so a NaN test runs that the checker had decided: ZIR-checker-facts |

What this table means for every pass below: with D, M, E (may-block), A, R and W not yet on
the graph, no back end can use them today. The rows ZIR-checker-facts, EXE-plan-carried and
ZIR-cost-facts are the prerequisite of every gain claimed below [C for the status; I for the
gains].

## 4. The passes

Columns: the pass and where the pipeline adds it; the analysis it needs and that analysis's cost
or cutoff (each cutoff is a place where the compiler gives up because the exact analysis costs
too much); the Zed fact that replaces it; what becomes exact or free; what must still be
computed; the expected gain. Cutoff values are [C] at the file:line given.

### 4.1 LLVM 22.1.8 (default O2/O3 pipeline)

| Pass | Analysis needed; its cost | Zed fact | Becomes exact or free | Still computed | Expected gain [I] |
|---|---|---|---|---|---|
| SROA (4 at O3; PBP:602, 739, 1141, 1445) | DominatorTree; non-escaping allocas; iterates to a fixpoint (Scalar/SROA.cpp:19-21) | A | nearly all: Zed emits SSA values, not allocas | allocas inlining exposes | compile time only |
| EarlyCSE (PBP:605, 1142) | MemorySSA clobber walk, `memssa-check-limit` 100 (Analysis/MemorySSA.cpp:75) | E, A | CSE of loads across calls | value-numbering walk | more loads removed where the cap cut the walk off |
| InstCombine (8 at O3) | KnownBits, dominating conditions (`dom-conditions-max-uses` 20, ValueTracking.cpp:90); "some N^2 behavior in pathological cases" (InstCombine/InstructionCombining.cpp:5990) | D, M, L | range folds, nsw/nuw, power-of-two and low-zero-bit queries | target-shaped canonical forms | fewer known-bits queries; folds the caps miss |
| AggressiveInstCombine (PBP:636) | expression trees for truncation | D | the needed bit width | legal type choice | narrower arithmetic |
| SimplifyCFG (8 at O3) | speculation cost; "at worst, this has quadratic complexity" (Utils/SimplifyCFG.cpp:2670); caps 2–24 (:112–:204) | E, D | legality of speculation; switch ranges | profitability (TTI) | branches removed that the caps leave |
| SCCP, IPSCCP (PBP:755, 1188) | constant-range lattice; specialization caps (IPO/FunctionSpecialization.cpp:39, :44, :66) | D | every range the checker proved | constants after inlining | analysis time; Zed's partial evaluation already folds constants |
| CorrelatedValuePropagation (PBP:625, 773) | LazyValueInfo per edge, costly to keep (CorrelatedValuePropagation.cpp:1389-1390) | D | every range query; LVI not needed | ranges of values later rewrites create | analysis time and memory |
| JumpThreading (PBP:624, 772) | LVI; `jump-threading-threshold` 6 (:87) | D, E | which edge's condition is known | duplication cost | small |
| TailCallElim (PBP:649, 1619) | alias analysis, "very primitive" (TailRecursionElimination.cpp:47-48) | E, A, L | legality; the accumulator for an associative operator | nothing | loops from recursion always |
| Reassociate (PBP:657) | ranks; on floats only under `reassoc` | L; T forbids it on floats | integer legality | rank order | none on floats by design: T fixes the order |
| ConstraintElimination (PBP:659) | Fourier–Motzkin "with some tricks from the paper Pugh... The Omega test" (Analysis/ConstraintSystem.cpp:22-28); `max-rows` 500 (:58) | D, M, P | every compare or bound the checker decided (the checker's Presburger layer is the same method, uncapped) | facts that appear only after inlining | bounds checks removed with no cap |
| LICM (4 at O3) | MemorySSA and alias analysis for hoisting and scalar promotion (Scalar/LICM.cpp:22-35); `licm-mssa-max-acc-promotion` 250 (:165) | E, A | hoisting legality; promotion is free (no aliased store) | register pressure, "the responsibility of the back-end" (LICM.cpp:17-20) | more hoisting in large loops |
| LoopRotate (PBP:689, 1570) | `rotation-max-header-size` 16 (LoopRotation.cpp:32) | W | the guard, where the trip count is proved ≥ 1 | header duplication | small |
| SimpleLoopUnswitch (O3) | AA, MemorySSA; "limit potentially exponential behavior" (:97) | E, D | invariance of the condition; the condition may be decided outright | code size | fewer versioned loops |
| LoopIdiomRecognize (PBP:700) | SCEV strides and AA; "a quadratic search on all of the given stores" (:643) | P, A | legality | idiom matching | small |
| IndVarSimplify (PBP:701) | SCEV; "O(I^2) for loop nests" (:1946) | D, M, W | trip counts and exit values | the rewrite | analysis time |
| LoopDeletion (PBP:712, 1577) | SCEV termination, side effects | E, W | both conditions | nothing | dead loops always removed |
| LoopUnroll, LoopFullUnroll (PBP:721, 1435) | SCEV trip counts; thresholds 150/300 (LoopUnrollPass.cpp:167, :171) | W, D | the trip count | size against speed | unrolling decided from exact counts |
| **LoopVectorize** (PBP:1322) | LoopAccessAnalysis: a runtime check for every pair of pointer groups, stopped after 100 merges (LoopAccessAnalysis.cpp:96, :700-704) and 100 dependences (:106, "a limit on this quadratic algorithm", :2412); refuses more than 128 checks (LoopVectorize.cpp:197-198); strict FP reductions not vectorized without `reassoc` (IVDescriptors.cpp:961-968, LoopVectorizationLegality.cpp:1343-1366) | P, A, D, M, W, T | every runtime alias check and the dependence analysis (**measured**, section 5); the exact trip count and alignment | vector width, interleave count, epilogue (target cost model); the **T order must be emitted by Zed as vector code**, since `reassoc` lets LLVM pick any order (section 5) | the largest single gain: loops vectorized with no checks; float sums vectorized at all |
| LoopLoadElimination (PBP:1359) | LAA; memchecks | P, A | dependences of distance one | nothing | small |
| LoopDistribute (PBP:1594, metadata only) | LAA with versioning | P | the dependence graph | whether the split pays | splits that are off by default become safe |
| LoopInterchange, LoopFuse (off by default) | DependenceAnalysis, an "(incomplete) implementation of" Goff, Kennedy and Tseng (Analysis/DependenceAnalysis.cpp:9-15), MIV threshold 7 (:109) | P, W | legality | the cache cost | makes them usable |
| SLPVectorizer (PBP:1414) | AA, TTI; "O(N^2) search over the gather/shuffle sequences" (:21644); `schedule-budget` 100000 (:162) | A, L, T | legality; operand permutation by commutativity | tree search and cost | fewer give-ups |
| GVN (PBP:750) | MemoryDependenceAnalysis, block scan 100 (Analysis/MemoryDependenceAnalysis.cpp:73), `max-num-deps` 100 (GVN.cpp:119) | E, A | the memory-dependence queries | value numbering | loads removed past the caps |
| MemCpyOpt, MergedLoadStoreMotion, LoopSink | AA | A | legality | profitability | small |
| BDCE (PBP:760) | DemandedBits | D | most demanded bits | the rest | small |
| ADCE (PBP:778) | side effects, post-dominators | E | which calls are removable | liveness | small |
| DSE (PBP:783) | MemorySSA and AA; `memoryssa-scanlimit` 150 (DeadStoreElimination.cpp:123); "Checking for aliasing is expensive" (:1341) | E, A, R | every alias query; a store to an object whose count reaches 0 is dead | nothing | stores removed past the caps |
| Inliner (PBP:1297) | InlineCost: threshold 225 (InlineCost.cpp:59), instruction cost 5 (:142); "terrible compile times" (Inliner.cpp:81) | W, E | the benefit estimate from proved cost | the size budget | inlining decided by work, not instruction count |
| FunctionAttrs, GlobalOpt, ArgumentPromotion, LibCallsShrinkWrap | call-graph walks, AA; GlobalOpt "the expensive (cubic) static resolution algorithm" (GlobalOpt.cpp:103-106) | E, A | the whole of each pass | nothing | analysis time |
| Float2Int (PBP:1545) | ranges | D | the range proof | integer width | small |
| CallSiteSplitting, CHR, DivRemPairs, VectorCombine, LoopInstSimplify, LoopSimplifyCFG, DeadArgElim, LowerConstantIntrinsics | target cost or profile | none | none | all | none |
| Alias analyses (PBP:2437: BasicAA, ScopedNoAliasAA, TBAA, GlobalsAA); CaptureTracking `max-uses-to-explore` 100 (Analysis/CaptureTracking.cpp:45) | — | A, E | every alias and mod/ref query | nothing | analysis time across all passes above |
| ScalarEvolution | caps 32–4096 (ScalarEvolution.cpp:153–:216) | D, M, W | trip counts, ranges, strides | expressions after inlining | analysis time |
| Polly (not in the default pipeline; `-mllvm -polly`, polly/docs/UsingPollyWithClang.rst:23-29) | isl; computeout 500000 (polly/lib/Analysis/DependenceInfo.cpp:48-52) | P | the dependences | schedule and tiling | tiling with no dependence search |
| Back end: MachineScheduler (`misched-limit` 256, CodeGen/MachineScheduler.cpp:247-250), greedy register allocator (RegAllocGreedy.cpp:96-120), MachineLICM, MachineCSE | — | A for memory edges only | exact memory dependence edges | scheduling and register allocation | none in register allocation [I] |

### 4.2 GCC 16.2

| Pass (`passes.def` line) | Analysis needed; its cost | Zed fact | Becomes exact or free | Still computed | Expected gain [I] |
|---|---|---|---|---|---|
| early inliner (:76), IPA inliner (:175) | ipa-fnsummary size and time; `max-inline-insns-auto` 15 (params.opt:635) | W, E | callee cost | the growth budget | as LLVM's inliner |
| ipa-cp (:172) | jump functions; `ipa-cp-value-list-size` 8 (:294) | D, M | argument ranges and bits | cloning | ranges past the cap |
| ipa-sra (:173) | escape analysis | A, E, R | splitting legality | ABI profitability | small |
| ipa-pure-const (:109, :177, :387) | SCC fixpoint | E, W | the whole pass | nothing | analysis time |
| ipa-modref (:110, :178, :388) | access summaries; caps 16–256 (params.opt:1134–:1150), past which the summary collapses | E, A | exact summaries with no cap | callers' queries | precision past the caps |
| ESRA/SRA (:89, :252) | address-taken, escape, TBAA | A, R | every aggregate scalarizable | profitability | small |
| CCP (:84, ...) | four-level lattice and nonzero bits | D, M | known bits and alignment | folds after other folds | analysis time |
| FRE/PRE (:95, :279, ...) | alias walks; `sccvn-max-alias-queries-per-access` 1000 (:1022) | A, E, L | load redundancy with no alias walk | value numbering, ANTIC | loads removed past the cap |
| DSE (:98, ...) | alias oracle; `dse-max-alias-queries-per-store` 256 (:143) | A, E, R | a def-use question, not an alias question | object liveness | stores removed past the cap |
| DCE/CD-DCE | side effects; `finite_loop_p` (tree-ssa-loop-niter.cc:3456) | E, W | pure dead calls and finite dead loops | the mark phase | small |
| EVRP/VRP (:96, :237, :363) | Ranger; fast VRP above 150000 blocks (tree-vrp.cc:1336-1352); `ranger-logical-depth` 6 | D, M | every range, no depth cap, no fallback | ranges of new values | precision in large functions |
| DOM, jump threading | path ranger; `max-jump-thread-paths` 64 | D, W | branches the intervals decide | path-sensitive facts | small |
| phiopt (:100, ...) | trap and alias analysis for conditional stores | E, A, L | speculation and store sinking legal | branch or select | small |
| reassoc (:267, :352) | floats need `-fassociative-math` | L; T forbids it on floats | integer legality | tree shape | none on floats by design |
| LIM (:137, ...) | alias oracle; always-executed check | A, E, P | invariance; hoisting without the trap check | profitability | more hoisting |
| ivopts (:337), ivcanon (:304), cunroll (:226, :327) | SCEV, niter; `max-iterations-to-track` 1000 (:675) | D, M, W | overflow decided; trip counts | IV set selection | analysis time |
| ldist (:305) | reduced dependence graph; `loop-max-datarefs-for-datadeps` 1000, above which `chrec_dont_know` (tree-data-ref.cc:5804) | P, A | the dependence graph, uncapped | partitioning | loops past the cap |
| linterchange, unroll-and-jam, lsplit, unswitch (O3 only) | distance vectors; caps 4–64 | P, D, E | legality | cost model | usable at O2-like cost |
| predcom (:326) | constant dependence distances | P, A | the distances | register rotation | small |
| **tree-vect** (:322) | dependence tests (tree-data-ref.cc:3715–:5729); runtime alias checks, refused under the O2 "very cheap" cost model (tree-vect-data-refs.cc:4202); float reductions in order unless `-fassociative-math` (`needs_fold_left_reduction_p`, tree-vect-loop.cc:3421) | P, A, D, M, T | dependence analysis and alias versioning removed; alignment known; a vector reduction in T's order without `-ffast-math` (emitted by Zed) | vector width, SLP or loop, if-conversion, masks | as LLVM: the largest single gain |
| SLP (:333, :345) | group dependences, alias | A, P, L, T | alias questions free; commutative operand permutation | grouping, cost | fewer give-ups |
| Graphite (:309, :311; off, "This option is experimental", invoke.texi:14994-14998) | isl; `max-isl-operations` 350000 (params.opt:667) | P, D, M, A | exact dependences and domains | schedule and tiling | tiling with no dependence search |
| parloops (:140, :316; off) | dependences, reductions, niter | P, W, T | independence; work estimate; parallel reductions | thread split | replaced by Zed's own strategies (section 6) |
| sched1/sched2 (:515, :548) | dependence graph with memory; sched1 off on x86, "It tends to make the problem with not enough registers even worse" (i386-common.cc:2051-2053) | A, E | exact memory edges | the schedule | small |
| IRA/LRA (:519, :520) | liveness, conflicts, frequencies | W, R | exact frequencies | register allocation | small |
| Points-to, TBAA, restrict, data dependence, SCEV, ranges, modref (shared analyses) | as above | A, P, D, M, E | free | — | analysis time across all passes |

### 4.3 Cranelift (wasmtime v51.0.0)

Cranelift runs a short pipeline (context.rs:160-198 [C]): NaN canonicalization (optional),
verify, unreachable code, `remove_constant_phis`, alias resolution, the acyclic e-graph pass
(`egraph_pass`, :361-397), lowering and register allocation. It has no vectorizer and no loop
unroller (a grep of `codegen/src` for `vectoriz` and `unroll` finds only unrelated uses [C]), and
inlining is a hook with no heuristics (inline.rs:1-20 [C]).

| Pass | Analysis needed; its cost | Zed fact | Becomes exact or free | Still computed | Expected gain [I] |
|---|---|---|---|---|---|
| remove_constant_phis (remove_constant_phis.rs:219-220) | forward dataflow to a fixpoint | D | constant block parameters | the pass | small |
| aegraph build (egraph/mod.rs:80-97) | hash-consing, ISLE rules applied at insertion; `MATCHES_LIMIT` 5 (:128), `ECLASS_ENODE_LIMIT` 5 (:131), `REWRITE_LIMIT` 5 (:392) | L, D, M, E | laws supply rules; D and M let side-conditioned rules fire; E moves more nodes out of the side-effect skeleton | matching | rules past the limits |
| alias analysis (alias_analysis.rs:1-85) | user-declared `AliasRegion` (ir/memflags.rs:32-55); a load with no region is a fence | A, E, R | each Zed object its own region: forwarding and DSE exact | last store per region | loads and stores removed |
| extraction (elaborate.rs:344-420) and cost (egraph/cost.rs) | fixed opcode weights; the comment at cost.rs:16-19 says costs scale by 1024 per loop level but the code does not [C] — a flaw in Cranelift's documentation, not fixed here | W | exact costs | the choice | better extraction |
| scoped elaboration: GVN, LICM, rematerialization (mod.rs:1261-1283) | domtree, loops; LICM speculative because "most loops execute at least once" | E, W | speculation always legal; never a loss when the trip count is proved ≥ 1 | placement | small |
| opts/*.isle: 1624 rules in 12 files | README: avoid general commutativity and associativity, "huge amounts of e-graph bloat" | L | rules generated from declared laws | termination discipline | — |
| (absent) vectorization, unrolling | — | P, A, T, W | legality of any loop transform added later | all of it | Zed must do these before Cranelift (section 6) |
| regalloc2 Ion (Cargo.toml:364, 0.15.2) | liveness, bundles, spill weights | W, R | spill weights | register allocation | small |

## 5. Two measurements

Run by this study with the installed `opt` 22.1.8, `-O3 -mtriple=x86_64-unknown-linux-gnu
-mcpu=znver3`, on a module with four functions [C]:

| Function | What `opt -O3` produced |
|---|---|
| `axpy(x, y)`, plain pointers | a `vector.memcheck` block (`%found.conflict = and i1 %bound0, %bound1`) choosing between the vector loop and the scalar loop |
| `axpy_noalias`, `noalias` on both | the vector loop, no memcheck |
| `sum`, strict FP | not vectorized: "cannot prove it is safe to reorder floating-point operations" |
| `sumfast`, `reassoc` | four accumulators of width 4, combined at the end by `llvm.vector.reduce.fadd`; the order depends on the width, the interleave count and n |

So fact A (no aliasing) given to LLVM as `noalias` removes the run-time check entirely. Fact T
cannot be given to LLVM at all: strict FP does not vectorize, and `reassoc` lets LLVM choose an
order that changes with the target. To keep G9 (bit-identical results at any core count and on
any target), Zed must emit a float reduction already shaped as the canonical tree, as vector
code, and hand LLVM or Cranelift no freedom to reorder it. GCC behaves the same way: in order
unless `-fassociative-math` (tree-vect-loop.cc:3421) [C].

## 6. The order of steps for parallel code generation

The question: in what order should ZIR be split into parallel work, optimized, vectorized and
scheduled, so that each step does not undo another.

**Recommendation.**

1. **Facts first, on the whole graph.** The checker's facts (section 3) reach ZIR before any
   other step (ZIR-checker-facts, EXE-plan-carried, ZIR-cost-facts). Every later step reads them
   and none works them out again.
2. **Split ZIR into work units by the strategy catalog (L24.1).** For each region the cost
   bounds W decide among: a static list schedule [HEFT] where W bounds the work tightly;
   divide-and-conquer whose split points are computed at run time from the residual cost model
   (sec:runtime, "the residual cost model is compiled into the program"); work stealing with
   heartbeat promotion where the work depends on data. The unit is the leaf task of that
   decomposition: the sequential grain below which no further split pays (the ~100 µs viability
   floor of [Heartbeat]).
3. **Fix the data layout and the reduction tree per unit**, from P and T: which level is
   contiguous, and which blocks of the canonical tree a unit computes. A unit owns whole
   power-of-two blocks of the tree, so the units' partial results combine in exactly the
   canonical order (the tree's blocks are the binary representation of n; a split at a block
   boundary keeps the tree). [I] This is the constraint that stops task parallelism from
   undoing the float result: a split that cuts a block would change the bits.
4. **Optimize and vectorize each unit** (L24.2): within a unit, vector lanes take the lowest
   levels of the unit's blocks (lane k sums the k-th of each group of w adjacent leaves, so the
   lanes are again whole sub-blocks when w is a power of two dividing the block). [I] This is
   what keeps vectorization from undoing the tree; the reduction across lanes then follows the
   tree's upper levels.
5. **Lower each unit and schedule its instructions last** (L29.1, the back end), with memory
   edges exact from A and E. Instruction scheduling and register allocation see one unit's
   straight-line or loop code and cannot move work across units, so they cannot undo the split.
6. **Pipelines (L24.3)** sit beside step 2: a synchronous dataflow pipeline is a split of the
   graph into stages instead of into data parts, with buffer sizes from W; each stage is then a
   unit for steps 3–5.

**Why this order and not another.**

| Order | Score | Reasoning |
|---|---|---|
| Facts → split into units → layout and tree per unit → vectorize per unit → lower and schedule per unit | 9 | each step works inside the boundaries the step before fixed; the float result is fixed by step 3; the vectorizer never sees a loop the split would later cut; costs come from W, not from measurement |
| Vectorize the whole loop, then split it into tasks | 4 | the vector width fixes a tree of lanes first, and a later split into tasks at a point that is not a multiple of the width breaks the canonical tree; GCC's parloops and LLVM have this order and need `-ffast-math` for parallel reductions |
| Hand ZIR to LLVM or Cranelift and let them parallelize | 1 | neither has task parallelism in its default pipeline (GCC parloops off; Cranelift none); both reorder float reductions under `reassoc` or not at all (section 5) |
| Split by run-time measurement (autotuning) | 2 | DESIGN forbids a crossover found by benchmarking (sec:runtime: "a crossing found by benchmarking the two plans is never used") |

The gap that remains: step 3's rule (a unit owns whole tree blocks) needs a proof that any
split at block boundaries, at any depth of divide-and-conquer, combines to the canonical tree.
It is stated here as [I] and filed as part of row CG-unit-split-tree (section 7).

## 7. Plan rows filed

Each row is consumed directly by one of the four steps the brief names, in that step's slot.

| Row | Passes it covers | Needs | Consumed by |
|---|---|---|---|
| CG-unit-split-tree | the order of section 6, steps 2–3: split by the strategy catalog, units owning whole blocks of the canonical tree, with the proof that such splits keep the tree | ZIR-cost-facts | L24.1 |
| CG-vectorize-facts | LoopVectorize, SLP, LoopAccessAnalysis, LoopLoadElimination, LoopDistribute, LoopInterchange, LoopFuse, tree-vect, ldist, Graphite, Polly: vectorize on P and A with no run-time alias check, the reduction emitted in the order of T | ZIR-checker-facts | L24.2 |
| CG-pipeline-fusion | LoopFuse, LoopDistribute, unroll-and-jam between pipeline stages: fuse or split stages on P with buffer sizes from W | ZIR-cost-facts | L24.3 |
| CG-scalar-facts | SCCP, IPSCCP, CorrelatedValuePropagation, ConstraintElimination, InstCombine range folds, BDCE, Float2Int, VRP, CCP, ipa-cp, remove_constant_phis: read D and M from the edge, run none of these analyses | ZIR-checker-facts | L29.1 |
| CG-memory-facts | alias analyses, MemorySSA queries, GVN loads, DSE, LICM promotion, MemCpyOpt, SROA, ArgumentPromotion, FunctionAttrs, ipa-modref, ipa-pure-const, Cranelift alias regions: read A, E and R | ZIR-checker-facts, EXE-plan-carried | L29.1 |
| CG-loop-cost-facts | ScalarEvolution, IndVarSimplify, LoopUnroll, LoopDeletion, LoopRotate, ivopts, ivcanon, cunroll, the inliner: trip counts and costs from W | ZIR-cost-facts | L29.1 |

Kept by L29.1 as its own work, with no row: instruction selection, instruction scheduling and
register allocation, where no checker fact replaces the analysis (sections 4.1–4.3, last rows).

## 8. What is not confirmed

1. Per-pass compile times were not measured; the cost column gives the algorithm and the
   cutoffs. `-ftime-report` on GCC and `-time-passes` on LLVM over a large unit would measure
   them.
2. Every "expected gain" is [I]. The one measured gain is the memcheck removed by `noalias`
   (section 5). Each other row can be tested the same way, by giving the fact to the compiler
   through an existing feature (`__restrict`, `__builtin_assume`, `llvm.assume`, range metadata,
   `safelen`) and reading the output.
3. Section 6 steps 3 and 4 (units and lanes owning whole tree blocks) are [I]; their proof is
   part of CG-unit-split-tree.
4. The source of the "7 times faster" claim was not found.
