# Deep-learning formats and lowering to matrix hardware: a study of Vx and what Zed needs

Plan row STUDY-vx-dl-lowering (author 2026-11-21). Written by study1, 2026-11-21.

Every claim is marked **[C]** (confirmed: the cited file was read at the cited lines, or the named program was run and printed the result) or **[I]** (inferred: a conclusion, with what would confirm it). DESIGN is cited by section name, never by line number.

Contents:

1. Sources and method
2. Vx v0.0.5 and its two ports
3. The system model: Vx's memory and compute hierarchies, and what Zed needs to match them with no annotation (main section)
4. Deliverable A: formats, proposals, scores, and the QUESTIONS entry
5. The Gemini claims
6. What the checker must prove to lower well: scored brainstorm
7. Deliverable B: the intrinsics by kind, and the kinds of lowering logic
8. Plan rows filed
9. Open claims, and the claim most likely wrong

---

## 1. Sources and method

**Repositories read.** The clones are in `/home/luke/Work/wt/trees/study1-scratch/vx/src/`. Nothing was built or run except where stated.

| Repository | Commit | Note |
| --- | --- | --- |
| Vx | tag v0.0.5 = `5b92da4ff` | All Vx file:line references are at this commit |
| glm-vx | `0589bc64f` (2026-11-20) | Its `moe_mma='vx16'` path needs Vx `10c6f478f`, newer than v0.0.5 |
| qwen-vx | `6992d3d13` (2026-11-20) | `VX_VERSION` is v0.0.5 |

**Primary specifications.** These were downloaded to `/home/luke/Work/wt/trees/study1-scratch/formats/src/`. Each source is recorded in `formats/verification/bib.md`, with the four arXiv papers fetched through the allpapers skill.

| Short name | Document |
| --- | --- |
| OFP8 | OCP 8-bit Floating Point Specification r1.0 (2023-12-01) |
| MX | OCP Microscaling Formats Specification v1.0 (2023-09) |
| FP8paper | arXiv:2209.05433 |
| MXpaper | arXiv:2310.10537 |
| NVFP4paper | arXiv:2509.25149 |
| DSV3 | arXiv:2412.19437 (DeepSeek-V3) |
| PTX | PTX ISA 9.5 |
| cuBLAS | cuBLAS documentation, updated 2026-11-02 |
| CDNA3, CDNA4 | AMD instruction-set guides |
| MSL | Metal Shading Language 4.1 |
| LLVM-x86, LLVM-AMDGPU | LLVM's x86 intrinsic headers (commit 83a19504f5c5) and `BuiltinsAMDGPU.td` |
| ACLE | Arm C Language Extensions (commit 74fa229b09d1) |
| IME | RISC-V integrated matrix extension, draft |
| SPIR-V | The SPV_KHR_cooperative_matrix, SPV_NV_cooperative_matrix2 and SPV_INTEL_joint_matrix extensions |
| SYCL | The SYCL joint_matrix extension |

**Programs run.** Three scratch Rust programs, built with `rustc -O`, are in the session scratchpad under `study1/fmtcheck/`. They are not repository code, since the repositories hold no scratch programs.

| Program | What it checks |
| --- | --- |
| `fmtcheck.rs` | It enumerates each narrow format from its bit layout and prints the limits. It checks that each finite value decodes exactly into f16, bf16 and f32. It also measures the clipping of the MX scale rule. |
| `exact.rs` | It finds the bits needed to sum a 32-element block of products exactly, and the share of random blocks whose f32 sum depends on the order of the additions. |
| `nvfp4.rs` | It runs the same exactness test for NVFP4 blocks, which have 16 elements and scales that are not powers of two. |

**Zed sources.**
- DESIGN.md at `/home/luke/Work/zed`.
- zed-impl at `a6b378c49`: `crates/zedc-base/src/cost.rs` and `zed/prelude/cost.zed`.

**Process note.** One of my research subagents wrote files into `/home/luke/Work/zed` against its brief. Its report says it wrote nothing there. I reverted its change to the bibliography with `git apply -R` and deleted the files it added, each by literal path. No commit contained them.

---

## 2. Vx v0.0.5 and its two ports

### 2.1 What Vx is [C]

- **Front end and checker.** They are written in Rust, in `src/parser`, `src/syntax` and `src/hir` (76,453 lines in `src/hir`). The checker uses Z3 in `prover.rs` and `solver.rs`. The proof that writes inside parallel loops do not collide, in `src/hir/across_proof.rs` (1,738 lines), does not use Z3.
- **Codegen.** It emits MLIR in a `vx` dialect (`src/codegen`). The C++ lowering in `src/dialect` includes `VxLowering.cpp` (14,173 lines), `MetalImage.cpp` (2,478 lines) and `NarrowFloats.cpp` (360 lines).
- **Outputs by target.**
  - The host goes through LLVM `opt` and `llc` with `-mcpu=native` (`src/jit.rs:465-520`).
  - NVIDIA gets PTX text.
  - Intel gets SPIR-V, loaded through Level Zero.
  - Apple gets Metal Shading Language source.
- **The system model** is a set of per-product machine files in `fleet/*.vx` (section 3).

### 2.2 The ports [C unless marked]

**glm-vx** serves GLM-5.3 in block FP8 on 8× H200 with tensor parallelism 8 (README.md:7-86). It has 177 `.vx` files and 29,213 lines.
- **What runs outside Vx.** cuBLASLt runs the prefill FP8 GEMMs, and NCCL runs the collectives.
- **Weights.** They are stored as `Tensor<f8e4m3,…,Memory::HBM>`, one byte per element. One f32 scale covers each 128×128 block.
- **Inline PTX.** 24 places in 15 files still use it, among them the FP8 `mma.sync` (Vx #3701) and Hopper `wgmma` (#3702).

**glm-vx speed claims, from its README:**

| Measure | Workload | glm-vx | SGLang | Ratio |
| --- | --- | ---: | ---: | ---: |
| TPOT (time per output token) | W1 | 8.55 ms | 9.18 ms | 0.93 |
| TPOT | ShareGPT | 8.34 ms | 9.00 ms | 0.93 |
| TPOT | W3 | 9.58 ms | 9.43 ms | 1.02 |
| TTFT (time to first token) | W1 | 624 ms | 88.7 ms | 7.0 times slower |
| TTFT | W3 | 114 s | 2.6 s | 43 times slower |

The README itself says: "SGLang was measured once, on another VM, and without speculative decoding." So the TPOT comparison is not like for like [I: the glm-vx speculative setting is not stated in the lines read].

**qwen-vx** runs Qwen2.5-Coder 0.5B and 7B (bf16, fp8 and Q4_0 weights) and Qwen3-Coder-30B-A3B (Q4_0) on an Apple M4 through Metal. It has 28 `.vx` files and 11,808 lines.
- **Speed.** A token took 28.0 ms against llama.cpp's 24.3 ms (README.md:291-294).
- **fp8 weights.** They are f8e4m3 codes packed four to a `u32`, decoded through a 256-entry table in shared memory. The table avoids subnormal f32 values "the GPU would flush to 0" (`stdlib/std/nn.vx:1295-1345`).
- **fp8 accuracy.** Perplexity is 20.030 against 20.054 for bf16 on 0.5B, and 10.085 against 10.072 on 7B.
- **Limits.** "the 32 KB of shared memory does not hold larger tiles (#19)" (README.md:330-333). Subgroup reductions and shuffles need `mlir!` blocks (`src/simd.vx:8-10`).

### 2.3 Narrow formats in Vx [C]

- **Types.** f8e4m3, f8e5m2, f4e2m1, f8e8m0, i4 and u4 (`src/syntax/types.rs:680-709`). Their MLIR names are `f8E4M3FN`, `f8E5M2`, `f4E2M1FN` and `f8E8M0FNU` (`mlir_ty.rs:25-40`).
- **Arithmetic.** It needs a written result type. The expression is computed in f32 and rounded once to nearest, ties to even (`NarrowFloats.cpp`; the book's low-precision chapter, lines 64-77). `let f = a * b;` on fp8 values is an error.
- **Saturation is silent.**
  - f8e4m3 saturates to 448 and f4e2m1 to 6.
  - f8e5m2 also saturates, to 57,344, even though the format has an infinity (book 43-49).
  - A literal too large for f8e4m3 folds to NaN (`types.rs:1342-1375`).
- **i4 and u4 wrap**, with no check.
- **Storage is not packed.** A 4-bit value takes one byte (`hir/memory.rs:129-132`; test at about 997-1008). Packing exists only inside the NVIDIA matmul lowering: two e2m1 per byte, low nibble first (`VxLowering.cpp:4581-4617`).
- **Scaled tensors.** "The compiler does not support the scaled tensor type yet (#1877)" (book 106-132).
  - The one block-scaled routine is `lanes::matmul_scaled` (`hir/check/lanes.rs:1312-1420`). It lowers to `mma.sync … m16n8k64 kind::mxf4nvf4` or `kind::mxf4` for sm_120a (`VxLowering.cpp:4301-4441`), and to an opt-in tcgen05 path (4443-4870, off unless `VX_TCGEN05=1`).
  - It accepts any block size (`lanes.rs:1406`).
- **Each device declares its types** in a `dtypes:` list, and any other type is error E6026. The H100 lists no fp4, and the M4 lists no fp8 and no fp4.

### 2.4 Parallel writes in Vx [C]

- **The loops.** A program maps loops to hardware levels with `across` (`for i in 0..n across blocks`). The meaning does not depend on `across`: "Remove each `across`, and the loops run one pass at a time with the same result."
- **The proof** in `across_proof.rs` (header 1-44) works on affine indices in the loop variables. It splits variables into mixed-radix digits, so `v/n` and `v%n` stay affine. It reads `idx[e]` from a `Distinct` tensor as fixing what `e` fixes. A write it cannot place is error E6032.
- **How the two properties are established.**
  - `Distinct<Tensor<i32,[?]>>` (no two elements equal) is checked on the CPU in O(n log n) by sorting (`stdlib/core/distinct.vx:23-116`).
  - `DisjointRanges` (half-open ranges with no overlap) is checked the same way.
  - Either may be asserted with `unsafe { Distinct(t) }`.
  - `std::nn` asserts it for the MoE grouping, "because the checker cannot see that no two pairs get the same position" (`nn.vx:1248-1294`).
  - glm-vx's Python passes the tensor through as a plain tensor (`gpu/spawn/build.py:194-195`).
  - So the property is checked at run time or trusted. It is never proved from the code that built the tensor.

### 2.5 Strengths and weaknesses

**Strengths [C]:**
1. A per-product machine model, with a stated source for every figure (section 3).
2. A compile-time capacity rule that covers everything from a microcontroller's 128 KiB to 183 GiB of HBM.
3. A proof that writes do not collide, without SMT, which leaves the program's meaning independent of the parallel mapping.
4. Exact narrow-float rounding: one rounding, ties to even, and the OCP E8M0 rule.
5. Working block-scaled FP4 tensor-core lowering.
6. NUMA placement end to end, predicting a 2.258 remote/local ratio against 2.348 measured.

**Weaknesses [C] (evidence in the vx report §9):**

| # | Weakness |
| --- | --- |
| W1 | 4-bit values take one byte each |
| W2 | No scaled type, no quantize or dequantize, no tensor scale; the ports hand-pack `u32` words |
| W3 | Any block size is accepted |
| W4 | No wgmma; the ports use inline PTX |
| W5 | tcgen05 is off by default |
| W6 | `Distinct` and `DisjointRanges` are checked at run time or trusted |
| W7 | No cluster level, no SM count in codegen, no CPU core or SIMD level, no latency, no compute throughput |
| W8 | Intel has no levels, no subgroup width, no XMX, and bf16 is declared but refused |
| W9 | Subgroup reduce and shuffle need `mlir!` |
| W10 | CPU code is built with `-mcpu=native` |
| W11 | Two doc comments are stale (`types.rs:1304, 1330-1336`) |
| W12 | The MoE rank loop costs O(l) per lane |

**Fixes for Vx, scored.** These are fixes for Vx itself, not for Zed. None was run, because building Vx was outside the brief.

| Fix | For | Score | Reasoning |
| --- | --- | ---: | --- |
| Correct the two doc comments | W11 | 10 | Comment only |
| Pack sub-byte storage two per byte, low nibble first | W1 | 9 | The order already exists at `VxLowering.cpp:4581-4617`; halves storage and traffic |
| Allow only block 16 with e4m3 scales and block 32 with e8m0 | W3 | 9 | One check near `lanes.rs:1406` |
| `subgroups::sum/max/shuffle` built-ins | W9 | 9 | qwen-vx already writes these ops in `mlir!` |
| A scaled tensor type with quantize and dequantize | W2 | 8 | Removes the hand-made formats of both ports |
| Emit wgmma on sm_90a | W4 | 8 | Removes glm-vx's largest inline-PTX file |
| `levels:` and a subgroup width for Intel | W8 | 8 | Mostly data |
| Prove `Distinct` from its construction | W6 | 7 | Removes `unsafe` from the stdlib; section 6 gives the proof |
| A baseline CPU for emitted objects | W10 | 7 | Portable objects |
| A prefix sum in place of the O(l) rank loop | W12 | 7 | O(l log l) or better |
| Cluster level and SM count | W7 | 6 | Touches every machine file |
| Compute throughput per type | W7 | 6 | Each figure needs a measurement per product |
| tcgen05 on by default | W5 | 6 | Depends on hardware results not seen |
| Run the Distinct check on the GPU | W6 | 5 | Still a check on every run |

---

## 3. The system model: Vx's memory and compute hierarchies, and what Zed needs to match them with no annotation

The author's note: "also study the Vx memory hierarchy and compute unit hierarchy, because this is at the core of the power of Vx: it has a very good model of the system characteristics."

### 3.1 How Vx describes a machine [C]

A machine file is plain declarations. A program is compiled against one of them: `vxc prog.vx --machine fleet/h100-sxm.vx` (book `writing-parallel-code.md:91`). The file `fleet/h100-sxm.vx`, read in full:

```
Memory HBM  { capacity: 80 GiB, bandwidth: 3.35 TB/s, managed: explicit, alignment: 16 B, scope: device }      // 18-21
Memory L2   { within: Memory::HBM, capacity: 50 MiB, bandwidth: 12 TB/s, managed: cached, scope: device }       // 25-27
Memory SMEM { within: Memory::L2, capacity: 228 KiB, bandwidth: 128 B/cyc, clock: 1.98 GHz, granule: 1 KiB,
              managed: explicit, alignment: 16 B, scope: sm, replicas: 132 }                                    // 32-37
Memory REG  { within: Memory::SMEM, capacity: 1020 B, managed: explicit, scope: thread }                        // 42-44
Topology Device {
  arch: nvptx64,
  levels: [blocks(max_lanes: 1024, memory: cta), subgroups(lanes: 32), lanes(memory: thread)],                  // 63
  chip: sm_90a,
  memory: Memory::HBM,
  visible: [Memory::HBM, Memory::L2, Memory::SMEM, Memory::REG],
  dtypes: [f64, f32, bf16, f16, f8e4m3, f8e5m2, i8, u8, i16, u16, i32, u32, i64, u64, bool],                  // 73
  transfer Memory::CPU_DRAM -> Memory::HBM : 63 GB/s,
  transfer Memory::HBM -> Memory::CPU_DRAM : 63 GB/s,
  transfer Memory::HBM -> Memory::L2,
  transfer Memory::L2 -> Memory::SMEM copy_engine                                                               // 74-81
}
```

**Every figure carries a `spec:` or `measured:` comment.**
- "replicas: measured: probe_edges reported SMs=132 on two rented H100 SXM boxes" (line 34).
- An unknown figure is left out rather than guessed. The Arc A770 L2 has no bandwidth, "left unpriceable rather than priced by a guess" (`arc-a770.vx:37-42`).
- The file names its own doubts. The host link "may reach the host over PCIe Gen5 or … NVLink-C2C at ~450 GB/s -- a 7x difference" (lines 54-58).

**The parser accepts exactly these keys** (`src/parser/decl.rs`, read 400-520 and 750-840):
- **`Topology`:** `arch`, `memory`, `visible`, `dtypes`, `chip`, `levels`, `count` (the number of devices of this kind) and `offload`; any other key is "Unknown topology field".
- **`Memory`:** `within`, `scope` (device, sm, cta or thread), `capacity`, `granule`, `alignment`, `bandwidth`, `clock`, `replicas`, `node`, `crossing` (streamed or sequenced) and `managed` (explicit or cached).
- No key states compute throughput or latency [C: the parser's full key list].

**Per-target figures [C, quoted from the machine files]:**

| Level | H100 SXM | B200 | Apple M4 | Arc A770 | Xeon 8275CL |
| --- | --- | --- | --- | --- | --- |
| Device memory | 80 GiB, 3.35 TB/s | 183,359 MiB, 7.7 TB/s | 32 GiB unified, 120 GB/s | 16 GiB, 560 GB/s | node 0: 96 GiB, 140 GB/s; node 1 as `PEER_HBM` |
| L2 / last level | 50 MiB, 12 TB/s | 126 MiB, 16 TB/s | 16 MiB, 400 GB/s | 16 MiB, unpriced | 36,608 KiB |
| Shared memory | 228 KiB, 128 B/cycle, 1.98 GHz, 132 copies | 228 KiB, 148 copies | 32 KiB, 10 copies | 64 KiB | none |
| Registers | 1,020 B per thread | as H100 | — | — | — |
| Host link | 63 GB/s each way | — | `shared` (no copy) | 31.5 GB/s; 10.8-11.7 measured (slot runs at Gen3) | UPI 62 GB/s; 51.55 measured |

Other files cover the A100, H200, MI300X (checks only; Vx has no AMD code path), multi-GPU nodes (the second GPU as `PEER_HBM`) and a Cortex-M7 (capacity check only).

### 3.2 How Vx uses the model [C]

**Capacity rule.** Every tensor placed in a space counts against its `capacity`, with `granule` and `alignment` rounding. Channel buffers count too (E6009). The same rule covers 128 KiB of DTCM and 183 GiB of HBM.

**Visibility rule.** A kernel that reads a space not in `visible:` is error E6003. For example, a kernel that reads host memory on NVIDIA or Intel is rejected (`arc-a770.vx:59-62`).

**Type rule.** A type not in `dtypes:` is error E6026.

**Transfer cost** (`src/hir/memory.rs`, read 15-60 and 445-595):
- **Formula.** The cost of moving `bytes` from `src` to `dst` is the sum over each space on the containment path of `ceil(bytes / bandwidth)` ("the paper's roofline").
  - A shared ancestor that is not an endpoint is excluded.
  - An ancestor that is an endpoint is included. The comment says that charging only the child "is what scored `L2->SMEM` at -91.3% against an H100".
- **Per-copy rates.** A device-wide figure on a path that crosses a per-SM space is divided by `replicas` (494-514). Without this, "the L2 term contributed nothing and `L2->SMEM` sat at -87%".
- **Combining legs.**
  - A destination declared `crossing: streamed` takes the slowest leg.
  - `sequenced` (the default) adds the legs.
  - A register file passed through on the way always adds. This was measured on H100 `L1->REG->SMEM`, M4 `L2->REG->SMEM` and `HBM->REG->SMEM`.
  - A route that ends at a register streams: "on an H100 `HBM->REG` measures 18.8 B/cyc, close to the 17.7 of its slowest leg and nowhere near the 10.1 that adding the legs predicts" (525-560).
- **Units.** Costs stay in cycles when every leg is in B/cycle, since "a cycle count is clock-invariant". Otherwise they are converted to picoseconds through the declared `clock`. A cycle-rated space with no clock gives no cost rather than an invented one (565-590).
- **Contention.** "`bandwidth / users` … recorded, not applied: whether that is the right law is unmeasured" (15-60).
- **One cost source per edge.** Each edge has exactly one cost source (E6013; comment at `h100-sxm.vx:46-52`). Edge costs are `Derived`, `Rate`, `Shared` (0 per byte, unified memory) or `Fixed(c)` (`src/arch.rs:155-175`). `Fixed` is "a relative latency" that "is not a time", which is the only notion of latency in Vx.

**NUMA.** Memory declares `node:`. Codegen gives each node a dispatch id (`arch.rs:367-387`). The runtime binds pages with `mbind(MPOL_BIND, MPOL_MF_MOVE)` (`runtime/host_dispatch_common.h:166-236`) and runs one node's CPUs after a placed dispatch (`runtime/vx_host_call.h:195-235`).

**Compute levels.** The `levels:` list is the compute hierarchy.
- The checker reads `max_lanes` and the subgroup width (`hir/check/across.rs:1133-1166`) and requires subgroups × width ≤ `max_lanes` (1284-1288).
- An `across` loop on a target with no levels is an error (1098-1106).
- The program names each level in its loops. The loop bounds set the launch shape (`stdlib/std/nn.vx:1670-1680`; glm-vx: "The loops give the launch shape (Vx #2097)").

### 3.3 What Vx leaves out [C]

| Level or quantity | Vx |
| --- | --- |
| SM or core count for sizing grids | Only `replicas:`, and only for cost. No file in `src/codegen` or `src/dialect` reads `replicas` [C: grep, rc 1] |
| Thread-block cluster | Not a level. "cluster" appears only as PTX scope text (`VxLowering.cpp:3312, 3503-3560, 4662`) |
| L1 | No GPU machine file declares one. It was used in measurements (`memory.rs:534`) but is not shipped |
| CPU cores and SIMD width | Not levels. Host parallelism is a run-time thread count. `CpuAvx512` and `CpuNeon` lower as `CPU` (`codegen/lower/tensors.rs:76`) |
| Matrix units | Only the name `Topology::AMX`. The ports reach the tensor cores through fixed routines and inline PTX |
| Intel subgroup width | Not modeled; `arc-a770.vx` has no `levels:` |
| Compute throughput, latency in time | Not modeled. The model prices data movement only |
| Who maps loops to levels | The programmer, with `across` |

### 3.4 What Zed has today [C]

`crates/zedc-base/src/cost.rs:17-41`, mirrored in `zed/prelude/cost.zed:7-14`:

```rust
pub struct Device { pub name: &'static str, pub cores: u64, pub op_time: u64, pub capacity: u64 }
pub struct Target { pub devices: Vec<Device>, pub transfer_latency: u64,
                    pub transfer_per_block: u64 /* per 64 bytes */, pub nominal_size: u64 }
```

The default profile is one CPU of 8 cores, one time unit per unit of work, and 16 GiB. DESIGN sets the frame Zed must fill:
- **"Placement is one optimization problem":** device, strategy, tile, grain, buffer depth and `k` are one choice, made per build "for the hardware declared".
- **"Cost model, two tiers":** symbolic formulas first, calibrated constants second. A crossing between plans is "solved from the two plans' symbolic cost formulas … a crossing found by benchmarking the two plans is never used".
- **Hardware identity.** Plans are cached by content address and hardware identity (step L24.6: core count, ISA level, accelerator model, memory sizes, interconnect).
- **No levels.** Zed has no memory levels below a device, no compute levels, no matrix units, no per-type rates and no latency.

So Zed's target model today is coarser than Vx's in every column. The difference is the one the author points at: Vx can reject a tile that does not fit shared memory and can price a copy within a few percent, and Zed can do neither [C for Vx: `memory.rs` comments with measured errors; I for "within a few percent" across all routes, which Vx shows for the routes it measured].

### 3.5 What Zed needs, with no annotation

**The difference in approach.** In Vx the programmer writes the hardware mapping: the space of every tensor (`Tensor<f32,[64,64],Memory::SMEM>`), the level of every parallel loop (`across blocks`), and the machine file. In Zed the program says none of this. A program states values and domains; the plan is chosen by the compiler (DESIGN "Placement is one optimization problem"). So Zed needs Vx's model in the compiler, as data, with the decisions Vx leaves to the programmer made by the placement solver.

**Proposals, scored:**

| # | Proposal | Empirical | Score | Reasoning |
| --- | --- | --- | ---: | --- |
| Z1 | **Target description per hardware identity**, written as Zed prelude data, not in user programs. Contents: memory levels (capacity, bandwidth, granule, alignment, scope, copies per device, clock, NUMA node, managed or cached, streamed or sequenced fill); compute levels (devices, SMs or cores, clusters, block lane limit, subgroup or SIMD widths); matrix units (shapes, operand types, accumulator types, rate); rate per operation and type; latency in time units; transfer edges with one cost source each (Vx E6013) | Vx shows the shape works across 17 machine files [C] | 9 | It is Vx's model with the four gaps of 3.3 filled; it is data, so it never touches the language; the identity already exists in step L24.6 |
| Z2 | **Two sources for each figure**: a vendor table with a citation in the description (Vx's `spec:` policy), and calibration probes per hardware identity as the second tier, stored as measured pins (step L24.7) and never re-measured silently | Vx's probes found 132 SMs and an 18.8 B/cycle register route that the vendor tables do not give [C] | 9 | DESIGN already splits the cost model into symbolic and calibrated tiers; Vx shows why both are needed: its comments record the -91.3% and -87% errors that measurement exposed |
| Z3 | **Capacity rule**: the peak footprint of each placed region at each memory level ≤ that level's capacity, rounded to the granule; a constraint of the placement solver, from the symbolic sizes; when no choice fits, the message names the level, the footprint formula and the capacity | Vx's E-codes cover the same cases [C] | 9 | DESIGN "Cost model, two tiers" already checks footprints against device capacity; this extends it one level down |
| Z4 | **Transfer cost from the containment path**, with Vx's corrections: endpoints included, per-copy denomination, registers in the middle added, streamed destinations taking the slowest leg; whole numbers in cycles or picoseconds as Vx does | Vx measured these corrections on H100 and M4 [C] | 8 | It reuses measured knowledge; integer arithmetic matches cost.rs, which saturates on integers |
| Z5 | **Compute rate per unit and type** (FMA/cycle for scalar, SIMD and matrix units per type), so the cost is a roofline: max(data time, compute time) per region | Not run | 8 | Vx has no compute term (3.3), so it cannot choose between a tensor-core plan and a SIMD plan by cost; Zed must, since the user does not choose |
| Z6 | **Automatic mapping of domain levels to compute levels.** The solver maps each level of a tensor domain to grid, cluster, block, subgroup or lane (GPU) or node, core or SIMD lane (CPU), with tile sizes, from the capacities and the cost model. Legality: the writes of parallel instances are proved disjoint by Presburger arithmetic and the witness catalog (DESIGN sec:remap_law), as Vx proves them for `across`. No `across` is written | Not run | 9 | The user writes no level names. DESIGN's "evaluation strategy changes no value" is exactly Vx's "remove each `across` … same result", made automatic |
| Z7 | **Contention** (`bandwidth / users`): measure per identity whether shared links divide evenly or fall off a cliff, then use the measured law | Vx records the term and does not apply it [C] | 6 | Unknown law; folded into Z2's calibration row as a measured question, not a separate row |
| Z8 | **User-written machine files**, Vx style, as the way to state hardware | — | 3 | It is annotation, which the author excludes; Zed detects the identity and the user may only name a known identity in `with target(…)` for a cross-build (already in L24.4) |
| Z9 | **Fixed per-vendor constants in the compiler** (no tables, no probes) | Vx's measured errors show the first constants were off by up to 91% [C] | 1 | Fails on the first new product and cannot be corrected without a compiler release |

**The NUMA, unified-memory and multi-GPU cases fit inside Z1 with no new mechanism:**
- A NUMA node is a memory level with a node number.
- Unified memory is a transfer edge of cost 0 per byte for borrowed data.
- A peer GPU is a memory level reached over a link edge.

**What the user writes.** Nothing beyond what DESIGN already has:
- `with target(#gpu)` is a hint, and `@require(@target(#gpu))` is a demand.
- The hardware identity is detected at build time, or named for a cross-build.

**What the checker proves:**
- the capacity constraints;
- the disjointness of parallel writes;
- that each chosen instruction exists on the identity, as Vx's `dtypes:` check does.

**What the lowering gets:** the level each loop runs at, its tile sizes, the memory level of each buffer, and the buffer depth of each pipeline.

**Rows** (section 8): TARGET-desc (Z1, Z3, Z4, Z5), TARGET-calibrate (Z2, Z7) and MAP-compute-levels (Z6), in the L24.x slot. MAP-compute-levels is consumed by L24.5 and TARGET-calibrate by L24.6.

---

## 4. Deliverable A: formats, proposals, scores

### 4.1 The formats, checked against the primary specifications

**Limits.** All are [C] twice: read in the specification, and printed by `fmtcheck.rs` from the bit layouts.

| Format | Layout, bias | Max | Min normal | Min subnormal | Inf | NaN | Source |
| --- | --- | ---: | --- | --- | --- | --- | --- |
| E4M3 (OCP FP8) | 1/4/3, 7 | 448 | 2^-6 | 2^-9 | none | S.1111.111 only | OFP8 §4.2 |
| E5M2 (OCP FP8) | 1/5/2, 15 | 57,344 | 2^-14 | 2^-16 | S.11111.00 | S.11111.{01,10,11} | OFP8 §4.2 |
| E3M2 (FP6) | 1/3/2, 3 | 28 | 2^-2 | 2^-4 | none | none | MX Table 4 |
| E2M3 (FP6) | 1/2/3, 1 | 7.5 | 2^0 | 2^-3 | none | none | MX Table 4 |
| E2M1 (FP4) | 1/2/1, 1 | 6 | 2^0 | 2^-1 | none | none | MX Table 5 |
| E8M0 (MX scale) | 0/8/0, 127 | 2^127 | — | 2^-127 | none | 0xFF | MX §5.4.1 |
| MXINT8 element | two's complement × 2^-6 | 127/64 | — | 2^-6 | none | none | MX Table 6 |
| UE4M3 (NVFP4 scale) | E4M3 with the sign ignored | 448 | 2^-6 | 2^-9 | none | as E4M3 | cuBLAS 9218 |
| MI300 "E4M3" | 1/4/3, **8** | **240** | 2^-7 | 2^-10 | none | 0x80 | CDNA3 Table 30 |
| bf16 | 1/8/7, 127 | ≈3.39e38 | 2^-126 | 2^-133 | IEEE | IEEE | OFP8 layout note [C]; limits derived [I] |

**Block formats.**

| Format | Elements per block | Scale | Second level | Source |
| --- | --- | --- | --- | --- |
| MXFP8, MXFP6, MXFP4, MXINT8 | 32 | one E8M0 per block | — | MX Table 1 [C] |
| NVFP4 | 16 E2M1 values | one UE4M3 per block | one f32 scale per tensor; 4.5 bits per value | NVFP4paper `main.tex:106-140` [C] |
| cuBLAS on Hopper (FP8) | 128 (1-D) or 128×128 (2-D) | one f32 per block | — | cuBLAS 9184-9199 [C] |

**Decoding is exact [C, `fmtcheck.rs`].** Every finite value of E4M3, E5M2, E3M2, E2M3, E2M1 and the MXINT8 element is exactly representable in f16, in bf16 and in f32. E8M0 is exact in bf16 and f32, but not in f16, whose range ends at 2^15 above and 2^-24 below. So reading a narrow element is a widening cast in the sense of DESIGN "The `inexact` fact", and sets no inexact fact. Applying an E8M0 scale is exact in f32 when the result stays normal.

**The MX scale rule clips [C, `fmtcheck.rs`].** The rule is X = 2^(floor(log2 amax) − emax_elem) (MX §6.3; MXpaper 122-135; the two statements agree, since the largest power of two in the element type is 2^emax_elem). The scaled block maximum then lies in [2^emax, 2^(emax+1)), which can exceed the element maximum, and those values clamp. The block maximum itself loses up to 1 − maxelem/2^(emax+1) of its value:

| Format | Scaled max reaches below | Element max | Values clamp from | Worst relative error of the block max |
| --- | ---: | ---: | --- | ---: |
| MXFP8 E4M3 | 512 | 448 | 1.75 × 2^k | 0.125 |
| MXFP8 E5M2 | 65,536 | 57,344 | 1.75 × 2^k | 0.125 |
| MXFP6 E3M2 | 32 | 28 | 1.75 × 2^k | 0.125 |
| MXFP6 E2M3 | 8 | 7.5 | 1.875 × 2^k | 0.0625 |
| MXFP4 E2M1 | 8 | 6 | 1.5 × 2^k | 0.25 |
| MXINT8 | 2 | 127/64 | 1.984 × 2^k | 0.0078 |

Plain round-to-nearest within range costs at most half a unit in the last place, 2^-(m+1) relative at the top of a binade (0.0625 for E4M3). So for FP8 and FP4 the clamping, not the rounding, sets the worst error of the block maximum.

**cuBLAS uses a different rule.** It computes amax/amax(type) and rounds the scale's exponent up, and says so: "The algorithm above differs from the OCP MXFP suggested rounding scheme" (cuBLAS 9312-9358) [C]. Rounding up never clamps and gives up to one binade of range instead. The NVFP4 paper notes the same loss for any power-of-two scale (`main.tex:544-546`) [C].

**Vendor document errors [C, each checked against the OCP specifications].**
- AMD CDNA4 Table 30 gives the BF6 (E3M2) minimum subnormal as "S.000.11 = 0.0675". It is S.000.01 = 0.0625; S.000.11 is 0.1875.
- Apple MSL 4.1 Table 2.16 gives the E5M2 NaN as "S 11111 {00,10,11}". The 00 pattern is infinity; it should read {01,10,11}.

### 4.2 Exact block sums: when matrix hardware gives the canonical tree's result

DESIGN sec:reduction item 1 fixes the default float sum: the canonical tree of power-of-two aligned blocks, combined left to right, with round to nearest even, no FMA contraction and the canonical NaN. Matrix units add in their own order, so in general an MMA result differs from the tree, and DESIGN allows it only under `unordered`. The study found a class where the order provably does not matter.

**Measured [C, `exact.rs`, 200,000 random blocks of 32, each summed in 50 random f32 orders].** "Bits" is the significand width an exact block sum of products needs. "Blocks that differed" counts blocks where some order gave a different f32 result from the exact sum.

| Elements | Bits needed (f32 has 24) | Blocks that differed |
| --- | ---: | --- |
| E2M1 (FP4) | 12.2 | 0 of 200,000 |
| E2M3 (FP6) | 16.8 | 0 of 200,000 |
| E3M2 (FP6) | 22.6 | 0 of 200,000 |
| MXINT8 | 19.0 | 0 of 200,000 |
| E4M3 (FP8) | 40.6 | 197,869 of 200,000 |
| E5M2 (FP8) | 68.6 | 200,000 of 200,000 |

**Proof** (the measurement only confirms it).
- Let q = minsub², the smallest product quantum. Every product of two elements is an integer multiple of q, so every partial sum of a block is too.
- Every partial sum satisfies |s| ≤ 32·max².
- So each partial sum is an integer of at most log2(32·max²/q) bits times q:
  - E2M1: 32·36/0.25 = 4,608, which is 12.2 bits.
  - E3M2: 32·784/2^-8 = 6,422,528, which is 22.6 bits.
- Below 24 bits, f32 holds every partial sum exactly, so every order gives the exact sum.
- E3M2 stays below 24 bits up to blocks of 64 (23.6 bits) but not 128 (24.6).

**NVFP4 too [C, `nvfp4.rs`, 200,000 random blocks of 16, 20 random orders each].**
- Its UE4M3 scales are not powers of two, but each has at most a 4-bit significand.
- An E2M1 block sum is an integer of at most 13 bits times 0.25 (at most 4,608), and two scales multiply it by at most 15·15 = 225, so the result needs at most 21 bits.
- No block differed from the exact value, whether the scales were applied to each element (as dequantizing would) or once to the block sum. The largest exact result needed 16.9 bits.
- The f32 per-tensor scale has a 24-bit significand, so it is exact only if applied once to the whole dot product, as NVIDIA's epilogue applies it [C: NVFP4paper 496-541 gives the two-level structure]. The quantized value's meaning must therefore keep the tensor scale as a separate factor, not folded into each element.

**Consequence: a lowering theorem (derivation).** Assume:
- K is a multiple of 32;
- the elements are FP4, FP6 or MXINT8 with E8M0 scales, or NVFP4 with its tensor scale kept apart;
- no scaled product underflows or overflows f32. The checker proves this from the scale domain. Under the MX rule applied to f32 data, the scale is at most 2^119 (from 448·2^s ≤ f32 max), so dequantized values are exact. An arbitrary loaded E8M0 scale needs a domain proof.

Then:
1. The canonical tree splits into aligned subtrees of 32 elements, because each power-of-two block of a length that is a multiple of 32 is itself a multiple of 32.
2. Each 32-subtree's value is its exact sum, by the bound above.
3. So "dequantize to f32, then the default `tree` sum" equals "exact block sums times scales, then the canonical tree over the block results".
4. The lowering may run each block (or each 64-element instruction, if the hardware is exact over 64) as an MMA with C = 0.
5. It then merges the block results with a stack of log2(K/32) f32 accumulators. That is a binary counter: when two subtrees of equal size are on top, add them. At the end, add the remaining stack bottom to top. This reproduces the canonical tree bit for bit, with amortized one f32 add per block.

The result is the tensor-core speed with Zed's default meaning: no `unordered`, no `@approx`, and the same bits on every target.

**Not proved:** that the hardware computes each block exactly [I]. MX §6.1 leaves the internal precision "implementation-defined" [C].
- The RISC-V IME draft sums integer MX blocks exactly and rounds once (`integrated-matrix.adoc:1282-1291`) [C, draft].
- CDNA4 gives an exponent formula but no width [C].
- NVIDIA states no accumulator width. The only figure is DeepSeek's: a 14-bit accumulation on H800 FP8 (DSV3 `fp8.tex:70-83`) [C that DeepSeek says it; not confirmed by NVIDIA].
- So the theorem licenses MMA only where a per-identity test shows the block result exact. That is row MMA-accumulator-tests: adversarial inputs (a large product plus many small ones of the opposite sign), per hardware identity, cached with the identity.
- The local RTX 3050 (compute capability 8.6) has no FP4 or FP8 units, so only its f16, bf16 and int8 MMA can be tested here [C: `nvidia-smi`].

**FP8 (E4M3, E5M2) is not exact.** Its MMA needs `unordered` with f32 accumulation stated, or `@approx`.

**Two further exact cases (derivation):**
- **int8 times int8 into int32 is exact** when K·16,384 ≤ 2^31 − 1, that is K ≤ 131,071. For symmetric `int[-127..=127]`, K ≤ 133,144. Integer addition is associative, so the order never matters.
- **f16 or bf16 products are exact in f32**: 22 and 16 significand bits, with exponents in range. Only the sums round, so f16/bf16 MMA equals the tree only under `unordered`, unless the domain proves the sums exact, for example whole numbers below 2^24.

### 4.3 How each proposal fits DESIGN

The anchors:
- **"The float formats are the four native ones"** (sec:reduction item 6): f64, f32, f16 and bf16.
- **"The `inexact` fact"**: rounding sets it, and widening casts are exact.
- **Ties to even** by default, with `ties: #away` as an option.
- **Casts are domain proofs** (sec:corner_cases). An integer cast is typed `T | #invalid | #overflow`; a float format has no overflow atom and gives an infinity with the fact `overflow()`.
- **"Machine operations"**: saturation is written as `clamp`; approximate instructions need `@approx`.
- **The tensor rule**: every vector or matrix operation is defined on tensors of any number of levels.
- **The `layout` facet**: a hint, which no result depends on.

**A1. Narrow formats as storage element types only.**
- **The user writes** `[f8e4m3; o: 4096, k: 4096]`, `[f4e2m1; …]`, `[f6e3m2; …]`, `[e8m0; …]` or `[ue4m3; …]`.
- **Reading is exact.** A read is a widening cast to f16, bf16 or f32 (4.1), so it sets no inexact fact.
- **Arithmetic happens in a native format.** `a * b` on two f8e4m3 values is typed f32 (or the written result type), exactly as DESIGN already computes f16 in f32. The narrow formats are not added to the arithmetic tower.
- **Units ride on the value** as for any number. A scale is dimensionless.
- **The checker proves:** that every store goes through a cast (A4), and that the packing is a bijection (A3).
- **It lowers to:** packed loads with a decode by table or bits (qwen-vx's 256-entry table is one option, chosen by cost), or the matrix unit's native operand type.
- **Score 9.**

**A2. Narrow formats as full scalar arithmetic types**, as Vx does: compute in f32, round once.
- It adds six formats to the tower, each with every operator, for almost no use: deep-learning arithmetic happens in the accumulator, not the storage format.
- Vx needs a written result type for each operation, which is A1's rule in another form.
- **Score 3.**

**A3. Packing.**
- FP4 and int4 go two per byte, low nibble first (the tcgen05 order, `VxLowering.cpp:4581-4617`).
- FP6 goes four values per three bytes.
- The packing is the affine repack of DESIGN sec:grouping. An element index i maps to byte ⌊i/2⌋ and nibble i mod 2. That is mixed-radix, so the catalog's affine-packing witness proves it bijective.
- The layout facet may choose another order, since no result depends on it.
- **Score 9.** Vx's weakness W1 shows the cost of not packing: twice the storage and traffic.

**A4. Cast rules into a narrow format.** These follow DESIGN's dividing line between formats with and without an infinity.
- **E5M2** (has an infinity): the float rule, giving infinity with the fact `overflow()`, rounding to nearest even with `inexact()`.
- **E4M3, FP6, FP4** (no infinity): the cast is typed `T | #overflow`, as integer casts are. The checker drops the atom where the domain proves |x| ≤ max (448, 28, 7.5 or 6).
- **NaN.** A NaN cast into FP6 or FP4 gives `#NaN`; E4M3 keeps NaN.
- **Saturation is written, never implied:** `f8e4m3(clamp(x, -448, 448))`, which lowers to PTX `cvt.rn.satfinite`, AMD with FP16_OVFL = 1, Arm FPMR bit 15 = 1, or AVX10.2's S forms. This matches DESIGN "Machine operations", where `clamp(a + b, lo, hi)` lowers to `add.sat`.
- **Lowering cost.** PTX makes `.satfinite` mandatory for f8, f6 and f4 destinations (`ptx.txt:12110`) [C]. So the infinity-giving E5M2 cast needs a compare and a select after the convert on NVIDIA. That is one extra instruction pair, paid only where the domain does not prove the range.
- **Score 9.**

**A5. Silent saturation on every cast**, as Vx and Metal's defaults do.
- A value changes with no message, against exact-by-default and against the user's standing rule of no surprises.
- **Score 2.**

**A6. Block-scaled tensors.**
- **What the user writes:** `quantize(x, #mxfp4)`, `quantize(x, #mxfp8e4m3)`, `quantize(x, #nvfp4)` and so on.
  - The result is a value of a block-scaled tensor type, which holds the element tensor, the scale tensor and, for NVFP4, the tensor scale.
  - Its block level is a named level split by an affine repack (`k` into `kb` and 32), so the scale tensor's levels match the data's levels by type check, by the tensor rule.
  - The block size is fixed by the format, which avoids Vx's W3.
- **Dequantize.** `dequantize(q)` gives an f32 tensor, exactly (4.1).
- **Quantize is inexact.** It sets `inexact()` and carries a checker-proved error bound per block. The bound is the rounding term 2^-(m+1) relative plus the clipping term of 4.1 under the OCP rule.
- **Dot products.** A dot of two quantized tensors means "dequantize, then the default sum", and lowers per 4.2.
- **The checker proves:** the block relation, the scale range (no overflow on dequantize), and K a multiple of 32 (or 16) for the exact-block lowering. Without those, it uses an ordinary peeled remainder with the same meaning.
- **It lowers to:** block-scaled MMA with in-instruction scales (PTX `kind::mxf8f6f4`, `mxf4nvf4`; CDNA4 `V_MFMA_SCALE_*`; gfx1250 `wmma_scale`), or decode-and-multiply on targets without them.
- **Score 8.** It needs DESIGN text and the decision in 4.6.

**A7. The scale rule inside `quantize`.**
- **Option (a):** OCP's floor rule by default, with the clipping bound reported, plus `rule: #ceil` for cuBLAS's round-up rule.
- **Option (b):** the reverse.
- The trade-off:
  - The floor rule clips up to 25% of the block maximum for FP4 (4.1).
  - The ceil rule never clips but spends up to one binade.
  - OCP-quantized checkpoints and AMD/NVIDIA scaled conversions follow the floor rule (CDNA4: "add an 8-bit exponent bias … shared by a block of 32"; PTX `.scaled::n1::ue8m0`) [C].
- **Score:** (a) 7, (b) 6. This is the author's decision, in 4.6.

**A8. Stochastic rounding.**
- **The user writes** `f8e4m3(x, rounding: #stochastic(bits))`, where `bits` come from a seeded Random port.
- The result is a function of x and the bits, so a run is deterministic given its seed and replays bit for bit, as DESIGN requires of every random source.
- **It lowers to:** PTX `cvt.rs` (the `rbits` operand, `ptx.txt:12291`), AMD `CVT_SR_*`, or a software fallback with identical bits: add the random bits to the truncated mantissa bits and truncate, the rule PTX states.
- It sets `inexact()`.
- **Score 7.**
- **Hardware stochastic rounding with bits the program does not supply** scores 1: the result would not replay.

**A9. int4.**
- int4 is the interval types `int[-8..=7]` and `int[0..=15]` packed per A3.
- Zed integers never wrap, so a store that might leave the interval is the ordinary domain-proof cast (`T | #overflow`), unlike Vx's wrapping i4 and u4.
- **It lowers to:** PTX `.s4`/`.u4` MMA (m8n8k32, up to Ampere), gfx11/12 `iu4` WMMA, Metal `int4b`, or unpack and int8 dot.
- **Score 9.**

**A10. Accumulation.**
- The default is f32 over the canonical tree.
- The exact-block theorem (4.2) licenses MMA for FP4, FP6, MXINT8 and NVFP4 with no change of meaning, and int8 into int32 is exact under the K bound.
- f16 or bf16 inputs take MMA under `unordered` (with the reorder facet DESIGN attaches) or under a domain proof of exact sums.
- **Score 9.**

**A11. fp16 accumulation** (MMA with an f16 accumulator).
- It is legal only where the user writes an f16 accumulator and `unordered`, since the hardware's order is not the tree.
- It is never chosen silently.
- **Score 6.** It is part of MMA-lowering's menu, with no row of its own.

**A12. The MI300 FP8 variants** (bias 8, max 240, NaN 0x80) as more storage formats.
- They are needed only to read MI300 checkpoints. MI355 uses OCP.
- **Score 5.** Not filed: noted in NARROW-storage-types as a later addition if a corpus program needs it.

**A13. TF32 MMA for f32 inputs.**
- It drops 13 significand bits of each input.
- It is allowed only under `@approx(relErr: e)`, with e at least the proved bound, as DESIGN treats `.approx` instructions.
- **Score 6.** It goes on the MMA-lowering menu, with no row of its own.

### 4.4 Summary table, sorted

| Proposal | Empirical result | Score | Reasoning |
| --- | --- | ---: | --- |
| A1 storage-only element types, read by an exact widening cast | Exact decode of all six formats into f16, bf16 and f32 [C] | 9 | Fits "the four native formats" unchanged; arithmetic stays in native formats |
| A3 packing as an affine repack | Not run | 9 | Witness already in the catalog; halves storage |
| A4 cast rules on DESIGN's inf/atom line, saturation written as `clamp` | `.satfinite` mandatory in PTX [C] | 9 | Follows "Casts are domain proofs" and "Machine operations" exactly |
| A9 int4 as packed interval types | Not run | 9 | No new type; no wrap |
| A10 f32 tree accumulation with the exact-block license | 0 of 200,000 FP4/FP6/MXINT8/NVFP4 blocks order-dependent [C] | 9 | Tensor-core speed with the default meaning |
| A6 block-scaled tensors with quantize and dequantize | Clipping bounds measured [C] | 8 | Removes hand-made formats (Vx W2); needs DESIGN text |
| A7(a) OCP scale rule by default, `rule: #ceil` | Clipping 0.25/0.125 measured [C] | 7 | Matches stored checkpoints and hardware conversions |
| A8 stochastic rounding with program-supplied bits | Not run | 7 | Deterministic given the seed; hardware forms exist on NVIDIA and AMD |
| A7(b) ceil rule by default | — | 6 | No clipping, but not OCP's rule |
| A11 f16 accumulation under `unordered` | — | 6 | Legal but never silent |
| A13 TF32 under `@approx` | — | 6 | Matches DESIGN's `@approx` rule |
| A12 MI300 FP8 variants | — | 5 | Only for MI300 checkpoints; not filed |
| A2 full scalar narrow types | — | 3 | Six formats in the tower for little use |
| A5 silent saturation | — | 2 | A changed value with no message |
| A8′ hardware stochastic rounding with unsupplied bits | — | 1 | Does not replay |

### 4.5 Rows from Deliverable A

| Row | Contents |
| --- | --- |
| DECIDE-narrow-formats | The author's decision (4.6) |
| NARROW-storage-types | A1, A3, A4, A9 |
| BLOCK-scaled-tensors | A6, A7 |
| SR-stochastic-rounding | A8 |
| MMA-lowering, MMA-cpu-units, MMA-accumulator-tests | A10, A11, A13 |

Section 8 gives the full rows.

### 4.6 QUESTIONS entry (text for the orchestrator to write into QUESTIONS.md)

> **Narrow storage formats for tensors (fp8, fp6, fp4, block-scaled), from STUDY-vx-dl-lowering.**
>
> Holds up: DECIDE-narrow-formats, then NARROW-storage-types, BLOCK-scaled-tensors, SR-stochastic-rounding and the matrix-unit lowering rows MMA-lowering and MMA-cpu-units.
>
> DESIGN says "The float formats are the four native ones" (f64, f32, f16, bf16). Deep-learning weights and activations are now stored in 8-, 6- and 4-bit formats (OCP FP8 E4M3 and E5M2; OCP MX FP6 and FP4 with a shared E8M0 scale per 32 values; NVIDIA's NVFP4 with an E4M3 scale per 16 values and an f32 scale per tensor), and every current matrix unit reads them. A program today cannot hold such a tensor except as bytes it decodes by hand.
>
> ```
> // A: storage element types (recommended)
> let w: [f4e2m1; o: 4096, k: 4096] = load(...);   // two values per byte
> let q = quantize(x, #mxfp4);                      // inexact(); error bound per block proved
> let y = dequantize(q) * w;                         // reads are exact casts to f32; default tree sum
> let h = f8e4m3(clamp(z, -448, 448));               // saturation written, as add.sat is
> let g = f8e4m3(z);                                 // typed f8e4m3 | #overflow unless |z| <= 448 is proved
> ```
>
> | Option | What it adds | Score |
> | --- | --- | ---: |
> | **A (recommended)** | The formats as tensor element types only: a read is an exact widening cast (every value of each format is exact in f16, bf16 and f32, checked by enumeration); arithmetic stays in the four native formats; casts in follow DESIGN's line: E5M2, which has an infinity, follows the float rule, while E4M3, FP6 and FP4 give `T \| #overflow`; saturation is written as `clamp`; block-scaled tensors through `quantize` and `dequantize` with the OCP scale rule by default and `rule: #ceil` for cuBLAS's | 9 |
> | B | A, with cuBLAS's ceil scale rule as the default and `rule: #ocp` as the option: no clipping (the OCP rule clips the block maximum by up to 25% for FP4, 12.5% for FP8, measured), but not the rule stored checkpoints and AMD/NVIDIA scaled conversions use | 7 |
> | C | Full scalar arithmetic types for each narrow format, as Vx has (each operation computed in f32 and rounded once) | 3 |
> | D | No narrow formats in the language; libraries decode bytes | 2 |
>
> With A, a matrix unit can run FP4, FP6, MXINT8 and NVFP4 dot products with no change of meaning: every block of 32 sums exactly in f32 in any order (proof in docs/dl-lowering-study.md 4.2; 0 of 200,000 random blocks differed), so the hardware result equals the default canonical tree once a per-hardware test confirms the unit sums each block exactly. FP8 is not exact (40.6 bits needed) and runs on matrix units only under `unordered` or `@approx`.
>
> Recommended: A. Apply to DESIGN: sec:reduction item 6 (the storage formats beside the four native ones), sec:corner_cases (the casts), "Machine operations" (the saturating converts), sec:linalg (quantize, dequantize, the block-scaled types).

---

## 5. The Gemini claims

The author's pasted Gemini summary made these claims. Verdicts are checked against the primary sources of 4.1 [C].

| Claim | Verdict |
| --- | --- |
| "E4M3 max about 448" | Holds, and exactly: 1.75 × 2^8 = 448, so "about" is wrong. False on AMD MI300, whose E4M3 has bias 8 and max 240 (CDNA3 Table 30) |
| "E5M2 max about 57,344" | Holds exactly (1.75 × 2^15), on OCP and on MI300 |
| "E2M1 max 6" | Holds exactly (1.5 × 2^2) |
| "Block sizes of 16 or 32" | Holds with attribution: 32 for OCP MX (E8M0 scale), 16 for NVFP4 (UE4M3 scale). Incomplete: cuBLAS on Hopper uses 128 and 128×128 blocks with f32 scales, and the RISC-V IME draft allows MX blocks of 16 |

Gemini's model of accumulation ("tensor cores accumulate in FP32") is not stated by NVIDIA in any document read. DeepSeek measured a 14-bit accumulation for FP8 on H800 (DSV3 `fp8.tex:70-83`). Hence the hardware-test row MMA-accumulator-tests.

---

## 6. What the checker must prove to lower well: scored brainstorm

Each item gives what is proved, how, and what the lowering gains. "Empirical" names a measurement where one exists.

| # | Item | Empirical | Score | Reasoning |
| --- | --- | --- | ---: | --- |
| P1 | **Exact block sums (bounds that allow narrow inputs without changing the result)**: K a multiple of 32 or 16, the element format in {FP4, FP6, MXINT8, NVFP4}, scales in range: the MMA's per-block result equals the canonical tree's (4.2); int8 into int32 under K ≤ 131,071 | 0 of 200,000 blocks order-dependent for each exact format; FP8 order-dependent in 99% of blocks [C] | 10 | The one route to tensor-core speed with the default meaning; a Presburger fact on the domain plus a range fact on the scales |
| P2 | **Tile shapes and alignment**: the domain's extents are multiples of the instruction shape (m16n8k32, m64nNk32, 16×16×128 …) and the base addresses are aligned (16 B for `ld.shared.v4`, 128 B for TMA); otherwise peel the remainder with the same meaning. Presburger divisibility on the domain; alignment from the allocator's facts | Not run | 9 | Every matrix instruction has a fixed shape; Vx proves the same for its `lanes::` routines (`across.rs:929-975`) |
| P3 | **Layouts and swizzles as bijections**: the XOR swizzles (ldmatrix bank spreading `swizzleLdmatrixTiles`, `VxLowering.cpp:5718-5776`; the TMA 128-byte swizzle) are linear maps over GF(2) on the address bits, bijective exactly when their bit matrix has full rank, checked by Gaussian elimination in O(b³) for b ≤ 64 address bits; mixed-radix layouts (cuBLAS's 128×4 scale tile, offset = (outer mod 32)·16 + ⌊outer/32⌋·4 + inner, cuBLAS 9360-9375 [C]) are affine packings already in the catalog | Not run | 9 | A swizzle is a repack, so DESIGN's layout facet covers it with no change of meaning; the GF(2) witness is one new catalog entry with a short proof (an invertible bit matrix is a bijection on the bit vectors) |
| P4 | **Independence of writes, affine**: the writes of parallel instances to the output are pairwise disjoint, by Presburger arithmetic on the index forms, as Vx's `across_proof.rs` does without SMT | Vx shows the method works on its stdlib and ports [C] | 9 | Zed already has Presburger; MAP-compute-levels uses it for legality |
| P5 | **Independence of writes through index tensors** (Vx's `Distinct` and `DisjointRanges`): prove injectivity from the code that built the index tensor. The common forms: (a) position = exclusive prefix sum of group sizes at the group + rank within the group, with rank < size, which gives disjoint ranges, since start[g+1] = start[g] + size[g]; (b) the output of a sort with duplicates removed; (c) `argsort`, a permutation. Each becomes a witness of the catalog (DESIGN sec:remap_law, `@injective` at L16.2) | Not run; Vx checks at run time in O(n log n) or trusts with `unsafe` [C] | 8 | It removes the run-time check and the `unsafe` of Vx W6, which the MoE grouping in both glm-vx and `std::nn` needs; DESIGN's rule (checker never runs user code) rules out Vx's run-time check as the proof |
| P6 | **Epilogue fusion**: bias, activation, scale, residual add and the narrowing cast applied to each output element before the store, in the same order as the unfused program, so no value changes; the proof is that each epilogue operation reads only its own output element and values already final | Not run | 9 | Saves a full read and write of the output; the order condition makes it exact |
| P7 | **Reduction order under split-K**: splitting K across blocks or SMs into power-of-two aligned parts, merged in tree order, gives the canonical tree's bits; a split into unequal or unaligned parts does not. So the solver offers only aligned power-of-two splits for `tree` and any split for `unordered` | Derivation | 9 | Keeps split-K and stream-K parallelism without `unordered` |
| P8 | **Memory hierarchy**: each tile's footprint at each level (registers, shared memory or L1, L2, device memory) within capacity, from symbolic sizes; the transfer cost along the containment path (section 3) | Vx's capacity rule and measured costs [C] | 9 | Without it the solver cannot reject a tile that spills or choose between tiles |
| P9 | **Asynchronous copies and pipelines**: the copy of tile i+d does not alias the compute on tile i; the buffer depth d and the barrier placement (mbarrier, `cp.async.wait_group`, `wgmma.wait_group`) follow from the dependency DAG, the depth chosen by the solver within shared-memory capacity | glm-vx sets up mbarrier by hand [C] | 8 | Overlaps copy with compute; the compiler, not the user, places barriers |
| P10 | **Scale range**: a dequantized value stays finite and normal in f32 (448·2^s ≤ f32 max needs s ≤ 119); quantize from f32 data gives this by the MX rule; a loaded scale needs a domain fact or a checked load | Derivation | 8 | Without it P1 fails at the edges |
| P11 | **Configuration state**: AMX's tile configuration, Arm's FPMR mode word, AMD's FP16_OVFL and SH_MEM_CONFIG bit 8 ("must be 1 for correct FP8/BF8 results", CDNA3 p.51 [C]) are set as the lowered code needs and restored at boundaries | Not run | 7 | A wrong mode gives wrong values silently; a lowering obligation more than a proof |
| P12 | **Per-identity hardware facts**: the instruction exists on this identity, its operand types are supported, and (for P1) the identity's MMA-accumulator test passed | — | 8 | Vx's `dtypes:` check (E6026) is the model; the identity cache holds the test result |
| P13 | Use SMT (Z3) for these proofs, as Vx's other checks do | — | 3 | Presburger and the catalog already cover the forms above; Vx itself proves `across` without SMT |
| P14 | Check `Distinct` at run time, as Vx does | Vx: O(n log n) on the host [C] | 2 | A run-time check is not a proof, and a failed check needs a failure value in the type; kept only as the `#collision` path L16.2 already defines |

---

## 7. Deliverable B: the intrinsics by kind, and the kinds of lowering logic

The user never writes an intrinsic. The lowering selects them from the plan.

### 7.1 Intrinsics by kind

Sources are [C] unless marked; details are in the formats report under `study1-scratch/formats/`.

**Matrix multiply-accumulate, synchronous** (one warp, wave or core issues it):

| Target | Instruction | Shapes and types |
| --- | --- | --- |
| NVIDIA | `mma.sync` (PTX §9.7.16.1) | f16/bf16 m16n8k8, m16n8k16; tf32 m16n8k4, m16n8k8; s8 m8n8k16; s4 m8n8k32; f64 m8n8k4; e4m3/e5m2 m16n8k32 (PTX 8.4); e3m2/e2m3/e2m1 m16n8k32 (PTX 8.7) |
| AMD CDNA3 | `V_MFMA_F32_16X16X32_{FP8,BF8}_*` | Also the 32X32X16, I8 and XF32 forms |
| AMD CDNA4 | `V_MFMA_F32_{16X16X128,32X32X64}_F8F6F4` | CBSZ/BLGP pick each operand's format (0 E4M3, 1 E5M2, 2 E2M3, 3 E3M2, 4 E2M1) |
| AMD RDNA | gfx11 WMMA 16x16x16 f16/bf16/iu8/iu4; gfx12 FP8/BF8 and SWMMAC | From LLVM; the gfx-to-RDNA mapping is [I] |
| x86 AMX | `TDPBSSD`/`SUD`/`USD`/`UUD`, `TDPBF16PS`, `TDPFP16PS`, AMX-FP8 `TDPBF8PS`/`TDPBHF8PS`/`TDPHBF8PS`/`TDPHF8PS` | Tiles up to 16 rows × 64 bytes |
| Intel XMX (SYCL joint_matrix) | int8 M≤8, N=16, K=32; fp16/bf16 K=16 | No FP8 listed |
| Arm | `BFMMLA`, `SMMLA`, `UMMLA` | Shapes from the Arm ARM, not read [I] |
| Arm SME | `svmopa_za32[_bf16/_f16/_s8/_f32]_m`, `svmopa_za64[_s16]_m` | ZA is SVL.B × SVL.B bytes |
| Arm SME2 FP8 | `svmopa_za16/za32[_mf8]_m_fpm` | "Beta" in ACLE |
| RISC-V IME (draft) | `vfmmacc`, `vfwmmacc`, `vfqmmacc`, `vf8wmmacc` | Not ratified [I] |
| Apple | `simdgroup_multiply_accumulate` on 8×8 half/bfloat/float | Metal 4 `matmul2d` adds char, int4b, fp4_e2m1 and fp8 (4.1) |
| SPIR-V | `OpCooperativeMatrixMulAddKHR` | Sizes queried at run time; an optional saturating accumulation |

**Matrix multiply-accumulate, asynchronous or group-wide:**

| Target | Instruction | Details |
| --- | --- | --- |
| NVIDIA sm_90a | `wgmma.mma_async` | m64nNk16 f16/bf16, k8 tf32, k32 e4m3/e5m2/s8; N 8-256 |
| NVIDIA sm_100a | `tcgen05.mma` | K 16/8/32/64 by kind; M 64-256 with `cta_group`; the accumulator lives in tensor memory (512 columns × 128 lanes × 32 bits per CTA) |
| SPIR-V | `SPV_NV_cooperative_matrix2` | Workgroup scope |

**Block-scaled multiply-accumulate:**

| Target | Instruction | Details |
| --- | --- | --- |
| NVIDIA sm_120a | `mma.sync` kinds `mxf8f6f4`, `mxf4`, `mxf4nvf4` | Scale vectors 1X, 2X or 4X |
| NVIDIA sm_100a | `tcgen05.mma` with scales in tensor memory | UE8M0, UE4M3 or UE5M3 scales; `.block16`/`.block32` |
| AMD CDNA4 | `V_MFMA_SCALE_*` | One E8M0 per 32 K values |
| AMD gfx1250 | `wmma_scale`, `wmma_scale16` | — |
| RISC-V IME (draft) | `v0.scale` | `vtype.bs` selects 32 or 16 |
| Metal | `tensor_blockwise<…, metal_fp8_ue8m0_format, 32, 1>` | — |

**Vector dot products:**

| Target | Instructions |
| --- | --- |
| x86 | AVX-512 VNNI `VPDPBUSD(S)`, `VPDPWSSD(S)`; `VDPBF16PS`; AVX512-FP16 `VFMADD*PH` |
| Arm | FEAT_FP8DOT2/DOT4/FP8FMA |
| RISC-V | `vfwmaccbf16` |
| NVIDIA | `dp4a` (already in L27.1b) |

**Conversion:**

| Target | Instructions |
| --- | --- |
| NVIDIA | `cvt.{rn,rz}.satfinite{.relu}` to e4m3x2, e5m2x2, e2m1x2, e2m3x2, e3m2x2 (satfinite mandatory); `.scaled::n1::ue8m0`; `cvt.rs` stochastic forms on sm_100a+ |
| AMD | `CVT_PK_FP8_F32`, `CVT_SR_FP8_F32` (CDNA3); `V_CVT_SCALEF32_*` (CDNA4) |
| x86 | AVX10.2 `VCVTPH2BF8/HF8(S)`, `VCVTBIASPH2*` (the bias forms as the stochastic mechanism is [I]), `VCVTHF82PH` |
| Arm | FPMR-controlled conversions (bits 0-8 formats; bit 15 overflow mode) |
| RISC-V | `vfncvtbf16`, `vfwcvtbf16` |
| Metal | fp4 and e4m3 convert with saturation by default, e5m2 without |

**Data movement into matrix operands:**

| Target | Instructions |
| --- | --- |
| NVIDIA | `ldmatrix`, `stmatrix`, `cp.async` (sm_80), `cp.async.bulk.tensor` (TMA, sm_90) |
| AMD | `V_PERMLANE16/32_SWAP_B32` |
| x86 | `LDTILECFG`, `TILELOADD(T1)`, `TILESTORED`, `TILEZERO`, `TILERELEASE` |
| Arm | ZA loads and stores, `svluti2/4_lane` table lookups |
| SPIR-V | `Load/StoreKHR`, NV `LoadTensorNV` with a decode callback |
| Metal | `simdgroup_load/store` |

**Synchronization:**

| Target | Instructions |
| --- | --- |
| NVIDIA | `wgmma.fence`, `commit_group`, `wait_group`; `mbarrier` (sm_80); `fence.proxy.async`; the tcgen05 commit and fence details [I] |
| SPIR-V | The matrix type's Scope operand |
| AMD and Metal | Barrier details not checked |

### 7.2 The kinds of lowering logic

| # | Kind | What it decides | From |
| --- | --- | --- | --- |
| K1 | Instruction shape selection | Which (m, n, k) and which instruction family (sync, async, block-scaled) per tile; padding or peeling of remainders | The target description's matrix-unit table and the cost model; P2 |
| K2 | Operand fragment mapping | Which lane holds which element of each operand and accumulator | A fixed table per instruction (PTX fragment layouts, MFMA layouts, Metal's unspecified mapping handled through `simdgroup_load`) |
| K3 | Type legalization | Decode narrow formats where the unit lacks them (table lookup or bit operations, chosen by cost), pack and unpack nibbles and 6-bit groups | A1, A3 |
| K4 | Scale placement | In the instruction (block-scaled MMA), in the epilogue (per-tensor scale), or dequantize before | A6; P1 for exactness |
| K5 | Accumulation strategy | Per-block MMA with C = 0 and the binary-counter merge (exact, 4.2), or one long accumulation (`unordered`), or int32 under the K bound | P1, P7 |
| K6 | Data staging | Device memory → shared memory or L1 → registers or tensor memory: async copies, swizzles, buffer depth, barriers | P3, P8, P9 |
| K7 | Mode state | AMX tile configuration, FPMR, FP16_OVFL, SME streaming mode and ZA enable, set and restored around kernels | P11 |
| K8 | Capability dispatch | One branch per hardware identity, each a static plan; fallbacks give the same bits | DESIGN's residual dispatch on hardware identity; P12 |
| K9 | Run-time-queried shapes | Vulkan cooperative-matrix sizes known only at run time: the residual cost model picks among compiled variants | DESIGN "Cost model, two tiers" (residual plan) |

---

## 8. Plan rows filed

Each row has a direct consumer. The rows were checked for transitive reduction against the existing needs.

| Row | Slot | Needs | Consumed by |
| --- | --- | --- | --- |
| DECIDE-narrow-formats | decision rows (priority 2) | QUESTIONS-answered | NARROW-storage-types |
| NARROW-storage-types | beside L1.18a (the float formats) | L1.18a, DECIDE-narrow-formats | BLOCK-scaled-tensors, SR-stochastic-rounding |
| SR-stochastic-rounding | beside NARROW-storage-types | NARROW-storage-types | L27.1b |
| BLOCK-scaled-tensors | beside REPACK-tile | NARROW-storage-types, L14.1 | MMA-lowering, MMA-cpu-units |
| SWIZZLE-layouts | beside REPACK-tile | REPACK-tile | MMA-lowering |
| INJECTIVE-index-tensors | beside L16.2 | L16.2 | L24.2 |
| TARGET-desc | L24.x, beside L24.5 | none | MAP-compute-levels, TARGET-calibrate, MMA-cpu-units |
| MAP-compute-levels | L24.x, beside L24.5 | TARGET-desc, REPACK-tile | L24.5 |
| TARGET-calibrate | L24.x, beside L24.6 | TARGET-desc | L24.6 |
| MMA-cpu-units | beside L29.1 | BLOCK-scaled-tensors, TARGET-desc, L24.2a | L29.1 |
| ASYNC-copy-pipeline | beside L27.1 | L27.1 | MMA-lowering |
| MMA-accumulator-tests | beside L27.1 | L27.1 | MMA-lowering |
| MMA-lowering | beside L27.1 | BLOCK-scaled-tensors, SWIZZLE-layouts, ASYNC-copy-pipeline, MMA-accumulator-tests | L27.1b |

**Existing rows edited:**
- L24.2 needs INJECTIVE-index-tensors.
- L24.5 needs MAP-compute-levels.
- L24.6 needs TARGET-calibrate.
- L27.1b needs MMA-lowering and SR-stochastic-rounding in place of L27.1, which it reaches through MMA-lowering.
- L29.1 needs MMA-cpu-units.

**Slots.** The system-model rows sit in the L24.x slot, as the author asked. The GPU matrix rows sit beside L27.1, because they need its GPU crate. MMA-cpu-units sits beside L29.1.

---

## 9. Open claims, and the claim most likely wrong

**Open claims:**
1. That each matrix unit sums an FP4, FP6, MXINT8 or NVFP4 block exactly [I]. No vendor document states an accumulator width. Row MMA-accumulator-tests settles it per hardware identity. The local GPU cannot test the narrow formats.
2. That a 64-element block-scaled instruction (two scale blocks) rounds once after an exact sum [I]. Same test.
3. That AVX10.2's bias conversions are its stochastic rounding [I]. The headers call them biases.
4. AMX palette 1 having 8 tiles; the Arm NEON matrix shapes; RDNA from AMD's own documents; Graphcore's stochastic rounding; whether CDNA3 BF8 has an infinity. All are unread or ambiguous (formats report Part 3).
5. That the glm-vx Python boundary does not re-check `DisjointRanges` [I]. Reading the wrapper `build.py` generates would settle it.
6. The bf16 limits and the int4 ranges, derived from the layouts and not quoted [I].

**The claim most likely wrong** is open claim 1: that block-scaled FP4 MMA hardware sums each block exactly. The proof in 4.2 shows an exact sum fits in f32, not that the hardware keeps it. DeepSeek's 14-bit figure for FP8 on H800 shows that NVIDIA's units can keep fewer bits than f32. If a unit truncates, the exact-block lowering is wrong on that unit. The test row exists so the plan never relies on the claim untested. Under the rule "commit, then prove", the lowering is licensed per identity only after the test passes.
