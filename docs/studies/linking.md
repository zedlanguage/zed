# Linking Zed programs, libraries and isolated libraries (STUDY-linking)

Plan row STUDY-linking, 2026-11-22, by b22-research3-h5 (author P296, P298). The design this
study chose is written in DESIGN sec:linking (zed branch wt/b22-research3-h5-spec, commit
1c7a537). This file holds what DESIGN leaves out: the survey, the measurements, the
candidates and their scores, the author questions, and the plan rows. Literature entries are in
zed `verification/bib.md` (entries Ueyama_2027, Johnson_2017, TGlek2010optimizing,
FaridZakaria2025symbol, ShravanNarayan2020retrofitting, and the rejected ChrisFallin2024partial).
Code facts are read at zed-impl b7b205533 with `git grep`. Every claim is marked confirmed, with
its evidence, or inferred.

Machine for every measurement: Fedora 44, Linux 7.3.3, 32 cores, `kernel.yama.ptrace_scope` 0,
Landlock in the LSM list, shared with other agents (load average 40 to 70 during the runs, so wall
times are noisy and instruction counts are the steadier figure). Scripts and raw output are in the
scratchpad of this run (`exp/link.sh`, `exp/mold.sh`, `exp/spawn.c`, `exp/launcher.c`,
`exp/links.txt`, `exp/mold.txt`, `exp/bench1.txt`, `exp/bench2.txt`, `exp/checks2.txt`,
`exp/checks3.txt`); they were not committed, since they are measurement aids.

## 1. What a linker does, and what each one offers

A native linker resolves each undefined symbol to one definition, lays out the sections it keeps,
applies relocations, drops sections no root reaches (`--gc-sections`), and may fold identical
sections (`--icf`).

| Linker or scheme | What matters for Zed | Source (confirmed unless marked) |
|---|---|---|
| GNU ld (bfd) | One thread (measured: task clock 1.79 s against 1.95 s wall). `--gc-sections` keeps the entry's section, the sections of `-u` symbols, the sections dynamic objects refer to, and in a shared library every visible symbol, then marks through relocations. Supports `-r --gc-sections`. | ld(1), `--gc-sections`; `exp/links.txt` |
| gold | Deprecated: binutils 2.44 ships without it, "the gold linker is now deprecated and will eventually be removed". Its incremental linking "falls back to a full link when a function definition is removed or preallocated patch space runs out". | binutils 2.44 announcement; Ueyama 2027 (mold paper), section on incremental linking |
| LLD | Multithreaded; ICF safe and all (lld `ICF.cpp`); supports `-r --gc-sections`. Already Zed's preferred linker: `link::Ld::Lld` when `ld.lld` is on PATH (crates/zed-native/src/link.rs:104-155, row LINK-lld-when-present, Done). | LLD docs index; lld source `ICF.cpp`; link.rs |
| mold 3.0.0 | Every pass data-parallel; symbol resolution by compare-and-swap on each symbol's owner; ICF as a fixed point of iterated section hashing. `--icf=safe` needs `.llvm_addrsig`, which Clang writes and GCC does not, so on GCC objects it folds nothing. Under `-r` it keeps every section whatever `--gc-sections` says (measured: 202 MB output against 37 MB for LLD). | Ueyama 2027; mold(1), `--icf`; `exp/links.txt` |
| wild 0.11.0 | Fast full link (measured 496 ms); "The plan is to eventually make it incremental, however that isn't yet implemented". Its `-r` output of the runtime is 40 KB and the program linked from it is 39 KB and crashes (measured). | wild README; `exp/links.txt` |
| ThinLTO | Per-module summaries; "fast purely summary-based Whole-Program Analysis (WPA), the only serial step"; importing and optimization in parallel back ends; a cache keyed per module. | Johnson, Amini and Li 2017 (abstract only, no free full text found); Clang ThinLTO docs |
| GCC WHOPR | Summaries in parallel, whole-program analysis serially on the call graph, partitions optimized in parallel. | Glek and Hubicka 2010 |
| Stable linking | Resolving dynamic symbols once at install: "a factor between 1.13 and 7.03, with a geometric mean of 2.19" faster startup than dynamic linking. Supports keeping Zed binaries free of Zed dynamic libraries (step L37.1). | Zakaria, Quinn and Scogland 2025 |
| RLBox (Firefox) | Process sandbox: "≈2ms" to create, "0.47μs" a call with spin locks and "7.4μs" with condition variables. The cost model for an isolated library. | Narayan et al. 2020 |

Rejected: Fallin and Bernstein 2024, "Partial Evaluation, Whole-Program Compilation" (weval). It
specializes an interpreter on its bytecode inside one Wasm module, and says nothing about linking
across modules, so it supports no claim here (entry kept in bib.md with the reason).

What follows for Zed (inferred from the table and DESIGN sec:ir): the work the native linkers spend
most effort on, resolving symbols in parallel and folding identical code, is work Zed does on ZIR
before code generation. Names are resolved at check time through interfaces and pinned by content
address, and identical definitions share one address. The native linker is left with joining a few
objects, so its speed matters less than the cache that avoids compiling units again.

## 2. Measurements

### 2.1 Link times

A stand-in program object (`exp/stub.c`: `main`, a call of `zed_main`, every runtime hook named)
linked with the real runtime archive `libzed_native.a` (206 MB) and `--gc-sections`, five runs
each, median. "Prelink" is the runtime's relocatable link with the hooks as roots
(`PRELINK_FLAGS`, link.rs:48); "after prelink" is the program's link against that one object.

| Linker | Full link | Prelink of the runtime | Program link after prelink | Instructions, full / after prelink |
|---|---|---|---|---|
| GNU ld | 1954 ms | 1518 ms | 753 ms | 3.34 G / 0.985 G (3.4 times fewer) |
| LLD | 408 ms | 692 ms | 336 ms | 0.761 G / 0.271 G (2.8 times fewer) |
| mold | 3153 ms at load about 60; see 2.2 | 10245 ms, keeps all 202 MB | 1952 ms | 0.87 G / 0.79 G |
| wild 0.11 | 496 ms | 540 ms, output broken | not usable | 0.672 G / — |

Confirmed (`exp/links.txt`). The program-link instruction count with LLD after prelink, 0.27 G,
agrees with row LINK-lld-when-present's 0.33 G on fahrenheit.zed.

### 2.2 mold on a loaded machine

mold's first full-link times (1.7 to 7.7 s) came from the load, not from mold: at load 42 its full
link took a median of 485 ms with one thread (0.80 G instructions), 249 ms with 4, 144 ms with 8,
and 286 ms with its default thread count, whose task clock was 1.8 to 4.5 s (confirmed,
`exp/mold.txt`). One thread of mold is near one link of LLD (408 ms). mold's default of one worker
per core makes it the worst choice on a machine shared by many builds, which is how Zed's build
machine runs.

### 2.3 Starting an isolated library's process

`exp/spawn.c`, 500 starts of a launcher that exits at once, median, p10 and p90 in µs (confirmed,
`exp/bench1.txt`, `exp/bench2.txt`). Starts used `vfork`; `osSpawn` uses `clone3`, whose cost is
inferred to be the same within noise, since both share the address space until `exec` (not
measured).

| Method | Parent heap 0 | Parent heap 1 GB (N=100) |
|---|---|---|
| memory file made once, `execveat` | 535 (460, 707) | 3372 (584, 6709) |
| memory file made at each start | 708 (556, 1102) | 2599 |
| `posix_spawn` of a file on disk | 560 (469, 727) | 2873 |
| re-exec `/proc/self/exe` | 514 (460, 600) | 2420 |
| fork without exec | 230 (193, 471) | 251769 (156157, 383558) |

The exec methods do not differ beyond noise; fork without exec is 2.3 times faster on a small
heap and 75 to 100 times slower on a 1 GB heap, and holds the heap (row 4 of section 3.1).

### 2.4 What the child can reach of the parent (P298)

Confirmed (`exp/checks2.txt`, rerun with the fixes below in `exp/checks3.txt`):

- After the memory-file exec, with the channel moved to descriptor 3 and
  `close_range(4, ~0U, CLOSE_RANGE_CLOEXEC)`, the child holds descriptors 0 to 3 only, no mapping
  of the parent's heap, and its `/proc/self/exe` is `/memfd:zed-launcher (deleted)`. Without
  `close_range` it inherited the parent's leaked descriptor 3.
- The seals refuse a write, `ftruncate` and `fchmod` (seals read back 0x3f).
- A library loaded with `dlopen` in the launcher runs (`zlibVersion()` returned 1.3.1.zlib-ng).
- A fork without exec reads the parent's heap byte directly.
- **With Yama at 0, an exec'd child of the same user reads the parent's heap**, through
  `/proc/PPID/mem` and through `process_vm_readv`. An address space of its own does not meet P298.
- In a Landlock domain with only `LANDLOCK_SCOPE_SIGNAL` (no file or network right handled), both
  reads are refused (EACCES, EPERM), `kill(parent, 0)` is refused, and opening a file still works.
- In a domain that handles one file right (`MAKE_SOCK`, ABI 1), both reads are refused and the
  signal is allowed.
- With the parent made non-dumpable and no Landlock, both reads are refused.

A fault in the first run, fixed: `exp/checks2.txt` ran the signal-scope case after the parent had
already made itself non-dumpable, which refuses the reads by itself. `exp/checks3.txt` runs it with
the parent dumpable (printed as 1) and adds the file tests, in a fresh directory per case
(confirmed, rc 0):

| Child's domain | `/proc/PPID/mem` | `process_vm_readv` | `kill(parent, 0)` | open a file | bind a Unix socket | rename between directories |
|---|---|---|---|---|---|---|
| none | read | read | allowed | allowed | — | — |
| signal scope only (ABI 6) | EACCES | EPERM | EPERM | allowed | allowed | allowed |
| `MAKE_SOCK` handled, not granted | EACCES | EPERM | allowed | allowed | EACCES | EXDEV |
| `MAKE_SOCK` and `REFER` handled, both granted beneath `/` | EACCES | EPERM | allowed | allowed | allowed | allowed |
| none, parent non-dumpable | EACCES | EPERM | allowed | allowed | — | — |

So the ABI 2 to 5 fallback denies nothing measured and still refuses both reads; the signal must
then be refused by a seccomp filter. Limits of this check: it ran on Linux 7.3, where every ABI is
present; that the same ruleset behaves the same on a 5.19 to 6.11 kernel is inferred from
landlock(7), not tested. The seccomp signal filter of DESIGN (`kill` and `tgkill` allowed only
with the wrapper's own pid, `EPERM` for `tkill`, `pidfd_send_signal` and the `rt_*sigqueueinfo`
calls aimed elsewhere) was not built or measured here; row FFI-isolate-domain tests it.

Primary sources (confirmed, man pages copied in the scratchpad `docs/`): landlock(7), "Ptrace
restrictions": the tracee must be in a sub-domain of the tracer; the signal scope is ABI 6
(Linux 6.12), ABI 1 is Linux 5.13, and "when using the first Landlock ABI version, Landlock will
always deny attempts to reparent files between different directories"; ptrace(2), Yama: at scope
1, the kernel default, a process may attach only to its descendants; proc_pid_mem(5): access needs
a `PTRACE_MODE_ATTACH_FSCREDS` check; process_vm_readv(2): `PTRACE_MODE_ATTACH_REALCREDS`; prctl(2),
`PR_SET_PDEATHSIG`: the signal follows "the thread that created this process".

## 3. Candidates

### 3.1 How the launcher starts

| Solution | Empirical result | Score | Reasoning |
|---|---|---|---|
| Wrapper bytes embedded; one sealed memory file per library per run; `execveat(AT_EMPTY_PATH)` through `osSpawn`; Landlock domain before `dlopen` | 535 µs; child sees fds 0-3, no heap mapping; reads refused in the domain | 9 | No file to install or lose; the bytes run are the bytes zedc wrote; cost equal to `posix_spawn`. Chosen. |
| Re-exec `/proc/self/exe` into the wrapper's code linked into the program | 514 µs; works after the program file is deleted | 7 | Works where a memory file cannot run (`vm.memfd_noexec = 2`, a policy), but the child also maps the program's code and the libraries it links. Chosen as the fallback. |
| Memory file made at each start | 708 µs | 6 | A copy of the bytes per start for nothing. |
| Write the wrapper to a cache directory and `posix_spawn` it | 560 µs | 5 | Needs a writable directory that allows exec, leaves files, and the file can be replaced between write and exec. |
| Resident zygote forked early | not measured | 3 | A process for the whole run to save one start per library; it holds whatever the runtime set up before it forked. |
| Exec a byte range of the program file | not possible | 2 | Linux has no exec at an offset; a user-space ELF loader would be needed. |
| Fork without exec | 230 µs small heap, 252 ms at 1 GB; child reads the heap | 0 | Breaks P298 outright, and slow on a large heap (decisions row "Foreign isolation"). |

### 3.2 Keeping the library out of the program's memory

| Solution | Empirical result | Score | Reasoning |
|---|---|---|---|
| Landlock domain, no file or network right handled, signal scope (ABI 6) | reads and signals refused; files work | 9 | Denies the library nothing else; joins the ruleset of `restrict` (step L7.4e). Chosen. |
| ABI 2 to 5: `MAKE_SOCK` and `REFER` handled and granted beneath `/`, plus a seccomp filter on signals; ABI 1: `MAKE_SOCK` alone | reads refused, bind and rename allowed (on 7.3); filter not measured | 7 | Covers Linux 5.13 to 6.11. On ABI 1 the library cannot move files between directories, a limit of ABI 1 itself. |
| Make the program non-dumpable (`PR_SET_DUMPABLE 0`) | reads refused | 4 | Changes the program, not the library: no core dumps, `/proc/PID` files owned by root, debuggers cannot attach. Only as an author choice (L-Q4). |
| Rely on Yama 1 | not Zed's setting | 1 | A system setting Zed cannot assume; this machine has 0. |
| seccomp alone (deny `ptrace`, `process_vm_readv`) | not measured | 3 | seccomp cannot see the path of an `open`, so `/proc/PPID/mem` stays open. |
| A user namespace for the child | not measured | 3 | Unprivileged user namespaces are disabled on some distributions; inferred, not tested. |

### 3.3 Which native linker

| Solution | Empirical result | Score | Reasoning |
|---|---|---|---|
| LLD for prelink and program link (built) | 336 ms, 0.27 G | 9 | Fastest working pair; already the code (link.rs:104-155). |
| GNU ld for both, where LLD is absent (built) | 753 ms, 0.985 G | 6 | Always present; 2.2 times slower. Kept as the fallback. |
| mold for the program link only | 485 ms one thread; 144 ms with 8 threads at load 42 | 6 | Fine for the final link; unusable for the prelink, since `-r` ignores `--gc-sections`. |
| A linker of Zed's own | none | 3 | Months of work to save part of 0.3 s a link, which the unit cache mostly removes from rebuilds. |
| wild 0.11 | 496 ms full; `-r` output broken | 2 | Revisit when its relocatable output loads. |
| gold | not measured | 1 | Deprecated upstream. |

### 3.4 Not filed

- Linker choice: already built (row LINK-lld-when-present, Done).
- Identical code folding: content addresses already merge identical Zed definitions; on C code
  only `--icf=safe` would be allowed, and it folds nothing in GCC objects. No program has been
  measured to need it, so no row; DESIGN sec:linking records the rule.
- Incremental native linking: gold's falls back to a full link in common cases, wild has none,
  and the program link after prelink is 0.27 G instructions; the unit cache (row LINK-unit-cache)
  removes the rebuild work that costs more.

## 4. Author questions

Each is a real choice of behavior; DESIGN names the question and does not decide it.
L-Q1 is settled as DESIGN is written (a), and L-Q5 waits for step S.12a under the rule that
portability comes last (b22-research3, 2026-11-22). L-Q2, L-Q3 and L-Q4 are the spec repository's
QUESTIONS A212, A213 and A214.

**L-Q1. One wrapper per library, or one generic launcher?** (a) zedc builds one wrapper per
isolated library with the library's call table compiled in (DESIGN as written); (b) one generic
launcher reads the call table from the channel. Recommendation: (a). Each wrapper checks messages
against its own format at compile time, and the size cost is one small binary per library; (b)
moves format checks to run time in the one process P298 does not trust.

**L-Q2. What stays dynamic in a standalone binary?** (a) glibc stays dynamic and everything else is
static; (b) fully static on every libc; (c) fully static on musl only, glibc dynamic.
Recommendation: (c). A static glibc breaks name lookup through NSS and `dlopen`, which every
wrapper needs; musl has neither problem. Under (c) a release built for musl targets is one file.

**L-Q3. The wrapper's environment and standard streams.** (a) the program's environment, stdin
from `/dev/null`, stdout and stderr shared with the program; (b) an empty environment; (c) the
environment written on the token's result type. Recommendation: (a), since a C library reads
`LANG`, `TZ` and similar variables, and its messages belong in the program's stderr; (c) can come
later with `restrict`.

**L-Q4. A host with no Landlock.** If Yama is 1 or more, the wrapper cannot read its parent and
needs only the seccomp signal filter, so it starts. If Yama is 0: (a) the token-giving call gives
`#ioError(op: "isolate", path: <library>, why: "Landlock unavailable")`; (b) the program makes
itself non-dumpable before the first wrapper starts; (c) start with a warning on stderr.
Recommendation: (a), since it never gives less separation than the program was built to expect
and says so; (b) changes the whole program's behavior (core dumps, debuggers) as a side effect;
(c) is a silent weakening in any program whose stderr no one reads.

**L-Q5. macOS and Windows.** Neither has a memory file that can be run. Options: (a) write the
wrapper once to a per-user cache directory, named by its content address, checked by hash before
each start; (b) re-exec the program's own file into the wrapper's code (the Linux fallback);
(c) defer both until step S.12a. Recommendation: (c), and (b) when S.12a starts, since (b) needs
no writable directory; what keeps the library out of the program's memory on each OS (task ports
on macOS, process access rights on Windows) is part of S.12a's own study.

## 5. Rows this study adds

New rows, each listed in its consumer's Needs, with a note under "Why each item waits":

| Level | Id | Title | Size | Hard | Needs | Paths |
|---|---|---|---|---|---|---|
| 63 | FFI-launcher-memfd | From STUDY-linking (DESIGN sec:linking, "The launcher of an isolated library"; study docs/studies/linking.md sections 2.3, 2.4, 3.1): zedc embeds each isolated library's wrapper bytes in the program's read-only data, and the OS layer starts a wrapper from those bytes: on the first start of a library's process `memfd_create` with `MFD_CLOEXEC \| MFD_ALLOW_SEALING \| MFD_EXEC` (again without `MFD_EXEC` on `EINVAL`), the descriptor moved to 100 or above with `F_DUPFD_CLOEXEC`, the bytes written once and sealed (`F_SEAL_SEAL \| F_SEAL_SHRINK \| F_SEAL_GROW \| F_SEAL_WRITE \| F_SEAL_EXEC`), the descriptor kept for the run and reused by each later start; the child made as `osSpawn` makes children (own process group and cgroup, parent-death signal from the long-lived runtime thread), with the channel on descriptor 3, `close_range(4, ~0U, CLOSE_RANGE_CLOEXEC)` and `execveat(fd, "", argv, envp, AT_EMPTY_PATH)`; where the memory file cannot be made or run, the re-exec of `/proc/self/exe` into the wrapper's code, which zedc also links into the program, entered before the runtime starts; where neither works, `#ioError(op: "spawn", …)`; the wrapper exits on end of file on the channel. Tests: the child's descriptors are exactly 0 to 3 (read from `/proc/self/fd` in a test wrapper) and its `/proc/self/maps` names no mapping of the parent's heap; after sealing, a write, `ftruncate` and `fchmod` are refused; two starts of one library use one memory file (one `memfd:` entry in the parent's `/proc/self/fd`); with `memfd_create` failed by a test hook the `/proc/self/exe` path starts the wrapper, also after the program's file is deleted; with both failed the token-giving call gives `#ioError(op: "spawn", …)`; the program killed with SIGKILL leaves no wrapper (parent-death signal), and with that signal cleared by a test hook the wrapper still exits when the channel closes. Negative controls, run once and not committed: `close_range` without `CLOSE_RANGE_CLOEXEC` (the exec fails, as the study saw); the seals left out (the write test fails); `close_range` left out (the descriptor test sees an extra descriptor). Benchmarks in `bench`: n and 8n starts, and wrappers of n and 8n bytes, ratio under 9 the goal, 10.5 the limit, judged by instructions | M | no | STUDY-linking, OS-intrinsics | `crates/zed-rt/src/`, `crates/zedc/src/`, `../libzed/`, `tests/steps/link_launcher/ (new)` |
| 2 | FFI-isolate-domain | From STUDY-linking (DESIGN sec:linking, the paragraph on what the child holds; author P298; study docs/studies/linking.md section 2.4): every wrapper, restricted or not, sets `no_new_privs` and enters a Landlock domain before it `dlopen`s its library: on ABI 6 or later a ruleset that handles no file or network access, with the scope `LANDLOCK_SCOPE_SIGNAL`; on ABI 2 to 5 `LANDLOCK_ACCESS_FS_MAKE_SOCK \| LANDLOCK_ACCESS_FS_REFER` handled with one rule granting both beneath `/`; on ABI 1 `MAKE_SOCK` alone; on ABI 1 to 5 also a seccomp filter that allows `kill` and `tgkill` only with the wrapper's own pid and returns `EPERM` for `tkill`, `pidfd_send_signal` and `rt_sigqueueinfo`/`rt_tgsigqueueinfo` aimed elsewhere. FFI-sandbox-linux later folds the scope into the one ruleset of `restrict`. A host with no Landlock follows the author's answer to the study's question L-Q4; until then the token-giving call gives `#ioError(op: "isolate", path: <library>, why: "Landlock unavailable")` when `kernel.yama.ptrace_scope` is 0, and starts the wrapper with the seccomp filter when it is 1 or more. Tests, each first checking that without the domain the wrapper reads its parent's heap (skipped with a printed reason when Yama is not 0): in the domain, `/proc/PPID/mem` gives EACCES and `process_vm_readv` EPERM; `kill(parent, 0)` gives EPERM; the program still stops the wrapper; the library opens a file, binds a Unix socket and renames a file between directories; the same on the ABI 2 to 5 and ABI 1 paths, chosen by a test hook that reports a lower ABI (on ABI 1 the rename gives EXDEV, as landlock(7) says); a library initializer that reads the parent's heap fails, since `dlopen` comes after the domain. Negative control, run once and not committed: the domain skipped (the read test fails); the seccomp filter left out on the ABI 2 to 5 path (the kill test fails). Benchmarks in `bench`: domain setup for n and 8n wrapper starts, ratio under 9 the goal, 10.5 the limit | M | yes | STUDY-linking | `crates/zed-rt/src/`, `../libzed/`, `tests/steps/link_isolate_domain/ (new)` |
| 67 | LINK-unit-cache | From STUDY-linking (DESIGN sec:linking, "Linking at the ZIR level"): each unit's specialized ZIR is cached under a key made of the address of the unit's text, the addresses of the interfaces it imports (ZIR-iface-key), the address of every body its `mix` unfolded (ZIR-iface-bodies), the build, and the compiler and spec versions; an instance of a generic function under the address of the function and of its type arguments, shared by every unit that needs it; one task per unit after the interfaces are read. NATIVE-cache then keys each unit's object code by the address of this specialized ZIR, so the two caches together are DESIGN's per-unit cache. Tests: a second build of an unchanged program runs no specialization (a counter); an edit to one library body specializes again exactly the units that unfolded it, and an edit to a body no unit unfolded specializes none; two units needing one instance specialize it once; a changed build or compiler version rebuilds all; output bytes equal a fresh build's in every case; a corrupt cache entry is rebuilt. Negative control, run once and not committed: the unfolded-body addresses left out of the key (the edit test runs a stale unit and the output differs from a fresh build). Benchmarks in `bench`: n and 8n units, cold and warm, ratio under 9 the goal, 10.5 the limit | M | yes | ZIR-iface-key, ZIR-iface-bodies | `crates/zedc/src/query.rs`, `crates/zedc/src/iface/`, `crates/zedc-stage/src/`, `tests/steps/link_unit_cache/ (new)` |
| 2 | LINK-fn-sections | From STUDY-linking (DESIGN sec:linking, "ZIR to native code, and native libraries"): the Cranelift object builder (`crates/zed-native/src/lib.rs:223`, `ObjectBuilder::new`) sets `per_function_section(true)` and `per_data_object_section(true)` (cranelift-object 0.137.1, `backend.rs` lines 133 and 139; neither is set at b7b205533), so `--gc-sections` can drop any one function or constant of a unit's object, as `-ffunction-sections -fdata-sections` gives C. Tests: an object of n functions has n `.text.*` sections (`readelf -S`); a function and a constant that no root reaches are absent from the linked program (`nm`), and one reached is present; output of the 31 corpus inputs unchanged; the program builds and runs with LLD and with GNU ld. Negative control, run once and not committed: the flag off (the unreached function is in `nm`'s list). Benchmarks in `bench`: link time and output size at n and 8n functions, ratio under 9 the goal, 10.5 the limit | S | no | STUDY-linking | `crates/zed-native/src/lib.rs`, `crates/zed-native/src/codegen.rs`, `tests/steps/link_fn_sections/ (new)` |

Changed rows: FFI-isolate (Needs FFI-launcher-memfd and FFI-isolate-domain, and no longer
STUDY-linking, which both of them need; its text now says the
wrapper loads the library and starts from embedded bytes, and its spawn-failure test fails both
start paths through a test hook instead of making a wrapper file not executable); FFI-cexport
(Needs LINK-fn-sections); NATIVE-cache (Needs LINK-unit-cache). Levels need `plan --fix`, which
this run may not run.
