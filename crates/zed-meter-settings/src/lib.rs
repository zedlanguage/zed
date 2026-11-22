//! The C library settings the scaling tests (`zed_tests::scaling`) count work under, and the start
//! of a test binary again with them when it was started without them.
//!
//! The settings are glibc tunables, which glibc reads from `GLIBC_TUNABLES` once, as the process
//! starts; a process cannot change them later. [`GLIBC_TUNABLES`] says what each does and why.
//! `tools/run_tests.sh` exports them, and before this crate a test binary run directly (by
//! `cargo test`, or a coverage run) counted under glibc's defaults and could give another verdict:
//! `l01_38_presburger` `nest_empty_project_each` with a Θ(k²) cost took 11.29 times the
//! instructions at 8n run directly and 10.41 under `tools/run_tests.sh`
//! (TEST-scaling-direct-run-verdict).
//!
//! So a binary that links this crate, which every binary holding `zed_tests::scaling` does, starts
//! itself again when the settings are missing, before `main` and before any test runs: a function
//! in `.init_array` calls `execve` on `/proc/self/exe` with the same arguments and the environment
//! with the settings added. The new process has the same pid, open files and arguments, so what
//! started the binary (cargo, a shell, a debugger following exec) sees one run. [`in_effect`] says
//! whether the process started with the settings; `zed_tests::scaling::Meter::new` refuses to
//! count when it did not, so a run that could not be started again (a setuid binary, an `execve`
//! that failed) gives no verdict rather than another one. These settings are glibc's; on other
//! systems this crate does nothing and [`in_effect`] is true.
//!
//! The start again happens at most once (proof at [`ZED_METER_STARTED_AGAIN`]), and keeps the
//! process's name: the kernel names a process after the file `execve` is given, here `exe`, so the
//! first process passes its name in [`ZED_METER_STARTED_AGAIN`] and the second sets it back. `ps`,
//! `top` and `perf report --sort comm` then show the binary's name, as without the start again,
//! but for the samples of the dynamic loader's work before `.init_array` runs, which keep `exe`.
//!
//! Under valgrind the binary does not start again. Valgrind runs a program under its own loader,
//! so there `/proc/self/exe` is valgrind's tool binary, which refuses to be started that way
//! ("valgrind: You cannot run '…' directly"; with `--trace-children=yes`, "mmap(0x58000000, …)
//! failed in UME"). The binary then runs without the settings: its tests run, and a scaling test
//! stops with the command to run, which sets `GLIBC_TUNABLES` before valgrind:
//! `env GLIBC_TUNABLES='…' valgrind <binary> <arguments>`, or, through `systemd-run` (as for the
//! memory limit of the zedtests.slice), `systemd-run --user -E GLIBC_TUNABLES='…' … valgrind …`,
//! since a unit `systemd-run` starts does not take the caller's environment. perf follows
//! `execve` and needs nothing (checked on `l07_03_unit_log_off`: the share of samples with Rust
//! frames is the same with and without the start again, with frame pointers and with DWARF).
//! TOOL-meter-reexec-profilers.
//!
//! Where the hardware has no counter of instructions and [`ZED_METER_DRRUN`] and
//! [`ZED_METER_ICOUNT`] name DynamoRIO and its client `zed_icount`, a test that makes a meter
//! starts the binary again under them, so that its instructions are counted in software
//! ([`start_under_dynamorio`] says when).

/// The settings, in the form `GLIBC_TUNABLES` takes: `name=value` items joined by `:`.
///
/// - `glibc.cpu.hwcaps=-ERMS,-FSRM` and the two thresholds of `2^64 - 1` bytes: glibc's `memcpy`
///   and `memset` use `rep movsb` and `rep stosb` on a CPU with erms or fsrm, and the hardware
///   counter sees either as one instruction or a few whatever the length, so a quadratic copy
///   would pass a scaling test. Without them, a copy or fill of `n` bytes takes instructions in
///   proportion to `n` (test `copies_and_fills_count_by_their_length`). A setting glibc does not
///   know is ignored; this glibc leaves the stosb threshold alone without erms.
///
/// Until TEST-meter-allocator-bias the settings also held `glibc.malloc.tcache_count=0`, which
/// turned off malloc's per-thread cache: with the cache the instructions malloc spends depend on
/// what earlier threads left in the arena a new thread takes over (one check took 30.39 or 30.65
/// billion instructions, SCALE-casts-spread), and without it each allocation took more
/// instructions, which lowered the ratio of a superlinear cost by 0.82% on average and 17.6% at
/// most (TEST-scaling-direct-run-verdict). A measured run now allocates from a heap of its own
/// (module `meter` of zed-alloc-count), so the setting is gone and glibc's cache serves the rest
/// of the process.
///
/// `tools/run_tests.sh` exports the same text (test
/// `run_tests_exports_the_settings_of_the_meter`). The mmap and trim thresholds are left at
/// glibc's defaults: a fixed threshold of 128 KiB makes a 64,000-deep l01_26 test 6 times slower,
/// and one of 32 MiB moves the sizes at which the memory limits of l01_17 and l01_36 refuse.
pub const GLIBC_TUNABLES: &str = "glibc.cpu.hwcaps=-ERMS,-FSRM:\
glibc.cpu.x86_rep_movsb_threshold=0xffffffffffffffff:\
glibc.cpu.x86_rep_stosb_threshold=0xffffffffffffffff";

/// The variable a process started again by this crate finds in its environment, and removes.
///
/// Its value is the name the process had before the start again (the kernel's `comm`, at most 15
/// bytes, never a NUL), which the new process sets back with `prctl(PR_SET_NAME)`.
///
/// Proof that a binary starts itself again at most once per start from outside: the function in
/// `.init_array` calls `execve` only when this variable is absent, and it passes the new process
/// an environment that holds it. The new process therefore finds it, removes it (so that programs
/// the tests start see the environment they were given) and does not call `execve`. Each process
/// image runs the function once, as glibc runs each entry of `.init_array` once, so the chain of
/// images from one start from outside has at most two.
pub const ZED_METER_STARTED_AGAIN: &str = "ZED_METER_STARTED_AGAIN";

/// The variable that names DynamoRIO's `drrun`, with [`ZED_METER_ICOUNT`] the client
/// `libzed_icount.so` (tools/icount), under which a test binary counts its instructions in
/// software where the hardware has no counter (BENCH-vm-no-instruction-counter; Colab's job.sh
/// sets both on its VMs, which have no counter).
///
/// [`start_under_dynamorio`] says when the process starts itself again under them.
pub const ZED_METER_DRRUN: &str = "ZED_METER_DRRUN";

/// The variable [`start_under_dynamorio`] passes to the process it starts under DynamoRIO, which
/// that process's function in `.init_array` notes and removes, so that it does not start itself
/// under DynamoRIO again when the client does not answer: such a start happens at most once.
pub const ZED_METER_UNDER_DRRUN: &str = "ZED_METER_UNDER_DRRUN";

/// Starts the process again under DynamoRIO, as `drrun -c <client> -- <binary> <arguments>` with
/// [`ZED_METER_DRRUN`] and [`ZED_METER_ICOUNT`], when both are set and not empty, the process was
/// started with `--exact`, it does not run under the client already (the client's system call
/// does not answer) and was not started by this function, and the hardware counter of
/// instructions does not open or does not move. It returns only when it does not start the
/// process again, or `execve` fails. Linux with glibc only; elsewhere it does nothing.
///
/// `zed_tests::scaling::Meter::new` calls it where it finds neither count, so only a test that
/// makes a meter pays the slowdown, in the process it runs in: the new image runs the same test
/// (`--exact`) from its start, and its meter reads the client's count. A benchmark, a check's
/// run in a new process and `the_instructions_of_a_run_repeat`'s run each start a test binary
/// with `--exact`. Until 2026-11-22 the function in `.init_array` started every `--exact` run
/// under DynamoRIO; a test farm runs each test that way, and the tests that measure nothing ran
/// 7.3 times slower there, so 94 of 3059 failed, most of them by their time limit (merge check of
/// b22-meter1). The slowdown and how the count compares with the hardware's are in the comment at
/// `zed_tests::scaling`.
pub fn start_under_dynamorio() {
    imp::start_under_dynamorio()
}

/// The variable that names the DynamoRIO client `libzed_icount.so`; see [`ZED_METER_DRRUN`].
pub const ZED_METER_ICOUNT: &str = "ZED_METER_ICOUNT";

/// Whether `tunables`, a value of `GLIBC_TUNABLES`, holds every item of [`GLIBC_TUNABLES`].
///
/// An item counts when it is present exactly; glibc applies items left to right, so an item that
/// sets the same name later would win, and is counted as a missing setting.
pub fn holds_the_settings(tunables: &str) -> bool {
    let items: Vec<&str> = tunables.split(':').collect();
    GLIBC_TUNABLES.split(':').all(|want| {
        let name = name_of(want);
        // The last item of this name is the one glibc keeps.
        items.iter().rev().find(|i| name_of(i) == name) == Some(&want)
    })
}

/// `tunables` with the items of [`GLIBC_TUNABLES`] in place of any of the same names, the
/// others kept in their order.
pub fn with_the_settings(tunables: &str) -> String {
    let ours: Vec<&str> = GLIBC_TUNABLES.split(':').map(name_of).collect();
    let mut items: Vec<&str> = tunables
        .split(':')
        .filter(|i| !i.is_empty() && !ours.contains(&name_of(i)))
        .collect();
    items.extend(GLIBC_TUNABLES.split(':'));
    items.join(":")
}

fn name_of(item: &str) -> &str {
    item.split_once('=').map_or(item, |(name, _)| name)
}

/// Whether the process started with the settings, as glibc read them.
///
/// On Linux with glibc: whether `GLIBC_TUNABLES` held them when the process started, and glibc
/// honored the variable, which it does unless the process runs setuid or setgid (`AT_SECURE`).
/// The binary does not start itself again when another thread already ran as it started (a
/// library preloaded with `LD_PRELOAD` that starts one; argument at `START` in this file), so
/// there the answer is whether it was started with them.
/// On other systems there are no such settings, and the answer is true.
pub fn in_effect() -> bool {
    imp::in_effect()
}

/// The number of threads of the process when the function in `.init_array` ran, as it counted
/// them in `/proc/self/task`; `None` if it could not, and on systems other than Linux with
/// glibc. 1 on every run of this workspace (argument at `START` in this file).
pub fn threads_at_start() -> Option<usize> {
    imp::threads_at_start()
}

/// Whether the process runs under valgrind, where it does not start again (see the module
/// comment). On Linux with glibc on x86_64, AArch64 and RISC-V 64 valgrind's own answer;
/// elsewhere false.
pub fn running_on_valgrind() -> bool {
    imp::running_on_valgrind()
}

/// Makes the process `command` starts get SIGKILL when the thread that starts it ends, so that a
/// process `zed_tests::scaling` starts for one check's run does not outlive the test binary
/// (zed_tests::scaling::fresh_command says why: on 2026-11-20 one ran on for 19 minutes, holding
/// 67 to 71 GB). It is here because the workspace forbids unsafe code in the crates that compile
/// the scaling harness, and this crate already holds its process-start hooks.
///
/// What the kernel promises (man page PR_SET_PDEATHSIG(2const), Linux man-pages 6.x): "The
/// parent-death signal is sent upon subsequent termination of the parent thread"; the setting "is
/// cleared for the child of a fork(2)" and is "preserved across execve(2)", except for a
/// set-user-ID or set-group-ID binary or one with file capabilities, which a test binary is not.
/// So it is set in `pre_exec`, in the child between the fork and the exec, and holds in the
/// program the exec starts. "Parent thread" is the thread that forks; a caller whose spawning
/// thread may end before the child should not use this.
///
/// The race, and its proof: "If the parent thread and all ancestor subreapers have already
/// terminated by the time of the PR_SET_PDEATHSIG operation, then no parent-death signal is
/// sent". A parent that dies between the fork and the prctl would leave the child unguarded. So
/// after the prctl the child reads its parent's pid. If it is still the pid the parent had
/// before the fork, the parent was alive after the prctl had taken effect (a child's parent pid
/// changes only when the parent dies, and then to another process), so the parent's death comes
/// later and sends the signal. If not, the parent has already died; the hook returns an error and
/// the child exits before the exec (std reports the error to a parent that no longer reads it).
/// Both pids are read in one pid namespace, which `fork` keeps. A pid reused within that window
/// by a new process that then becomes the child's parent is impossible: an orphan's new parent
/// is a subreaper or init, which were running before the fork.
///
/// Async-signal safety: the hook runs in the child after a fork of a process with other threads,
/// so it may call only async-signal-safe functions. `prctl` and `getppid` are system calls; the
/// errors are made from errno numbers, which allocates nothing.
///
/// Cost: with a `pre_exec` hook std forks and execs instead of calling `posix_spawn`; one start
/// per check's run, nothing next to the run. On other systems it does nothing (the first release
/// is Linux x86_64 only). Test: zed_tests
/// scaling_tests::a_fresh_child_ends_when_its_parent_is_killed.
#[cfg(target_os = "linux")]
#[allow(unsafe_code)]
pub fn kill_with_parent(command: &mut std::process::Command) {
    use std::os::unix::process::CommandExt;
    let parent = std::process::id();
    // SAFETY: the hook runs in the child between fork and exec and makes only the two
    // async-signal-safe system calls `prctl` and `getppid`; it allocates nothing.
    unsafe {
        command.pre_exec(move || {
            if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL as libc::c_ulong) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            if libc::getppid() as u32 != parent {
                return Err(std::io::Error::from_raw_os_error(libc::ESRCH));
            }
            Ok(())
        });
    }
}

/// Does nothing: the parent-death signal is Linux's (see the Linux version).
#[cfg(not(target_os = "linux"))]
pub fn kill_with_parent(_command: &mut std::process::Command) {}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[allow(unsafe_code)]
mod imp {
    use super::{ZED_METER_STARTED_AGAIN, holds_the_settings, with_the_settings};
    use std::ffi::{CStr, CString, c_char, c_int};
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};

    /// Set by [`start`] when the process started with the settings in effect.
    static IN_EFFECT: AtomicBool = AtomicBool::new(false);

    pub(super) fn in_effect() -> bool {
        IN_EFFECT.load(Relaxed)
    }

    /// glibc calls each function of the main program's `.init_array` with `argc`, `argv` and
    /// `envp`, before `main` (glibc `csu/libc-start.c` `call_init` for a static program,
    /// `elf/dl-init.c` `call_init` for a dynamic one: `(*init) (argc, argv, env)`). This is a
    /// glibc convention, not one of the ELF standard; hence `target_env = "gnu"`.
    ///
    /// `#[used]` keeps the entry when nothing names it: rustc lists every `#[used]` static of a
    /// crate it links in the object it adds for the crate's exported symbols, so the linker
    /// keeps the entry of a crate it links (checked: `readelf` shows the entry in the test
    /// binaries, and test `a_binary_started_without_the_settings_runs_with_them` fails without
    /// it). Each binary of `zed_tests::scaling` links this crate, since `Meter::new` calls
    /// [`super::in_effect`].
    ///
    /// Why [`start`] reads the environment vector raw and calls `std::env::remove_var` only when
    /// no other thread exists, and why that is the case on every run this workspace makes
    /// (PROOF-meter-no-thread-before-main, 2026-11-20). `remove_var`'s contract is that no other
    /// thread reads or writes the environment meanwhile; reading `envp` while another thread calls
    /// `setenv` could read freed memory.
    ///
    /// The check in the code. [`start`] first counts the entries of `/proc/self/task`, the
    /// kernel's list of the threads of this process (proc(5), "/proc/pid/task"). If it counts
    /// exactly 1, the calling thread is the only one, and stays so while `start` runs: a new
    /// thread of a process is made only by one of its threads calling `clone` with
    /// `CLONE_THREAD` (clone(2); `pthread_create` does), and `start` calls nothing that does
    /// (`std::fs::read_dir`, `getauxval`, `prctl`, allocation, `execve`). Otherwise (more than
    /// one, or `/proc` cannot be read) `start` reads the environment only through
    /// `std::env::vars_os`, which is safe to call with other threads, does not call `remove_var`
    /// and does not start the binary again (its environment would be read raw); [`in_effect`]
    /// then says whether `GLIBC_TUNABLES` held the settings, and a scaling test refuses when it
    /// did not: no verdict rather than another one. The second image with another thread keeps
    /// the marker in its environment and the name `exe`; a binary it starts inherits the marker
    /// with `GLIBC_TUNABLES` and runs with the settings, under the first image's name. Tests
    /// `no_other_thread_exists_when_start_runs` (here, and in `zed_tests`'s own tests, whose
    /// binary loads the workspace's dylibs) and `a_thread_running_before_start_is_seen`.
    ///
    /// Not covered by the check: a child made by `clone` with `CLONE_VM` and without
    /// `CLONE_THREAD` shares the memory but is another process, not listed in
    /// `/proc/self/task`; and a signal handler a preloaded library installed that starts a
    /// thread while `start` runs. No library below does either (the reading below); a library
    /// preloaded with `LD_PRELOAD` or `LD_AUDIT` that does is not handled.
    ///
    /// Why the count is 1 on the runs of this workspace, by reading the code that runs before
    /// `start`. Sources read 2026-11-20: glibc 2.43
    /// (<https://ftp.gnu.org/gnu/glibc/glibc-2.43.tar.xz>; Fedora runs 2.43-9, whose patches were
    /// not read), Rust std at the commit of the toolchain
    /// (59cbdee2e7b3ee50e44b460561c43c9e3023d9f0, rust-src of
    /// <https://static.rust-lang.org/dist/2026-11-18/>), and gcc's libgcc at the head of
    /// releases/gcc-16 (04a71db17257f5e61efacc1e9a01f5f2cc2face6; Fedora's libgcc 16.2.1-3 is a
    /// snapshot of 2026-10-29, so the machine code below was read as well).
    ///
    /// 1. The order. For a dynamic program the loader first calls `__libc_early_init`
    ///    (elf/libc_early_init.c:32-51), then `_dl_init` (elf/dl-init.c:79-127): any
    ///    `DF_1_INITFIRST` object, the main program's `DT_PREINIT_ARRAY` (this binary has none:
    ///    `readelf -d`), then for every loaded object, dependencies first (lines 119-121),
    ///    `call_init` (lines 25-76), which runs `DT_INIT` and then each entry of
    ///    `DT_INIT_ARRAY` in order, and skips the main program (lines 46-48). Then
    ///    `__libc_start_main` runs the main program's `DT_INIT` and `.init_array` in order
    ///    (csu/libc-start.c:124-147, called at line 347), then `main`. So before `start` run:
    ///    the loader, `__libc_early_init`, the constructors of every loaded library, the main
    ///    program's `DT_INIT`, and the entries of its `.init_array` before this one.
    /// 2. `__libc_early_init` calls `__ctype_init`, sets `__libc_single_threaded`,
    ///    `__pthread_early_init` (sysdeps/nptl/pthread_early_init.h:28-57: `getrlimit` and the
    ///    default thread attributes), `__getrandom_early_init`
    ///    (sysdeps/unix/sysv/linux/getrandom.c:237: one vDSO call and `sysconf`) and
    ///    `__ptmalloc_init` (malloc/arena.c:250: the main arena and malloc's tunables). None
    ///    calls `clone`.
    /// 3. The loaded libraries (`readelf -d` and `ldd` on this crate's test binary and the
    ///    workspace's dylibs, 2026-11-20): `ld-linux-x86-64.so.2` (no `DT_INIT`, no
    ///    `DT_INIT_ARRAY`); `libc.so.6`, whose `.init_array` holds `_init_first`
    ///    (csu/init-first.c:44-72: stores `argc`, `argv`, `environ`, may set the FPU control
    ///    word by `__setfpucw`, math/setfpucw.c, then `__init_misc`, misc/init-misc.c, which
    ///    sets `__progname`), `check_stdfiles_vtables` (libio/vtables.c:544, at most one
    ///    relaxed store, libio/libioP.h:1011-1015) and `_IO_stdfiles_init`
    ///    (libio/stdfiles.c:61-70, links the three `FILE`s); `libstd-*.so`, whose
    ///    `.init_array` holds `ARGV_INIT_ARRAY` (library/std/src/sys/args/unix.rs:102-135,
    ///    section `.init_array.00099`: two stores, `ARGC` and `ARGV`; the other constructor of
    ///    std, `RUST_LSE_INIT` in library/std/src/sys/configure_builtins.rs:33-62, is built for
    ///    aarch64 only) and `frame_dummy`; `libgcc_s.so.1`, whose `.init_array` holds
    ///    `__cpu_indicator_init` (libgcc/config/i386/cpuinfo.c:58-64, `cpuid` and `xgetbv` into
    ///    `__cpu_model`) and `frame_dummy`; `librt.so.1`, `libpthread.so.0` and `libdl.so.2`,
    ///    which libstd needs, and the 17 dylibs of the workspace a step binary loads
    ///    (`libzed_kernel-*.so` and the others), each with `frame_dummy` alone. Each library's
    ///    `DT_INIT` is the `_init` of crti (sysdeps/x86_64/crti.S:63-75), which calls
    ///    `__gmon_start__` only when it is defined; it is weak and undefined here (`nm -D`), so
    ///    `_init` calls nothing. Each `frame_dummy` (gcc crtstuff.c) jumps to
    ///    `register_tm_clones`, which returns at once when `.tm_clone_table` is empty; it has
    ///    size 0 in every one of these objects (`readelf -S`).
    /// 4. The main program's `DT_INIT` is the same crti `_init`; its `.init_array` holds two
    ///    entries (`INIT_ARRAYSZ` 16): `frame_dummy`, then this one (the relocations of the
    ///    array, resolved by `nm`). No crate of the workspace puts another function in
    ///    `.init_array` (`grep` for `init_array` and `link_section` under `crates/` and
    ///    `tests/`; this crate's tests add one, see `a_thread_running_before_start_is_seen`),
    ///    and `Cargo.lock` holds none of the crates that do (`ctor`, `linkme`, `inventory`).
    ///
    /// How the reading was checked: `objdump -d` of every function named in 3 and 4 in the
    /// installed libraries, which shows no `syscall` and no call but to `strrchr`,
    /// `__setfpucw`, `__stack_chk_fail` and the weak symbols above; `__cpu_indicator_init`
    /// (0x12f3 bytes) has no call or `syscall`, and its three jump tables jump inside it. And
    /// `strace -f -e trace=clone,clone3,fork,vfork,execve` on this crate's test binary started
    /// without `GLIBC_TUNABLES` shows the `execve` of `/proc/self/exe` with no `clone` before
    /// it; the first `clone3` (the test harness's thread) comes after `main`. What the reading
    /// cannot catch: a library added later, a new version of these with a constructor that
    /// starts a thread, or a preloaded one; the check above covers those, and
    /// `no_other_thread_exists_when_start_runs` fails on them.
    #[used]
    #[unsafe(link_section = ".init_array")]
    static START: extern "C" fn(c_int, *const *const c_char, *const *const c_char) = start;

    /// The threads of this process when [`start`] ran, as it counted them; 0 if it could not.
    static THREADS_AT_START: AtomicUsize = AtomicUsize::new(0);

    pub(super) fn threads_at_start() -> Option<usize> {
        Some(THREADS_AT_START.load(Relaxed)).filter(|&n| n > 0)
    }

    extern "C" fn start(_argc: c_int, argv: *const *const c_char, envp: *const *const c_char) {
        // Each test gives back the free memory of the C library as it ends, in this binary as in
        // every test binary (TEST-l01-26-peak-memory; why and what it costs:
        // zed_alloc_count::give_back_as_each_test_ends). It stores one flag and allocates nothing.
        zed_alloc_count::give_back_as_each_test_ends();
        // The check of the argument at `START`.
        let threads = std::fs::read_dir("/proc/self/task").map_or(0, |d| d.count());
        THREADS_AT_START.store(threads, Relaxed);
        // SAFETY: getauxval reads the auxiliary vector the kernel gave the process.
        let secure = unsafe { libc::getauxval(libc::AT_SECURE) } != 0;
        if threads != 1 {
            // Another thread may exist (argument at `START`): the environment is read through
            // std, which is safe with other threads, and neither changed nor passed on.
            let tunables = std::env::vars_os()
                .filter(|(k, _)| k == "GLIBC_TUNABLES")
                .last()
                .map(|(_, v)| v.to_string_lossy().into_owned());
            let held = tunables.as_deref().is_some_and(holds_the_settings);
            IN_EFFECT.store(held && !secure, Relaxed);
            return;
        }
        // SAFETY: glibc passes the program's argument and environment vectors, each ended by a
        // null pointer, and the calling thread is the only one (checked above; argument at
        // `START`).
        //
        // Why the `expect`s on `CString::new` below cannot fire: `CString::new` fails only on a
        // NUL byte in its argument. Each environment string here is `CStr::to_bytes` of an entry
        // (in `strings`), which ends before the first NUL, so it holds none; the marker's value
        // `name` is such a string's suffix in the second image, and in the first the bytes of
        // `PR_GET_NAME`'s buffer before its first NUL (`CStr::from_bytes_until_nul`); the
        // tunables text is `String::from_utf8_lossy` of such a string (which writes U+FFFD for a
        // bad byte, never a NUL) joined by `:` with the items of `GLIBC_TUNABLES`, which hold no
        // NUL. Tested only on the strings of real runs (test
        // `a_binary_started_without_the_settings_starts_again_with_them_and_its_name`); the
        // argument covers the rest.
        let env = unsafe { strings(envp) };
        let tunables = env
            .iter()
            .rev()
            .find_map(|e| e.strip_prefix(b"GLIBC_TUNABLES="))
            .map(|v| String::from_utf8_lossy(v).into_owned());
        // The value of the marker, the name to set back; empty for a marker with no `=`.
        let again = env.iter().find_map(|e| {
            let name = e.split(|&b| b == b'=').next()?;
            (name == ZED_METER_STARTED_AGAIN.as_bytes())
                .then(|| &e[(name.len() + 1).min(e.len())..])
        });
        let held = tunables.as_deref().is_some_and(holds_the_settings);
        IN_EFFECT.store(held && !secure, Relaxed);
        let under = super::ZED_METER_UNDER_DRRUN.as_bytes();
        if env.iter().any(|e| {
            e.strip_prefix(under)
                .is_some_and(|r| r.first() == Some(&b'='))
        }) {
            STARTED_UNDER_DYNAMORIO.store(true, Relaxed);
            // SAFETY: the calling thread is the only one (checked at the top), and `envp`'s
            // strings were copied into `env` above.
            unsafe { std::env::remove_var(super::ZED_METER_UNDER_DRRUN) };
        }
        if let Some(name) = again {
            if !name.is_empty() {
                let name = CString::new(name).expect("an environment string has no NUL");
                // SAFETY: PR_SET_NAME reads a NUL-ended string and keeps its first 15 bytes as
                // the name of the calling thread, here the only one.
                unsafe { libc::prctl(libc::PR_SET_NAME, name.as_ptr()) };
            }
            // SAFETY: the calling thread is the only one (checked at the top; argument at
            // `START`), so no other thread reads the environment while this changes it. `envp`'s
            // strings were copied into `env` above, so nothing here reads the vector `remove_var`
            // may change.
            unsafe { std::env::remove_var(ZED_METER_STARTED_AGAIN) };
            return;
        }
        if secure || running_on_valgrind() || held {
            return;
        }
        // The kernel's name of the process, at most 15 bytes and a NUL.
        let mut name = [0u8; 16];
        // SAFETY: PR_GET_NAME writes at most 16 bytes, NUL included, to the buffer.
        unsafe { libc::prctl(libc::PR_GET_NAME, name.as_mut_ptr()) };
        let name = CStr::from_bytes_until_nul(&name).map_or(&[][..], CStr::to_bytes);
        let mut new_env: Vec<CString> = env
            .iter()
            .filter(|e| !e.starts_with(b"GLIBC_TUNABLES="))
            .map(|e| CString::new(e.as_slice()).expect("an environment string has no NUL"))
            .collect();
        let tunables = with_the_settings(tunables.as_deref().unwrap_or(""));
        new_env.push(CString::new(format!("GLIBC_TUNABLES={tunables}")).expect("no NUL"));
        let marker = [ZED_METER_STARTED_AGAIN.as_bytes(), b"=", name].concat();
        new_env.push(CString::new(marker).expect("no NUL"));
        let mut ptrs: Vec<*const c_char> = new_env.iter().map(|c| c.as_ptr()).collect();
        ptrs.push(std::ptr::null());
        // SAFETY: `argv` is the program's own null-ended vector, and `ptrs` is null-ended and
        // points into `new_env`, which lives across the call. execve returns only on failure;
        // the process then goes on without the settings, and `in_effect` says so.
        unsafe { libc::execve(c"/proc/self/exe".as_ptr(), argv, ptrs.as_ptr()) };
    }

    /// Set by [`start`] when the process was started by [`start_under_dynamorio`], so that it
    /// does not start itself under DynamoRIO a second time when the client does not answer.
    static STARTED_UNDER_DYNAMORIO: AtomicBool = AtomicBool::new(false);

    /// See [`super::start_under_dynamorio`].
    pub(super) fn start_under_dynamorio() {
        let var = |name: &str| {
            std::env::var_os(name)
                .filter(|v| !v.is_empty())
                .and_then(|v| CString::new(v.into_encoded_bytes()).ok())
        };
        let (Some(drrun), Some(client)) =
            (var(super::ZED_METER_DRRUN), var(super::ZED_METER_ICOUNT))
        else {
            return;
        };
        let args: Vec<CString> = std::env::args_os()
            .filter_map(|a| CString::new(a.into_encoded_bytes()).ok())
            .collect();
        if STARTED_UNDER_DYNAMORIO.load(Relaxed)
            || !args.iter().skip(1).any(|a| a.as_bytes() == b"--exact")
            || zed_alloc_count::os::software_instructions().is_some()
            || hardware_counter_moves()
        {
            return;
        }
        // `drrun -c <client> -- <this binary> <its arguments>`. The binary is named by the file
        // `/proc/self/exe` links to, read here, since the new process is drrun's. The environment
        // is this one, which holds the settings (the caller checks `in_effect` first), with the
        // marker of a start again, so that the new image's `start` sets the name back and does
        // not start again, and [`super::ZED_METER_UNDER_DRRUN`], so that it does not come here
        // again. Each argument and variable came from a NUL-ended string, so `CString::new`
        // drops none of them (`filter_map` above, `flat_map` below).
        let Some(exe) = std::fs::read_link("/proc/self/exe")
            .ok()
            .and_then(|p| CString::new(p.into_os_string().into_encoded_bytes()).ok())
        else {
            return;
        };
        let mut name = [0u8; 16];
        // SAFETY: PR_GET_NAME writes at most 16 bytes, NUL included, to the buffer.
        unsafe { libc::prctl(libc::PR_GET_NAME, name.as_mut_ptr()) };
        let name = CStr::from_bytes_until_nul(&name).map_or(&[][..], CStr::to_bytes);
        let mut env: Vec<CString> = std::env::vars_os()
            .flat_map(|(k, v)| {
                CString::new([k.as_encoded_bytes(), b"=", v.as_encoded_bytes()].concat())
            })
            .collect();
        env.push(
            CString::new([ZED_METER_STARTED_AGAIN.as_bytes(), b"=", name].concat())
                .expect("no NUL"),
        );
        env.push(CString::new(format!("{}=1", super::ZED_METER_UNDER_DRRUN)).expect("no NUL"));
        let mut ptrs: Vec<*const c_char> = env.iter().map(|c| c.as_ptr()).collect();
        ptrs.push(std::ptr::null());
        let mut dargs = vec![drrun, c"-c".to_owned(), client, c"--".to_owned(), exe];
        dargs.extend(args.into_iter().skip(1));
        let mut dptrs: Vec<*const c_char> = dargs.iter().map(|c| c.as_ptr()).collect();
        dptrs.push(std::ptr::null());
        // Output written before this point, such as the test harness's "running 1 test", is
        // written once more by the new image; std's stdout is flushed at each line, so none is
        // lost. SAFETY: `dptrs` and `ptrs` are null-ended and point into `dargs` and `env`,
        // which live across the call. execve returns only on failure, and the kernel ends the
        // other threads of the process when it succeeds.
        unsafe { libc::execve(dargs[0].as_ptr(), dptrs.as_ptr(), ptrs.as_ptr()) };
    }

    /// Whether `perf_event_open` opens the hardware counter of the instructions this thread runs
    /// in user mode, and it counts some of a loop of 10^5 steps: the test of
    /// `zed_tests::scaling::Meter::new` (`Meter::open`, `first_that_moves`), made here with the
    /// system call itself, since this crate does not link perf-event. Some virtual machines open
    /// the counter and leave it at 0, as that test says.
    ///
    /// The attribute is `struct perf_event_attr` of `linux/perf_event.h` at its first size,
    /// `PERF_ATTR_SIZE_VER0` = 64 bytes, which every kernel since 2.6.31 takes (perf_event_open(2):
    /// "size ... for forward/backward compatibility"): `type` `PERF_TYPE_HARDWARE` (0), `config`
    /// `PERF_COUNT_HW_INSTRUCTIONS` (1), and in the flags word the bit fields `exclude_kernel`
    /// (bit 5) and `exclude_hv` (bit 6) in declaration order. GCC places the first bit field of a
    /// unit at its least significant bit on a little-endian target and at its most significant
    /// bit on a big-endian one (the System V ABIs of x86_64, AArch64 and RISC-V are little-endian;
    /// s390x and big-endian PowerPC, where this crate also builds, are not), so bit `k` is `1 << k` or
    /// `1 << (63 - k)` by `target_endian`; `disabled` (bit 0) is clear, so the counter counts from
    /// the call on. pid 0 and cpu -1: this thread, on any processor. Run only on x86_64 Colab VMs,
    /// where the counter does not open (strace of 2026-11-22 shows the start under drrun that
    /// follows); neither the case where it opens nor the big-endian form has been run.
    fn hardware_counter_moves() -> bool {
        #[repr(C)]
        struct Attr {
            kind: u32,
            size: u32,
            config: u64,
            sample_period: u64,
            sample_type: u64,
            read_format: u64,
            flags: u64,
            wakeup_events: u32,
            bp_type: u32,
            config1: u64,
        }
        const _: () = assert!(std::mem::size_of::<Attr>() == 64);
        let bit = |k: u32| {
            if cfg!(target_endian = "little") {
                1 << k
            } else {
                1 << (63 - k)
            }
        };
        let attr = Attr {
            kind: 0,
            size: 64,
            config: 1,
            sample_period: 0,
            sample_type: 0,
            read_format: 0,
            flags: bit(5) | bit(6),
            wakeup_events: 0,
            bp_type: 0,
            config1: 0,
        };
        // SAFETY: the kernel reads `size` = 64 bytes of `attr`, which is 64 bytes long and lives
        // across the call; the other arguments are numbers.
        let fd = unsafe { libc::syscall(libc::SYS_perf_event_open, &raw const attr, 0, -1, -1, 0) };
        let Ok(fd) = c_int::try_from(fd) else {
            return false;
        };
        if fd < 0 {
            return false;
        }
        let mut k = 100_000u64;
        while std::hint::black_box(k) > 0 {
            k -= 1;
        }
        let mut count = 0u64;
        // SAFETY: `fd` is the counter just opened; a read of it without `read_format` writes one
        // u64 to `count`, 8 bytes long. `close` ends it.
        let read = unsafe { libc::read(fd, (&raw mut count).cast(), 8) };
        // SAFETY: as above.
        unsafe { libc::close(fd) };
        read == 8 && count > 0
    }

    /// Whether the process runs under valgrind: valgrind's client request
    /// `RUNNING_ON_VALGRIND`, which valgrind's header `include/valgrind.h` defines as "the number
    /// of Valgrinds this code is running under. That is, 0 if running natively, 1 if running
    /// under Valgrind, …". On amd64 a client request is the four rotations of `rdi` below,
    /// `__SPECIAL_INSTRUCTION_PREAMBLE` (3 + 13 + 61 + 51 = 128 bits, so `rdi` ends as it began),
    /// then `xchg rbx, rbx`, with `rax` the address of six words (the request code, then five
    /// arguments) and `rdx` the default; valgrind's translator recognizes the sequence and puts
    /// the answer in `rdx`, and natively it changes no register and leaves the default, 0.
    /// `0x1001` is `VG_USERREQ__RUNNING_ON_VALGRIND` of the enum `Vg_ClientRequest` in the same
    /// header. Read 2026-11-20 in the copy of the header at
    /// github.com/LouisBrunner/valgrind-macos (`include/valgrind.h.in`, the macros of the amd64
    /// platforms and the enum), since sourceware.org refused the request; the client request is
    /// valgrind's interface to programs, kept the same across releases. Checked by running it:
    /// 0 natively, 1 under valgrind 3.27.1 with the tools none, memcheck and callgrind; test
    /// `under_valgrind_the_binary_runs_without_starting_again` runs this binary under valgrind.
    ///
    /// AArch64 and RISC-V 64 (PORTABLE-meter-valgrind; the Linux targets of REL-aarch64 and
    /// REL-riscv) have their own sequences, from the macros `PLAT_arm64_linux` and
    /// `PLAT_riscv64_linux` of the same header and copy, read 2026-11-22: on AArch64 `x12` rotated
    /// by 3, 13, 51 and 61 bits (128 in all), then `orr x10, x10, x10`, with `x4` the address of
    /// the six words and `x3` the default and the answer; on RISC-V `srli zero, zero, 3`, 13, 51
    /// and 61 (shifts into the zero register, which do nothing) in uncompressed form
    /// (`.option norvc`, as the header does, so that the translator sees the 4-byte encodings),
    /// then `or a0, a0, a0`, with `a4` the address and `a3` the default and the answer. Natively
    /// each changes no register. Other architectures valgrind runs on Linux (32-bit ARM, PowerPC,
    /// s390x, MIPS) are no target of the plan; there valgrind gives the failure the module
    /// comment describes.
    #[cfg(target_arch = "x86_64")]
    pub(super) fn running_on_valgrind() -> bool {
        let request: [u64; 6] = [0x1001, 0, 0, 0, 0, 0];
        let mut answer: u64 = 0;
        // SAFETY: natively the sequence changes no register but the flags (`rdi` is rotated by
        // 128 bits in all) and reads no memory; valgrind reads the six words at `rax`, which live
        // across the call, and writes only `rdx`.
        unsafe {
            std::arch::asm!(
                "rol rdi, 3",
                "rol rdi, 13",
                "rol rdi, 61",
                "rol rdi, 51",
                "xchg rbx, rbx",
                in("rax") request.as_ptr(),
                inout("rdx") answer,
            );
        }
        answer != 0
    }

    #[cfg(target_arch = "aarch64")]
    pub(super) fn running_on_valgrind() -> bool {
        let request: [u64; 6] = [0x1001, 0, 0, 0, 0, 0];
        let mut answer: u64 = 0;
        // SAFETY: natively the sequence changes no register (`x12` is rotated by 128 bits in all,
        // `orr` writes `x10` its own value; neither sets the flags) and reads no memory; valgrind
        // reads the six words at `x4`, which live across the call, and writes only `x3`.
        unsafe {
            std::arch::asm!(
                "ror x12, x12, #3",
                "ror x12, x12, #13",
                "ror x12, x12, #51",
                "ror x12, x12, #61",
                "orr x10, x10, x10",
                in("x4") request.as_ptr(),
                inout("x3") answer,
            );
        }
        answer != 0
    }

    #[cfg(target_arch = "riscv64")]
    pub(super) fn running_on_valgrind() -> bool {
        let request: [u64; 6] = [0x1001, 0, 0, 0, 0, 0];
        let mut answer: u64 = 0;
        // SAFETY: natively the sequence changes no register (shifts into `zero` are discarded,
        // `or` writes `a0` its own value) and reads no memory; valgrind reads the six words at
        // `a4`, which live across the call, and writes only `a3`.
        unsafe {
            std::arch::asm!(
                ".option push",
                ".option norvc",
                "srli zero, zero, 3",
                "srli zero, zero, 13",
                "srli zero, zero, 51",
                "srli zero, zero, 61",
                "or a0, a0, a0",
                ".option pop",
                in("a4") request.as_ptr(),
                inout("a3") answer,
            );
        }
        answer != 0
    }

    #[cfg(not(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "riscv64"
    )))]
    pub(super) fn running_on_valgrind() -> bool {
        false
    }

    /// The strings of a null-ended vector of C strings.
    ///
    /// # Safety
    /// `v` is null or points to a null-ended array of pointers to NUL-ended strings.
    unsafe fn strings(v: *const *const c_char) -> Vec<Vec<u8>> {
        let mut out = Vec::new();
        if v.is_null() {
            return out;
        }
        let mut i = 0;
        loop {
            // SAFETY: the array is null-ended, and `i` stops at the null pointer.
            let p = unsafe { *v.add(i) };
            if p.is_null() {
                return out;
            }
            // SAFETY: each entry before the null pointer is a NUL-ended string.
            out.push(unsafe { CStr::from_ptr(p) }.to_bytes().to_vec());
            i += 1;
        }
    }
}

#[cfg(not(all(target_os = "linux", target_env = "gnu")))]
mod imp {
    pub(super) fn in_effect() -> bool {
        true
    }

    pub(super) fn threads_at_start() -> Option<usize> {
        None
    }

    pub(super) fn start_under_dynamorio() {}

    pub(super) fn running_on_valgrind() -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The start hook turns on the trim at the end of each test (TEST-l01-26-peak-memory):
    /// `zed_alloc_count::give_back_as_each_test_ends` has been called before any test runs.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn each_test_gives_back_its_free_memory_as_it_ends() {
        assert!(zed_alloc_count::gives_back());
    }

    #[test]
    fn the_settings_are_held_only_when_each_is_the_last_of_its_name() {
        assert!(holds_the_settings(GLIBC_TUNABLES));
        assert!(holds_the_settings(&format!(
            "glibc.malloc.check=3:{GLIBC_TUNABLES}"
        )));
        assert!(!holds_the_settings(""));
        assert!(!holds_the_settings("glibc.cpu.hwcaps=-ERMS,-FSRM"));
        assert!(!holds_the_settings(&format!(
            "{GLIBC_TUNABLES}:glibc.cpu.hwcaps=-AVX2"
        )));
    }

    #[test]
    fn adding_the_settings_keeps_other_items_and_replaces_those_of_the_same_names() {
        assert_eq!(with_the_settings(""), GLIBC_TUNABLES);
        let added = with_the_settings("glibc.cpu.hwcaps=-AVX2:glibc.malloc.check=3");
        assert_eq!(added, format!("glibc.malloc.check=3:{GLIBC_TUNABLES}"));
        assert!(holds_the_settings(&added));
    }

    /// Run with or without `GLIBC_TUNABLES`, this binary has started itself again with the
    /// settings by the time a test runs, and the variable that marks the start again is gone.
    /// Under valgrind, where it does not start again, it runs with the settings exactly when
    /// valgrind was started with them.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn a_binary_started_without_the_settings_runs_with_them() {
        let tunables = std::env::var("GLIBC_TUNABLES").unwrap_or_default();
        if running_on_valgrind() {
            assert_eq!(in_effect(), holds_the_settings(&tunables), "{tunables:?}");
        } else {
            assert!(in_effect());
            assert!(holds_the_settings(&tunables), "{tunables:?}");
        }
        assert!(std::env::var_os(ZED_METER_STARTED_AGAIN).is_none());
    }

    /// The kernel's name of this process is the start of the file name of this binary, as when
    /// it is started directly: the start again sets back the name `execve` of `/proc/self/exe`
    /// gives (`exe`). Under valgrind every program has the name of valgrind's tool binary
    /// (`valgrind --tool=none cat /proc/self/comm` prints `none-amd64-linu`), so there is
    /// nothing to check.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn the_name_of_the_process_is_that_of_its_binary() {
        if running_on_valgrind() {
            return;
        }
        let name = std::fs::read_to_string("/proc/self/comm").unwrap();
        let exe = std::env::current_exe().unwrap();
        let file = exe.file_name().unwrap().to_str().unwrap();
        assert_eq!(name.trim_end(), &file[..file.len().min(15)]);
    }

    /// The two tests above, in this binary started without the settings, so that it starts
    /// itself again whatever the settings of this run (`tools/run_tests.sh` exports them).
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn a_binary_started_without_the_settings_starts_again_with_them_and_its_name() {
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "--test-threads=1"])
            .arg("tests::a_binary_started_without_the_settings_runs_with_them")
            .arg("tests::the_name_of_the_process_is_that_of_its_binary")
            .env_remove("GLIBC_TUNABLES")
            .env_remove(ZED_METER_STARTED_AGAIN)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            out.status.success() && stdout.contains(" 2 passed;"),
            "{stdout}{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    /// When this crate's function in `.init_array` ran, this process had one thread. Fails when a
    /// constructor that runs before it (of a library, or of the program) has started a thread:
    /// [`a_thread_running_before_start_is_seen`] runs it with such a constructor and checks that
    /// it fails there. Covers only the libraries this binary loads; `zed_tests` has the same test
    /// for a binary that loads the workspace's dylibs.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn no_other_thread_exists_when_start_runs() {
        assert_eq!(threads_at_start(), Some(1));
    }

    /// Set by [`a_thread_running_before_start_is_seen`] for the runs of this binary in which
    /// [`THREAD`] starts a thread before this crate's function in `.init_array` runs.
    const THREAD_BEFORE_START: &str = "ZED_METER_TEST_THREAD_BEFORE_START";

    /// A constructor of this test binary that runs before this crate's (the linker puts the
    /// sections `.init_array.N` before `.init_array`; checked by the runs below, which see two
    /// threads) and, when [`THREAD_BEFORE_START`] is set, starts a thread that sleeps until the
    /// process ends, as a preloaded library could.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[allow(unsafe_code)]
    #[used]
    #[unsafe(link_section = ".init_array.65535")]
    static THREAD: extern "C" fn() = {
        extern "C" fn thread() {
            if std::env::var_os(THREAD_BEFORE_START).is_some() {
                std::thread::spawn(|| {
                    loop {
                        std::thread::park();
                    }
                });
            }
        }
        thread
    };

    /// In a run with [`THREAD_BEFORE_START`] set (one of those
    /// [`a_thread_running_before_start_is_seen`] starts): the function in `.init_array` saw two
    /// threads, so it neither started the binary again nor removed the marker, and
    /// [`in_effect`] says whether the binary was started with the settings.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn with_a_thread_before_start_the_binary_does_not_start_again() {
        if std::env::var_os(THREAD_BEFORE_START).is_none() {
            return;
        }
        assert_eq!(threads_at_start(), Some(2));
        let tunables = std::env::var("GLIBC_TUNABLES").ok();
        let marker = std::env::var(ZED_METER_STARTED_AGAIN).ok();
        if let Some(name) = marker {
            // Started as a second image: the marker stays, the settings came with it.
            assert_eq!(name, "first-name");
            assert!(in_effect());
        } else {
            // Started without the settings: not started again, so still without them.
            assert_eq!(tunables, None);
            assert!(!in_effect());
        }
    }

    /// This binary started with a thread running before this crate's function in `.init_array`
    /// (by [`THREAD`]): once without the settings, as a first image, and once with them and the
    /// marker, as a second image. In each, [`no_other_thread_exists_when_start_runs`] fails
    /// (the negative control: that test sees the thread) and
    /// [`with_a_thread_before_start_the_binary_does_not_start_again`] passes.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn a_thread_running_before_start_is_seen() {
        for second_image in [false, true] {
            let mut run = std::process::Command::new(std::env::current_exe().unwrap());
            run.args(["--exact", "--test-threads=1"])
                .arg("tests::no_other_thread_exists_when_start_runs")
                .arg("tests::with_a_thread_before_start_the_binary_does_not_start_again")
                .env_remove("GLIBC_TUNABLES")
                .env_remove(ZED_METER_STARTED_AGAIN)
                .env(THREAD_BEFORE_START, "1");
            if second_image {
                run.env("GLIBC_TUNABLES", GLIBC_TUNABLES)
                    .env(ZED_METER_STARTED_AGAIN, "first-name");
            }
            let out = run.output().unwrap();
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert!(
                stdout.contains(" 1 passed; 1 failed;")
                    && stdout.contains("tests::no_other_thread_exists_when_start_runs ... FAILED")
                    && stdout.contains("left: Some(2)"),
                "second image: {second_image}\n{stdout}{}",
                String::from_utf8_lossy(&out.stderr)
            );
        }
    }

    /// Set by [`under_valgrind_the_binary_runs_without_starting_again`] for the run of this
    /// binary under valgrind it starts.
    const UNDER_VALGRIND: &str = "ZED_METER_TEST_UNDER_VALGRIND";

    /// Valgrind is seen exactly when the run is under it, which valgrind also shows by preloading
    /// its library `vgpreload_core` into every program it runs (valgrind 3.27.1 with the tools
    /// none and memcheck: `LD_PRELOAD=/usr/libexec/valgrind/vgpreload_core-amd64-linux.so…`).
    /// In the runs [`under_valgrind_the_binary_runs_without_starting_again`] starts the binary
    /// did not start again, so it runs with the settings exactly when it was started with them
    /// ([`UNDER_VALGRIND`] is "with" or "without").
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn valgrind_is_seen_exactly_under_valgrind() {
        let preload = std::env::var("LD_PRELOAD").unwrap_or_default();
        let under = preload.contains("vgpreload_core");
        assert_eq!(running_on_valgrind(), under, "LD_PRELOAD={preload:?}");
        if let Ok(settings) = std::env::var(UNDER_VALGRIND) {
            assert!(under);
            let with = settings == "with";
            let tunables = std::env::var("GLIBC_TUNABLES").unwrap_or_default();
            assert_eq!(in_effect(), with, "{tunables:?}");
            assert_eq!(holds_the_settings(&tunables), with, "{tunables:?}");
        }
    }

    /// This binary, started under valgrind with the tools none and memcheck, each without and
    /// with the settings, runs its tests without starting again: valgrind's tool binary, which
    /// `/proc/self/exe` names there, would refuse to be started ("You cannot run '…' directly").
    /// On the architectures whose client request [`running_on_valgrind`] sends
    /// (PORTABLE-meter-valgrind). Needs valgrind.
    #[cfg(all(
        target_os = "linux",
        target_env = "gnu",
        any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "riscv64"
        )
    ))]
    #[test]
    fn under_valgrind_the_binary_runs_without_starting_again() {
        for tool in ["--tool=none", "--tool=memcheck"] {
            for with in [false, true] {
                let mut run = std::process::Command::new("valgrind");
                run.args(["-q", tool, "--error-exitcode=99"])
                    .arg(std::env::current_exe().unwrap())
                    .args(["--exact", "tests::valgrind_is_seen_exactly_under_valgrind"])
                    .env_remove("GLIBC_TUNABLES")
                    .env_remove(ZED_METER_STARTED_AGAIN)
                    .env(UNDER_VALGRIND, if with { "with" } else { "without" });
                if with {
                    run.env("GLIBC_TUNABLES", GLIBC_TUNABLES);
                }
                let out = run.output().expect(
                    "this test runs valgrind, which is not installed (Fedora: dnf install valgrind)",
                );
                let stdout = String::from_utf8_lossy(&out.stdout);
                assert!(
                    out.status.success() && stdout.contains(" 1 passed;"),
                    "{tool}, with the settings: {with}\n{stdout}{}",
                    String::from_utf8_lossy(&out.stderr)
                );
            }
        }
    }
}
