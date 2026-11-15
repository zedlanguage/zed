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
//! The start again happens at most once (proof at [`ZED_METER_STARTED_AGAIN`]). A tool that runs
//! the binary under its own loader and does not follow `execve` (valgrind with
//! `--trace-children=no`, the default) sees the process end at the `execve`; such a run sets
//! `GLIBC_TUNABLES` itself, as the message of `Meter::new` shows.

/// The settings, in the form `GLIBC_TUNABLES` takes: `name=value` items joined by `:`.
///
/// - `glibc.cpu.hwcaps=-ERMS,-FSRM` and the two thresholds of `2^64 - 1` bytes: glibc's `memcpy`
///   and `memset` use `rep movsb` and `rep stosb` on a CPU with erms or fsrm, and the hardware
///   counter sees either as one instruction or a few whatever the length, so a quadratic copy
///   would pass a scaling test. Without them, a copy or fill of `n` bytes takes instructions in
///   proportion to `n` (test `copies_and_fills_count_by_their_length`). A setting glibc does not
///   know is ignored; this glibc leaves the stosb threshold alone without erms.
/// - `glibc.malloc.tcache_count=0`: no per-thread cache in malloc. With the cache, the
///   instructions malloc spends depend on what earlier threads left in the arena a new thread
///   takes over: one check of the same program, on a new thread each time, took 30.39 or 30.65
///   billion instructions, and the difference of two checks that l01_29's casts tests take came
///   out 1.5 times its size in 3 of 30 runs; without it, 30 runs in 15 processes repeat to within
///   0.04% (SCALE-casts-spread, test `malloc_keeps_no_state_from_earlier_threads`). The price is
///   more instructions per allocation, a cost linear in the allocations, which lowers the ratio of
///   a superlinear cost a little (TEST-scaling-direct-run-verdict measured it on each benchmark).
///
/// `tools/run_tests.sh` exports the same text (test
/// `run_tests_exports_the_settings_of_the_meter`). The mmap and trim thresholds are left at
/// glibc's defaults: a fixed threshold of 128 KiB makes a 64,000-deep l01_26 test 6 times slower,
/// and one of 32 MiB moves the sizes at which the memory limits of l01_17 and l01_36 refuse.
pub const GLIBC_TUNABLES: &str = "glibc.cpu.hwcaps=-ERMS,-FSRM:\
glibc.cpu.x86_rep_movsb_threshold=0xffffffffffffffff:\
glibc.cpu.x86_rep_stosb_threshold=0xffffffffffffffff:\
glibc.malloc.tcache_count=0";

/// The variable a process started again by this crate finds in its environment, and removes.
///
/// Proof that a binary starts itself again at most once per start from outside: the function in
/// `.init_array` calls `execve` only when this variable is absent, and it passes the new process
/// an environment that holds it. The new process therefore finds it, removes it (so that programs
/// the tests start see the environment they were given) and does not call `execve`. Each process
/// image runs the function once, as glibc runs each entry of `.init_array` once, so the chain of
/// images from one start from outside has at most two.
pub const ZED_METER_STARTED_AGAIN: &str = "ZED_METER_STARTED_AGAIN";

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
/// On other systems there are no such settings, and the answer is true.
pub fn in_effect() -> bool {
    imp::in_effect()
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[allow(unsafe_code)]
mod imp {
    use super::{ZED_METER_STARTED_AGAIN, holds_the_settings, with_the_settings};
    use std::ffi::{CStr, CString, c_char, c_int};
    use std::sync::atomic::{AtomicBool, Ordering::Relaxed};

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
    #[used]
    #[unsafe(link_section = ".init_array")]
    static START: extern "C" fn(c_int, *const *const c_char, *const *const c_char) = start;

    extern "C" fn start(_argc: c_int, argv: *const *const c_char, envp: *const *const c_char) {
        // SAFETY: glibc passes the program's argument and environment vectors, each ended by a
        // null pointer, and no other thread exists before `main`.
        let env = unsafe { strings(envp) };
        let tunables = env
            .iter()
            .rev()
            .find_map(|e| e.strip_prefix(b"GLIBC_TUNABLES="))
            .map(|v| String::from_utf8_lossy(v).into_owned());
        let again = env
            .iter()
            .any(|e| e.split(|&b| b == b'=').next() == Some(ZED_METER_STARTED_AGAIN.as_bytes()));
        // SAFETY: getauxval reads the auxiliary vector the kernel gave the process.
        let secure = unsafe { libc::getauxval(libc::AT_SECURE) } != 0;
        let held = tunables.as_deref().is_some_and(holds_the_settings);
        IN_EFFECT.store(held && !secure, Relaxed);
        if again {
            // SAFETY: no other thread exists before `main`, so no other thread reads the
            // environment while this changes it.
            unsafe { std::env::remove_var(ZED_METER_STARTED_AGAIN) };
            return;
        }
        if held || secure {
            return;
        }
        let mut new_env: Vec<CString> = env
            .iter()
            .filter(|e| !e.starts_with(b"GLIBC_TUNABLES="))
            .map(|e| CString::new(e.as_slice()).expect("an environment string has no NUL"))
            .collect();
        let tunables = with_the_settings(tunables.as_deref().unwrap_or(""));
        new_env.push(CString::new(format!("GLIBC_TUNABLES={tunables}")).expect("no NUL"));
        new_env.push(CString::new(format!("{ZED_METER_STARTED_AGAIN}=1")).expect("no NUL"));
        let mut ptrs: Vec<*const c_char> = new_env.iter().map(|c| c.as_ptr()).collect();
        ptrs.push(std::ptr::null());
        // SAFETY: `argv` is the program's own null-ended vector, and `ptrs` is null-ended and
        // points into `new_env`, which lives across the call. execve returns only on failure;
        // the process then goes on without the settings, and `in_effect` says so.
        unsafe { libc::execve(c"/proc/self/exe".as_ptr(), argv, ptrs.as_ptr()) };
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_settings_are_held_only_when_each_is_the_last_of_its_name() {
        assert!(holds_the_settings(GLIBC_TUNABLES));
        assert!(holds_the_settings(&format!(
            "glibc.malloc.check=3:{GLIBC_TUNABLES}"
        )));
        assert!(!holds_the_settings(""));
        assert!(!holds_the_settings("glibc.malloc.tcache_count=0"));
        assert!(!holds_the_settings(&format!(
            "{GLIBC_TUNABLES}:glibc.malloc.tcache_count=7"
        )));
    }

    #[test]
    fn adding_the_settings_keeps_other_items_and_replaces_those_of_the_same_names() {
        assert_eq!(with_the_settings(""), GLIBC_TUNABLES);
        let added = with_the_settings("glibc.malloc.tcache_count=7:glibc.malloc.check=3");
        assert_eq!(added, format!("glibc.malloc.check=3:{GLIBC_TUNABLES}"));
        assert!(holds_the_settings(&added));
    }

    /// Run with or without `GLIBC_TUNABLES`, this binary has started itself again with the
    /// settings by the time a test runs, and the variable that marks the start again is gone.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn a_binary_started_without_the_settings_runs_with_them() {
        assert!(in_effect());
        let tunables = std::env::var("GLIBC_TUNABLES").unwrap_or_default();
        assert!(holds_the_settings(&tunables), "{tunables:?}");
        assert!(std::env::var_os(ZED_METER_STARTED_AGAIN).is_none());
    }
}
