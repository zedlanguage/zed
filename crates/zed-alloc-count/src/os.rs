//! The counters of work that macOS and Windows give a process, which `zed_tests::scaling` reads
//! where Linux's `perf_event_open` does not exist. Each counts the whole process, every thread of
//! it, and not a thread and the threads it starts as `perf_event_open` does, so the scaling tests
//! read them one test at a time. These calls are compiled on Linux by `cargo check --target`
//! for x86_64-apple-darwin, aarch64-apple-darwin and x86_64-pc-windows-msvc; they have not been
//! run.
//!
//! macOS: `proc_pid_rusage(getpid(), RUSAGE_INFO_V4, ...)` fills a `struct rusage_info_v4`,
//! whose `ri_instructions` and `ri_cycles` are the instructions retired and the cycles of the
//! process (libproc.h: "Return resource usage information for the given pid, which can be a live
//! process or a zombie. Returns 0 on success; or -1 on failure, with errno set"; available from
//! macOS 10.9; the flavors and the struct are in sys/resource.h, xnu
//! bsd/sys/resource.h and libsyscall/wrappers/libproc/libproc.h). A machine whose counters the
//! kernel does not read leaves `ri_instructions` at 0; the scaling tests then read `ri_cycles`.
//!
//! Windows: `QueryProcessCycleTime(GetCurrentProcess(), &cycles)` gives "the number of CPU clock
//! cycles used by the threads of the process", in user and kernel mode, and returns nonzero on
//! success (Microsoft Learn, "QueryProcessCycleTime function (realtimeapiset.h)"; Windows Vista
//! and later; the handle needs PROCESS_QUERY_INFORMATION or PROCESS_QUERY_LIMITED_INFORMATION,
//! which the pseudo handle of `GetCurrentProcess` has). `GetThreadTimes(GetCurrentThread(), ...)`
//! gives the kernel-mode and user-mode time of this thread in units of 100 ns (Microsoft Learn,
//! "GetThreadTimes function (processthreadsapi.h)").

#[cfg(windows)]
use std::time::Duration;

/// The instructions the process has retired, user and kernel mode; 0 where the kernel does not
/// read the hardware counter.
#[cfg(target_os = "macos")]
pub fn process_instructions() -> u64 {
    rusage().ri_instructions
}

/// The cycles of the process, user and kernel mode; 0 where the kernel does not read them.
#[cfg(target_os = "macos")]
pub fn process_cycles() -> u64 {
    rusage().ri_cycles
}

/// The process's `rusage_info_v4`.
#[cfg(target_os = "macos")]
fn rusage() -> libc::rusage_info_v4 {
    let mut info = std::mem::MaybeUninit::<libc::rusage_info_v4>::zeroed();
    #[expect(unsafe_code, reason = "a call of the C library")]
    // SAFETY: `info` is a writable `rusage_info_v4`, the struct the flavor RUSAGE_INFO_V4 asks
    // the call to fill; the C declaration types the buffer as `rusage_info_t *` and its callers
    // pass the address of the struct, as this does.
    let failed = unsafe {
        libc::proc_pid_rusage(
            libc::getpid(),
            libc::RUSAGE_INFO_V4,
            info.as_mut_ptr().cast::<libc::rusage_info_t>(),
        )
    };
    assert!(
        failed == 0,
        "proc_pid_rusage(getpid(), RUSAGE_INFO_V4) failed: {}",
        std::io::Error::last_os_error()
    );
    #[expect(unsafe_code, reason = "reading the struct the call filled")]
    // SAFETY: the struct is of integers only, zeroed before the call, so every bit pattern in it
    // is a valid value; the call succeeded and filled it.
    unsafe {
        info.assume_init()
    }
}

/// The cycles of the process, user and kernel mode.
#[cfg(windows)]
pub fn process_cycles() -> u64 {
    use windows_sys::Win32::System::Threading::GetCurrentProcess;
    use windows_sys::Win32::System::WindowsProgramming::QueryProcessCycleTime;
    let mut cycles = 0u64;
    #[expect(unsafe_code, reason = "a call of the Windows API")]
    // SAFETY: `GetCurrentProcess` returns the pseudo handle of this process, which has every
    // access right; `cycles` is a writable u64 for the count.
    let ok = unsafe { QueryProcessCycleTime(GetCurrentProcess(), &mut cycles) };
    assert!(
        ok != 0,
        "QueryProcessCycleTime(GetCurrentProcess()) failed: {}",
        std::io::Error::last_os_error()
    );
    cycles
}

/// The processor time this thread has used, in kernel and user mode.
#[cfg(windows)]
pub fn thread_cpu_time() -> Duration {
    use windows_sys::Win32::Foundation::FILETIME;
    use windows_sys::Win32::System::Threading::{GetCurrentThread, GetThreadTimes};
    let zero = FILETIME {
        dwLowDateTime: 0,
        dwHighDateTime: 0,
    };
    let (mut created, mut exited, mut kernel, mut user) = (zero, zero, zero, zero);
    #[expect(unsafe_code, reason = "a call of the Windows API")]
    // SAFETY: `GetCurrentThread` returns the pseudo handle of this thread, which has every access
    // right; the four FILETIMEs are writable.
    let ok = unsafe {
        GetThreadTimes(
            GetCurrentThread(),
            &mut created,
            &mut exited,
            &mut kernel,
            &mut user,
        )
    };
    assert!(
        ok != 0,
        "GetThreadTimes(GetCurrentThread()) failed: {}",
        std::io::Error::last_os_error()
    );
    let hundreds = |t: FILETIME| (u64::from(t.dwHighDateTime) << 32) | u64::from(t.dwLowDateTime);
    Duration::from_nanos((hundreds(kernel) + hundreds(user)) * 100)
}
