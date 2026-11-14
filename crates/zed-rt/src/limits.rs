//! The limits `main` sets on its own run (DESIGN.md sec:ports, "`main` may limit its own
//! run"), enforced in the program's own process: `zedc run` sets them once the program is
//! compiled, and an executable at its start. The checker read them ([`MainLimits`]); here they
//! become the operating system's limits and the handlers that stop the run with a message and
//! exit status 3 when one is passed.
//!
//! - `memory: b`: the soft `RLIMIT_DATA` is set to `b` more than the process held before the
//!   run (the compiler's data for `zedc run`; the decoded program and the runtime for an
//!   executable), its hard limit left as inherited. An allocation past it is refused: the kernel's numbers ask the system
//!   first and stop with "Memory limit of `main` passed" ([`zed_kernel::value::under_memory_limit`]);
//!   an allocation that Rust's allocator reports by aborting the process stops at the abort
//!   (`on_abort`); and the run's stack, reserved without access and made writable as it grows
//!   (`crate::stack`), stops when the kernel refuses a part of it.
//! - `cpu: d`: the soft `RLIMIT_CPU` is `d` rounded up to whole seconds, its unit, and the hard
//!   limit that plus the grace period of `@kill`, at least a second more, so that the kernel's
//!   `SIGXCPU` at the soft limit reaches the handler (`on_cpu`) before its `SIGKILL` at the
//!   hard one (getrlimit(2)).
//! - `@timeout(d)`: a thread sleeps until `d` after the process started, on `CLOCK_BOOTTIME`,
//!   which counts time suspended, and then stops the run.
//!
//! Departures from DESIGN.md, each with a plan row: the runtime keeps no count of its own
//! allocations, so a stop names the operating system's count only, and the site of the
//! allocation only where the kernel's error carries one (MAIN-limits-count); the messages for
//! processor time and the deadline give the limit and the time used, not the limit's site or
//! the statement each thread was running (MAIN-limits-site); and a stop runs no releases
//! (STOP-releases-rt).

use std::ffi::c_int;
use std::fmt::Write as _;
use std::io;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Duration;

use zed_kernel::limits::{MainLimits, data_bytes, duration_text, set_memory};

/// The exit status of a run stopped by a fault (DESIGN.md sec:ports).
pub const FAULT: c_int = 3;

/// Sets the limits `limits` on this process. Called once, by the process that
/// runs the program, before the run starts: a limit holds for every thread of the process, so
/// a test harness never calls it. An error, a fault of the system, when the system refuses a
/// limit or a handler.
pub fn enforce(limits: &MainLimits) -> Result<(), String> {
    if let Some(d) = limits.cpu {
        cpu(d, limits.kill.grace())?;
    }
    // The thread is started before the memory limit is set, since its stack counts against it.
    if let Some(d) = limits.timeout {
        deadline(d)?;
    }
    if let Some(b) = limits.memory {
        memory(b)?;
    }
    Ok(())
}

/// Writes `bytes` to standard error and ends the process at once with [`FAULT`]: what a
/// handler does, with no allocation, no lock and no unwinding, all of which may be held by the
/// code the signal stopped.
pub(crate) fn fault_exit(bytes: &[u8]) -> ! {
    #[expect(unsafe_code, reason = "write and _exit are libc calls")]
    // SAFETY: `write` reads `bytes`, which is borrowed for the call; `write` and `_exit` are
    // async-signal-safe (signal-safety(7)).
    unsafe {
        let mut rest = bytes;
        while !rest.is_empty() {
            let n = libc::write(libc::STDERR_FILENO, rest.as_ptr().cast(), rest.len());
            if n <= 0 {
                break;
            }
            rest = &rest[n.unsigned_abs()..];
        }
        libc::_exit(FAULT)
    }
}

/// A message built in a fixed buffer, for a handler that may not allocate; text past its end
/// is dropped.
pub(crate) struct Line {
    bytes: [u8; 512],
    len: usize,
}

impl Line {
    /// An empty line.
    pub(crate) const fn new() -> Line {
        Line {
            bytes: [0; 512],
            len: 0,
        }
    }

    /// The bytes written.
    pub(crate) fn bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl std::fmt::Write for Line {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        let n = s.len().min(self.bytes.len() - self.len);
        self.bytes[self.len..self.len + n].copy_from_slice(&s.as_bytes()[..n]);
        self.len += n;
        Ok(())
    }
}

/// Writes `n` bytes to `out` as a message gives a size: `8388608 B (8 MiB)`, the binary unit
/// the largest with a whole part of at least 1 and one decimal where it is not whole; `512 B`
/// below 1 KiB. No allocation, for a handler.
pub(crate) fn write_bytes(out: &mut Line, n: u64) {
    const UNITS: [&str; 6] = ["KiB", "MiB", "GiB", "TiB", "PiB", "EiB"];
    let _ = write!(out, "{n} B");
    let Some(k) = (0..UNITS.len()).rev().find(|&k| n >> (10 * (k + 1)) > 0) else {
        return;
    };
    let shift = 10 * (k as u32 + 1);
    let (whole, part) = (n >> shift, n & ((1u64 << shift) - 1));
    // The tenths, rounded down, so that a size is never written above what it is.
    let tenths = ((u128::from(part) * 10) >> shift) as u64;
    let _ = match tenths {
        0 => write!(out, " ({whole} {})", UNITS[k]),
        t => write!(out, " ({whole}.{t} {})", UNITS[k]),
    };
}

/// The processor-time limit, as its message's first words write it; the process's processor
/// time when the run started, in nanoseconds; and whether the limit has stopped the run. Set
/// by [`cpu`].
static CPU_LIMIT: OnceLock<String> = OnceLock::new();
static CPU_START: AtomicU64 = AtomicU64::new(0);
static CPU_PASSED: AtomicBool = AtomicBool::new(false);

/// The processor time of all the process's threads together; zero where the clock cannot be
/// read. Async-signal-safe.
pub(crate) fn cpu_now() -> Duration {
    let mut t = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    #[expect(unsafe_code, reason = "clock_gettime is a libc call")]
    // SAFETY: `t` is a timespec owned here; clock_gettime is async-signal-safe.
    let read = unsafe { libc::clock_gettime(libc::CLOCK_PROCESS_CPUTIME_ID, &mut t) };
    match read {
        0 => Duration::new(t.tv_sec.unsigned_abs(), t.tv_nsec as u32),
        _ => Duration::ZERO,
    }
}

/// Limits the run's processor time to `d` from now: a timer on the process's processor-time
/// clock sends `SIGXCPU` when the run has used `d` (timer_create(2)), and `RLIMIT_CPU` stops the
/// process if that fails: its soft limit is the time used so far plus `d`, rounded up to whole
/// seconds, its unit, and its hard one that plus `grace`, at least a second more, so that the
/// kernel's `SIGXCPU` at the soft limit reaches the handler ([`on_cpu`]) before its `SIGKILL` at
/// the hard one (getrlimit(2)).
// Complexity tradeoff: `RLIMIT_CPU` alone counts whole seconds from the process's start, so a
// limit of 0.5 s stopped a run at 1 s, and `zedc run` would charge the run for its compiling;
// the timer adds one kernel timer and fires at `d` of the run's own time, O(1).
fn cpu(d: Duration, grace: Duration) -> Result<(), String> {
    let now = cpu_now();
    CPU_START.store(
        u64::try_from(now.as_nanos()).unwrap_or(u64::MAX),
        Ordering::Relaxed,
    );
    let whole = |t: Duration| t.as_secs() + u64::from(t.subsec_nanos() > 0);
    let soft = whole(now + d);
    let hard = whole(now + d + grace).max(soft + 1);
    let _ = CPU_LIMIT.set(format!(
        "Processor-time limit of `main` passed: {}.",
        duration_text(d)
    ));
    install(libc::SIGXCPU, on_cpu)?;
    set_limit(libc::RLIMIT_CPU, soft, Some(hard), "processor time")?;
    #[expect(unsafe_code, reason = "timer_create and timer_settime are libc calls")]
    // SAFETY: the event and the times are owned here and read by the calls; the timer is the
    // process's for its life, never deleted.
    unsafe {
        let mut event: libc::sigevent = std::mem::zeroed();
        event.sigev_notify = libc::SIGEV_SIGNAL;
        event.sigev_signo = libc::SIGXCPU;
        let mut timer: libc::timer_t = std::ptr::null_mut();
        if libc::timer_create(libc::CLOCK_PROCESS_CPUTIME_ID, &mut event, &mut timer) != 0 {
            return Err(system(
                "start a timer on its processor time",
                &io::Error::last_os_error(),
            ));
        }
        let at = libc::itimerspec {
            it_interval: libc::timespec {
                tv_sec: 0,
                tv_nsec: 0,
            },
            it_value: libc::timespec {
                tv_sec: libc::time_t::try_from(d.as_secs()).unwrap_or(libc::time_t::MAX),
                tv_nsec: d.subsec_nanos().into(),
            },
        };
        if libc::timer_settime(timer, 0, &at, std::ptr::null_mut()) != 0 {
            return Err(system(
                "start a timer on its processor time",
                &io::Error::last_os_error(),
            ));
        }
    }
    Ok(())
}

/// The handler of `SIGXCPU`: the first stops the run with the limit and the processor time the
/// run used; the kernel's repeats, one a second, are ignored (DESIGN.md sec:ffi).
extern "C" fn on_cpu(_: c_int, _: *mut libc::siginfo_t, _: *mut libc::c_void) {
    if CPU_PASSED.swap(true, Ordering::SeqCst) {
        return;
    }
    let mut line = Line::new();
    let _ = line.write_str(
        CPU_LIMIT
            .get()
            .map_or("Processor-time limit of `main` passed.", |s| s),
    );
    let used = cpu_now().saturating_sub(Duration::from_nanos(CPU_START.load(Ordering::Relaxed)));
    let _ = writeln!(
        line,
        " The run used {}.{:02} s of processor time.",
        used.as_secs(),
        used.subsec_millis() / 10
    );
    fault_exit(line.bytes())
}

/// Starts the thread that stops the run `d` after the process started.
fn deadline(d: Duration) -> Result<(), String> {
    let message = format!("Deadline of `main` passed: {}.\n", duration_text(d));
    let at = started().map_or_else(boot_now, Ok)? + d;
    std::thread::Builder::new()
        .name("deadline of main".into())
        // Enough for the sleep and the write; it counts against the memory limit, set after.
        .stack_size(64 << 10)
        .spawn(move || {
            sleep_until(at);
            fault_exit(message.as_bytes())
        })
        .map(drop)
        .map_err(|e| system("start the thread of the deadline", &e))
}

/// When the process started, on `CLOCK_BOOTTIME`: field 22 of `/proc/self/stat`, in clock
/// ticks since boot (proc_pid_stat(5)); `None` where it cannot be read.
fn started() -> Option<Duration> {
    let stat = std::fs::read_to_string("/proc/self/stat").ok()?;
    // The command name, field 2, is in parentheses and may hold spaces; field 3 follows them.
    let after = stat.rsplit_once(')')?.1;
    let ticks: u64 = after.split_whitespace().nth(22 - 3)?.parse().ok()?;
    #[expect(unsafe_code, reason = "sysconf is a libc call")]
    // SAFETY: sysconf only reads.
    let hz = u64::try_from(unsafe { libc::sysconf(libc::_SC_CLK_TCK) }).ok()?;
    (hz > 0).then(|| Duration::from_secs(ticks / hz) + Duration::from_secs(ticks % hz) / hz as u32)
}

/// Now, on `CLOCK_BOOTTIME`.
fn boot_now() -> Result<Duration, String> {
    let mut now = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    #[expect(unsafe_code, reason = "clock_gettime is a libc call")]
    // SAFETY: `now` is a timespec owned here.
    if unsafe { libc::clock_gettime(libc::CLOCK_BOOTTIME, &mut now) } != 0 {
        return Err(system(
            "read the time since boot",
            &io::Error::last_os_error(),
        ));
    }
    Ok(Duration::new(now.tv_sec.unsigned_abs(), now.tv_nsec as u32))
}

/// Sleeps until `at` on `CLOCK_BOOTTIME`, an absolute time, so that a wake by a signal sleeps
/// again only for what is left.
fn sleep_until(at: Duration) {
    let ts = libc::timespec {
        tv_sec: libc::time_t::try_from(at.as_secs()).unwrap_or(libc::time_t::MAX),
        tv_nsec: at.subsec_nanos().into(),
    };
    #[expect(unsafe_code, reason = "clock_nanosleep is a libc call")]
    // SAFETY: `ts` is a timespec owned here; the remainder is not asked for.
    while unsafe {
        libc::clock_nanosleep(
            libc::CLOCK_BOOTTIME,
            libc::TIMER_ABSTIME,
            &ts,
            std::ptr::null_mut(),
        )
    } == libc::EINTR
    {}
}

/// The memory limit in bytes, for the handlers' messages; 0 where none is set.
static MEMORY_LIMIT: AtomicU64 = AtomicU64::new(0);

/// The memory limit in force, for the stack's growth (`crate::stack`).
pub(crate) fn memory_limit() -> Option<u64> {
    Some(MEMORY_LIMIT.load(Ordering::Relaxed)).filter(|&b| b > 0)
}

/// Sets the soft `RLIMIT_DATA` to `b` more than the process holds now and catches the abort
/// of an allocation it refuses.
fn memory(b: u64) -> Result<(), String> {
    let base = data_bytes().ok_or_else(|| {
        system(
            "read how much data the process holds",
            &io::Error::from(io::ErrorKind::NotFound),
        )
    })?;
    install(libc::SIGABRT, on_abort)?;
    MEMORY_LIMIT.store(b, Ordering::Relaxed);
    set_memory(b, base);
    set_limit(libc::RLIMIT_DATA, base.saturating_add(b), None, "memory")
}

/// The handler of `SIGABRT` under a memory limit: Rust's allocator aborts the process when the
/// system refuses an allocation it cannot report otherwise, after writing `memory allocation
/// of n bytes failed`, so under the limit an abort is that refusal (the runtime's own code
/// unwinds a panic and never aborts).
extern "C" fn on_abort(_: c_int, _: *mut libc::siginfo_t, _: *mut libc::c_void) {
    let mut line = Line::new();
    let _ = line.write_str(
        "Memory limit of `main` passed: the system refused an allocation of the run, which may \
         hold ",
    );
    write_bytes(&mut line, MEMORY_LIMIT.load(Ordering::Relaxed));
    let _ = line.write_str(".\n");
    fault_exit(line.bytes())
}

/// Sets the soft limit `soft` on `resource`, and the hard limit `hard`, or leaves the hard one
/// as inherited; a soft limit above an inherited hard one is lowered to it, the most the
/// process may set.
fn set_limit(
    resource: libc::__rlimit_resource_t,
    soft: u64,
    hard: Option<u64>,
    what: &str,
) -> Result<(), String> {
    let mut r = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    #[expect(unsafe_code, reason = "getrlimit and setrlimit are libc calls")]
    // SAFETY: `r` is an rlimit owned here, which getrlimit fills and setrlimit reads.
    unsafe {
        if libc::getrlimit(resource, &mut r) != 0 {
            return Err(system(
                &format!("read its limit on {what}"),
                &io::Error::last_os_error(),
            ));
        }
        let max = hard.map_or(r.rlim_max, |h| h.min(r.rlim_max));
        r.rlim_cur = soft.min(max);
        r.rlim_max = max;
        if libc::setrlimit(resource, &r) != 0 {
            return Err(system(
                &format!("set its limit on {what}"),
                &io::Error::last_os_error(),
            ));
        }
    }
    Ok(())
}

/// Installs `handler` for `signal`, on the thread's alternate signal stack where it has one.
pub(crate) fn install(
    signal: c_int,
    handler: extern "C" fn(c_int, *mut libc::siginfo_t, *mut libc::c_void),
) -> Result<(), String> {
    #[expect(unsafe_code, reason = "sigaction is a libc call")]
    // SAFETY: the action is zeroed and filled here; the handler is a function of the right
    // type for SA_SIGINFO, which writes and exits or returns.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = handler as usize;
        action.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
        libc::sigemptyset(&mut action.sa_mask);
        if libc::sigaction(signal, &action, std::ptr::null_mut()) != 0 {
            return Err(system(
                "catch a signal of its limits",
                &io::Error::last_os_error(),
            ));
        }
    }
    Ok(())
}

/// The message for a limit the system refused to set: the run did not start.
fn system(what: &str, e: &io::Error) -> String {
    format!(
        "the program could not start: it limits its own run, written before `main`, and the \
         system refused to {what} ({e}). Repair: run the program again; if it fails the same \
         way, remove the limit before `main`"
    )
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    #[test]
    fn a_size_is_written_with_its_binary_unit() {
        let text = |n| {
            let mut l = Line::new();
            write_bytes(&mut l, n);
            String::from_utf8(l.bytes().to_vec()).unwrap()
        };
        assert_eq!(text(512), "512 B");
        assert_eq!(text(8 << 20), "8388608 B (8 MiB)");
        assert_eq!(text(1536), "1536 B (1.5 KiB)");
        assert_eq!(text(u64::MAX), "18446744073709551615 B (15.9 EiB)");
    }

    #[test]
    fn a_line_drops_what_passes_its_end() {
        let mut l = Line::new();
        for _ in 0..100 {
            let _ = l.write_str("0123456789");
        }
        assert_eq!(l.bytes().len(), 512);
    }

    #[test]
    fn the_process_start_is_before_now() {
        let (start, now) = (started().unwrap(), boot_now().unwrap());
        assert!(start <= now, "{start:?} > {now:?}");
    }
    /// Runs `body`, which sets limits on its process, in a child process of this test binary
    /// that runs the test `test` alone: a limit holds for every thread of a process, so the
    /// test harness's own process never sets one. In the child, `body` runs and the result is
    /// `None`; in the parent, the child's output.
    pub(crate) fn in_child(test: &str, body: impl FnOnce()) -> Option<std::process::Output> {
        const CHILD: &str = "ZED_RT_LIMITS_CHILD";
        if std::env::var(CHILD).as_deref() == Ok(test) {
            body();
            return None;
        }
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", test, "--test-threads=1", "--nocapture"])
            .env(CHILD, test)
            .output()
            .unwrap();
        Some(out)
    }

    /// The child's exit status and standard error.
    pub(crate) fn status(out: &std::process::Output) -> (Option<i32>, String) {
        (
            out.status.code(),
            String::from_utf8_lossy(&out.stderr).into_owned(),
        )
    }

    /// Spins for `d` of processor time.
    fn spin(d: Duration) {
        let start = cpu_now();
        while cpu_now() - start < d {
            std::hint::black_box(0);
        }
    }

    #[test]
    fn processor_time_past_the_limit_stops_the_run_with_status_3() {
        let Some(out) = in_child(
            "limits::tests::processor_time_past_the_limit_stops_the_run_with_status_3",
            || {
                let limits = MainLimits {
                    cpu: Some(Duration::from_millis(200)),
                    ..MainLimits::default()
                };
                enforce(&limits).unwrap();
                spin(Duration::from_secs(5));
            },
        ) else {
            return;
        };
        let (code, err) = status(&out);
        assert_eq!(code, Some(3), "{err}");
        assert!(
            err.starts_with("Processor-time limit of `main` passed: 0.2 s. The run used 0.2"),
            "{err}"
        );
    }

    #[test]
    fn processor_time_within_the_limit_runs_to_the_end() {
        let Some(out) = in_child(
            "limits::tests::processor_time_within_the_limit_runs_to_the_end",
            || {
                let limits = MainLimits {
                    cpu: Some(Duration::from_secs(5)),
                    ..MainLimits::default()
                };
                enforce(&limits).unwrap();
                spin(Duration::from_millis(100));
            },
        ) else {
            return;
        };
        assert_eq!(status(&out).0, Some(0), "{}", status(&out).1);
    }

    #[test]
    fn a_run_past_its_deadline_stops_with_status_3() {
        let Some(out) = in_child(
            "limits::tests::a_run_past_its_deadline_stops_with_status_3",
            || {
                // The deadline counts from the process's start, sleep included: no processor
                // time is used.
                let limits = MainLimits {
                    timeout: Some(Duration::from_millis(500)),
                    ..MainLimits::default()
                };
                enforce(&limits).unwrap();
                std::thread::sleep(Duration::from_secs(10));
            },
        ) else {
            return;
        };
        let (code, err) = status(&out);
        assert_eq!(
            (code, err.as_str()),
            (Some(3), "Deadline of `main` passed: 0.5 s.\n")
        );
    }

    #[test]
    fn a_run_within_its_deadline_runs_to_the_end() {
        let Some(out) = in_child(
            "limits::tests::a_run_within_its_deadline_runs_to_the_end",
            || {
                let limits = MainLimits {
                    timeout: Some(Duration::from_secs(30)),
                    ..MainLimits::default()
                };
                enforce(&limits).unwrap();
                std::thread::sleep(Duration::from_millis(100));
            },
        ) else {
            return;
        };
        assert_eq!(status(&out).0, Some(0), "{}", status(&out).1);
    }

    #[test]
    fn an_allocation_past_the_memory_limit_stops_the_run_with_status_3() {
        let Some(out) = in_child(
            "limits::tests::an_allocation_past_the_memory_limit_stops_the_run_with_status_3",
            || {
                let limits = MainLimits {
                    memory: Some(64 << 20),
                    ..MainLimits::default()
                };
                enforce(&limits).unwrap();
                // Within the limit: the run goes on.
                std::hint::black_box(vec![1u8; 32 << 20]);
                // Past it: Rust's allocator aborts, and the run stops.
                std::hint::black_box(Vec::<u8>::with_capacity(128 << 20));
                unreachable!("an allocation past the limit was given");
            },
        ) else {
            return;
        };
        let (code, err) = status(&out);
        assert_eq!(code, Some(3), "{err}");
        assert!(
            err.contains(
                "Memory limit of `main` passed: the system refused an allocation of the run, \
                 which may hold 67108864 B (64 MiB).\n"
            ),
            "{err}"
        );
    }

    #[test]
    fn which_mappings_the_limit_on_data_counts() {
        // Measured on Linux: under a soft `RLIMIT_DATA` of 256 MiB, a mapping of 512 MiB that
        // the limit counts is refused, and one it does not count is given. The runtime relies
        // on each row (the module's documentation and `crate::stack`).
        let Some(out) = in_child(
            "limits::tests::which_mappings_the_limit_on_data_counts",
            || {
                const LIMIT: u64 = 256 << 20;
                const SIZE: usize = 512 << 20;
                assert!(
                    data_bytes().unwrap() < LIMIT / 2,
                    "the test binary holds too much"
                );
                #[expect(unsafe_code, reason = "the mappings are libc calls")]
                // SAFETY: each mapping is new, never touched, and unmapped before the next.
                unsafe {
                    let dir =
                        std::ffi::CString::new(std::env::temp_dir().as_os_str().as_encoded_bytes())
                            .unwrap();
                    // A file with no name, removed when closed, of 512 MiB that holds no block.
                    let fd = libc::open(dir.as_ptr(), libc::O_TMPFILE | libc::O_RDWR, 0o600);
                    assert!(fd >= 0, "{}", io::Error::last_os_error());
                    assert_eq!(libc::ftruncate(fd, SIZE as libc::off_t), 0);
                    set_limit(libc::RLIMIT_DATA, LIMIT, None, "memory").unwrap();
                    let map = |prot, flags, fd| {
                        let p = libc::mmap(std::ptr::null_mut(), SIZE, prot, flags, fd, 0);
                        let given = p != libc::MAP_FAILED;
                        if given {
                            libc::munmap(p, SIZE);
                        }
                        given
                    };
                    let (rw, private, anon) = (
                        libc::PROT_READ | libc::PROT_WRITE,
                        libc::MAP_PRIVATE,
                        libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                    );
                    let shared = libc::MAP_SHARED;
                    // Counted.
                    assert!(!map(rw, anon, -1), "a private writable mapping");
                    assert!(!map(rw, anon | libc::MAP_NORESERVE, -1), "MAP_NORESERVE");
                    assert!(!map(rw, private, fd), "a private writable file mapping");
                    assert!(
                        std::thread::Builder::new()
                            .stack_size(SIZE)
                            .spawn(|| ())
                            .is_err(),
                        "a thread's stack"
                    );
                    let p = libc::mmap(std::ptr::null_mut(), SIZE, libc::PROT_NONE, anon, -1, 0);
                    assert_ne!(p, libc::MAP_FAILED, "a reservation with no access");
                    assert_ne!(libc::mprotect(p, SIZE, rw), 0, "mprotect of a reservation");
                    // A part within the limit is given, as the stack grows.
                    assert_eq!(libc::mprotect(p, 1 << 20, rw), 0, "mprotect of a part");
                    libc::munmap(p, SIZE);
                    // Not counted.
                    assert!(
                        map(libc::PROT_READ, private, fd),
                        "a read-only file mapping"
                    );
                    assert!(
                        map(rw, shared | libc::MAP_ANONYMOUS, -1),
                        "a shared mapping"
                    );
                    assert!(map(rw, shared, fd), "a shared file mapping");
                    assert!(
                        map(libc::PROT_NONE, anon, -1),
                        "a reservation with no access"
                    );
                    libc::close(fd);
                }
                // The first thread's stack: the operating system's count of data, `VmData`, is the
                // sum of the private writable mappings other than `[stack]`, the first thread's.
                let maps = std::fs::read_to_string("/proc/self/maps").unwrap();
                let (mut counted, mut stack) = (0, 0);
                for line in maps.lines() {
                    let mut words = line.split_whitespace();
                    let (range, perms) = (words.next().unwrap(), words.next().unwrap());
                    let (lo, hi) = range.split_once('-').unwrap();
                    let size =
                        u64::from_str_radix(hi, 16).unwrap() - u64::from_str_radix(lo, 16).unwrap();
                    if perms.as_bytes()[1] == b'w' && perms.as_bytes()[3] == b'p' {
                        match line.ends_with("[stack]") {
                            true => stack += size,
                            false => counted += size,
                        }
                    }
                }
                assert!(stack > 0, "no stack of the first thread in {maps}");
                assert_eq!(data_bytes().unwrap(), counted, "{maps}");
            },
        ) else {
            return;
        };
        assert_eq!(
            status(&out).0,
            Some(0),
            "{}",
            String::from_utf8_lossy(&out.stdout)
        );
    }
}
