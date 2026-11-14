//! The stack native code runs on (COMPLEXITY.md R10). Generated code calls itself on the machine
//! stack for each Zed call and keeps a function's words in its frame, so a run needs stack in
//! proportion to its depth of calls and the size of its functions, more than any fixed thread
//! stack holds. A run therefore switches, once, to a stack mapped for it as large as the machine's
//! memory and swap together. Its pages are reserved, not committed: a page takes memory only once
//! the run touches it, as on any stack, and all of them are returned when the run ends. Since
//! touched stack pages are real memory, a program the reservation is too small for is one the
//! machine cannot run in any case, so the reservation adds no limit on depth of its own; depth is
//! limited by memory, as the heap is.
//!
//! A page that cannot be read or written lies below the stack. Cranelift's inline stack probes
//! (set in `zed-native`) touch each page of a large frame in turn, so a run that does exhaust
//! memory stops at that page instead of writing past it.
//!
//! Under a memory limit of `main` (DESIGN.md sec:ports, [`crate::limits`]) a reservation that
//! may be written counts in full against the limit (`RLIMIT_DATA` counts every private writable
//! mapping, reserved or not), so there the stack is reserved with no access, which the limit
//! does not count, and made writable from the top down as the run reaches it: a fault below the
//! writable part is caught on a stack of its own (`sigaltstack`), and the part from the fault to
//! the writable part, rounded to `GROW`, is made writable with `mprotect`, which counts it.
//! When the system refuses that, or the fault is in the guard page below a stack as large as the
//! limit, the run stops with "Memory limit of `main` passed" and exit status 3.

use std::io;
use std::panic::{self, AssertUnwindSafe};
use std::ptr;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use std::sync::{Once, OnceLock};

use crate::limits::{Line, fault_exit, install, memory_limit, write_bytes};

/// A stack mapped for one run, with the guard page below it; unmapped when dropped.
#[derive(Debug)]
pub struct Stack {
    /// The low end of the mapping: the guard page, then the stack.
    base: *mut libc::c_void,
    /// The bytes mapped, the guard page included.
    len: usize,
    /// The bytes of the guard page.
    page: usize,
    /// Under a memory limit: the stack's record for the handler of faults, which makes it
    /// writable as it grows, and the stack that handler runs on.
    grows: Option<(&'static Grows, Alt)>,
}

impl Stack {
    /// Maps a stack as large as the machine's memory and swap together, reserved and not
    /// committed, with a guard page below it.
    /// Under a memory limit of `main`, the stack is as large as the limit at most, reserved
    /// with no access and made writable as the run reaches it (the module's documentation).
    pub fn new() -> Result<Stack, String> {
        if let Some(limit) = memory_limit() {
            return Stack::limited(limit);
        }
        #[expect(
            unsafe_code,
            reason = "the page size, the memory size and the mapping come from libc calls"
        )]
        // SAFETY: `sysconf` and `sysinfo` only read; `sysinfo` writes the struct it is given,
        // which is zeroed and owned here. The mapping is new and anonymous, so it overlaps no
        // memory in use; `mprotect` covers its first page only, which nothing else refers to.
        unsafe {
            let page = usize::try_from(libc::sysconf(libc::_SC_PAGESIZE))
                .map_err(|_| unable("the system did not report its memory page size"))?;
            let mut info: libc::sysinfo = std::mem::zeroed();
            if libc::sysinfo(&mut info) != 0 {
                return Err(unable(&format!(
                    "the system did not report how much memory and swap the machine has ({})",
                    io::Error::last_os_error()
                )));
            }
            let unit = u64::from(info.mem_unit);
            let bytes = (info.totalram + info.totalswap) * unit;
            let bytes = usize::try_from(bytes).map_err(|_| {
                unable("the machine's memory and swap together are more than a program can address")
            })?;
            let len = bytes.div_ceil(page) * page + page;
            let base = libc::mmap(
                ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_STACK,
                -1,
                0,
            );
            // Complexity tradeoff: a process whose address space is limited below memory and swap
            // together (`ulimit -v`, `RLIMIT_AS`) cannot reserve this stack, and every native run
            // in it is refused with the error below, even one that a smaller stack would hold.
            // Why: no size short of memory holds every run, and retrying smaller would make the
            // size a switch, which changes which programs run with the limit. Trigger: the
            // limit on the address space, not the program. Test: the unit test
            // `tests::a_limited_address_space_refuses_the_reservation`; COMPLEXITY.md row R10. A
            // complete solution is a stack that grows by segments: generated code compares the
            // stack pointer with the segment's end at each function entry and, when a frame would
            // not fit, calls the runtime to map a new segment and continue on it, so only the
            // stack in use is reserved, at the cost of a compare and branch per call.
            if base == libc::MAP_FAILED {
                return Err(reserve(len - page, &io::Error::last_os_error()));
            }
            let s = Stack {
                base,
                len,
                page,
                grows: None,
            };
            if libc::mprotect(base, page, libc::PROT_NONE) != 0 {
                return Err(unable(&format!(
                    "the system refused to make the page below that stack unreadable, the page \
                     that stops a run which uses all of it ({})",
                    io::Error::last_os_error()
                )));
            }
            Ok(s)
        }
    }

    /// The bytes of the stack, the guard page not included.
    pub fn len(&self) -> usize {
        self.len - self.page
    }

    /// Whether the stack has no bytes; never, since it holds at least a page.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Runs `f` on this stack and gives its result. A panic in `f` is carried back and resumed
    /// on the caller's stack. Under a memory limit, the thread's faults are handled on the
    /// stack's own alternate stack for the call, since a fault in the part of the stack not yet
    /// writable cannot be handled on that stack, and the thread's alternate stack before it is
    /// restored after.
    pub fn run<R>(&self, f: impl FnOnce() -> R) -> R {
        let before = self.grows.as_ref().map(|(_, alt)| {
            #[expect(unsafe_code, reason = "sigaltstack is a libc call")]
            // SAFETY: `alt` is a writable mapping of `ALT` bytes that outlives the call, since
            // `self` is borrowed for it; the one before is read into a struct owned here.
            unsafe {
                let mut before: libc::stack_t = std::mem::zeroed();
                let new = libc::stack_t {
                    ss_sp: alt.0,
                    ss_flags: 0,
                    ss_size: ALT,
                };
                libc::sigaltstack(&new, &mut before);
                before
            }
        });
        let caught = {
            #[expect(unsafe_code, reason = "switching stacks is an unsafe call")]
            // SAFETY: the stack is the mapping above the guard page: page-aligned, of a size that
            // is a multiple of the page size, mapped for reading and writing, and used by no other
            // code; it outlives the call, since `self` is borrowed for it. `f` cannot unwind out of
            // the callback, since `catch_unwind` stops it there.
            unsafe {
                psm::on_stack(self.base.cast::<u8>().add(self.page), self.len(), || {
                    panic::catch_unwind(AssertUnwindSafe(f))
                })
            }
        };
        if let Some(before) = before {
            #[expect(unsafe_code, reason = "sigaltstack is a libc call")]
            // SAFETY: `before` is the alternate stack the thread had, or none.
            unsafe {
                libc::sigaltstack(&before, ptr::null_mut());
            }
        }
        caught.unwrap_or_else(|p| panic::resume_unwind(p))
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        // The handler of faults no longer reads the stack as one of its own.
        if let Some((grows, _)) = &self.grows {
            grows.high.store(0, Ordering::Relaxed);
        }
        #[expect(unsafe_code, reason = "unmapping is a libc call")]
        // SAFETY: `base` and `len` are the mapping `new` made, unmapped only here, and no code
        // runs on it: `run` has returned, since it borrows `self`.
        unsafe {
            libc::munmap(self.base, self.len);
        }
    }
}

/// The bytes a stack under a memory limit is made writable by at a time, at least: a run that
/// uses `s` bytes of stack takes `s / GROW` faults, each a few microseconds, and holds at most
/// `GROW` bytes it has not reached, counted against the limit.
// Complexity tradeoff: growth by a fixed step makes the faults O(s / GROW) and keeps the count
// against the limit within `GROW` of the stack used; doubling the writable part would take
// O(log s) faults and count up to twice the stack used, which a run near its limit would pass
// for memory it never touched. 256 KiB makes a run with 1 GiB of stack take 4096 faults.
const GROW: usize = 256 << 10;

/// The bytes of the stack the handler of faults runs on, apart from the run's stack.
const ALT: usize = 64 << 10;

/// A stack under a memory limit, as the handler of faults ([`on_fault`]) reads it: the guard
/// page is `[low - page, low)`, the stack `[low, high)`, and `[writable, high)` may be written.
/// Each record is leaked and stays in [`GROWING`] for the process's life, `high` 0 once its stack
/// is unmapped, so the handler reads it with no lock and never a freed record; there is one
/// for each stack made under a limit, one a run.
#[derive(Debug)]
struct Grows {
    low: AtomicUsize,
    high: AtomicUsize,
    writable: AtomicUsize,
    page: usize,
    next: AtomicPtr<Grows>,
}

/// The records of the stacks made under a memory limit, newest first.
static GROWING: AtomicPtr<Grows> = AtomicPtr::new(ptr::null_mut());

/// The action for `SIGSEGV` before [`on_fault`] was installed, which a fault outside every
/// stack under a limit is passed to.
static BEFORE: OnceLock<libc::sigaction> = OnceLock::new();

/// A stack for the handler of faults, mapped writable and unmapped when dropped.
#[derive(Debug)]
struct Alt(*mut libc::c_void);

impl Drop for Alt {
    fn drop(&mut self) {
        #[expect(unsafe_code, reason = "unmapping is a libc call")]
        // SAFETY: the mapping `Stack::limited` made, of `ALT` bytes, no longer the thread's
        // alternate stack: `Stack::run` restored the one before it.
        unsafe {
            libc::munmap(self.0, ALT);
        }
    }
}

impl Stack {
    /// A stack under the memory limit `limit`: as large as the limit, or as memory and swap
    /// together if those are less, reserved with no access, its top [`GROW`] bytes writable,
    /// with a guard page below it and a stack for the handler of faults that makes the rest
    /// writable as the run reaches it.
    fn limited(limit: u64) -> Result<Stack, String> {
        #[expect(
            unsafe_code,
            reason = "the page size, the mappings and the handler's install are libc calls"
        )]
        // SAFETY: as in `Stack::new`; `mprotect` covers the top of the new mapping only, and
        // the record is leaked, so the handler may read it for the process's life.
        unsafe {
            let page = usize::try_from(libc::sysconf(libc::_SC_PAGESIZE))
                .map_err(|_| unable("the system did not report its memory page size"))?;
            let mut info: libc::sysinfo = std::mem::zeroed();
            let machine = match libc::sysinfo(&mut info) {
                0 => (info.totalram + info.totalswap) * u64::from(info.mem_unit),
                _ => u64::MAX,
            };
            let bytes = usize::try_from(limit.min(machine)).unwrap_or(usize::MAX);
            let len = bytes.div_ceil(page).max(1) * page + page;
            let base = libc::mmap(
                ptr::null_mut(),
                len,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
                -1,
                0,
            );
            if base == libc::MAP_FAILED {
                return Err(reserve(len - page, &io::Error::last_os_error()));
            }
            let alt = libc::mmap(
                ptr::null_mut(),
                ALT,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            );
            if alt == libc::MAP_FAILED {
                libc::munmap(base, len);
                return Err(too_small(limit));
            }
            let (low, high) = (base as usize + page, base as usize + len);
            let writable = high - GROW.min(len - page);
            let mut s = Stack {
                base,
                len,
                page,
                grows: None,
            };
            if libc::mprotect(
                writable as *mut libc::c_void,
                high - writable,
                libc::PROT_READ | libc::PROT_WRITE,
            ) != 0
            {
                libc::munmap(alt, ALT);
                return Err(too_small(limit));
            }
            static INSTALL: Once = Once::new();
            let mut installed = Ok(());
            INSTALL.call_once(|| {
                let mut before: libc::sigaction = std::mem::zeroed();
                libc::sigaction(libc::SIGSEGV, ptr::null(), &mut before);
                let _ = BEFORE.set(before);
                installed = install(libc::SIGSEGV, on_fault);
            });
            installed.inspect_err(|_| {
                libc::munmap(alt, ALT);
            })?;
            let grows: &'static Grows = Box::leak(Box::new(Grows {
                low: AtomicUsize::new(low),
                high: AtomicUsize::new(high),
                writable: AtomicUsize::new(writable),
                page,
                next: AtomicPtr::new(ptr::null_mut()),
            }));
            let mut head = GROWING.load(Ordering::Acquire);
            loop {
                grows.next.store(head, Ordering::Relaxed);
                match GROWING.compare_exchange_weak(
                    head,
                    ptr::from_ref(grows).cast_mut(),
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => break,
                    Err(h) => head = h,
                }
            }
            s.grows = Some((grows, Alt(alt)));
            Ok(s)
        }
    }
}

/// The handler of `SIGSEGV`: a fault in a stack under a memory limit, below its writable part,
/// makes the stack writable down to the fault, rounded to [`GROW`], and the run continues; one
/// the system refuses, or one in the guard page below the stack, stops the run (exit status 3).
/// Any other fault is passed to the action before this one, or, with none, ends the process as
/// `SIGSEGV` does. O(stacks under a limit), one a run.
extern "C" fn on_fault(
    signal: libc::c_int,
    info: *mut libc::siginfo_t,
    context: *mut libc::c_void,
) {
    #[expect(
        unsafe_code,
        reason = "the fault's address and the remedies are libc calls"
    )]
    // SAFETY: the kernel passes a valid `info` for a handler installed with SA_SIGINFO; the
    // records are leaked and never freed; `mprotect` covers a part of a stack's own mapping,
    // whose `high` is not 0, so it is still mapped. Each call is async-signal-safe.
    unsafe {
        let at = (*info).si_addr() as usize;
        let mut g = GROWING.load(Ordering::Acquire);
        while let Some(r) = g.as_ref() {
            g = r.next.load(Ordering::Acquire);
            let (low, high) = (
                r.low.load(Ordering::Relaxed),
                r.high.load(Ordering::Relaxed),
            );
            if high == 0 || at < low - r.page || at >= high {
                continue;
            }
            let writable = r.writable.load(Ordering::Relaxed);
            if at >= writable {
                // A fault on a page already writable is not the stack's growth.
                break;
            }
            if at < low {
                stack_stop(high - writable, None);
            }
            let to = writable - (writable - at).div_ceil(GROW) * GROW;
            let to = to.max(low);
            if libc::mprotect(
                to as *mut libc::c_void,
                writable - to,
                libc::PROT_READ | libc::PROT_WRITE,
            ) != 0
            {
                stack_stop(high - writable, Some(writable - to));
            }
            r.writable.store(to, Ordering::Relaxed);
            return;
        }
        match BEFORE.get() {
            Some(b)
                if b.sa_sigaction != libc::SIG_DFL
                    && b.sa_sigaction != libc::SIG_IGN
                    && b.sa_flags & libc::SA_SIGINFO != 0 =>
            {
                let before: extern "C" fn(libc::c_int, *mut libc::siginfo_t, *mut libc::c_void) =
                    std::mem::transmute(b.sa_sigaction);
                before(signal, info, context);
            }
            Some(b) if b.sa_sigaction != libc::SIG_DFL && b.sa_sigaction != libc::SIG_IGN => {
                let before: extern "C" fn(libc::c_int) = std::mem::transmute(b.sa_sigaction);
                before(signal);
            }
            // The default: the fault happens again on return and ends the process.
            _ => {
                let mut default: libc::sigaction = std::mem::zeroed();
                default.sa_sigaction = libc::SIG_DFL;
                libc::sigaction(libc::SIGSEGV, &default, ptr::null_mut());
            }
        }
    }
}

/// Stops a run whose stack, `used` bytes writable, the memory limit of `main` cannot hold:
/// `more` bytes more the system refused, or none when the stack reached its reservation, which
/// is as large as the limit.
fn stack_stop(used: usize, more: Option<usize>) -> ! {
    let mut line = Line::new();
    let _ = std::fmt::Write::write_str(
        &mut line,
        "Memory limit of `main` passed: the run's stack holds ",
    );
    write_bytes(&mut line, used as u64);
    let _ = std::fmt::Write::write_str(
        &mut line,
        match more {
            Some(_) => " and needs ",
            None => " and needs more, past ",
        },
    );
    if let Some(m) = more {
        write_bytes(&mut line, m as u64);
        let _ = std::fmt::Write::write_str(&mut line, " more; the run may hold ");
    }
    write_bytes(&mut line, memory_limit().unwrap_or(0));
    let _ = std::fmt::Write::write_str(&mut line, ".\n");
    fault_exit(line.bytes())
}

/// The message for a stack under the memory limit `limit` that could not be set up: the limit
/// leaves no room for the stack's first part.
fn too_small(limit: u64) -> String {
    let mut l = Line::new();
    write_bytes(&mut l, limit);
    format!(
        "Memory limit of `main` passed: the run's stack cannot start within the {} the run may \
         hold. Repair: raise `memory:` in `@limits` before `main`",
        String::from_utf8_lossy(l.bytes())
    )
}

/// The opening every refusal to set up the stack shares: the program never started.
const START: &str = "the program could not start: before it runs, it reserves address space for \
                     a stack as large as the machine's memory and swap together, so that deep \
                     recursion is limited by memory alone";

/// The message for a stack that could not be set up for `why`, a fault of the system.
fn unable(why: &str) -> String {
    format!(
        "{START}, and {why}. Repairs: run the program again; if it fails the same way, run it \
         with `zedc run`, which does not reserve this stack"
    )
}

/// The message for a reservation of `bytes` the system refused with `err`.
fn reserve(bytes: usize, err: &io::Error) -> String {
    format!(
        "{START}, and the system refused to reserve {bytes} bytes ({err}). The usual cause is a \
         limit on the address space of a process, set with `ulimit -v`. Repairs: lift the limit \
         with `ulimit -v unlimited` and run the program again, or run it with `zedc run`, which \
         does not reserve this stack"
    )
}

#[cfg(test)]
mod bench;

#[cfg(test)]
mod completeness;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::limits::tests::{in_child, status};

    /// How deep `depth` goes before it returns.
    pub(super) fn depth(n: u64) -> u64 {
        // A frame of a kilobyte, which the optimizer cannot remove, so the recursion uses stack.
        let frame = std::hint::black_box([n; 128]);
        if n == 0 { 0 } else { 1 + depth(frame[0] - 1) }
    }

    /// The small instance of `bench::a_run_goes_deeper_than_its_thread_stack`: the frames of a
    /// run lie in the stack mapped for it, above its guard page, and not on the thread's stack,
    /// so the run's depth is limited by that stack alone; and the run gives its result.
    #[test]
    fn a_run_is_on_its_own_stack_and_gives_its_result() {
        let s = Stack::new().unwrap();
        let (low, high) = (s.base as usize + s.page, s.base as usize + s.len);
        let (at, got) = s.run(|| {
            let local = std::hint::black_box(0u8);
            (std::ptr::from_ref(&local) as usize, depth(100))
        });
        assert!(
            low <= at && at < high,
            "{at:#x} outside {low:#x}..{high:#x}"
        );
        assert_eq!(got, 100);
    }

    #[test]
    fn the_stack_is_as_large_as_memory_and_swap() {
        let s = Stack::new().unwrap();
        // SAFETY: as in `Stack::new`.
        #[expect(unsafe_code, reason = "sysinfo is a libc call")]
        let info = unsafe {
            let mut info: libc::sysinfo = std::mem::zeroed();
            assert_eq!(libc::sysinfo(&mut info), 0);
            info
        };
        let bytes = (info.totalram + info.totalswap) * u64::from(info.mem_unit);
        assert!(s.len() as u64 >= bytes);
        assert!(!s.is_empty());
    }

    /// Set in the child process of `a_limited_address_space_refuses_the_reservation`.
    const CHILD: &str = "ZED_RT_STACK_LIMITED_CHILD";

    /// The address space the child may use: far below memory and swap on a machine that can run
    /// the test suite, and room enough for the test binary.
    const LIMIT: libc::rlim_t = 8 << 30;

    #[test]
    fn a_limited_address_space_refuses_the_reservation() {
        if std::env::var_os(CHILD).is_some() {
            let e = Stack::new().unwrap_err();
            assert!(
                e.starts_with("the program could not start: before it runs, it reserves")
                    && e.contains("ulimit -v unlimited"),
                "unexpected error: {e}"
            );
            return;
        }
        // The limit is set in a child process, since it holds for every thread of a process.
        let mut child = std::process::Command::new(std::env::current_exe().unwrap());
        child
            .args([
                "--exact",
                "stack::tests::a_limited_address_space_refuses_the_reservation",
                "--test-threads=1",
            ])
            .env(CHILD, "1");
        #[expect(unsafe_code, reason = "a hook run in the child is an unsafe call")]
        // SAFETY: the hook runs in the child between fork and exec and calls only `setrlimit`,
        // which is async-signal-safe and allocates nothing.
        unsafe {
            use std::os::unix::process::CommandExt;
            child.pre_exec(|| {
                let r = libc::rlimit {
                    rlim_cur: LIMIT,
                    rlim_max: LIMIT,
                };
                if libc::setrlimit(libc::RLIMIT_AS, &r) == 0 {
                    Ok(())
                } else {
                    Err(io::Error::last_os_error())
                }
            });
        }
        let out = child.output().unwrap();
        let text = String::from_utf8_lossy(&out.stdout);
        assert!(
            out.status.success() && text.contains("1 passed"),
            "the child under a limit of {LIMIT} bytes failed: {text}{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    #[test]
    fn a_panic_on_the_stack_reaches_the_caller() {
        let s = Stack::new().unwrap();
        let r = panic::catch_unwind(AssertUnwindSafe(|| s.run(|| panic!("from the run"))));
        let p = r.unwrap_err();
        assert_eq!(p.downcast_ref::<&str>(), Some(&"from the run"));
    }
    /// The limits of a run that may hold 64 MiB.
    fn memory_64_mib() -> zed_kernel::limits::MainLimits {
        zed_kernel::limits::MainLimits {
            memory: Some(64 << 20),
            ..Default::default()
        }
    }

    #[test]
    fn a_stack_under_a_memory_limit_grows_as_the_run_reaches_it() {
        let Some(out) = in_child(
            "stack::tests::a_stack_under_a_memory_limit_grows_as_the_run_reaches_it",
            || {
                crate::limits::enforce(&memory_64_mib()).unwrap();
                let s = Stack::new().unwrap();
                // As large as the limit, not as memory and swap.
                assert_eq!(s.len(), 64 << 20);
                let (grows, _) = s.grows.as_ref().unwrap();
                let (high, writable) = (&grows.high, &grows.writable);
                let held = || high.load(Ordering::Relaxed) - writable.load(Ordering::Relaxed);
                assert_eq!(held(), GROW);
                // 5,000 frames of at least a kilobyte: several steps of growth.
                assert_eq!(s.run(|| depth(5_000)), 5_000);
                assert!(held() > 4 * GROW && held() % GROW == 0, "{}", held());
                // A second run on the stack goes as deep with no more growth.
                let before = held();
                assert_eq!(s.run(|| depth(5_000)), 5_000);
                assert_eq!(held(), before);
            },
        ) else {
            return;
        };
        let (code, err) = status(&out);
        assert_eq!(
            code,
            Some(0),
            "{err}{}",
            String::from_utf8_lossy(&out.stdout)
        );
    }

    #[test]
    fn a_stack_past_the_memory_limit_stops_the_run_with_status_3() {
        let Some(out) = in_child(
            "stack::tests::a_stack_past_the_memory_limit_stops_the_run_with_status_3",
            || {
                crate::limits::enforce(&memory_64_mib()).unwrap();
                // 1,000,000 frames of at least a kilobyte: more than 1 GB.
                Stack::new().unwrap().run(|| depth(1_000_000));
                unreachable!("a stack past the limit was given");
            },
        ) else {
            return;
        };
        let (code, err) = status(&out);
        assert_eq!(code, Some(3), "{err}");
        assert!(
            err.starts_with("Memory limit of `main` passed: the run's stack holds ")
                && err.ends_with("67108864 B (64 MiB).\n"),
            "{err}"
        );
        // P188: the system refuses the next part, `GROW` bytes, before the run reaches the
        // guard page, since the data the process held before counts against the limit too.
        assert!(
            err.contains(" and needs 262144 B (256 KiB) more; the run may hold "),
            "{err}"
        );
    }

    /// P188: the handler of faults finds each stack's own record among several, live and
    /// dropped: a dropped stack's record stays in the list with no stack (`high` 0) and is
    /// passed over, and each live stack grows on its own.
    #[test]
    fn stacks_under_a_memory_limit_grow_each_on_its_own() {
        let Some(out) = in_child(
            "stack::tests::stacks_under_a_memory_limit_grow_each_on_its_own",
            || {
                crate::limits::enforce(&memory_64_mib()).unwrap();
                let held = |s: &Stack| {
                    let (grows, _) = s.grows.as_ref().unwrap();
                    grows.high.load(Ordering::Relaxed) - grows.writable.load(Ordering::Relaxed)
                };
                let dropped = Stack::new().unwrap();
                assert_eq!(dropped.run(|| depth(1_000)), 1_000);
                drop(dropped);
                let (a, b) = (Stack::new().unwrap(), Stack::new().unwrap());
                assert_eq!(b.run(|| depth(2_000)), 2_000);
                assert_eq!(held(&a), GROW, "a grew with b");
                assert!(held(&b) > GROW, "{}", held(&b));
                assert_eq!(a.run(|| depth(1_000)), 1_000);
                assert!(held(&a) > GROW, "{}", held(&a));
            },
        ) else {
            return;
        };
        let (code, err) = status(&out);
        assert_eq!(
            code,
            Some(0),
            "{err}{}",
            String::from_utf8_lossy(&out.stdout)
        );
    }

    /// P188: a fault that is in no stack under the limit is not the stack's growth: the handler
    /// passes it to the action before its own, std's, which ends the process as `SIGSEGV` does,
    /// with no message of the memory limit.
    #[test]
    fn a_fault_outside_the_stacks_ends_the_process_as_sigsegv_does() {
        let Some(out) = in_child(
            "stack::tests::a_fault_outside_the_stacks_ends_the_process_as_sigsegv_does",
            || {
                crate::limits::enforce(&memory_64_mib()).unwrap();
                let _s = Stack::new().unwrap();
                #[expect(
                    unsafe_code,
                    reason = "prctl is a libc call; the test writes through a null pointer"
                )]
                // SAFETY: prctl only sets a flag of the process, so that its end by `SIGSEGV`
                // leaves no core dump; the write faults, as the test means it to.
                unsafe {
                    assert_eq!(libc::prctl(libc::PR_SET_DUMPABLE, 0), 0);
                    std::ptr::write_volatile(std::ptr::null_mut::<u8>(), 1);
                }
                unreachable!("a write through a null pointer was given");
            },
        ) else {
            return;
        };
        use std::os::unix::process::ExitStatusExt;
        let (_, err) = status(&out);
        assert_eq!(out.status.signal(), Some(libc::SIGSEGV), "{err}");
        assert!(!err.contains("Memory limit"), "{err}");
    }

    /// P188: a memory limit that leaves no room for the stack's first part, `GROW` bytes and the
    /// handler's stack of `ALT` bytes, is refused with its own message, `too_small`.
    #[test]
    fn a_memory_limit_too_small_for_the_stack_refuses_it() {
        let Some(out) = in_child(
            "stack::tests::a_memory_limit_too_small_for_the_stack_refuses_it",
            || {
                crate::limits::enforce(&zed_kernel::limits::MainLimits {
                    memory: Some(128 << 10),
                    ..Default::default()
                })
                .unwrap();
                let e = Stack::new().unwrap_err();
                assert_eq!(
                    e,
                    "Memory limit of `main` passed: the run's stack cannot start within the \
                     131072 B (128 KiB) the run may hold. Repair: raise `memory:` in `@limits` \
                     before `main`"
                );
            },
        ) else {
            return;
        };
        let (code, err) = status(&out);
        assert_eq!(
            code,
            Some(0),
            "{err}{}",
            String::from_utf8_lossy(&out.stdout)
        );
    }
}
