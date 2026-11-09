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

use std::io;
use std::panic::{self, AssertUnwindSafe};
use std::ptr;

/// A stack mapped for one run, with the guard page below it; unmapped when dropped.
#[derive(Debug)]
pub struct Stack {
    /// The low end of the mapping: the guard page, then the stack.
    base: *mut libc::c_void,
    /// The bytes mapped, the guard page included.
    len: usize,
    /// The bytes of the guard page.
    page: usize,
}

impl Stack {
    /// Maps a stack as large as the machine's memory and swap together, reserved and not
    /// committed, with a guard page below it.
    pub fn new() -> Result<Stack, String> {
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
            let s = Stack { base, len, page };
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
    /// on the caller's stack.
    pub fn run<R>(&self, f: impl FnOnce() -> R) -> R {
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
        caught.unwrap_or_else(|p| panic::resume_unwind(p))
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        #[expect(unsafe_code, reason = "unmapping is a libc call")]
        // SAFETY: `base` and `len` are the mapping `new` made, unmapped only here, and no code
        // runs on it: `run` has returned, since it borrows `self`.
        unsafe {
            libc::munmap(self.base, self.len);
        }
    }
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
mod tests {
    use super::*;

    /// How deep `depth` goes before it returns.
    fn depth(n: u64) -> u64 {
        // A frame of a kilobyte, which the optimizer cannot remove, so the recursion uses stack.
        let frame = std::hint::black_box([n; 128]);
        if n == 0 { 0 } else { 1 + depth(frame[0] - 1) }
    }

    #[test]
    fn a_run_goes_deeper_than_its_thread_stack() {
        // 100,000 frames of at least a kilobyte: more than 100 MB, on a thread of 2 MiB.
        let got = std::thread::Builder::new()
            .stack_size(2 << 20)
            .spawn(|| Stack::new().unwrap().run(|| depth(100_000)))
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(got, 100_000);
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
}
