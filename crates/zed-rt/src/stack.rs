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
                .map_err(|_| "runtime: the system gives no page size".to_string())?;
            let mut info: libc::sysinfo = std::mem::zeroed();
            if libc::sysinfo(&mut info) != 0 {
                return Err(format!(
                    "runtime: cannot read the size of memory for the stack of a run: {}",
                    io::Error::last_os_error()
                ));
            }
            let unit = u64::from(info.mem_unit);
            let bytes = (info.totalram + info.totalswap) * unit;
            let bytes = usize::try_from(bytes)
                .map_err(|_| "runtime: memory exceeds the address space".to_string())?;
            let len = bytes.div_ceil(page) * page + page;
            let base = libc::mmap(
                ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_STACK,
                -1,
                0,
            );
            // Complexity tradeoff: a refused reservation (an address-space limit such as
            // `ulimit -v`) refuses the run, even one that a smaller stack would hold; retrying
            // smaller would make the size a switch, and no size short of memory holds every run.
            if base == libc::MAP_FAILED {
                return Err(format!(
                    "runtime: cannot reserve a stack of {} bytes for a run: {}",
                    len - page,
                    io::Error::last_os_error()
                ));
            }
            let s = Stack { base, len, page };
            if libc::mprotect(base, page, libc::PROT_NONE) != 0 {
                return Err(format!(
                    "runtime: cannot protect the guard page below the stack of a run: {}",
                    io::Error::last_os_error()
                ));
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

    #[test]
    fn a_panic_on_the_stack_reaches_the_caller() {
        let s = Stack::new().unwrap();
        let r = panic::catch_unwind(AssertUnwindSafe(|| s.run(|| panic!("from the run"))));
        let p = r.unwrap_err();
        assert_eq!(p.downcast_ref::<&str>(), Some(&"from the run"));
    }
}
