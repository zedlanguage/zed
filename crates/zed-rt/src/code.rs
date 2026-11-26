//! The machine code zedc made for a program, as the handler of faults reads it (plan row
//! RT-internal-fault): a fault in that code that no rule of the language explains, a read or
//! write of memory the run does not own (`SIGSEGV`), an instruction the processor refuses
//! (`SIGILL`) or an arithmetic trap (`SIGFPE`), is a bug in zedc, never an error of the
//! program, and the run stops with zedc's message for a bug (`zed_kernel::bug`), the program's
//! content address and the source site of the node whose code faulted, and status 3, as a
//! panic of the runtime stops it (`zedc::run::stop_at_bug`).
//!
//! The code of each node is found by the address of the faulting instruction: Cranelift
//! records, for each function, the ranges of code made under each source location
//! (`MachSrcLoc`), and the generator sets the node's number as the location of its code. A
//! fault at an address no node's range holds, but in a function of the program, is still
//! reported, with no site. A fault in the run's own stack, where a run without a memory limit
//! ends as `SIGSEGV` ends it, and every fault outside the program's code, take the path they
//! took before (`stack::serve`).

use std::cell::Cell;
use std::fmt::Write as _;
use std::ptr;

use crate::close::write_all;
use crate::limits::fault_exit;
use crate::line::Line;

/// The code of one function: where it starts, its length in bytes, and the code of each node
/// in it, as `(start, end, node)` with `start` and `end` offsets from the function's start.
#[derive(Clone, Debug)]
pub struct Function {
    /// The address of the function's first instruction.
    pub start: usize,
    /// The bytes of its code.
    pub len: usize,
    /// The code made for each node, by its offsets in the function and the node's number.
    pub nodes: Vec<(u32, u32, u32)>,
}

/// The machine code of a program: its functions, the code of each node, the place in the
/// source of each node, and the message of a fault, all made before the run so that the
/// handler only reads them.
#[derive(Debug)]
pub struct CodeMap<'a> {
    /// Each function's code, `[start, end)`, sorted by start.
    functions: Vec<(usize, usize)>,
    /// The code of each node, `[start, end)` as addresses and the node's number, sorted by
    /// start.
    nodes: Vec<(usize, usize, u32)>,
    /// The byte of `text` each node's site starts at, by the node's number, when it has one.
    starts: Vec<Option<usize>>,
    /// The program's source text, which the sites are spans of.
    text: &'a str,
    /// The message up to the name of the signal.
    head: String,
    /// The name of the program's source file and a colon, as an error's site gives it, or
    /// nothing when it was read from no file.
    file: String,
}

impl<'a> CodeMap<'a> {
    /// The map of `functions`, the code of the program whose content address is `program`,
    /// read from the file `file` with the text `text`, the site of each node `k` starting at
    /// byte `starts[k]` of `text` when it has one. O(f log f + r log r) for `f` functions and
    /// `r` ranges of nodes. The line and column of a site are found only at a fault, in one
    /// pass over the text (`zed_kernel::sites::line_col`), so that a run that does not fault
    /// pays nothing for them.
    pub fn new(
        program: &str,
        file: Option<&str>,
        text: &'a str,
        starts: Vec<Option<usize>>,
        functions: Vec<Function>,
    ) -> CodeMap<'a> {
        let mut nodes = Vec::new();
        let mut spans = Vec::with_capacity(functions.len());
        for f in functions {
            spans.push((f.start, f.start + f.len));
            for (s, e, k) in f.nodes {
                nodes.push((f.start + s as usize, f.start + e as usize, k));
            }
        }
        spans.sort_unstable();
        nodes.sort_unstable();
        let message = zed_kernel::bug::report(
            zed_kernel::bug::Stopped::Run,
            "The machine code zedc made for the program reached memory or an instruction that \
             no rule of the language lets it reach.",
            "this message, the program's source and the input it was given",
        );
        let head = zed_kernel::bug::with_details(message, &[("program", program.to_owned())]);
        CodeMap {
            functions: spans,
            nodes,
            starts,
            text,
            head: head + "\n  signal: ",
            file: file.map_or_else(String::new, |f| format!("{f}:")),
        }
    }

    /// Whether `pc` is in a function of the program. O(log f).
    fn holds(&self, pc: usize) -> bool {
        let k = self.functions.partition_point(|&(s, _)| s <= pc);
        // Cannot panic: `k > 0` is tested first, and `partition_point` is at most the length.
        k > 0 && pc < self.functions[k - 1].1
    }

    /// The node whose code holds `pc`, if any. Two ranges never overlap: Cranelift gives each
    /// instruction one location. O(log r).
    fn node_at(&self, pc: usize) -> Option<u32> {
        let k = self.nodes.partition_point(|&(s, _, _)| s <= pc);
        // Cannot panic: `k > 0` is tested first, and `partition_point` is at most the length.
        (k > 0 && pc < self.nodes[k - 1].1).then(|| self.nodes[k - 1].2)
    }

    /// The line and column of node `k`'s site, if it has one. O(length of the text), with no
    /// allocation.
    fn place(&self, k: u32) -> Option<(usize, usize)> {
        let at = (*self.starts.get(k as usize)?)?;
        let at = at.min(self.text.len());
        Some(zed_kernel::sites::line_col(self.text.as_bytes(), at))
    }

    /// The text of the fault of `signal` at `pc`, after [`CodeMap::head`] and before the
    /// file's name, and after it: the signal and the line and column, or that the code is of
    /// no node. With no allocation.
    fn tail(&self, signal: libc::c_int, pc: usize) -> (Line, Option<Line>) {
        let name = match signal {
            libc::SIGSEGV => "SIGSEGV",
            libc::SIGILL => "SIGILL",
            libc::SIGFPE => "SIGFPE",
            _ => "another signal",
        };
        let (mut before, mut after) = (Line::new(), Line::new());
        let _ = write!(before, "{name}\n  site: ");
        match self.node_at(pc).and_then(|k| self.place(k)) {
            Some((l, c)) => {
                let _ = writeln!(after, "{l}:{c}");
                (before, Some(after))
            }
            None => {
                let _ = writeln!(before, "none: the code is of no node of the program");
                (before, None)
            }
        }
    }
}

/// The run on this thread whose code faults are reported in: its map and its stack's
/// addresses, `[low, high)`, guard page included.
struct Running {
    /// The map, its lifetime erased: [`with_map`] keeps it alive while the run is set.
    map: *const CodeMap<'static>,
    stack: (usize, usize),
}

thread_local! {
    /// The run of this thread under [`with_map`], or null.
    //
    // Read by the handler of faults. A `thread_local!` with a `const` initializer and a type
    // that needs no drop is a plain thread-local variable on Linux: no lazy initialization
    // and no destructor to register, so its read takes no lock and allocates nothing (Rust
    // standard library, `std::thread::local`, "const" initializer; `Cell<*const _>` needs no
    // drop). A fault is a synchronous signal, so the handler runs on the faulting thread and
    // reads that thread's run.
    static RUNNING: Cell<*const Running> = const { Cell::new(ptr::null()) };
}

/// Runs `f` with faults in the code of `map` reported as bugs, on the stack `[low, high)`.
/// The run before it on this thread, if any, is put back after, also when `f` panics.
pub(crate) fn with_map<R>(map: &CodeMap<'_>, stack: (usize, usize), f: impl FnOnce() -> R) -> R {
    struct Back(*const Running);
    impl Drop for Back {
        fn drop(&mut self) {
            RUNNING.with(|r| r.set(self.0));
        }
    }
    let running = Running {
        map: ptr::from_ref(map).cast(),
        stack,
    };
    let _back = Back(RUNNING.with(|r| r.replace(&raw const running)));
    f()
}

/// Stops the run with a bug report when a fault of `signal`, at the instruction `pc` and, for
/// `SIGSEGV`, at the address `at`, is in the code of this thread's run and not in its stack;
/// else returns. Async-signal-safe: reads of the thread's run, which `with_map` keeps alive
/// while it is set, and of its map, which is not changed while it runs; formatting into
/// buffers on the handler's stack; then `write` and `fault_exit`.
pub(crate) fn report(signal: libc::c_int, pc: usize, at: Option<usize>) {
    let r = RUNNING.with(Cell::get);
    if r.is_null() {
        return;
    }
    #[expect(unsafe_code, reason = "the run is read through a pointer to it")]
    // SAFETY: `with_map` sets the pointer to a `Running` on its own frame and puts the one
    // before back before the frame ends, and the `Running` holds a map borrowed for that frame:
    // while it is set, both are alive and not changed.
    let (map, stack) = unsafe { (&*(*r).map, (*r).stack) };
    if at.is_some_and(|a| (stack.0..stack.1).contains(&a)) || !map.holds(pc) {
        return;
    }
    let (before, after) = map.tail(signal, pc);
    write_all(map.head.as_bytes());
    write_all(before.bytes());
    if let Some(after) = after {
        write_all(map.file.as_bytes());
        write_all(after.bytes());
    }
    fault_exit(&[])
}

/// The address of the instruction a signal stopped, from the context the kernel passes a
/// handler installed with `SA_SIGINFO`.
///
/// # Safety
///
/// `context` is the third argument of such a handler: a valid `ucontext_t`.
#[expect(unsafe_code, reason = "the context is read through a pointer to it")]
pub(crate) unsafe fn pc_of(context: *mut libc::c_void) -> usize {
    let u = context.cast::<libc::ucontext_t>();
    // SAFETY: the caller's contract. The registers are Linux's `mcontext_t`: `gregs[REG_RIP]`
    // on x86_64, `pc` on AArch64 (libc 0.2.191, `linux_like/linux/gnu/b64/x86_64/mod.rs` and
    // `aarch64/mod.rs`).
    unsafe {
        #[cfg(target_arch = "x86_64")]
        // Cannot panic: `gregs` is `[greg_t; 23]` and `REG_RIP` is 16 (libc 0.2.191, x86_64
        // `mod.rs` lines 195 and 639), a constant index into a fixed array.
        let pc = (*u).uc_mcontext.gregs[libc::REG_RIP as usize] as usize;
        #[cfg(target_arch = "aarch64")]
        let pc = (*u).uc_mcontext.pc as usize;
        pc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn map() -> CodeMap<'static> {
        // Node 1 at line 3, column 7 (after `é`, two bytes, one column), node 2 at line 4,
        // column 1, after a `\r\n`.
        let text = "a\n\nb = é + c\r\nd";
        let starts = vec![
            None,
            Some(text.find('+').unwrap()),
            Some(text.find('d').unwrap()),
        ];
        CodeMap::new(
            "ab12",
            Some("f.zed"),
            text,
            starts,
            vec![
                Function {
                    start: 1000,
                    len: 100,
                    nodes: vec![(10, 20, 1), (20, 30, 0), (40, 50, 2)],
                },
                Function {
                    start: 500,
                    len: 10,
                    nodes: vec![],
                },
            ],
        )
    }

    fn text(m: &CodeMap<'_>, signal: libc::c_int, pc: usize) -> String {
        let (b, a) = m.tail(signal, pc);
        let mut s = String::from_utf8(b.bytes().to_vec()).unwrap();
        if let Some(a) = a {
            s += &m.file;
            s += std::str::from_utf8(a.bytes()).unwrap();
        }
        s
    }

    #[test]
    fn a_fault_is_placed_at_the_node_whose_code_holds_it() {
        let m = map();
        assert!(m.head.contains("bug in zedc, not in your program"));
        assert!(m.head.contains("\n  program: ab12\n  signal: "));
        assert_eq!(
            text(&m, libc::SIGSEGV, 1015),
            "SIGSEGV\n  site: f.zed:3:7\n"
        );
        assert_eq!(text(&m, libc::SIGFPE, 1049), "SIGFPE\n  site: f.zed:4:1\n");
        // Node 0 has no site; offsets 30..40 are of no node; 500..510 is a function of none.
        for pc in [1025, 1035, 505] {
            assert!(m.holds(pc), "{pc}");
            assert_eq!(
                text(&m, libc::SIGILL, pc),
                "SIGILL\n  site: none: the code is of no node of the program\n"
            );
        }
        // Outside every function, and at each one's end.
        for pc in [0, 499, 510, 999, 1100, usize::MAX] {
            assert!(!m.holds(pc), "{pc}");
        }
    }

    #[test]
    fn the_run_is_set_for_the_call_and_put_back_after() {
        let m = map();
        assert!(RUNNING.with(Cell::get).is_null());
        with_map(&m, (1, 2), || {
            assert!(!RUNNING.with(Cell::get).is_null());
            // Outside the code, and in the run's stack: no report, the call returns.
            report(libc::SIGSEGV, 10, None);
            report(libc::SIGSEGV, 1015, Some(1));
        });
        assert!(RUNNING.with(Cell::get).is_null());
        let caught = std::panic::catch_unwind(|| with_map(&m, (1, 2), || panic!("in the run")));
        assert!(caught.is_err());
        assert!(RUNNING.with(Cell::get).is_null());
    }
}
