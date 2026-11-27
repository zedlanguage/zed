//! The global allocator of the test binaries: the system allocator, counting the bytes each
//! thread allocates, for the second measure of the scaling tests (`zed_tests::scaling`).
//!
//! A block of `n` bytes counts `n` when it is allocated, and a block grown or shrunk in place or
//! by a copy counts its new size, which is what a copy writes. A request the system refuses writes
//! nothing and counts nothing, so a probe such as `try_reserve` of an impossible size leaves the
//! count as it was. Freeing counts nothing toward that count; [`live`] measures, on one thread,
//! the bytes a run leaves allocated, frees counted, and its peak.
//!
//! The count of a thread is of the bytes it and every thread it starts, and every thread those
//! start, allocate, as the kernel's counters of instructions count a thread and the threads it
//! starts. Tests that run beside a measured one in the same process have counts of their own and
//! do not change it, whatever the scheduling. The threads a thread starts add to its count as
//! they allocate, so a count read once a thread has been joined holds all of that thread's bytes.
//!
//! A thread learns its parent by this crate's own `pthread_create`, which the binary's calls to
//! `pthread_create` reach in place of the C library's (std starts every thread by it); it passes
//! the parent's count to the new thread and then calls the C library's. The main thread was not
//! started that way: it counts its own bytes only, and the threads it starts, such as the test
//! harness's thread for each test, count on their own, so the tests running at once do not all
//! add to one count. [`allocated`] on the main thread is therefore of its own bytes, and a test
//! that the harness runs on the main thread, as libtest does when it cannot start a thread for it,
//! does not count the bytes of the threads it starts. Giving the main thread a count would make
//! every test's thread add to it, one atomic shared by all threads at each allocation.
//!
//! Each thread started adds, at its start and on itself, a block that std's map of the live
//! threads allocates (`std::sys::pal::unix::stack_overflow::thread_info`, one map for the
//! process). Whether the insertion allocates, 0 bytes or about 1 KiB, depends on which other
//! threads are alive, so a count that holds the start of a thread is not the same in every run
//! beside other tests. `zed_tests::scaling` compares the bytes counted inside the thread of each
//! run, which do not hold that thread's start; a run that starts threads of its own still holds
//! their starts.
//!
//! The counting allocator forwards to `System`, the C library's `malloc`. In a binary that
//! invokes [`meter_entry_points`], which every test binary that holds `zed_tests::scaling` does,
//! `malloc` and the functions like it are those of module `meter`: inside [`metered`] each thread
//! allocates from a heap of its own, whose instructions per call depend on nothing but that
//! thread's own calls, and elsewhere they forward to the C library's (TEST-meter-allocator-bias).
//! Since they sit under the C library's functions and not under the Rust allocator, they also
//! serve the C library's own allocations.
//!
//! The standard library's own allocations, made inside libstd.so when std is a shared library
//! (zrun's `-C prefer-dynamic`), are counted in every binary that links this crate, since there
//! the global allocator's entry points (`__rust_alloc` and the others) are exported and libstd.so
//! binds to them. A binary built from this crate itself would hide them, and libstd.so would then
//! call `System` past the count (FAIL-std-allocations-uncounted), so the crate's tests are an
//! integration test (`tests/zed_alloc_count.rs`) and its unit tests are turned off
//! (`[lib] test = false`).
//!
//! All of the above is the Linux build. On every other system there is one count, of the bytes
//! every thread of the process allocates: Windows has no `pthread_create` to stand in for, and on
//! macOS the counters of work (module `os`) are of the whole process too, so the scaling tests
//! there run one test at a time and a count of the whole process is what they need. The macOS and
//! Windows builds are compiled here (on Linux, by `cargo check --target`) but have not been run.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
#[cfg(target_os = "linux")]
use std::ffi::{c_int, c_void};
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
#[cfg(target_os = "linux")]
use std::sync::{Arc, OnceLock};

#[cfg(target_os = "linux")]
#[doc(hidden)]
pub mod meter;
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
pub mod os;

#[cfg(target_os = "linux")]
/// The bytes a thread started by `pthread_create` and the threads it starts have allocated.
struct Count {
    bytes: AtomicU64,
    /// The count of the thread that started this one, if that thread has one.
    parent: Option<Arc<Count>>,
}

/// What the allocator keeps for each thread, in one thread-local, so that an allocation and a
/// free find all of it from one address. A `const` value of a type with no destructor, so reading
/// it allocates nothing, has no check of a first use, and works while the thread ends.
struct Local {
    /// This thread's [`Count`], or null on a thread not started by `pthread_create`. The `Arc`
    /// that keeps it lives in [`start`] on this thread's stack, and is dropped only after this
    /// is set back to null.
    #[cfg(target_os = "linux")]
    count: Cell<*const Count>,
    /// The bytes allocated on a thread with no [`Count`]: the main thread, and any thread after
    /// [`start`] has set its `count` back to null while it ends.
    #[cfg(target_os = "linux")]
    own: Cell<u64>,
    /// Whether a measurement of [`live`] is running on this thread: the one field a free reads
    /// when none is.
    on: Cell<bool>,
    /// The bytes allocated less the bytes freed since the measurement started.
    net: Cell<i64>,
    /// The largest `net` has been.
    peak: Cell<i64>,
    /// The blocks the system gave this thread, each allocation and each reallocation one, for
    /// [`allocations`].
    calls: Cell<u64>,
}

thread_local! {
    /// This thread's [`Local`].
    static LOCAL: Local = const {
        Local {
            #[cfg(target_os = "linux")]
            count: Cell::new(std::ptr::null()),
            #[cfg(target_os = "linux")]
            own: Cell::new(0),
            on: Cell::new(false),
            net: Cell::new(0),
            peak: Cell::new(0),
            calls: Cell::new(0),
        }
    };
}

#[cfg(target_os = "linux")]
impl Local {
    /// This thread's [`Count`], if it has one.
    fn count(&self) -> Option<&Count> {
        let count = self.count.get();
        #[expect(
            unsafe_code,
            reason = "the count is shared with the threads this one starts, which it must outlive"
        )]
        // SAFETY: `count` is null or points into the `Arc` that `start` holds on this thread's
        // stack while it is set (see `Local::count`). The reference lives no longer than `self`,
        // a borrow of this thread's `Local` taken inside `LOCAL.with`, which ends before `start`
        // drops that `Arc`.
        unsafe {
            count.as_ref()
        }
    }
}

#[cfg(target_os = "linux")]
/// The bytes this thread and the threads it started have allocated so far.
pub fn allocated() -> u64 {
    LOCAL.with(|local| match local.count() {
        Some(count) => count.bytes.load(Relaxed),
        None => local.own.get(),
    })
}

#[cfg(target_os = "linux")]
/// Adds `bytes`, which the system gave, to this thread's count and its parents'. The walk is as
/// long as the chain of threads that started this one, a handful in any test.
///
/// Complexity tradeoff: the other version, one count per thread with a thread's descendants
/// summed at each read, is O(1) per allocation but O(threads) per read and needs the live
/// threads listed. Used: each allocation walks the chain of threads that started this one,
/// O(d) for a chain `d` threads long, and a read is O(1). Tradeoffs: allocation costs grow
/// with `d`, which only a test's own threads set, about three; the compiler and runtime start
/// none. COMPLEXITY.md row "`zed_alloc_count` `count`".
fn count(local: &Local, bytes: usize) {
    let mut count = local.count();
    if count.is_none() {
        local.own.set(local.own.get() + bytes as u64);
    }
    while let Some(c) = count {
        c.bytes.fetch_add(bytes as u64, Relaxed);
        count = c.parent.as_deref();
    }
}

/// The bytes every thread of the process has allocated, off Linux.
#[cfg(not(target_os = "linux"))]
static ALL: AtomicU64 = AtomicU64::new(0);

/// The bytes every thread of this process has allocated so far: off Linux there is one count
/// (see the crate's documentation).
#[cfg(not(target_os = "linux"))]
pub fn allocated() -> u64 {
    ALL.load(Relaxed)
}

/// Adds `bytes`, which the system gave, to the count of the process.
#[cfg(not(target_os = "linux"))]
fn count(_: &Local, bytes: usize) {
    ALL.fetch_add(bytes as u64, Relaxed);
}

/// Adds `added` bytes and takes away `freed` bytes from the measurement running on this thread,
/// if one is. Both are worked out only when one is, so a free with none running reads one flag.
fn track(local: &Local, added: usize, freed: usize) {
    if local.on.get() {
        let net = local.net.get() + added as i64 - freed as i64;
        local.net.set(net);
        local.peak.set(local.peak.get().max(net));
    }
}

/// Counts a block of `bytes` the system gave (`block` is not null) and returns `block`; `freed`
/// is the size of the block it replaced, 0 for a new block.
fn allocated_block(block: *mut u8, bytes: usize, freed: usize) -> *mut u8 {
    if !block.is_null() {
        LOCAL.with(|local| {
            local.calls.set(local.calls.get() + 1);
            count(local, bytes);
            track(local, bytes, freed);
        });
    }
    block
}

/// The blocks the system has given this thread so far, each allocation and each reallocation
/// one: not those of the threads it started. The difference over a run is how often the run
/// went to the allocator, whatever the sizes (PERF-walk-allocator-no-coalesce).
pub fn allocations() -> u64 {
    LOCAL.with(|l| l.calls.get())
}

/// What [`live`] measured.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Live {
    /// The bytes allocated less the bytes freed: what the run left allocated, or, when negative,
    /// what it freed of the blocks it was given.
    pub net: i64,
    /// The most bytes the run had allocated and not yet freed at any one time, at least 0.
    pub peak: u64,
}

/// Runs `f` and returns its result with the bytes it left allocated and its peak, counting only
/// the allocations and frees made on this thread: a block a thread started by `f` allocates is
/// not counted, and a block `f` frees that was allocated before it counts as negative. A
/// measurement inside another adds its bytes to the outer one.
pub fn live<R>(f: impl FnOnce() -> R) -> (R, Live) {
    /// A measurement's state: whether it runs, its `net` and its `peak`.
    type State = (bool, i64, i64);
    fn get() -> State {
        LOCAL.with(|l| (l.on.get(), l.net.get(), l.peak.get()))
    }
    fn set((on, net, peak): State) {
        LOCAL.with(|l| {
            l.on.set(on);
            l.net.set(net);
            l.peak.set(peak);
        });
    }
    /// Puts the outer measurement back when `f` returns or unwinds.
    struct Restore(State);
    impl Drop for Restore {
        fn drop(&mut self) {
            set(self.0);
        }
    }
    let outer = get();
    let restore = Restore(outer);
    set((true, 0, 0));
    let out = f();
    let (_, net, peak) = get();
    drop(restore);
    let (outer_on, outer_net, outer_peak) = outer;
    if outer_on {
        set((true, outer_net + net, outer_peak.max(outer_net + peak)));
    }
    let live = Live {
        net,
        peak: peak.unsigned_abs(),
    };
    (out, live)
}

/// Whether a measurement of [`live`] is running on this thread, for the crate's tests
/// (`tests/zed_alloc_count.rs`), which check that one that panics leaves none running.
#[doc(hidden)]
pub fn measuring() -> bool {
    LOCAL.with(|l| l.on.get())
}

/// Runs `f` with a heap of its own for this thread and the threads `f` starts, whose
/// instructions per call depend only on each thread's own calls (module `meter`;
/// TEST-meter-allocator-bias), so that a count of instructions of `f` repeats from run to run and
/// the allocator adds the same cost to each call at every size. The scaling tests run each
/// measured run in it (`zed_tests::scaling`); no other caller needs it. A block `f` leaves
/// allocated may be freed anywhere afterwards. Inside another call of `metered` on this thread,
/// `f` uses the outer heap. Off Linux this runs `f`.
pub fn metered<R>(f: impl FnOnce() -> R) -> R {
    #[cfg(target_os = "linux")]
    return meter::run(f);
    #[cfg(not(target_os = "linux"))]
    f()
}

/// Makes ready what [`metered`] needs, so that a count taken afterwards does not hold that work:
/// the reservation of the address space of its heaps, made once per process, and the check that
/// the binary's `malloc` is the meter's ([`meter_entry_points`]), which stops the process with
/// the fix when it is not. Off Linux, nothing.
pub fn ready_to_meter() {
    #[cfg(target_os = "linux")]
    meter::ready();
}

/// Defines the C library's allocation functions (`malloc`, `free`, `calloc`, `realloc`,
/// `reallocarray`, `memalign`, `aligned_alloc`, `posix_memalign`, `valloc`, `pvalloc` and
/// `malloc_usable_size`) in the binary whose crate invokes it, once, as the meter's allocator
/// (module `meter`): the heap of a metered run on its threads, the C library's elsewhere. The
/// dynamic linker then sends every call of them in the process there, the C library's own
/// included, as the C library allows a program that replaces `malloc` (glibc manual, "Replacing
/// malloc"). Only the test binaries invoke it, so `zedc` and the programs it compiles keep the C
/// library's allocator unchanged. Off Linux it defines nothing.
#[macro_export]
macro_rules! meter_entry_points {
    () => {
        #[cfg(target_os = "linux")]
        const _: () = {
            use ::std::ffi::{c_int, c_void};
            use $crate::meter;
            #[unsafe(no_mangle)]
            unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
                // SAFETY: the caller's guarantees, passed on.
                unsafe { meter::malloc(size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn calloc(n: usize, size: usize) -> *mut c_void {
                // SAFETY: as `malloc`.
                unsafe { meter::calloc(n, size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn free(block: *mut c_void) {
                // SAFETY: as `malloc`.
                unsafe { meter::free(block) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn realloc(block: *mut c_void, size: usize) -> *mut c_void {
                // SAFETY: as `malloc`.
                unsafe { meter::realloc(block, size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn reallocarray(
                block: *mut c_void,
                n: usize,
                size: usize,
            ) -> *mut c_void {
                // SAFETY: as `malloc`.
                unsafe { meter::reallocarray(block, n, size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn memalign(align: usize, size: usize) -> *mut c_void {
                // SAFETY: as `malloc`.
                unsafe { meter::memalign(align, size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn aligned_alloc(align: usize, size: usize) -> *mut c_void {
                // SAFETY: as `malloc`.
                unsafe { meter::memalign(align, size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn posix_memalign(
                out: *mut *mut c_void,
                align: usize,
                size: usize,
            ) -> c_int {
                // SAFETY: as `malloc`.
                unsafe { meter::posix_memalign(out, align, size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn valloc(size: usize) -> *mut c_void {
                // SAFETY: as `malloc`.
                unsafe { meter::valloc(size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn pvalloc(size: usize) -> *mut c_void {
                // SAFETY: as `malloc`.
                unsafe { meter::pvalloc(size) }
            }
            #[unsafe(no_mangle)]
            unsafe extern "C" fn malloc_usable_size(block: *mut c_void) -> usize {
                // SAFETY: as `malloc`.
                unsafe { meter::malloc_usable_size(block) }
            }
        };
    };
}

/// The system allocator, counting bytes per thread.
pub struct Counting;

#[expect(
    unsafe_code,
    reason = "GlobalAlloc is an unsafe trait; each method only adds to a counter and calls System"
)]
// SAFETY: every method forwards its arguments unchanged to `System`, which meets the contract of
// `GlobalAlloc`; counting reads thread-local cells and adds to atomics, and never allocates.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's guarantees about `layout` are passed on unchanged.
        allocated_block(unsafe { System.alloc(layout) }, layout.size(), 0)
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: as in `alloc`.
        allocated_block(unsafe { System.alloc_zeroed(layout) }, layout.size(), 0)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LOCAL.with(|local| track(local, 0, layout.size()));
        // SAFETY: `ptr` and `layout` come from this allocator, which is `System`.
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: as in `dealloc`; the caller's guarantees about `new_size` are passed on.
        let block = unsafe { System.realloc(ptr, layout, new_size) };
        allocated_block(block, new_size, layout.size())
    }
}

/// Whether this thread is in a metered run.
#[cfg(target_os = "linux")]
fn in_metered_run() -> bool {
    meter::in_run()
}

/// The allocator of every binary that links this crate.
#[global_allocator]
static COUNTING: Counting = Counting;

#[cfg(target_os = "linux")]
/// The function a new thread runs, as `pthread_create` takes it.
type Routine = extern "C" fn(*mut c_void) -> *mut c_void;

#[cfg(target_os = "linux")]
/// The C library's `pthread_create`.
type Create = unsafe extern "C" fn(
    *mut libc::pthread_t,
    *const libc::pthread_attr_t,
    Routine,
    *mut c_void,
) -> c_int;

#[cfg(target_os = "linux")]
/// What [`start`] needs: the thread's own routine and argument, the count of its parent, and
/// whether the parent is in a metered run ([`metered`]), which the thread then joins with a heap
/// of its own.
struct Start {
    routine: Routine,
    arg: *mut c_void,
    parent: Option<Arc<Count>>,
    metered: bool,
}

#[cfg(target_os = "linux")]
/// The C library's `pthread_create`, found once.
fn create() -> Create {
    static CREATE: OnceLock<Create> = OnceLock::new();
    *CREATE.get_or_init(|| {
        #[expect(unsafe_code, reason = "finding the C library's function by its name")]
        // SAFETY: `RTLD_NEXT` and a C string are what `dlsym` takes; the symbol it finds after
        // this binary's is the C library's `pthread_create`, whose type is `Create`. A null
        // result, which would mean there is no such function, stops the process.
        unsafe {
            let found = libc::dlsym(libc::RTLD_NEXT, c"pthread_create".as_ptr());
            assert!(
                !found.is_null(),
                "the C library has no pthread_create to start a thread by"
            );
            std::mem::transmute::<*mut c_void, Create>(found)
        }
    })
}

#[cfg(target_os = "linux")]
/// Starts a thread as the C library's `pthread_create` does, giving it a count that adds to the
/// count of this thread, if this thread has one.
///
/// # Safety
///
/// The contract of the C library's `pthread_create`, whose arguments this passes on.
#[expect(
    unsafe_code,
    reason = "a thread learns its parent only from the call that starts it"
)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pthread_create(
    thread: *mut libc::pthread_t,
    attr: *const libc::pthread_attr_t,
    routine: Routine,
    arg: *mut c_void,
) -> c_int {
    let parent = LOCAL.with(|local| {
        local.count().map(|count| {
            // SAFETY: `count` points into the `Arc` that `start` holds on this thread's stack
            // (see `Local::count`), so the `Arc` has a strong count while this adds one more for
            // the new thread.
            unsafe {
                let ptr: *const Count = count;
                Arc::increment_strong_count(ptr);
                Arc::from_raw(ptr)
            }
        })
    });
    let start_arg = Box::into_raw(Box::new(Start {
        routine,
        arg,
        parent,
        metered: in_metered_run(),
    }));
    // SAFETY: the caller's guarantees about `thread` and `attr` are passed on; `start` with
    // `start_arg` runs `routine` with `arg`, as the caller asked.
    let failed = unsafe { create()(thread, attr, start, start_arg.cast()) };
    if failed != 0 {
        // SAFETY: no thread was started, so `start_arg` is still this call's own.
        drop(unsafe { Box::from_raw(start_arg) });
    }
    failed
}

#[cfg(target_os = "linux")]
/// The routine of every thread this crate's `pthread_create` starts: it gives the thread its
/// count, runs the thread's own routine, and takes the count away again before dropping it. A
/// thread that ends by `pthread_exit` keeps its count, which is never dropped, and leaves its
/// metered heap's spans mapped; std ends none that way. A thread started in a metered run runs
/// in [`metered`] from before its count is made until after it is dropped.
extern "C" fn start(start_arg: *mut c_void) -> *mut c_void {
    #[expect(unsafe_code, reason = "taking back the argument pthread_create boxed")]
    // SAFETY: `start_arg` is the `Box<Start>` `pthread_create` made for this thread alone.
    let Start {
        routine,
        arg,
        parent,
        metered: in_run,
    } = *unsafe { Box::from_raw(start_arg.cast::<Start>()) };
    // A thread with no parent count was started by the main thread: in a test binary, libtest's
    // thread for one test, which libtest starts from the main thread and names after the test.
    let started_by_main = parent.is_none();
    let run = || {
        let count = Arc::new(Count {
            bytes: AtomicU64::new(0),
            parent,
        });
        LOCAL.with(|local| local.count.set(Arc::as_ptr(&count)));
        let out = routine(arg);
        LOCAL.with(|local| local.count.set(std::ptr::null()));
        drop(count);
        out
    };
    let out = if in_run { metered(run) } else { run() };
    if started_by_main && GIVE_BACK.load(Relaxed) {
        release_free_memory();
    }
    out
}

/// Whether [`give_back_as_each_test_ends`] has been called.
#[cfg(target_os = "linux")]
static GIVE_BACK: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Makes each thread the main thread starts give the C library's free memory back to the kernel
/// as it ends (`release_free_memory`), for the rest of the process. Test binaries turn it on:
/// `zed_meter_settings` calls it as the process starts, in every binary that links it, which
/// are the test binaries only. Other binaries that link this crate, the `zedc` executable of
/// zed-native, keep glibc's own behavior, so a program whose main thread starts many short
/// threads pays no trim for each. On other systems it does nothing.
pub fn give_back_as_each_test_ends() {
    #[cfg(target_os = "linux")]
    GIVE_BACK.store(true, Relaxed);
}

/// Whether [`give_back_as_each_test_ends`] has been called in this process: true in every test
/// binary that links `zed_meter_settings` on Linux, false elsewhere. Read by the tests that check
/// each test binary gives its free memory back (TEST-l01-26-peak-memory).
pub fn gives_back() -> bool {
    #[cfg(target_os = "linux")]
    return GIVE_BACK.load(Relaxed);
    #[cfg(not(target_os = "linux"))]
    false
}

#[cfg(target_os = "linux")]
/// Gives the kernel back the free memory the C library's allocator holds in every arena; called,
/// once [`give_back_as_each_test_ends`] has been, as each thread the main thread started ends,
/// which in a test binary is the end of each test, once the test's own threads have been joined
/// and its values dropped (TEST-l01-26-peak-memory).
///
/// Why: glibc's malloc gives threads that allocate at once arenas of their own, and returns memory
/// to the kernel only from the top of an arena's heap past its trim threshold. A test that builds
/// its inputs on several threads at once and drops them leaves the free pages in several arenas,
/// and the next test's threads, taking arenas in another order or asking for blocks the freed ones
/// do not fit, add their own peak to what is held. Measured on l01_26_type_resolution at
/// 1ce03f689 (`--test-threads=1`, `/usr/bin/time -v`, maximum resident set):
/// `bench::deep_ops::meets_takes_linear_time_in_the_depth` alone 2,468,244 kB,
/// `bench::deep_ops::fits_sig_takes_linear_time_in_the_depth` alone 2,489,244 kB, the two in that
/// order in one process 4,169,604 kB, and the pair with `glibc.malloc.arena_max=1` 2,493,328 kB.
/// The whole binary passed its 942 tests at 40,348,564 kB in one process with one test thread,
/// and with 8 test threads was killed by the out-of-memory killer at 51.5 GB, while no test alone
/// reaches 3,000,000 kB. A trim at the start of each scaling check was tried first and changed
/// nothing (4,169,016 kB): the next test builds its inputs before its first check.
///
/// What the C library promises (malloc_trim(3), Linux man-pages 6.x, read 2026-11-22): "Since
/// glibc 2.8 this function frees memory in all arenas and in all chunks with whole free pages";
/// it does so by `madvise(MADV_DONTNEED)` on free pages inside a heap as well as by shrinking each
/// heap's top. Its argument, 0 here, is the free space left at the top of the main heap; its
/// return value only says whether any memory was released, so it is not read.
///
/// Why this and not a glibc setting: `glibc.malloc.arena_max=1` also holds the pair at its larger
/// test's peak, but puts every allocation of the tests that run at once behind one lock; a fixed
/// `glibc.malloc.mmap_threshold` or `glibc.malloc.trim_threshold` (either one turns off glibc's
/// moving mmap threshold) made a 64,000-deep l01_26 test 6 times slower (see
/// `zed_meter_settings::GLIBC_TUNABLES`).
///
/// Cost: one walk of the free chunks of every arena and a system call per run of free pages, once
/// per test; never inside a measured run, since a thread the main thread starts is not in one (a
/// run starts on a test's thread or below it). Thread safety: glibc's `malloc_trim` takes each
/// arena's lock while it trims it, as `malloc` and `free` do, so other tests may allocate
/// meanwhile. Blocks of the metered heap (module `meter`) are not the C library's and are not
/// touched; a metered heap unmaps its own spans when its run ends.
///
/// Test: `a_test_gives_back_what_it_freed_when_it_ends` in tests/zed_alloc_count.rs.
fn release_free_memory() {
    #[cfg(target_env = "gnu")]
    #[expect(unsafe_code, reason = "calling the C library's malloc_trim")]
    // SAFETY: `malloc_trim` takes a size and frees only pages of free chunks of the C library's
    // own arenas, each under its arena's lock; it reads or writes no memory the caller owns.
    unsafe {
        libc::malloc_trim(0);
    }
}
