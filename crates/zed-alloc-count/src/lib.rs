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
//! serve the C library's own allocations. A binary whose std is a shared library and which links
//! no other workspace dylib (this crate's own tests) still sends std's allocations past the
//! counting allocator (FAIL-std-allocations-uncounted).
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
#[cfg(any(target_os = "macos", windows))]
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
            count(local, bytes);
            track(local, bytes, freed);
        });
    }
    block
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
    if in_run { metered(run) } else { run() }
}

/// The meter's `malloc` in this crate's test binary, which the tests of [`metered`] need.
#[cfg(test)]
#[expect(unsafe_code, reason = "defining the C library's allocation functions")]
mod entry_points {
    crate::meter_entry_points!();
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(target_os = "linux")]
    use meter::ours;
    use std::hint::black_box;

    /// The bytes `f` allocates on this thread and the threads it starts.
    fn bytes_of(f: impl FnOnce()) -> u64 {
        let start = allocated();
        f();
        allocated() - start
    }

    #[test]
    fn a_block_counts_its_size_and_a_grown_block_its_new_size() {
        assert_eq!(bytes_of(|| drop(black_box(vec![0u8; 1000]))), 1000);
        assert_eq!(
            bytes_of(|| drop(black_box(Vec::<u64>::with_capacity(10)))),
            80
        );
        let grown = bytes_of(|| {
            let mut v = Vec::<u8>::with_capacity(100);
            v.reserve_exact(300);
            black_box(v);
        });
        assert_eq!(grown, 100 + 300);
    }

    #[test]
    fn a_refused_request_counts_nothing() {
        // Two requests near `isize::MAX` bytes would overflow the count if they were counted.
        for _ in 0..2 {
            let asked = bytes_of(|| {
                assert!(
                    Vec::<u8>::new()
                        .try_reserve_exact(isize::MAX as usize)
                        .is_err()
                );
            });
            assert_eq!(asked, 0);
        }
    }

    #[test]
    fn freeing_counts_nothing() {
        let v = black_box(vec![1u8; 4096]);
        assert_eq!(bytes_of(|| drop(v)), 0);
    }

    #[test]
    fn live_bytes_count_what_is_kept_and_the_peak_counts_what_was_held_at_once() {
        let (kept, l) = live(|| {
            drop(black_box(vec![0u8; 5000]));
            black_box(vec![0u8; 1000])
        });
        assert_eq!(
            l,
            Live {
                net: 1000,
                peak: 5000
            }
        );
        let (_, l) = live(|| drop(kept));
        assert_eq!(
            l,
            Live {
                net: -1000,
                peak: 0
            }
        );
        let (grown, l) = live(|| {
            let mut v = Vec::<u8>::with_capacity(100);
            v.reserve_exact(300);
            black_box(v)
        });
        assert_eq!(l.net, 300);
        assert_eq!(grown.capacity(), 300);
    }

    #[test]
    fn a_measurement_inside_another_adds_to_it() {
        let ((inner, keep), outer) = live(|| {
            let a = black_box(vec![0u8; 100]);
            let (b, inner) = live(|| {
                drop(black_box(vec![0u8; 700]));
                black_box(vec![0u8; 200])
            });
            (inner, (a, b))
        });
        assert_eq!(
            inner,
            Live {
                net: 200,
                peak: 700
            }
        );
        assert_eq!(
            outer,
            Live {
                net: 300,
                peak: 800
            }
        );
        drop(keep);
        // Off again: a free outside any measurement changes nothing.
        assert_eq!(live(|| ()).1, Live { net: 0, peak: 0 });
    }

    #[test]
    fn a_measurement_that_panics_leaves_none_running() {
        let caught = std::panic::catch_unwind(|| live(|| panic!("inside")));
        assert!(caught.is_err());
        assert!(!LOCAL.with(|local| local.on.get()));
    }

    #[test]
    fn a_measurement_counts_no_other_thread() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
        // Another thread allocates and frees all through the measurement; the measurement
        // waits until it has done so 100 times, and still sees only its own blocks.
        let (stop, done) = (
            Arc::new(AtomicBool::new(false)),
            Arc::new(AtomicU64::new(0)),
        );
        let other = {
            let (stop, done) = (Arc::clone(&stop), Arc::clone(&done));
            std::thread::spawn(move || {
                let mut kept = Vec::new();
                while !stop.load(Ordering::Relaxed) {
                    kept.push(black_box(vec![0u8; 4096]));
                    if kept.len() == 8 {
                        kept.clear();
                    }
                    done.fetch_add(1, Ordering::Relaxed);
                }
            })
        };
        let (kept, l) = live(|| {
            let start = done.load(Ordering::Relaxed);
            drop(black_box(vec![0u8; 64]));
            while done.load(Ordering::Relaxed) < start + 100 {
                std::hint::spin_loop();
            }
            black_box(vec![0u8; 10])
        });
        stop.store(true, Ordering::Relaxed);
        other.join().unwrap();
        drop(kept);
        assert_eq!(l, Live { net: 10, peak: 64 });
    }

    // Off Linux the count is of the whole process, which other threads add to.
    #[cfg(target_os = "linux")]
    #[test]
    fn other_threads_do_not_change_this_threads_count() {
        let stop = std::sync::atomic::AtomicBool::new(false);
        std::thread::scope(|s| {
            // Four threads beside the measured one, as tests running beside it are: none of them
            // started by it.
            for _ in 0..4 {
                s.spawn(|| {
                    while !stop.load(Relaxed) {
                        black_box(vec![0u8; 64]);
                    }
                });
            }
            let measured = s.spawn(|| {
                (0..100)
                    .map(|_| bytes_of(|| drop(black_box(vec![0u8; 512]))))
                    .collect::<Vec<_>>()
            });
            let bytes = measured.join().unwrap();
            stop.store(true, Relaxed);
            assert_eq!(bytes, vec![512; 100]);
        });
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn a_thread_counts_in_the_count_of_the_thread_that_started_it() {
        let mut child = 0;
        let mut grandchild = 0;
        let all = bytes_of(|| {
            std::thread::spawn(|| {
                let start = allocated();
                let inner = std::thread::spawn(|| bytes_of(|| drop(black_box(vec![0u8; 4096]))));
                let inner = inner.join().unwrap();
                (allocated() - start, inner)
            })
            .join()
            .map(|(c, g)| (child, grandchild) = (c, g))
            .unwrap()
        });
        assert_eq!(grandchild, 4096);
        // The child's count holds the grandchild's block and what starting it allocated.
        assert!(child >= 4096, "{child}");
        assert!(all >= child, "{all} {child}");
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[expect(
        unsafe_code,
        reason = "starting a thread by pthread_create itself, as C code does"
    )]
    fn a_thread_started_by_a_direct_call_of_pthread_create_is_counted() {
        extern "C" fn run(_: *mut c_void) -> *mut c_void {
            black_box(vec![0u8; 3000]);
            std::ptr::null_mut()
        }
        let bytes = bytes_of(|| {
            let mut thread = 0;
            // SAFETY: a fresh `pthread_t` to fill, no attributes, and a routine that takes no
            // argument; the thread is joined at once.
            unsafe {
                assert_eq!(
                    pthread_create(&mut thread, std::ptr::null(), run, std::ptr::null_mut()),
                    0
                );
                assert_eq!(libc::pthread_join(thread, std::ptr::null_mut()), 0);
            }
        });
        assert!(bytes >= 3000, "{bytes}");
    }

    /// A fixed workload of every kind of request: 100 blocks of 1 to 100 bytes, all held at
    /// once (`alloc`); 100 zeroed blocks of 10 to 1,000 bytes, each freed at once
    /// (`alloc_zeroed`); and a vector of 16 bytes grown in place or by a copy to 64, 256 and
    /// 1,024 bytes (`realloc`).
    fn workload() {
        let held: Vec<Box<[u8]>> = (1..=100u8)
            .map(|n| black_box(vec![n; usize::from(n)]).into_boxed_slice())
            .collect();
        drop(black_box(held));
        for n in 1..=100 {
            drop(black_box(vec![0u8; 10 * n]));
        }
        let mut v = Vec::<u8>::with_capacity(16);
        for size in [64, 256, 1024] {
            v.reserve_exact(size);
            assert_eq!(v.capacity(), size);
        }
        drop(black_box(v));
    }

    /// The bytes [`workload`] allocates: its blocks, the vector of 100 boxes that holds the
    /// first ones (16 bytes a box), and the four sizes of the grown vector.
    const WORKLOAD_BYTES: u64 = 5050 + 100 * 16 + 10 * 5050 + 16 + 64 + 256 + 1024;

    /// The most bytes [`workload`] holds at once: the first 100 blocks and the vector of boxes.
    const WORKLOAD_PEAK: u64 = 5050 + 100 * 16;

    #[test]
    fn a_fixed_workload_counts_its_bytes_exactly() {
        for _ in 0..3 {
            assert_eq!(bytes_of(workload), WORKLOAD_BYTES);
            let ((), l) = live(workload);
            assert_eq!(
                l,
                Live {
                    net: 0,
                    peak: WORKLOAD_PEAK
                }
            );
        }
    }

    // Off Linux the count is of the whole process, which other threads add to.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_fixed_workload_counts_its_bytes_exactly_on_each_of_many_threads() {
        // Eight threads run the workload at once, ten times each, each measured on its own
        // thread; the thread that started them counts all of their bytes and their starts.
        let threads = 8;
        let mut each = Vec::new();
        let all = bytes_of(|| {
            std::thread::scope(|s| {
                let runs: Vec<_> = (0..threads)
                    .map(|_| {
                        s.spawn(|| {
                            (0..10)
                                .map(|_| (bytes_of(workload), live(workload).1))
                                .collect::<Vec<_>>()
                        })
                    })
                    .collect();
                each = runs.into_iter().map(|r| r.join().unwrap()).collect();
            });
        });
        for runs in &each {
            for &(bytes, l) in runs {
                assert_eq!(bytes, WORKLOAD_BYTES);
                assert_eq!(
                    l,
                    Live {
                        net: 0,
                        peak: WORKLOAD_PEAK
                    }
                );
            }
        }
        assert!(all >= threads * 20 * WORKLOAD_BYTES, "{all}");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn a_fixed_workload_counts_the_same_bytes_in_a_metered_run() {
        assert_eq!(metered(|| bytes_of(workload)), WORKLOAD_BYTES);
        assert_eq!(
            metered(|| live(workload).1),
            Live {
                net: 0,
                peak: WORKLOAD_PEAK
            }
        );
    }

    /// The layouts the metered heap's tests ask for: each class's edges, sizes past a span, and
    /// alignments from 1 to a page.
    #[cfg(target_os = "linux")]
    fn layouts() -> Vec<Layout> {
        let sizes = [
            1,
            15,
            16,
            17,
            64,
            65,
            80,
            81,
            127,
            128,
            129,
            4095,
            4096,
            100_000,
            meter::SPAN - 1,
            meter::SPAN,
            3 * meter::SPAN + 5,
        ];
        let aligns = [1, 8, 16, 32, 64, 4096];
        sizes
            .iter()
            .flat_map(|&s| aligns.map(|a| Layout::from_size_align(s, a).unwrap()))
            .collect()
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[expect(unsafe_code, reason = "calling the allocator by hand")]
    fn a_metered_run_gives_distinct_aligned_blocks_of_its_own_that_hold_what_is_written() {
        metered(|| {
            let mut blocks = Vec::new();
            for layout in layouts().into_iter().cycle().take(3 * layouts().len()) {
                // SAFETY: every layout has a size that is not 0.
                let block = unsafe { COUNTING.alloc(layout) };
                assert!(!block.is_null(), "{layout:?}");
                assert!(ours(block), "{layout:?}");
                assert_eq!(block as usize % layout.align(), 0, "{layout:?}");
                // SAFETY: the block is `layout.size()` bytes long.
                unsafe { block.write_bytes(blocks.len() as u8, layout.size()) };
                blocks.push((block, layout));
            }
            let mut ranges: Vec<_> = blocks
                .iter()
                .map(|&(b, l)| (b as usize, b as usize + l.size()))
                .collect();
            ranges.sort_unstable();
            assert!(
                ranges.windows(2).all(|w| w[0].1 <= w[1].0),
                "blocks overlap"
            );
            for (i, &(block, layout)) in blocks.iter().enumerate() {
                // SAFETY: the block is live and `layout.size()` bytes long.
                let bytes = unsafe { std::slice::from_raw_parts(block, layout.size()) };
                assert!(bytes.iter().all(|&b| b == i as u8), "{layout:?}");
                // SAFETY: allocated just above with `layout`.
                unsafe { COUNTING.dealloc(block, layout) };
            }
        });
    }

    /// Where a fixed metered run places its blocks: for each block, the order in which the run
    /// first used its span, and its offset in the span. Spans start at multiples of
    /// [`meter::SPAN`] (the reservation is aligned to it), and every block here is smaller.
    #[cfg(target_os = "linux")]
    #[expect(unsafe_code, reason = "calling the allocator by hand")]
    fn placements() -> Vec<(usize, usize)> {
        metered(|| {
            let mut spans = Vec::new();
            let mut place = |b: *mut u8| {
                let span = b as usize / meter::SPAN;
                let i = spans.iter().position(|&s| s == span).unwrap_or_else(|| {
                    spans.push(span);
                    spans.len() - 1
                });
                (i, b as usize % meter::SPAN)
            };
            let mut out = Vec::new();
            let mut live = Vec::new();
            for i in 0..3000usize {
                let layout = Layout::from_size_align(1 + i * 37 % 5000, 1 << (i % 7)).unwrap();
                // SAFETY: a size that is not 0.
                let b = unsafe { COUNTING.alloc(layout) };
                out.push(place(b));
                live.push((b, layout));
            }
            for i in 0..1500usize {
                let (b, layout) = live[i * 7919 % 3000];
                if !b.is_null() {
                    // SAFETY: allocated above with `layout` and not yet freed.
                    unsafe { COUNTING.dealloc(b, layout) };
                    live[i * 7919 % 3000].0 = std::ptr::null_mut();
                }
            }
            for (b, layout) in &mut live {
                if !b.is_null() {
                    // SAFETY: live, allocated with `layout`; the new size is not 0.
                    *b = unsafe { COUNTING.realloc(*b, *layout, layout.size() * 3) };
                    *layout = Layout::from_size_align(layout.size() * 3, layout.align()).unwrap();
                    out.push(place(*b));
                }
            }
            for (b, layout) in live {
                if !b.is_null() {
                    // SAFETY: live, allocated or grown with `layout`.
                    unsafe { COUNTING.dealloc(b, layout) };
                }
            }
            out
        })
    }

    /// A metered run's heap follows the run's own calls alone, so the instructions each call
    /// spends do too: the same run places every block the same way whatever came before it, a
    /// churned glibc heap, earlier metered runs, and another metered run holding spans at the
    /// same time (TEST-meter-allocator-bias). This is the exact form of what
    /// `zed_tests::scaling_tests::the_instructions_of_a_run_repeat` sees through the counter.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_metered_run_places_its_blocks_the_same_way_whatever_came_before() {
        let first = placements();
        let kept: Vec<Vec<u8>> = (0..2000).map(|i| vec![1; 1 + i * 13 % 900]).collect();
        let held = std::sync::Barrier::new(2);
        let done = std::sync::Barrier::new(2);
        std::thread::scope(|s| {
            s.spawn(|| {
                metered(|| {
                    let mine: Vec<Vec<u64>> = (0..5000).map(|i| vec![2; 1 + i % 3000]).collect();
                    held.wait();
                    done.wait();
                    black_box(mine);
                })
            });
            held.wait();
            for _ in 0..3 {
                assert_eq!(placements(), first);
            }
            done.wait();
        });
        black_box(kept);
        assert_eq!(placements(), first);
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[expect(unsafe_code, reason = "calling the allocator by hand")]
    fn a_block_freed_in_a_metered_run_serves_the_next_request_of_its_class_zeroed_if_asked() {
        metered(|| {
            for layout in layouts() {
                // SAFETY: a size that is not 0, and blocks freed with the layout they came with.
                unsafe {
                    let a = COUNTING.alloc(layout);
                    a.write_bytes(7, layout.size());
                    COUNTING.dealloc(a, layout);
                    let b = COUNTING.alloc_zeroed(layout);
                    assert_eq!(a, b, "{layout:?}");
                    let bytes = std::slice::from_raw_parts(b, layout.size());
                    assert!(bytes.iter().all(|&x| x == 0), "{layout:?}");
                    COUNTING.dealloc(b, layout);
                }
            }
        });
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn a_metered_block_grown_in_its_class_stays_and_one_grown_past_it_moves_with_its_bytes() {
        metered(|| {
            let mut v: Vec<u8> = Vec::with_capacity(65);
            let at = v.as_ptr();
            v.extend(0..65);
            v.reserve_exact(80 - 65);
            assert_eq!(v.as_ptr(), at, "65 and 80 bytes are one class");
            v.reserve_exact(1000);
            assert_ne!(v.as_ptr(), at);
            assert!(ours(v.as_ptr().cast_mut()));
            assert!(v.iter().copied().eq(0..65));
            v.shrink_to_fit();
            assert!(v.iter().copied().eq(0..65));
        });
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[expect(unsafe_code, reason = "calling the allocator by hand")]
    fn blocks_outside_a_metered_run_are_the_c_librarys_and_a_metered_block_grown_after_moves_out() {
        let mut outside = vec![1u8; 100];
        assert!(!ours(outside.as_mut_ptr()));
        let mut inside = metered(|| {
            outside.reserve_exact(100_000);
            assert!(
                !ours(outside.as_mut_ptr()),
                "grown inside a run: still the C library's"
            );
            // Aligned to half a span: the C library's.
            let big = Layout::from_size_align(16, meter::SPAN / 2).unwrap();
            // SAFETY: a size that is not 0, freed with its layout.
            unsafe {
                let b = COUNTING.alloc(big);
                assert!(!b.is_null() && !ours(b));
                COUNTING.dealloc(b, big);
            }
            vec![2u8; 5000]
        });
        assert!(ours(inside.as_mut_ptr()));
        inside.reserve_exact(50_000);
        assert!(
            !ours(inside.as_mut_ptr()),
            "grown after the run: moved out of its heap"
        );
        assert!(outside[..100].iter().all(|&b| b == 1) && inside.iter().all(|&b| b == 2));
    }

    /// Whether the page at `at` is mapped readable, by `/proc/self/maps`.
    #[cfg(target_os = "linux")]
    fn readable(at: usize) -> bool {
        let maps = std::fs::read_to_string("/proc/self/maps").unwrap();
        maps.lines().any(|line| {
            let mut fields = line.split_whitespace();
            let range = fields.next().unwrap();
            let perms = fields.next().unwrap();
            let (lo, hi) = range.split_once('-').unwrap();
            let lo = usize::from_str_radix(lo, 16).unwrap();
            let hi = usize::from_str_radix(hi, 16).unwrap();
            (lo..hi).contains(&at) && perms.starts_with('r')
        })
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn a_span_is_unmapped_once_its_heap_has_ended_and_its_last_block_is_freed_anywhere() {
        // A span of its own (larger than `SPAN`), so no other test's block shares it.
        let kept = metered(|| vec![3u8; 2 * meter::SPAN]);
        let at = kept.as_ptr() as usize;
        assert!(readable(at));
        let kept = std::thread::spawn(move || {
            assert!(
                readable(at),
                "the heap has ended but one block of the span is out"
            );
            kept
        })
        .join()
        .unwrap();
        std::thread::spawn(move || drop(kept)).join().unwrap();
        assert!(
            !readable(at),
            "the last block freed on another thread unmaps its span"
        );
        let at = metered(|| {
            let v = vec![4u8; 2 * meter::SPAN];
            let at = v.as_ptr() as usize;
            drop(v);
            at
        });
        assert!(
            !readable(at),
            "a span whose blocks were all freed is unmapped as its heap ends"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn threads_started_in_a_metered_run_have_heaps_of_their_own_and_threads_outside_none() {
        let (theirs, mine) = metered(|| {
            let mut mine = vec![0u8; 100];
            let theirs = std::thread::spawn(|| {
                let mut v = vec![0u8; 100];
                assert!(ours(v.as_mut_ptr()));
                v
            })
            .join()
            .unwrap();
            mine.push(1);
            (theirs, mine)
        });
        assert!(ours(theirs.as_ptr().cast_mut()) && ours(mine.as_ptr().cast_mut()));
        assert_ne!(
            meter::owner(theirs.as_ptr().cast_mut()),
            meter::owner(mine.as_ptr().cast_mut())
        );
        let mut outside = std::thread::spawn(|| vec![0u8; 100]).join().unwrap();
        assert!(!ours(outside.as_mut_ptr()));
    }
}
