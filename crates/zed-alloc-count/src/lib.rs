//! The global allocator of the test binaries: the system allocator, counting the bytes each
//! thread allocates, for the second measure of the scaling tests (`zed_tests::scaling`).
//!
//! A block of `n` bytes counts `n` when it is allocated, and a block grown or shrunk in place or
//! by a copy counts its new size, which is what a copy writes. A request the system refuses writes
//! nothing and counts nothing, so a probe such as `try_reserve` of an impossible size leaves the
//! count as it was. Freeing counts nothing.
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
//! All of the above is the Linux build. On every other system there is one count, of the bytes
//! every thread of the process allocates: Windows has no `pthread_create` to stand in for, and on
//! macOS the counters of work (module [`os`]) are of the whole process too, so the scaling tests
//! there run one test at a time and a count of the whole process is what they need. The macOS and
//! Windows builds are compiled here (on Linux, by `cargo check --target`) but have not been run.

use std::alloc::{GlobalAlloc, Layout, System};
#[cfg(target_os = "linux")]
use std::cell::Cell;
#[cfg(target_os = "linux")]
use std::ffi::{c_int, c_void};
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
#[cfg(target_os = "linux")]
use std::sync::{Arc, OnceLock};

#[cfg(any(target_os = "macos", windows))]
pub mod os;

#[cfg(target_os = "linux")]
/// The bytes a thread started by `pthread_create` and the threads it starts have allocated.
struct Count {
    bytes: AtomicU64,
    /// The count of the thread that started this one, if that thread has one.
    parent: Option<Arc<Count>>,
}

#[cfg(target_os = "linux")]
thread_local! {
    /// This thread's [`Count`], or null on a thread not started by `pthread_create`. The `Arc`
    /// that keeps it lives in [`start`] on this thread's stack, and is dropped only after this
    /// is set back to null. A `const` cell of a type with no destructor, so reading it allocates
    /// nothing and works while the thread ends.
    static COUNT: Cell<*const Count> = const { Cell::new(std::ptr::null()) };
    /// The bytes allocated on a thread with no [`Count`]: the main thread, and any thread after
    /// [`start`] has set its [`COUNT`] back to null while it ends.
    static OWN: Cell<u64> = const { Cell::new(0) };
}

#[cfg(target_os = "linux")]
/// This thread's [`Count`], if it has one.
fn this_count() -> Option<&'static Count> {
    let count = COUNT.get();
    #[expect(
        unsafe_code,
        reason = "the count is shared with the threads this one starts, which it must outlive"
    )]
    // SAFETY: `COUNT` is null or points into the `Arc` that `start` holds on this thread's stack
    // while it is set (see `COUNT`). The reference does not leave the caller's use on this
    // thread, which happens while that `Arc` lives.
    unsafe {
        count.as_ref()
    }
}

#[cfg(target_os = "linux")]
/// The bytes this thread and the threads it started have allocated so far.
pub fn allocated() -> u64 {
    match this_count() {
        Some(count) => count.bytes.load(Relaxed),
        None => OWN.get(),
    }
}

#[cfg(target_os = "linux")]
/// Adds `bytes` to this thread's count and its parents', from inside the allocator, when the
/// system gave the block (`block` is not null) and returns `block`. The walk is as long as the
/// chain of threads that started this one, a handful in any test.
fn count(block: *mut u8, bytes: usize) -> *mut u8 {
    if !block.is_null() {
        let mut count = this_count();
        if count.is_none() {
            OWN.set(OWN.get() + bytes as u64);
        }
        while let Some(c) = count {
            c.bytes.fetch_add(bytes as u64, Relaxed);
            count = c.parent.as_deref();
        }
    }
    block
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

/// Adds `bytes` to the count of the process, from inside the allocator, when the system gave the
/// block (`block` is not null), and returns `block`.
#[cfg(not(target_os = "linux"))]
fn count(block: *mut u8, bytes: usize) -> *mut u8 {
    if !block.is_null() {
        ALL.fetch_add(bytes as u64, Relaxed);
    }
    block
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
        count(unsafe { System.alloc(layout) }, layout.size())
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: as in `alloc`.
        count(unsafe { System.alloc_zeroed(layout) }, layout.size())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` and `layout` come from this allocator, which is `System`.
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: as in `dealloc`; the caller's guarantees about `new_size` are passed on.
        count(unsafe { System.realloc(ptr, layout, new_size) }, new_size)
    }
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
/// What [`start`] needs: the thread's own routine and argument, and the count of its parent.
struct Start {
    routine: Routine,
    arg: *mut c_void,
    parent: Option<Arc<Count>>,
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
    let parent = this_count().map(|count| {
        // SAFETY: `count` points into the `Arc` that `start` holds on this thread's stack (see
        // `COUNT`), so the `Arc` has a strong count while this adds one more for the new thread.
        unsafe {
            let ptr: *const Count = count;
            Arc::increment_strong_count(ptr);
            Arc::from_raw(ptr)
        }
    });
    let start_arg = Box::into_raw(Box::new(Start {
        routine,
        arg,
        parent,
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
/// thread that ends by `pthread_exit` keeps its count, which is never dropped; std ends none
/// that way.
extern "C" fn start(start_arg: *mut c_void) -> *mut c_void {
    #[expect(unsafe_code, reason = "taking back the argument pthread_create boxed")]
    // SAFETY: `start_arg` is the `Box<Start>` `pthread_create` made for this thread alone.
    let Start {
        routine,
        arg,
        parent,
    } = *unsafe { Box::from_raw(start_arg.cast::<Start>()) };
    let count = Arc::new(Count {
        bytes: AtomicU64::new(0),
        parent,
    });
    COUNT.set(Arc::as_ptr(&count));
    let out = routine(arg);
    COUNT.set(std::ptr::null());
    drop(count);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
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
}
