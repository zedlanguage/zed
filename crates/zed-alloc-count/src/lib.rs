//! The global allocator of the test binaries: the system allocator, counting the bytes each
//! thread allocates, for the second measure of the scaling tests (`zed_tests::scaling`).
//!
//! A block of `n` bytes counts `n` when it is allocated, and a block grown or shrunk in place or
//! by a copy counts its new size, which is what a copy writes. A request the system refuses writes
//! nothing and counts nothing, so a probe such as `try_reserve` of an impossible size leaves the
//! count as it was. Freeing counts nothing. The count is kept per thread, so tests that run beside
//! a measured one in the same process do not change it, whatever the scheduling. A thread a
//! measured run starts counts on its own; the run adds that count to its own with [`add`] when
//! the thread ends, as `zed_tests::deep` and `zed_tests::scaling` do.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

thread_local! {
    /// The bytes this thread has allocated, with those [`add`] gave it. A `const` cell of a type
    /// with no destructor, so reading it allocates nothing and works while the thread ends.
    static BYTES: Cell<u64> = const { Cell::new(0) };
}

/// The bytes this thread has allocated so far, with those given to it by [`add`].
pub fn allocated() -> u64 {
    BYTES.get()
}

/// Gives this thread's count the `bytes` a thread it started allocated.
pub fn add(bytes: u64) {
    BYTES.set(BYTES.get() + bytes);
}

/// Adds `bytes` to this thread's count, from inside the allocator, when the system gave the block
/// (`block` is not null) and returns `block`.
fn count(block: *mut u8, bytes: usize) -> *mut u8 {
    if !block.is_null() {
        BYTES.set(BYTES.get() + bytes as u64);
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
// `GlobalAlloc`; counting reads and writes a thread-local `Cell` and never allocates.
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::hint::black_box;

    /// The bytes `f` allocates on this thread.
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
    fn other_threads_do_not_change_this_threads_count() {
        let stop = std::sync::atomic::AtomicBool::new(false);
        std::thread::scope(|s| {
            for _ in 0..4 {
                s.spawn(|| {
                    while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                        black_box(vec![0u8; 64]);
                    }
                });
            }
            for _ in 0..100 {
                assert_eq!(bytes_of(|| drop(black_box(vec![0u8; 512]))), 512);
            }
            stop.store(true, std::sync::atomic::Ordering::Relaxed);
        });
    }

    #[test]
    fn a_thread_counts_on_its_own_until_its_count_is_added() {
        let child = std::thread::spawn(|| bytes_of(|| drop(black_box(vec![0u8; 2048]))));
        let child = child.join().unwrap();
        assert_eq!(child, 2048);
        assert_eq!(bytes_of(|| add(child)), child);
    }
}
