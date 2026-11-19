//! The allocator of a metered run (TEST-meter-allocator-bias): a heap of its own for each thread,
//! whose instructions on each call depend only on that thread's own calls, and not on the
//! addresses the kernel gives, the threads before it, the other threads running, or the order
//! in which a hash table frees its blocks.
//!
//! glibc's malloc does not have that property. With its per-thread cache, the instructions a run
//! spends in malloc depend on the threads before it (a difference of two counts was up to 1.5
//! times its size: SCALE-casts-spread); without the cache (`glibc.malloc.tcache_count=0`, the
//! meter's setting until this row), each call costs more as the heap's bins fill, which adds a
//! cost linear in the number of allocations to every run and so lowers the ratio of a
//! superlinear one (TEST-scaling-direct-run-verdict measured -0.82% on average and -17.6% at
//! worst against an allocator of fixed cost per call). Here every call takes one of a few fixed
//! paths, and which one it takes is decided by the thread's own sequence of calls alone:
//!
//! - A block is of a size class: sizes up to 64 bytes round up to a multiple of 16, larger ones
//!   to one of the four sizes `2^k (1 + j/4)`, `j` in 1..=4, that follow the power of two below.
//!   A request aligned to more than 16 bytes takes the power of two at or above its size and
//!   alignment, placed at a multiple of it (of [`SPAN`] / 4 at most). A request aligned to
//!   [`SPAN`] / 2 or more goes to the C library.
//! - A thread's heap ([`Heap`]) keeps, for each class, a list of free blocks and a span it cuts
//!   new blocks from. An allocation takes the first block of its class's list, or else the next
//!   block of its class's span, or else a new span. Freeing a block of the thread's own heap puts
//!   it first on its list. No block is split or merged, so no call walks anything.
//! - A span is a run of address space aligned to [`SPAN`], at least [`SPAN`] long, holding blocks
//!   of one class, taken from one reservation of the process by a single `fetch_add` and mapped
//!   by `mmap`. Its first 64 bytes hold a `Span` header: the heap that owns it, its class, the
//!   blocks the owner holds, and the frees of other threads. Every block starts inside the first
//!   [`SPAN`] bytes of its span, so the header of a block is at the block's address rounded down
//!   to [`SPAN`], and `free`, which is not told the size, reads the class there.
//! - A block freed by another thread, or after its heap has ended, is not reused: the free takes
//!   one from the span's count of blocks owed to it, by one `fetch_sub`. When a heap ends, each of
//!   its spans adds the blocks still out (one `fetch_add`); a span whose count then reaches 0, or
//!   later reaches 0 by a free, is unmapped (mapped again with no access, so that its addresses
//!   stay reserved and are never given out twice).
//!
//! There is no lock and no loop that retries: each atomic operation is one instruction whatever
//! the other threads do, so the counts of a run that starts threads repeat too. A spin lock, as
//! the allocator TEST-scaling-direct-run-verdict compared against had, adds the instructions of
//! each turn it spins, which depend on the other threads.
//!
//! The heap sits under the C library's allocation functions (`malloc`, `free` and the rest),
//! which a binary that meters defines by [`meter_entry_points`](crate::meter_entry_points), and
//! not under the Rust allocator: the C library's own allocations (a directory stream, a thread's
//! TLS) then come from it too, and so do those of a binary whose std, linked as a shared library,
//! allocates through its own copy of the Rust allocator. Only the threads of a measured run use
//! the heap (`run`); every other thread, and every binary that does not define the entry
//! points (`zedc` and every compiled program among them), uses the C library's allocator. A
//! block is this allocator's when its address lies in the reservation, which is made only by
//! `ready`, so in a binary that defines the entry points a call outside a run adds a read of
//! one thread-local (allocations) or one atomic (frees) to the C library's work.
//!
//! Complexity tradeoff: glibc's malloc, with its cache off, is O(1) amortized per call but its
//! cost per call grows with the bins it searches (measured above). This allocator is O(1) per
//! call in the worst case, and the only part linear in anything is the end of a heap, O(spans).
//! What it gives up is memory: a freed block is reused only by a request of its own class and
//! thread, and blocks freed by another thread wait for their span's end, so a run that frees
//! blocks of one class and then allocates another holds both; each class a heap uses holds a
//! span; a heap lasts one measured run. COMPLEXITY.md row TEST-meter-allocator-bias. Tests: the
//! `metered` tests of this crate, `scaling_tests::the_instructions_of_a_run_repeat` in
//! `zed_tests`, and the scaling test `scaling_tests::bench::a_metered_heap_is_linear`.

use std::cell::Cell;
use std::ffi::{c_int, c_void};
use std::ptr::null_mut;
use std::sync::Once;
use std::sync::atomic::{
    AtomicI64, AtomicU64, AtomicUsize,
    Ordering::{AcqRel, Acquire, Relaxed, Release},
};

/// The alignment of a span, and the least length of one. Every block starts in the first `SPAN`
/// bytes of its span (see `Heap::take`). It sets how often a heap asks the kernel for memory,
/// work the meter does not count (it counts instructions in user mode), and how much a heap that
/// allocates little holds; no call's count of instructions depends on it except through which
/// call takes a new span, which the thread's own sequence of calls decides.
pub const SPAN: usize = 4 << 20;

/// The bytes of a span before its first block: the [`Span`] header, padded to a cache line.
const HEADER: usize = 64;

/// The address space of the reservation, 64 TiB, half of what x86-64 gives a process. Spans are
/// never given out twice, so this bounds the address space all metered runs of a process take
/// (spans, not bytes live); a request beyond it is refused as the system refuses one. Not proved
/// to be enough for a process that runs any number of metered runs: COMPLEXITY.md row
/// TEST-meter-allocator-bias bounds one run's share (about 370 runs of the largest bench).
/// That claim is about how many runs one process can meter, not about any answer
/// (PROOF-sweep-front-end): this allocator serves only metered test and bench processes, and
/// past the reservation a request is refused as the system refuses one, so a process that
/// meters too many runs stops on an allocation failure instead of giving a wrong count.
const RESERVED: usize = 1 << 46;

/// The size classes of requests aligned to 16 bytes or less: 4 up to 64 bytes, then 4 for each
/// power of two from `2^6` up to `2^62` (`isize::MAX` bounds a size).
const SIZES: usize = 4 + 57 * 4;

/// All classes: [`SIZES`], then one per power of two for requests aligned to more than 16 bytes.
const CLASSES: usize = SIZES + 64;

/// The header at the start of each span.
#[repr(C)]
struct Span {
    /// The id of the heap that owns the span ([`Heap::id`]).
    heap: u64,
    /// The class of the span's blocks, and their size.
    class: usize,
    size: usize,
    /// The bytes mapped, from the header on.
    len: usize,
    /// The blocks of this span the owning heap has given out and not had back, read and written
    /// by the owning thread alone while its heap lasts.
    held: i64,
    /// The blocks the span is owed, less those freed by other threads: at most 0 while the heap
    /// lasts, and the blocks still out once it has ended. The span is unmapped by whichever
    /// operation takes it to 0 after the heap has ended (see [`Heap::end`]).
    owed: AtomicI64,
    /// The next span of the same heap.
    next: *mut Span,
}

/// The heap of one thread's metered run.
pub struct Heap {
    /// This heap's id, never 0 and never given to another heap of the process.
    id: u64,
    /// Every span of this heap, linked by [`Span::next`].
    spans: *mut Span,
    /// For each class: the first free block (a free block holds the next one), the next byte of
    /// the class's current span, the end of that span, and the end of its first [`SPAN`] bytes,
    /// where a block may start (0 before the class has a span).
    lists: [*mut u8; CLASSES],
    bump: [usize; CLASSES],
    end: [usize; CLASSES],
    starts: [usize; CLASSES],
}

/// The start of the reservation, or 0 before [`ready`].
static BASE: AtomicUsize = AtomicUsize::new(0);

/// The next byte of the reservation not yet given to a span, counted in [`SPAN`]s. In `u64` and
/// in spans, so that no number of `fetch_add`s past the end can wrap: each adds at most
/// `RESERVED / SPAN = 2^24`, the check before it lets a thread add only while the count is at
/// most `2^24`, and Linux runs fewer than `2^22` threads (`PID_MAX_LIMIT`), so the count stays
/// below `2^24 · (2^22 + 1) < 2^47`.
static NEXT: AtomicU64 = AtomicU64::new(0);

/// The id of the next heap.
static HEAPS: AtomicU64 = AtomicU64::new(1);

thread_local! {
    /// The heap of the metered run this thread is in ([`run`]), or null. The heap lives on the
    /// stack of [`run`], which sets this back to null before it ends the heap. A constant with
    /// no destructor, so that reading it never allocates, even inside `malloc`.
    static HEAP: Cell<*mut Heap> = const { Cell::new(null_mut()) };
}

/// Whether this thread is in a metered run.
pub(crate) fn in_run() -> bool {
    !HEAP.get().is_null()
}

/// Runs `f` with a heap of its own for this thread ([`crate::metered`]); inside a run, runs `f`.
pub(crate) fn run<R>(f: impl FnOnce() -> R) -> R {
    if in_run() {
        return f();
    }
    ready();
    with_heap(f)
}

/// Runs `f` with a new heap for this thread, which is in no run; the reservation is made.
fn with_heap<R>(f: impl FnOnce() -> R) -> R {
    let mut heap = Heap::new();
    /// Takes the heap from this thread and ends it, when `f` returns or unwinds.
    struct End(*mut Heap);
    impl Drop for End {
        fn drop(&mut self) {
            HEAP.set(null_mut());
            #[expect(unsafe_code, reason = "the heap on the stack of `run`")]
            // SAFETY: the heap outlives this guard, which `run` drops first, and no other pointer
            // to it is used once the thread-local is null.
            unsafe {
                (*self.0).end();
            }
        }
    }
    let end = End(&raw mut heap);
    HEAP.set(end.0);
    let out = f();
    drop(end);
    out
}

/// Makes the reservation if it has not been made, and checks that `malloc` reaches this
/// allocator. A meter calls this before it counts, so that no count holds it.
pub(crate) fn ready() {
    static RESERVE: Once = Once::new();
    RESERVE.call_once(|| {
        let len = RESERVED + SPAN;
        #[expect(unsafe_code, reason = "reserving address space")]
        // SAFETY: a new private mapping with no access at an address the kernel picks touches no
        // memory this process uses.
        let at = unsafe {
            libc::mmap(
                null_mut(),
                len,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
                -1,
                0,
            )
        };
        assert!(
            at != libc::MAP_FAILED,
            "reserving {len} bytes of address space for the meter's allocator: {}",
            std::io::Error::last_os_error()
        );
        BASE.store((at as usize).next_multiple_of(SPAN), Release);
    });
    // After the reservation, and apart from it: the probe runs on a heap, whose spans need it.
    static CHECK: Once = Once::new();
    CHECK.call_once(|| {
        let reached = with_heap(|| {
            #[expect(unsafe_code, reason = "a probe of `malloc`")]
            // SAFETY: a block of one byte, freed at once.
            unsafe {
                let block = libc::malloc(1);
                let reached = ours(block.cast());
                libc::free(block);
                reached
            }
        });
        assert!(
            reached,
            "The meter's allocator is not this binary's `malloc`: add \
             `zed_alloc_count::meter_entry_points!();` to the binary's crate (TEST-meter-allocator-bias)."
        );
    });
}

/// Whether `block` is a block of this allocator: whether it lies in the reservation.
pub fn ours(block: *mut u8) -> bool {
    let base = BASE.load(Acquire);
    base != 0 && (block as usize).wrapping_sub(base) < RESERVED
}

/// The class of a request of `size` bytes aligned to `align` (a power of two), with the size of
/// its blocks and the alignment they are placed at; `None` for a request aligned to `SPAN / 2`
/// or more, which goes to the C library, and for a size no block can have.
fn class(size: usize, align: usize) -> Option<(usize, usize, usize)> {
    let size = size.max(1);
    if size > isize::MAX as usize {
        return None;
    }
    if align <= 16 {
        if size <= 64 {
            let i = size.div_ceil(16) - 1;
            return Some((i, 16 * (i + 1), 16));
        }
        // `size` in (2^k, 2^(k+1)], k >= 6; `size <= isize::MAX` gives k <= 62.
        let k = (usize::BITS - 1 - (size - 1).leading_zeros()) as usize;
        let step = 1usize << (k - 2);
        let j = (size - (1 << k)).div_ceil(step);
        return Some((4 + (k - 6) * 4 + (j - 1), (1 << k) + j * step, 16));
    }
    if align >= SPAN / 2 {
        return None;
    }
    // Placed at a multiple of `p`, up to `SPAN / 4`, the largest power of two below `SPAN / 2`:
    // at least `align`, and small enough that the first block starts in its span's first `SPAN`
    // bytes (see `Heap::take`). `size <= isize::MAX` gives `p <= 2^63`.
    let p = size.max(align).next_power_of_two();
    Some((SIZES + p.trailing_zeros() as usize, p, p.min(SPAN / 4)))
}

impl Heap {
    /// A new heap, holding no span.
    fn new() -> Self {
        Self {
            id: HEAPS.fetch_add(1, Relaxed),
            spans: null_mut(),
            lists: [null_mut(); CLASSES],
            bump: [0; CLASSES],
            end: [0; CLASSES],
            starts: [0; CLASSES],
        }
    }

    /// A block of class `c`, of `size` bytes placed at a multiple of `align` (what [`class`]
    /// gives for `c`), or null when the system refuses one, and whether its bytes are zero: a
    /// block never given out before lies in memory the kernel mapped zeroed.
    fn alloc(&mut self, (c, size, align): (usize, usize, usize)) -> (*mut u8, bool) {
        let block = self.lists[c];
        if !block.is_null() {
            #[expect(unsafe_code, reason = "a free block holds the next one")]
            // SAFETY: `block` was put on this list by `free`, which wrote the old first block
            // into its first word; a block is at least 16 bytes, aligned to 16; its span is this
            // heap's, mapped while the heap lasts.
            unsafe {
                self.lists[c] = *block.cast::<*mut u8>();
                (*span_of(block)).held += 1;
            }
            return (block, false);
        }
        let start = self.bump[c];
        if start < self.starts[c] && size <= self.end[c] - start {
            self.bump[c] = start + size;
            #[expect(unsafe_code, reason = "the current span's header")]
            // SAFETY: `starts[c]` is not 0, so class `c` has a current span of this heap, mapped,
            // and `start` lies in its first `SPAN` bytes.
            unsafe {
                (*span_of(start as *mut u8)).held += 1;
            }
            return (start as *mut u8, true);
        }
        self.take(c, size, align)
    }

    /// A block of class `c` at the start of a new span, which becomes the class's current one.
    fn take(&mut self, c: usize, size: usize, align: usize) -> (*mut u8, bool) {
        // `align <= SPAN / 4`, so the block starts in the span's first `SPAN` bytes, and so do
        // the blocks after it while `bump < starts`; every block is a multiple of `align` from
        // the first, since `size` is (a multiple of 16, or `p >= align`).
        let offset = HEADER.next_multiple_of(align);
        let Some(len) = offset
            .checked_add(size)
            .and_then(|b| b.checked_next_multiple_of(SPAN))
            .filter(|&len| len <= RESERVED)
        else {
            return (null_mut(), false);
        };
        let spans = (len / SPAN) as u64;
        if NEXT.load(Relaxed) > (RESERVED / SPAN) as u64 {
            return (null_mut(), false);
        }
        let first = NEXT.fetch_add(spans, Relaxed);
        if first + spans > (RESERVED / SPAN) as u64 {
            return (null_mut(), false);
        }
        let at = BASE.load(Acquire) + first as usize * SPAN;
        #[expect(unsafe_code, reason = "mapping a span of the reservation")]
        // SAFETY: `[at, at + len)` lies in the reservation, and `NEXT` gave it to this call
        // alone, so no block lies in it; mapping it again replaces only reserved space.
        let mapped = unsafe {
            libc::mmap(
                at as *mut c_void,
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_FIXED,
                -1,
                0,
            )
        };
        if mapped == libc::MAP_FAILED {
            return (null_mut(), false);
        }
        let span = at as *mut Span;
        #[expect(unsafe_code, reason = "writing the header of a new span")]
        // SAFETY: the span is mapped, readable and writable, and aligned to `SPAN`.
        unsafe {
            span.write(Span {
                heap: self.id,
                class: c,
                size,
                len,
                held: 1,
                owed: AtomicI64::new(0),
                next: self.spans,
            });
        }
        self.spans = span;
        self.bump[c] = at + offset + size;
        self.end[c] = at + len;
        self.starts[c] = at + SPAN;
        ((at + offset) as *mut u8, true)
    }

    /// Frees `block`, a live block of this allocator, on the thread whose heap `heap` is (or
    /// null, on a thread outside a run).
    ///
    /// # Safety
    ///
    /// `block` is a live block of this allocator; `heap` is null or this thread's heap.
    #[expect(unsafe_code, reason = "a span header and the heap of this thread")]
    unsafe fn free(heap: *mut Self, block: *mut u8) {
        let span = span_of(block);
        // SAFETY: `block` is live, so its span is mapped (see `release`); `heap` is null or
        // this thread's heap, which only this thread reads or writes.
        unsafe {
            if let Some(heap) = heap.as_mut()
                && heap.id == (*span).heap
            {
                let c = (*span).class;
                *block.cast::<*mut u8>() = heap.lists[c];
                heap.lists[c] = block;
                (*span).held -= 1;
            } else if (*span).owed.fetch_sub(1, AcqRel) == 1 {
                release(span);
            }
        }
    }

    /// Ends the heap: each span adds the blocks still out to what it is owed, and a span owed
    /// none is unmapped. A block freed afterwards on this thread is freed as another thread's.
    fn end(&mut self) {
        let mut span = self.spans;
        while !span.is_null() {
            #[expect(unsafe_code, reason = "the spans of this heap")]
            // SAFETY: a span of a heap that has not ended is mapped. Until this call `owed` has
            // only been lowered (by `r` frees of other threads, so it is `-r <= 0`), and a free
            // unmaps a span only when it takes `owed` from 1 to 0. `held` counts the blocks given
            // out less those freed on this thread, so `held - r` blocks are still out, and that
            // is what `owed` holds after the addition: 0 unmaps the span here, and otherwise the
            // free of its last block out does.
            unsafe {
                let next = (*span).next;
                let held = (*span).held;
                if (*span).owed.fetch_add(held, AcqRel) + held == 0 {
                    release(span);
                }
                span = next;
            }
        }
        self.spans = null_mut();
        self.starts = [0; CLASSES];
    }
}

/// The header of the span `block` lies in.
fn span_of(block: *mut u8) -> *mut Span {
    ((block as usize) & !(SPAN - 1)) as *mut Span
}

/// The id of the heap that owns the span of `block`, a live block of this allocator, for the
/// crate's tests (`tests/zed_alloc_count.rs`).
#[doc(hidden)]
pub fn owner(block: *mut u8) -> u64 {
    #[expect(unsafe_code, reason = "a span header")]
    // SAFETY: a live block's span is mapped, and its header was written when it was taken.
    unsafe {
        (*span_of(block)).heap
    }
}

/// Unmaps `span`, mapping its addresses again with no access, so that they stay reserved and
/// are never given to a span again. A failure leaves the memory mapped, which is lost but harms
/// nothing, since no span is given those addresses again.
///
/// # Safety
///
/// No block of `span` is live and no thread reads its header again.
#[expect(unsafe_code, reason = "unmapping a span")]
unsafe fn release(span: *mut Span) {
    // SAFETY: the caller's guarantee; the range is the span's own.
    unsafe {
        let len = (*span).len;
        libc::mmap(
            span.cast(),
            len,
            libc::PROT_NONE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_FIXED | libc::MAP_NORESERVE,
            -1,
            0,
        );
    }
}

// The C library's own allocator, under the names it exports for programs that replace `malloc`.
#[expect(unsafe_code, reason = "declaring C functions")]
unsafe extern "C" {
    fn __libc_malloc(size: usize) -> *mut c_void;
    fn __libc_calloc(n: usize, size: usize) -> *mut c_void;
    fn __libc_realloc(block: *mut c_void, size: usize) -> *mut c_void;
    fn __libc_free(block: *mut c_void);
    fn __libc_memalign(align: usize, size: usize) -> *mut c_void;
}

/// Sets `errno` to `ENOMEM` and returns null, as the C library's allocator does on a refusal.
fn refused() -> *mut c_void {
    #[expect(unsafe_code, reason = "writing errno")]
    // SAFETY: `__errno_location` gives this thread's `errno`.
    unsafe {
        *libc::__errno_location() = libc::ENOMEM;
    }
    null_mut()
}

/// A block of `size` bytes aligned to `align`, from this thread's heap when it is in a run and
/// the request has a class, and whether its bytes are zero; `None` when the C library serves it.
fn from_heap(size: usize, align: usize) -> Option<(*mut c_void, bool)> {
    let heap = HEAP.get();
    if heap.is_null() {
        return None;
    }
    let class = class(size, align)?;
    #[expect(unsafe_code, reason = "the heap on the stack of `run`")]
    // SAFETY: a non-null `heap` is this thread's, alive while the thread-local holds it (see
    // `HEAP`), and only this thread uses it; no call of it allocates, so this is the only
    // reference to it while it lasts.
    let (block, zero) = unsafe { (*heap).alloc(class) };
    Some((
        if block.is_null() {
            refused()
        } else {
            block.cast()
        },
        zero,
    ))
}

/// `malloc`: the heap's block in a run, else the C library's.
///
/// # Safety
///
/// None beyond `malloc`'s; unsafe as the C library's allocation functions are.
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn malloc(size: usize) -> *mut c_void {
    match from_heap(size, 16) {
        Some((block, _)) => block,
        // SAFETY: `malloc`'s contract, passed on.
        None => unsafe { __libc_malloc(size) },
    }
}

/// `calloc`.
///
/// # Safety
///
/// As [`malloc`].
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn calloc(n: usize, size: usize) -> *mut c_void {
    let Some(bytes) = n.checked_mul(size) else {
        return refused();
    };
    match from_heap(bytes, 16) {
        Some((block, zero)) => {
            if !block.is_null() && !zero {
                // SAFETY: the block is `bytes` bytes long or more.
                unsafe { block.cast::<u8>().write_bytes(0, bytes) };
            }
            block
        }
        // SAFETY: `calloc`'s contract, passed on.
        None => unsafe { __libc_calloc(n, size) },
    }
}

/// `free`.
///
/// # Safety
///
/// `block` is null or a live block of `malloc` and the functions like it.
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn free(block: *mut c_void) {
    if ours(block.cast()) {
        // SAFETY: a live block of this allocator; the heap given is null or this thread's.
        unsafe { Heap::free(HEAP.get(), block.cast()) }
    } else {
        // SAFETY: a block outside the reservation is the C library's, or null.
        unsafe { __libc_free(block) }
    }
}

/// The bytes of `block`, a live block of this allocator.
fn block_size(block: *mut c_void) -> usize {
    #[expect(unsafe_code, reason = "a span header")]
    // SAFETY: a live block's span is mapped and its header written.
    unsafe {
        (*span_of(block.cast())).size
    }
}

/// `realloc`. A block of this allocator grown or shrunk within its class stays where it is;
/// otherwise it is copied into a block from wherever `malloc` would take it on this thread, and
/// freed. A block of the C library's stays the C library's.
///
/// # Safety
///
/// As [`free`].
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn realloc(block: *mut c_void, size: usize) -> *mut c_void {
    if !ours(block.cast()) {
        // SAFETY: a block outside the reservation is the C library's, or null.
        return unsafe { __libc_realloc(block, size) };
    }
    if size == 0 {
        // As the C library: the block is freed and null returned.
        // SAFETY: a live block of this allocator.
        unsafe { free(block) };
        return null_mut();
    }
    #[expect(unsafe_code, reason = "a span header")]
    // SAFETY: a live block's span is mapped and its header written.
    let c = unsafe { (*span_of(block.cast())).class };
    if class(size, 16).is_some_and(|(d, _, _)| d == c) {
        return block;
    }
    // SAFETY: `malloc`'s contract; the two blocks are distinct and live, each at least the
    // smaller size long, and `block` is freed once, after the copy.
    unsafe {
        let to = malloc(size);
        if !to.is_null() {
            std::ptr::copy_nonoverlapping(
                block.cast::<u8>(),
                to.cast(),
                block_size(block).min(size),
            );
            free(block);
        }
        to
    }
}

/// `reallocarray`.
///
/// # Safety
///
/// As [`free`].
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn reallocarray(block: *mut c_void, n: usize, size: usize) -> *mut c_void {
    match n.checked_mul(size) {
        // SAFETY: as `realloc`.
        Some(bytes) => unsafe { realloc(block, bytes) },
        None => refused(),
    }
}

/// `memalign` and `aligned_alloc`: `align` rounded up to a power of two, as the C library does.
///
/// # Safety
///
/// As [`malloc`].
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn memalign(align: usize, size: usize) -> *mut c_void {
    let Some(align) = align.checked_next_power_of_two() else {
        return refused();
    };
    match from_heap(size, align) {
        Some((block, _)) => block,
        // SAFETY: `memalign`'s contract, passed on.
        None => unsafe { __libc_memalign(align, size) },
    }
}

/// `posix_memalign`.
///
/// # Safety
///
/// `out` is valid for a write.
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn posix_memalign(out: *mut *mut c_void, align: usize, size: usize) -> c_int {
    if !align.is_power_of_two() || !align.is_multiple_of(size_of::<*mut c_void>()) {
        return libc::EINVAL;
    }
    // SAFETY: as `memalign`.
    let block = unsafe { memalign(align, size) };
    if block.is_null() {
        return libc::ENOMEM;
    }
    // SAFETY: the caller's guarantee.
    unsafe { out.write(block) };
    0
}

/// The page size.
fn page() -> usize {
    #[expect(unsafe_code, reason = "a libc call")]
    // SAFETY: `sysconf` takes a constant and reads no memory of the caller.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    usize::try_from(page).unwrap_or(4096)
}

/// `valloc`.
///
/// # Safety
///
/// As [`malloc`].
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn valloc(size: usize) -> *mut c_void {
    // SAFETY: as `memalign`.
    unsafe { memalign(page(), size) }
}

/// `pvalloc`: the size rounded up to a page.
///
/// # Safety
///
/// As [`malloc`].
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn pvalloc(size: usize) -> *mut c_void {
    let page = page();
    match size.max(1).checked_next_multiple_of(page) {
        // SAFETY: as `memalign`.
        Some(size) => unsafe { memalign(page, size) },
        None => refused(),
    }
}

/// `malloc_usable_size`: a block's class size here, else the C library's answer.
///
/// # Safety
///
/// As [`free`].
#[expect(unsafe_code, reason = "the C library's allocator")]
pub unsafe fn malloc_usable_size(block: *mut c_void) -> usize {
    if ours(block.cast()) {
        return block_size(block);
    }
    /// The C library's `malloc_usable_size`, which it exports under that name alone.
    static FOUND: AtomicUsize = AtomicUsize::new(0);
    let mut found = FOUND.load(Relaxed);
    if found == 0 {
        // SAFETY: `RTLD_NEXT` and a C string are what `dlsym` takes.
        found = unsafe { libc::dlsym(libc::RTLD_NEXT, c"malloc_usable_size".as_ptr()) } as usize;
        assert!(found != 0, "the C library has no `malloc_usable_size`");
        FOUND.store(found, Relaxed);
    }
    // SAFETY: `found` is the C library's `malloc_usable_size`, of this type, and `block` is
    // null or one of its live blocks.
    unsafe {
        std::mem::transmute::<usize, unsafe extern "C" fn(*mut c_void) -> usize>(found)(block)
    }
}
