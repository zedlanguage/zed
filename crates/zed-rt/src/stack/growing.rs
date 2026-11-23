// The list of stacks under a memory limit that the handler of faults reads with no lock.
//
// One source, two builds: `stack.rs` includes this file with std's atomics, and the loom tests
// (`stack/weakmem.rs`) include it again with loom's, so the orderings loom checks are the very
// ones the handler runs (TEST-rt-weakmem). Each including module brings `AtomicPtr`,
// `AtomicUsize`, `Ordering` and `ptr` into scope. A trait over both kinds of atomic would do the
// same with a type parameter on every item and no gain: loom's types are for tests only, and
// std's `AtomicPtr::new` is `const`, so the static list is built in `stack.rs`, outside this
// file, where loom's non-`const` constructor never has to compile.
//
// Why the list needs no lock, from the orderings below (the claims loom checks in weakmem.rs,
// for two and three threads, in every interleaving and every weak-memory outcome it models):
// (G1) A record is written in full before it is published. `push` fills the record (`new`) and
//      stores its `next` before the compare-and-exchange that makes it the head, and that
//      exchange is a release on success; a reader's load of the head, or of a `next`, is an
//      acquire. A reader that reaches record r loaded a pointer to r from the head or from the
//      `next` of a newer record r'. In the first case the load read the value of r's exchange,
//      or of a later exchange of the head, which continues the release sequence of r's exchange
//      since every later write of the head is a read-modify-write; so r's exchange synchronizes
//      with the load, and every write `push` made to r happens before the reader reads it. In
//      the second case r' was published the same way, and r's own `push` happens before r''s:
//      r''s `push` read r as the head with an acquire (its first load, or a failed exchange),
//      and r's `next` is written only before r's publication (C++20 [atomics.order] and
//      [intro.races], the release-sequence and synchronizes-with rules, which Rust's atomics
//      follow; the Rustonomicon, "Atomics"). By induction on the records the reader passed, each
//      record's fields and its `next` are seen as `push` wrote them, so the walk from any head
//      it reads reaches every record older than that head, each once: `next` pointers only
//      point to older records, so the walk never meets a record twice and ends at the null of
//      the first record. Test: `two_pushes_at_once_are_each_reached_once`,
//      `three_pushes_at_once_are_each_reached_once`, `a_walk_beside_a_push_sees_a_whole_list`.
// (G2) No record is lost by two pushes at once: a compare-and-exchange is one indivisible
//      read-modify-write whatever its ordering ([atomics.order] 10: it reads the last value in
//      the modification order of the head), so of two pushes that read the same head one
//      fails, reads the other's record, and tries again with it. Same tests.
// (G3) A record is never freed (each is leaked), so a pointer a reader loads always points to
//      live memory, whatever it reads of `high`.
// What loom cannot reach: the handler runs in a signal handler, which loom has no model of;
// the handler's own reads are the plain loads of `find` and `records`, which run here as
// written, so what loom leaves out is only where they run.

/// A stack under a memory limit, as the handler of faults ([`super::on_fault`]) reads it: the
/// guard page is `[low - page, low)`, the stack `[low, high)`, and `[writable, high)` may be
/// written. Each record is leaked and stays in the list for the process's life, `high` 0 once
/// its stack is unmapped, so the handler reads it with no lock and never a freed record; there
/// is one for each stack made under a limit, one a run.
#[derive(Debug)]
pub(super) struct Grows {
    pub(super) low: AtomicUsize,
    pub(super) high: AtomicUsize,
    pub(super) writable: AtomicUsize,
    pub(super) page: usize,
    next: AtomicPtr<Grows>,
}

impl Grows {
    /// A record of a stack `[low, high)` with the guard page of `page` bytes below it and
    /// `[writable, high)` writable, in no list yet.
    pub(super) fn new(low: usize, high: usize, writable: usize, page: usize) -> Grows {
        Grows {
            low: AtomicUsize::new(low),
            high: AtomicUsize::new(high),
            writable: AtomicUsize::new(writable),
            page,
            next: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// Marks the stack unmapped: the handler of faults no longer reads it as a stack. Called by
    /// the thread that made and ran the stack (`Stack` is neither `Send` nor `Sync`), just
    /// before the stack is unmapped.
    //
    // Relaxed suffices, and Release on this store with Acquire on the handler's load would add
    // nothing (TEST-rt-weakmem, the case of a reader of a record whose `Drop` has run). Claim:
    // a handler that serves a fault after the stack's range is unmapped reads `high` as 0, so it
    // never makes a range writable that is no longer this stack's. Argument: the fault that
    // could do harm is at an address of the old range after `munmap`, in memory a later `mmap`
    // gave out again (a fault in the range while it is still mapped is an access to this stack
    // after its run, through a pointer that outlived the run, which safe code cannot make). The
    // thread that faults there reached the address from that later `mmap`, so its access
    // happens after the `mmap` returned, through the program's own synchronization or its own
    // order. The kernel orders the `munmap` before that `mmap` of the same addresses: both
    // take the address space's lock for writing (`mmap_write_lock` in mm/mmap.c and
    // mm/vma.c of Linux 6.x, read from memory, not checked against a source tree here), whose
    // unlock is a release and whose lock is an acquire, and a release orders every earlier
    // store of its thread, this relaxed one included, before every access that follows the
    // acquire (release cumulativity; in the language model, a release fence after this store
    // would play the part of the unlock, and the program orders the store before the call to
    // `munmap`: the compiler cannot move it past a call into code it cannot see, which may read
    // the list through its static). So the faulting thread's load of `high`, which follows its
    // fault, follows the store of 0 and reads it, or a later value, of which there is none.
    // The loom test `a_walk_after_the_unmap_does_not_see_the_stack` checks exactly this, with
    // the kernel's lock modeled as a release store and an acquire load of a flag; it cannot
    // check the kernel itself, which is the claim above taken from memory.
    pub(super) fn unmapped(&self) {
        self.high.store(0, Ordering::Relaxed);
    }

    /// The stack's `low` and `high`, read once, when the fault at `at` is in the stack or in its
    /// guard page and the stack is still mapped.
    fn holds(&self, at: usize) -> Option<(usize, usize)> {
        let (low, high) = (
            self.low.load(Ordering::Relaxed),
            self.high.load(Ordering::Relaxed),
        );
        (high != 0 && at >= low - self.page && at < high).then_some((low, high))
    }
}

/// The records of the stacks made under a memory limit, newest first.
#[derive(Debug)]
pub(super) struct Growing {
    head: AtomicPtr<Grows>,
}

impl Growing {
    /// Puts `grows` first in the list. Lock-free: a push that loses a race for the head tries
    /// again with the head the winner wrote (G2). O(1) per try.
    pub(super) fn push(&self, grows: &'static Grows) {
        let mut head = self.head.load(Ordering::Acquire);
        loop {
            grows.next.store(head, Ordering::Relaxed);
            match self.head.compare_exchange_weak(
                head,
                ptr::from_ref(grows).cast_mut(),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => break,
                Err(h) => head = h,
            }
        }
    }

    /// The records, newest first, as a walk with no lock reads them (G1). Async-signal-safe:
    /// loads of atomics only.
    pub(super) fn records(&self) -> Records {
        Records {
            at: self.head.load(Ordering::Acquire),
        }
    }

    /// The newest record of a mapped stack that holds the fault at `at` in the stack or its
    /// guard page, if any, with the `low` and `high` it was found by: the caller works from
    /// these and never reads `high` again, which could have become 0 since. O(records).
    /// Async-signal-safe, as `records` is.
    pub(super) fn find(&self, at: usize) -> Option<(&'static Grows, usize, usize)> {
        self.records()
            .find_map(|r| r.holds(at).map(|(low, high)| (r, low, high)))
    }
}

/// A walk of [`Growing`]'s records, newest first.
#[derive(Debug)]
pub(super) struct Records {
    at: *mut Grows,
}

impl Iterator for Records {
    type Item = &'static Grows;

    fn next(&mut self) -> Option<&'static Grows> {
        #[expect(unsafe_code, reason = "the list holds pointers to leaked records")]
        // SAFETY: every pointer in the list is null or was made by `push` from a
        // `&'static Grows`, and no record is ever freed (G3).
        let r = unsafe { self.at.as_ref() }?;
        self.at = r.next.load(Ordering::Acquire);
        Some(r)
    }
}
