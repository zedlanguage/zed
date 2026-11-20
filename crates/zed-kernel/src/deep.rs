//! Dropping a deep structure in a loop: a drop reached from inside another queues its part on
//! the thread's queue and returns, so a chain of parts is freed whatever its depth, with no
//! recursion on the machine stack (DESIGN.md sec:kernel, "Reference semantics"). Values
//! (`value`), terms (`term`) and types (`types`, `types/rec`) each keep a queue of their own.
//!
//! Complexity tradeoff (COMPLEXITY.md K22, K39): the naive drop recurses through the parts on
//! the thread's stack, O(depth) native stack, an abort with no message past the stack size
//! (depth 100,000 on 2 MiB). Used: a drop reached from inside another queues its part, and the
//! outermost drop empties the queue in a loop, O(size) time as before and O(depth) heap. Given
//! up: a constant factor per part queued, and one allocation of the queue's buffer per
//! outermost drop that queues a part (the buffer is freed when the queue is empty again, so a
//! thread that ends leaves none); parts are freed later than their holder, in queue order.

use std::cell::{Cell, RefCell};
use std::mem::ManuallyDrop;
use std::thread::LocalKey;

/// A thread's parts of one kind waiting to be dropped, for [`free_in`]. It has no destructor, so
/// the thread-local that holds it is never dropped: it is there while the thread's other
/// thread-locals are dropped, whatever the order in which they were first used, and a type they
/// hold is freed in a loop too (round 8, X39: a table first used before the queue was dropped
/// after it, and a type 4096 lists deep was freed by recursion and overflowed a 256 MiB stack).
///
/// Tests (PROOF-kernel-proofdoc3a-gaps (l)): "no destructor" is checked when the crate is
/// compiled (the `const` assert in [`Queue::new`]). A queue used after it was destroyed would
/// panic in `crate::local::with` in
/// `l01_23_groups_and_refusals::refusals::r8_x39_type_drop_at_thread_exit_in_either_initialization_order`,
/// `::r8_type_cached_before_queue_initialization_drops_at_thread_exit` and
/// `l01_23_subtyping::deep_rec::a_nested_type_kept_by_the_verdicts_is_freed_when_its_thread_ends`;
/// those types are 16 to 20 deep, so freeing in a loop is checked only by the benchmarks
/// `l01_23_subtyping::deep_rec::bench` (20 000 deep on a 256 KiB stack) and
/// `refusals::bench::r8_x39_deep_type_drop_does_not_overflow_stack`. That `parts` has no
/// buffer when not busy is checked by `deep::tests::the_queue_holds_no_buffer_between_drops`.
pub(crate) struct Queue<T> {
    /// Whether a drop further up this thread's stack is already emptying `parts`.
    busy: Cell<bool>,
    /// Empty, with no buffer, whenever `busy` is false: the outermost drop frees the buffer.
    parts: ManuallyDrop<RefCell<Vec<T>>>,
}

impl<T> Queue<T> {
    pub(crate) const fn new() -> Queue<T> {
        const { assert!(!std::mem::needs_drop::<Queue<T>>()) };
        Queue {
            busy: Cell::new(false),
            parts: ManuallyDrop::new(RefCell::new(Vec::new())),
        }
    }
}

/// Drops `part` with the thread's `queue`, as `value::free` does.
pub(crate) fn free_in<T: 'static>(queue: &'static LocalKey<Queue<T>>, part: T) {
    let mut held = Some(part);
    let first = crate::local::with(queue, |q| {
        if q.busy.replace(true) {
            q.parts.borrow_mut().extend(held.take());
            false
        } else {
            true
        }
    });
    if !first {
        return;
    }
    drop(held);
    // The borrow ends with the pop: dropping a part can reach `free_in` again.
    while let Some(next) = crate::local::with(queue, |q| q.parts.borrow_mut().pop()) {
        drop(next);
    }
    crate::local::with(queue, |q| {
        // Complexity tradeoff: the buffer is freed here, O(1), and made again by the next
        // outermost drop that queues a part, amortized O(1) per part; kept, it would be lost
        // when the thread ends, as the queue is never dropped.
        let mut parts = q.parts.borrow_mut();
        if parts.capacity() != 0 {
            *parts = Vec::new();
        }
        q.busy.set(false)
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A link of a chain that frees the rest of the chain through [`QUEUE`].
    struct Link(Option<Box<Link>>);

    thread_local! {
        static QUEUE: Queue<Box<Link>> = const { Queue::new() };
    }

    impl Drop for Link {
        fn drop(&mut self) {
            if let Some(next) = self.0.take() {
                free_in(&QUEUE, next);
            }
        }
    }

    /// A chain 10 000 links deep is freed through the queue, which queues each link below the
    /// first and so makes a buffer; once the outermost drop returns the queue is not busy and
    /// holds no buffer (the claim at [`Queue`], PROOF-kernel-proofdoc3a-gaps (l)), and a second
    /// chain is freed the same way.
    #[test]
    fn the_queue_holds_no_buffer_between_drops() {
        for _ in 0..2 {
            let mut chain = Link(None);
            for _ in 0..10_000 {
                chain = Link(Some(Box::new(chain)));
            }
            drop(chain);
            QUEUE.with(|q| {
                assert!(!q.busy.get(), "busy after the outermost drop");
                assert_eq!(
                    q.parts.borrow().capacity(),
                    0,
                    "a buffer left between drops"
                );
            });
        }
    }
}
