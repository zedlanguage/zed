//! Dropping a deep structure in a loop: a drop reached from inside another queues its part on
//! the thread's queue and returns, so a chain of parts is freed whatever its depth, with no
//! recursion on the machine stack (DESIGN.md sec:kernel, "Reference semantics"). Values
//! (`value`), terms (`term`) and types (`types`, `types/rec`) each keep a queue of their own.

use std::cell::{Cell, RefCell};
use std::thread::LocalKey;

/// A thread's parts of one kind waiting to be dropped, for [`free_in`].
pub(crate) struct Queue<T> {
    /// Whether a drop further up this thread's stack is already emptying `parts`.
    busy: Cell<bool>,
    parts: RefCell<Vec<T>>,
}

impl<T> Queue<T> {
    pub(crate) const fn new() -> Queue<T> {
        Queue {
            busy: Cell::new(false),
            parts: RefCell::new(Vec::new()),
        }
    }
}

/// Drops `part` with the thread's `queue`, as `value::free` does. While the thread is ending and its
/// queue is gone, the part is dropped here, by recursion; [`hold`] keeps a queue until after the
/// tables that hold its parts are gone.
pub(crate) fn free_in<T: 'static>(queue: &'static LocalKey<Queue<T>>, part: T) {
    let mut held = Some(part);
    let first = queue.try_with(|q| {
        if q.busy.replace(true) {
            q.parts.borrow_mut().extend(held.take());
            false
        } else {
            true
        }
    });
    if !matches!(first, Ok(true)) {
        return;
    }
    drop(held);
    // The borrow ends with the pop: dropping a part can reach `free_in` again.
    while let Ok(Some(next)) = queue.try_with(|q| q.parts.borrow_mut().pop()) {
        drop(next);
    }
    let _ = queue.try_with(|q| q.busy.set(false));
}

/// Makes `queue` outlive every thread-local made after this call. A thread's locals are dropped
/// in the reverse of the order in which they were first used, so a table first used after this
/// call is dropped while the queue is still there to free its parts in a loop.
pub(crate) fn hold<T: 'static>(queue: &'static LocalKey<Queue<T>>) {
    let _ = queue.try_with(|_| ());
}
