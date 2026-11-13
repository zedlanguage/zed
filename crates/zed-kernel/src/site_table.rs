//! The table of source sites a thread records while a program is built (plan row RT-sites),
//! by node name ([`crate::sites::key`]): the part of [`crate::sites`] that dropping and copying
//! a term change. It names nodes by number only and reads no term, so `term` can call it and
//! `sites`, which reads terms, can build on it, with no import cycle between them.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

/// A stretch of the program's source, in bytes from its start: `start..end`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    /// The first byte.
    pub start: usize,
    /// One past the last byte.
    pub end: usize,
}

thread_local! {
    /// Whether this thread records sites: read on every drop and copy of a node, so a plain
    /// flag, apart from the table.
    static ON: Cell<bool> = const { Cell::new(false) };
    /// The sites recorded on this thread.
    static TABLE: RefCell<HashMap<usize, Span>> = RefCell::new(HashMap::new());
}

/// Whether this thread records sites. O(1).
pub(crate) fn recording() -> bool {
    ON.get()
}

/// Puts `table` and `on` in place of this thread's table and flag, and gives the old ones.
pub(crate) fn swap(table: HashMap<usize, Span>, on: bool) -> (HashMap<usize, Span>, bool) {
    let old = ON.replace(on);
    (TABLE.with_borrow_mut(|t| std::mem::replace(t, table)), old)
}

/// Runs `f` on this thread's table.
pub(crate) fn with<R>(f: impl FnOnce(&mut HashMap<usize, Span>) -> R) -> R {
    TABLE.with_borrow_mut(f)
}

/// Gives node `to` the site of node `from` when `to` has none. O(1). Does nothing when this
/// thread is not recording.
pub(crate) fn copy(from: usize, to: usize) {
    if !recording() || from == to {
        return;
    }
    TABLE.with_borrow_mut(|table| {
        if let Some(&s) = table.get(&from) {
            table.entry(to).or_insert(s);
        }
    });
}

/// Forgets the site of node `key`, which is being dropped. O(1). Does nothing when this thread
/// is not recording, or while the table is being read or torn down.
pub(crate) fn forget(key: usize) {
    if !recording() {
        return;
    }
    let _ = TABLE.try_with(|table| {
        if let Ok(mut table) = table.try_borrow_mut() {
            table.remove(&key);
        }
    });
}
