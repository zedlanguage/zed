//! A source of numbers, each drawn once in the process.

use std::sync::atomic::{AtomicU64, Ordering};

/// Numbers drawn in increasing order from a start, each once, by any thread: ids for nodes,
/// stamps for searches, versions. A `static` of the workspace's id counters, which were each an
/// `AtomicU64` and a `fetch_add` of 1.
///
/// `Relaxed` is enough: each number is drawn once by the read-modify-write alone, and no other
/// memory is ordered by it. The count does not wrap in practice: 2^64 draws at 10^9 a second
/// take 584 years.
#[derive(Debug)]
pub struct IdSource(AtomicU64);

impl IdSource {
    /// A source whose first number is `start`. Each site keeps its own start: a start of 1 or
    /// 2 keeps 0, or 0 and 1, free to mean "none" or a fixed node.
    pub const fn starting_at(start: u64) -> IdSource {
        IdSource(AtomicU64::new(start))
    }

    /// The next number, never drawn before.
    pub fn next(&self) -> u64 {
        self.take(1)
    }

    /// The first of `count` consecutive numbers, none drawn before: for a node that also
    /// names a second thing by its id plus one (a BDD cell and its complement).
    ///
    /// Panics with "drawing {count} numbers from {first} passes u64::MAX" when the draw would
    /// carry the count past `u64::MAX`.
    pub fn take(&self, count: u64) -> u64 {
        let first = self.0.fetch_add(count, Ordering::Relaxed);
        // `fetch_add` wraps: a draw past `u64::MAX` would leave the count at the low numbers,
        // and the next draws would give numbers already drawn, two nodes with one id. Draws
        // from 0 reach `u64::MAX` only after 584 years (above), so the case is a start set near
        // the top or a huge `count`; it is refused here. The draws are numbered `first ..
        // first + count`, all at most `u64::MAX` exactly when `first + count` does not overflow,
        // which `checked_add` tests. Once it fails the count has wrapped already, and a draw
        // racing on another thread may get a reused number; the panic names the fault, and it
        // costs one branch per draw (TEST-dry-shared-units: before, the wrap was silent).
        assert!(
            first.checked_add(count).is_some(),
            "drawing {count} numbers from {first} passes u64::MAX"
        );
        first
    }
}

#[cfg(test)]
mod tests {
    use super::IdSource;

    /// Numbers come from the start up, each once, across threads.
    #[test]
    fn each_number_is_drawn_once_from_the_start() {
        static IDS: IdSource = IdSource::starting_at(2);
        let mut all: Vec<u64> = std::thread::scope(|s| {
            let hs: Vec<_> = (0..4)
                .map(|_| s.spawn(|| (0..1000).map(|_| IDS.next()).collect::<Vec<_>>()))
                .collect();
            hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
        });
        all.sort_unstable();
        assert_eq!(all, (2..4002).collect::<Vec<u64>>());
    }

    /// `take(2)` keeps both numbers from later draws: the next is past them.
    #[test]
    fn a_block_taken_is_not_drawn_again() {
        let ids = IdSource::starting_at(2);
        assert_eq!(ids.take(2), 2);
        assert_eq!(ids.next(), 4);
        assert_eq!(ids.take(2), 5);
        assert_eq!(ids.next(), 7);
    }
}
