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
        self.0.fetch_add(1, Ordering::Relaxed)
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
}
