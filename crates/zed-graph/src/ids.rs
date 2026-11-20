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
    /// carry the count past `u64::MAX`, and leaves the source as it was. So `u64::MAX` itself
    /// is never drawn.
    pub fn take(&self, count: u64) -> u64 {
        // Each draw stores `first + count` only when it does not overflow, by a compare and
        // swap (`try_update`, which this toolchain's std names in place of `fetch_update`), so
        // the count never wraps and no draw, on any thread, gets a number twice
        // (FAIL-idsource-take-wrap-race; `fetch_add` stored the wrapped sum first and checked
        // it after, when a racing draw could already have read the low numbers).
        //
        // Proof that each number is drawn once. The count only grows: every store is
        // `c + count` for the `c` it replaces, checked not to overflow, and `count` is 0 or
        // more. A draw that succeeds read `c` and stored `c + count` in one atomic step (the
        // swap fails, and `try_update` reads again, if any other store came between), so it
        // owns `c .. c + count`, and the next draw on any thread starts at `c + count` or
        // later. So the ranges of two draws are disjoint, and every one lies at or above the
        // start and at most at `u64::MAX - 1` (its end, exclusive, is at most `u64::MAX`). A
        // refused draw stores nothing. `Relaxed` is enough, as above: the swap alone orders the
        // draws on the one atomic, and no other memory is read through it.
        //
        // The check is one draw stricter than needed: a draw ending at exactly `u64::MAX` has
        // `first + count = 2^64`, which does not fit, so it is refused though its own numbers
        // fit. That costs nothing a caller can reach (one number of 2^64), and it is what lets
        // the count, which must hold the next number, never read 0 after the top.
        //
        // Tests: `a_refused_draw_leaves_the_source_unchanged` and
        // `racing_draws_past_the_top_are_refused_and_reuse_no_number` (below; both fail on the
        // `fetch_add` version), `units::ids::a_draw_past_the_largest_number_is_refused` (the
        // start `u64::MAX - 1`, `take(2)`, the one-draw-early case).
        //
        // Complexity tradeoff: a compare-and-swap loop for `fetch_add`'s single add. O(1) per
        // draw with no other thread drawing; under contention a draw retries once for each
        // draw that lands between its read and its swap, so a burst of t threads costs O(t)
        // retries per draw at worst (lock-free, not wait-free), where `fetch_add` never
        // retries. Measured by `id_draws_take_linear_time_and_cost_near_fetch_add` (zed-graph
        // `bench/units.rs`); numbers in COMPLEXITY.md, FAIL-idsource-take-wrap-race.
        // The callers draw an id per node, type, block or search they make, each far more work
        // than a draw, so the difference should not show in them (inferred from the call
        // sites, not measured).
        match self
            .0
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |c| {
                c.checked_add(count)
            }) {
            Ok(first) => first,
            Err(first) => panic!("drawing {count} numbers from {first} passes u64::MAX"),
        }
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

    /// A draw refused for passing `u64::MAX` leaves the source as it was: the next draw that
    /// fits gives the next number, not one past a wrap (FAIL-idsource-take-wrap-race).
    #[test]
    fn a_refused_draw_leaves_the_source_unchanged() {
        let ids = IdSource::starting_at(u64::MAX - 3);
        assert_eq!(ids.next(), u64::MAX - 3);
        let refused = std::panic::catch_unwind(|| ids.take(10));
        assert!(
            refused.is_err(),
            "drawing 10 from u64::MAX - 2 was not refused"
        );
        assert_eq!(ids.next(), u64::MAX - 2);
        assert!(std::panic::catch_unwind(|| ids.take(2)).is_err());
        assert_eq!(ids.next(), u64::MAX - 1);
        // `u64::MAX` itself is never drawn: its draw would carry the count past the top.
        assert!(std::panic::catch_unwind(|| ids.next()).is_err());
        assert!(std::panic::catch_unwind(|| ids.next()).is_err());
    }

    /// Threads drawing from a source near the top get each number of `start .. u64::MAX` once,
    /// none below the start (a number past a wrap, which a source started low has drawn
    /// already), and each thread is refused once the numbers are gone, every draw after it too
    /// (FAIL-idsource-take-wrap-race). Before the fix the first refused draw wrapped the count,
    /// so the racing and later draws gave 0, 1, 2, … with no panic.
    #[test]
    fn racing_draws_past_the_top_are_refused_and_reuse_no_number() {
        const THREADS: u64 = 8;
        const LEFT: u64 = 1000;
        let ids = IdSource::starting_at(u64::MAX - LEFT);
        let runs: Vec<(Vec<u64>, bool)> = std::thread::scope(|s| {
            let hs: Vec<_> = (0..THREADS)
                .map(|_| {
                    s.spawn(|| {
                        // Each thread could draw all `LEFT` numbers, so every thread runs out.
                        let mut got = Vec::new();
                        for _ in 0..LEFT + 1 {
                            match std::panic::catch_unwind(|| ids.next()) {
                                Ok(id) => got.push(id),
                                Err(_) => return (got, true),
                            }
                        }
                        (got, false)
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        assert!(
            runs.iter().all(|(_, refused)| *refused),
            "a thread drew {} numbers with no refusal",
            LEFT + 1
        );
        let mut all: Vec<u64> = runs.into_iter().flat_map(|(got, _)| got).collect();
        all.sort_unstable();
        assert_eq!(all, (u64::MAX - LEFT..u64::MAX).collect::<Vec<u64>>());
    }
}
