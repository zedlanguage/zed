//! The work meter of the exact cover (module `exact`): its limit, its counters and the charge
//! the solver makes at each of its steps while a question of the cover runs.
//!
//! It is a module of its own, below the solver (`presburger.rs`) and the cover (`exact.rs`,
//! `exact/projection.rs`), because all three read it: the solver charges its steps here and
//! stops when the meter is spent, and the cover asks the solver. Kept in `exact.rs`, the
//! solver's charge made the solver import the cover and the cover the solver, an import cycle
//! (row MAIN-red-pugh-land; `s_01f_import_graph`). This module imports nothing of either, but
//! the formula's types: the steps of the solver the cover asks come to it as function values
//! ([`Solver`]).

use std::cell::Cell;

use super::{Atom, Con, Formula, Model, Refusal};

/// The work allowed to the cover of one symbol in `exact_each`. A unit is one value or residue
/// the cover lists, or a hundredth of a constraint, term or row read ([`SOLVER_UNIT`]; each
/// charging site says what it counts): a question of the solver is charged the constraints of the
/// formula asked and the solver's own steps (`charge`), and a cell the constraints read to
/// make it. Past it the symbol is refused with [`Refusal::Questions`]. The predicted work of
/// a cover is 2 ms and 80 ns a unit of its CPU time, so 3,100,000 units are 250 ms (QUESTIONS
/// A99): of 38,984 calls of `exact_each` in the step tests, run with no limit at loads of 65
/// to 82 on 32 cores and measured whole (all their symbols' covers together), none took more
/// CPU time than that, the closest 1.6 ms under it at 178,156 units (COMPLEXITY.md,
/// PRES-pugh-work-budget). The 2 ms are two ticks of the clock read.
// Complexity tradeoff: before PRES-pugh-work-budget a question was charged `size + 2` and its
// run of the solver was not counted, so one question ran from 40 ms to more than 25 s
// (`s22::chains_on_two_inputs_keep_their_boxes_at_50_and_51`) under a limit of 2·10^7. Naive
// alternatives: time each question and stop at 250 ms, which makes the answer depend on the
// machine and its load (deterministic checking forbids it); or keep the solver's coarser set
// past the limit, which P197 and P13 forbid. Used: the solver charges its own steps (each
// system solved, each row the Omega test makes, each canonical order, each row `live3`
// reads, each probe, each search by halves) to the question's meter, a count the same on
// every run, and stops at its next step once the meter is spent (`spent`); a question is
// charged each constraint of its formula, which the checks before the solver's steps read at
// about 4 µs each, a piece read by a residue question 16 units ([`PIECE`]), and each row an
// exact elimination of a cell makes as it makes it. Cost: one thread-local read per charge.
// Not proved: that 2 ms and 80 ns a unit bound the CPU time of every cover, at every load
// and size of coefficient. It is measured, and the bound is loose for most covers: on the 185
// calls past 3,100,000 units the CPU time per unit ran from 0.6 to 28 ns, median 16, and 139
// of them took under 250 ms, so a cover refused at the limit may have needed far less
// (COMPLEXITY.md, PRES-pugh-work-budget). After the refit of PRES-work-charge-fit
// ([`SOLVER_STEP`], [`QUESTION_ROW`]) no cover of the step tests or the benchmarks ran past
// its prediction at loads of 36 to 65; still measured, not proved.
pub const EXACT_LIMIT: u64 = 3_100_000;

thread_local! {
    /// Test control: a work limit in place of [`EXACT_LIMIT`].
    pub static EXACT_LIMIT_SET: Cell<Option<u64>> = const { Cell::new(None) };
    /// Test control: the solver's answer as it is, with no cover (the answer before
    /// PRES-project-exact-solver), for the tests that compare the two.
    pub static EXACT_OFF: Cell<bool> = const { Cell::new(false) };
    /// Test control: the cover of each symbol asks its questions without first trying the
    /// projection read from the structure of the formula (`exact::direct`), for the tests
    /// that compare the two.
    pub static DIRECT_OFF: Cell<bool> = const { Cell::new(false) };
    /// Test control: the cover of each symbol does not try the forward certificate
    /// (`exact::guarded::forward`), for the tests that compare the cover with and without it.
    pub static GUARDED_OFF: Cell<bool> = const { Cell::new(false) };
    /// Test control: `exact_each` skips the shared step (`exact::shared_cells`), for the tests
    /// that compare the covers with and without it.
    pub static SHARED_OFF: Cell<bool> = const { Cell::new(false) };
    /// The questions `exact_each` has asked on this thread, read by tests.
    pub static EXACT_QUESTIONS: Cell<u64> = const { Cell::new(0) };
    /// The work `exact_each` has used on this thread, read by tests and benchmarks.
    pub static EXACT_WORK: Cell<u64> = const { Cell::new(0) };
}

/// A solver step that eliminates the atoms a test picks from constraints ([`Solver`]).
pub(super) type Eliminate = fn(&[Con], &dyn Fn(&Atom) -> bool) -> Option<Vec<Con>>;

/// The steps of the solver (`presburger.rs`) that the cover asks, handed to it as function
/// values. Named in `exact.rs`, they made the cover import the solver, which calls the cover
/// from `project_each`: an import cycle (`s_01f_import_graph`). The solver builds this once
/// (`presburger::SOLVER`) and gives it to the cover with each call, so the cover imports
/// only this module and the formula's types (row PRES-cover-wire).
#[derive(Clone, Copy)]
pub(super) struct Solver {
    /// `presburger::satisfiable`.
    pub(super) satisfiable: fn(&Formula) -> Result<Option<Model>, Refusal>,
    /// `presburger::eliminated_counted`.
    pub(super) eliminated_counted: Eliminate,
    /// `presburger::eliminated_whole`.
    pub(super) eliminated_whole: Eliminate,
    /// `presburger::point_of`.
    pub(super) point_of: fn(&[Con], bool) -> Option<Model>,
}

/// The units of work used and allowed, and the solver the work asks.
pub(super) struct Work {
    pub(super) used: u64,
    pub(super) limit: u64,
    pub(super) solver: Solver,
}

impl Work {
    pub(super) fn charge(&mut self, units: u64) -> Result<(), Refusal> {
        self.used = self.used.saturating_add(units);
        EXACT_WORK.set(EXACT_WORK.get().saturating_add(units));
        if self.used > self.limit {
            return Err(Refusal::Questions);
        }
        Ok(())
    }

    /// Charges `rows` constraints or rows read whole (the formula read at a point, an
    /// implicant's rows), [`SOLVER_UNIT`] each, where a value the cover lists costs tens of
    /// nanoseconds; a question's formula is charged by [`Work::question`].
    pub(super) fn read(&mut self, rows: u64) -> Result<(), Refusal> {
        self.charge(rows.saturating_mul(SOLVER_UNIT))
    }

    /// Charges the `rows` constraints of a question's formula, [`QUESTION_ROW`] each, before
    /// the question is asked: the checks the solver makes before its own steps read them.
    pub(super) fn question(&mut self, rows: u64) -> Result<(), Refusal> {
        self.charge(rows.saturating_mul(QUESTION_ROW))
    }

    /// `run`, its work counted by the solver's meter ([`charge`]) and charged here, the meter
    /// given the work left: refused with [`Refusal::Questions`] where it passes the limit,
    /// whatever `run` returned, since a step that reads a spent meter as no point (as
    /// `eliminated_whole` and the solver's searches do) could have changed it.
    pub(super) fn metered<T>(&mut self, run: impl FnOnce() -> T) -> Result<T, Refusal> {
        let left = self.limit.saturating_sub(self.used);
        let outer = METER.replace(Some(Meter {
            used: 0,
            limit: left,
        }));
        let out = run();
        let Meter { used, limit } = METER.get().expect("the meter set above");
        // A meter open around this one (none is today: neither the solver nor an elimination
        // asks a projection) is charged what this one used, in units, as it counts them.
        METER.set(outer.map(|o| Meter {
            used: o.used.saturating_add(used),
            limit: o.limit,
        }));
        self.charge(used)?;
        if used > limit {
            return Err(Refusal::Questions);
        }
        Ok(out)
    }

    /// `satisfiable` of `q`, its work counted by the solver's meter ([`charge`]) and charged
    /// here, the meter given the work left, and added to [`QUESTION_WORK`]. A question that
    /// passes it is refused with [`Refusal::Questions`], whatever the solver answered after:
    /// an error the solver drops on its way (a search that reads a refusal as no point) could
    /// have changed that answer. Asked by the cover (`exact.rs`) and by `exact::projection`'s
    /// `rays`; here, in the module both import, so that neither imports the other.
    pub(super) fn ask(&mut self, q: &Formula) -> Result<Option<Model>, Refusal> {
        let before = self.used;
        let satisfiable = self.solver.satisfiable;
        let answer = self.metered(|| satisfiable(q));
        QUESTION_WORK.set(QUESTION_WORK.get().saturating_add(self.used - before));
        answer?
    }
}

/// The solver's work while a question of the cover runs (`exact::Work::ask`): units used and
/// allowed.
#[derive(Clone, Copy)]
struct Meter {
    used: u64,
    limit: u64,
}

thread_local! {
    /// The meter of the question running, if any.
    static METER: Cell<Option<Meter>> = const { Cell::new(None) };
    /// The units the questions of the cover have used on this thread, read by tests and
    /// benchmarks.
    pub static QUESTION_WORK: Cell<u64> = const { Cell::new(0) };
    /// The units the fast paths of the cover (`exact::tried`) have used on this thread,
    /// answered or not, read by tests: counted in [`EXACT_WORK`] but not against a cover's
    /// limit.
    pub static FAST_WORK: Cell<u64> = const { Cell::new(0) };
}

/// The units of [`EXACT_LIMIT`] one unit of the solver's work counts for: a row, term or
/// constraint read by the solver costs about a hundred times a value or residue the cover
/// lists (PRES-pugh-work-budget).
pub const SOLVER_UNIT: u64 = 100;

/// The units of [`EXACT_LIMIT`] one step of the solver counts for ([`charge`]): 100, as
/// one constraint of a question's formula counted for ([`QUESTION_ROW`]) in
/// PRES-pugh-work-budget. Seat Opus of PRES-pugh-xr round 3 fit 45 and 150 on the
/// thread CPU time of whole covers (13,248 covers over 2 ms, loads 54 to 94: none over the
/// prediction 2 ms + 80 ns a unit, least ratio 1.028, median 1.95), on a tree without that
/// round's counted shadows (`exact::Work::eliminate`). With those shadows also charged, 45 and
/// 150 refused `omega::twin_definitions_merge_in_time_near_linear`, which 100 and 100 answer,
/// so the fit no longer described the charges in force and was not merged.
///
/// The refit on the merged charges (PRES-work-charge-fit) kept a step at 100 and added the
/// charges the per-site timings showed missing: each atom the Omega test takes from its queue
/// (`shadow_logged`), each piece of a cell the cover cuts from its gap (`exact::cover`), and
/// none for a call whose solver answer is already empty (`exact_each`). Replayed on every
/// cover the step tests and the benchmarks make (28,838 and about 9,030 covers, run at
/// [`EXACT_LIMIT`] at loads of 36 to 65 on 32 cores), none then took more CPU time than its prediction;
/// the least ratio was 1.09 (`bench::exact_cover::the_cover_takes_a_bounded_time_per_unit_of_work`,
/// record 1, load 62) and in the step tests 1.82. COMPLEXITY.md, PRES-work-charge-fit.
// Complexity tradeoff: one factor for all solver steps and one for question rows is the
// naive charge; a factor per site fit by a linear program held on the data it was fit on
// and not on held-out data (round 3, least ratio 0.42 on the benchmarks), so a per-site fit
// needs per-site timings (a batch of one site's steps between two reads of
// `CLOCK_THREAD_CPUTIME_ID`, which reads to 1 ns at about 0.6 µs a read).
pub(super) const SOLVER_STEP: u64 = 100;
/// The units one constraint of a question's formula counts for ([`Work::question`]): the
/// passes each question makes over its formula before the solver's first charged step
/// (`signed`, `forced`, `row_sums`, `reduced`, `modular_answer`, `Renamed::of`, `absorbed`,
/// the hulls of its disjunctions and `drop_by_bounds`), none of which charge the meter. Timed
/// on the cover of record 1 of `bench::exact_cover::the_cover_takes_a_bounded_time_per_unit_of_work`
/// (1,001 questions of 10 rows): 23, 2, 8, 18, 17, 14, 6 and 17 µs a question, about 95 µs
/// with the timer's own cost taken out, 9.5 µs a row; that cover took 84 to 105 ms of CPU time
/// at loads of 55 to 72.
// Complexity tradeoff: at 100 (8 µs a row) that cover was charged 1,157,868 units, a
// prediction of 94.6 ms, and ran 1.02 times it at load 72 and under it (105 ms) at load 62.
// At 150 it was safe (least ratio 1.43) but refused one more cover of the step tests (s22
// `remainder_cases_cut_at_their_neighbors_at_modulus_5_seed_1`, 41 ms of CPU time). Used: 125
// (10 µs a row), the least whole charge measured with no cover over its prediction at both
// loads and no refusal added (PRES-work-charge-fit). A charge per pass by what it reads is the
// alternative; each pass reads the formula once, so the rows count it to within that factor.
pub(super) const QUESTION_ROW: u64 = 125;

/// The units a piece read by `exact::residues` or `exact::outside` is charged: its ends
/// converted, two residues taken and a set joined or met, measured at 0.6 to 0.8 µs a piece
/// where a unit of a cover costs at most 56 ns (s22
/// `remainder_splits_at_their_corners_keep_their_preimages`, PRES-pugh-work-budget), so 16,
/// not the [`LISTED`] a listed value costs.
pub(super) const PIECE: u64 = 16;

/// The units a value the cover lists is charged (`exact::projection::listed`): the value made
/// and pushed, about 150 ns, and its share of the sets built from the values listed after it
/// (the list sorted into a set and joined to the cell, and the gap and the values found cut and
/// joined by it), about 370 ns more, measured on a cover that lists 1,958,315 values at loads
/// of 75 to 90 on 32 cores (s22 `split_pieces_reach_each_kind_of_touched`, PRES-pugh-xr
/// round 3, F): 526 ns, so 7 units of 80 ns. With the round-3 fit of [`SOLVER_STEP`] (45) 7 was the least
/// whole charge with no cover over its prediction: at 6 that cover took 1.006 times its prediction.
/// With [`SOLVER_STEP`] at 100 that check is not repeated (PRES-work-charge-fit).
// Complexity tradeoff: before, a listed value was charged 1 unit, which left the sets built
// from the list uncounted, and that cover was refused at the limit after 1.5 s of CPU time,
// six times the 250 ms the limit stands for (QUESTIONS A99). Naive alternative: charge each
// set operation by the pieces it reads, one more charge at each of four sites for the same
// count. Used: the count is the values listed, so each is charged its share where it is made.
pub(super) const LISTED: u64 = 7;

/// Charges `units` of the solver's work, [`SOLVER_STEP`] each, to the meter of the question
/// running, and refuses with
/// [`Refusal::Questions`] once it is past its limit; with no question running, as for every
/// question but the cover's, it does nothing. A unit is one constraint, term or disjunct read
/// by a step of the solver (each site says what it charges), and the units charged are a
/// count, the same on every run.
pub(super) fn charge(units: u64) -> Result<(), Refusal> {
    match METER.get() {
        None => Ok(()),
        Some(Meter { used, limit }) => {
            let used = used.saturating_add(units.saturating_mul(SOLVER_STEP));
            METER.set(Some(Meter { used, limit }));
            if used > limit {
                Err(Refusal::Questions)
            } else {
                Ok(())
            }
        }
    }
}

/// Whether the question running is past its limit: a search that reads a refusal as no point
/// stops at once, since the question's answer is then refused whatever it finds.
pub(super) fn spent() -> bool {
    METER.get().is_some_and(|m| m.used > m.limit)
}
