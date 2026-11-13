//! The crossover benchmarks of DESIGN.md sec:plan (author, 2026-11-12, QUESTIONS A96). Where the
//! code changes from one method to another at a size, the two giving the same output, a
//! benchmark times both methods on both sides of the threshold, checks that their outputs are
//! equal there, and sets the threshold at the measured crossover. The tests check both sides
//! too, wherever a check runs in under 60 s; this crate is for the measurements that set the
//! thresholds, which are not tests.
//!
//! **Run on each target platform, on real hardware.** A crossover depends on the processor, the
//! compiler and the code on both sides, so each benchmark is run on each target platform, on
//! real hardware and not under emulation, and sets that platform's threshold; and run again
//! when the code of either method changes. The work is counted in instructions where the
//! hardware counts them ([`zed_tests::scaling::Meter`]), which load does not change, in the
//! build the tests use (the `dev` profile); the load is printed with each table all the same.
//!
//! [`Crossover`] is for a threshold on the size of the input: it measures at given sizes, then
//! halves the interval in which the faster method changes until it is narrower than a given
//! fraction, and reports the least measured size from which the second method is never slower
//! at any measured size. [`settings`] is for a setting with a few possible values (a leaf width,
//! say): it measures each value on each input and checks that every value gives the same
//! output. The binary `crossover` runs the benchmarks one by one; COMPLEXITY.md section
//! "Crossovers" records what they measured.

use std::fmt::Debug;
use std::hint::black_box;

use zed_tests::scaling::{Meter, Work};

/// How many runs each measurement takes the least of: instruction counts of the same run differ
/// by a fraction of a percent, mostly in the first run, which finds the allocator cold.
const RUNS: usize = 3;

/// One of two methods with the same output.
pub struct Method<'a, I, O> {
    /// Its name, for the tables.
    pub name: &'static str,
    /// The method.
    pub run: &'a dyn Fn(&I) -> O,
}

/// The two methods' work at one size.
#[derive(Clone, Copy, Debug)]
pub struct Point {
    /// The size.
    pub size: usize,
    /// The work of the method used below the threshold.
    pub below: Work,
    /// The work of the method used from the threshold on.
    pub above: Work,
}

impl Point {
    /// The second method's work over the first's, in the meter's unit.
    pub fn ratio(&self) -> f64 {
        self.above.units as f64 / self.below.units as f64
    }

    /// The second method's bytes over the first's.
    pub fn bytes_ratio(&self) -> f64 {
        self.above.bytes as f64 / self.below.bytes as f64
    }

    /// Whether the second method does at most the first's work here.
    pub fn above_wins(&self) -> bool {
        self.above.units <= self.below.units
    }
}

/// Where the second method takes over, among the sizes measured.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Threshold {
    /// The second method is never slower at any size measured, the least being this one.
    AtOrBelow(usize),
    /// The least measured size from which the second method is never slower at any size
    /// measured, the next size below it measured within the tolerance.
    At(usize),
    /// The first method is faster at the largest size measured, this one.
    Above(usize),
}

/// A change of method at a size between two methods with the same output.
pub struct Crossover<'a, I, O> {
    /// What a size counts, for the tables ("words").
    pub unit: &'static str,
    /// Text added to each size in the tables, such as the same size in other units; may be
    /// empty.
    pub note: &'a dyn Fn(usize) -> String,
    /// The inputs at a size: the first is timed, and every one is checked for equal output.
    pub inputs: &'a dyn Fn(usize) -> Vec<I>,
    /// The method used below the threshold.
    pub below: Method<'a, I, O>,
    /// The method used from the threshold on.
    pub above: Method<'a, I, O>,
}

impl<I, O: PartialEq + Debug> Crossover<'_, I, O> {
    /// Both methods' work on the first input at `size`, after checking that they give the same
    /// output on every input at `size`.
    pub fn measure(&self, meter: &mut Meter, size: usize) -> Point {
        let inputs = (self.inputs)(size);
        for (k, x) in inputs.iter().enumerate() {
            let (b, a) = ((self.below.run)(x), (self.above.run)(x));
            assert!(
                b == a,
                "{} and {} give different outputs on input {k} of {size} {}",
                self.below.name,
                self.above.name,
                self.unit
            );
        }
        let x = inputs.first().expect("at least one input at each size");
        Point {
            size,
            below: least(meter, || drop(black_box((self.below.run)(x)))),
            above: least(meter, || drop(black_box((self.above.run)(x)))),
        }
    }

    /// The work at each of `sizes`, and then at sizes between the two measured sizes around the
    /// change, each the geometric mean of the two around it, until those two are within
    /// `tolerance` of each other (`hi <= lo (1 + tolerance)`) or next to each other. The
    /// points come back in order of size, with where the second method takes over: the least
    /// measured size from which it is never slower at a measured size. Sizes where the faster
    /// method changes more than once show in the points; only the last change is narrowed.
    pub fn find(
        &self,
        meter: &mut Meter,
        sizes: &[usize],
        tolerance: f64,
    ) -> (Vec<Point>, Threshold) {
        let mut points: Vec<Point> = sizes.iter().map(|&s| self.measure(meter, s)).collect();
        loop {
            points.sort_by_key(|p| p.size);
            let first_win = points
                .iter()
                .rposition(|p| !p.above_wins())
                .map_or(0, |j| j + 1);
            let (Some(lo), Some(hi)) = (
                first_win.checked_sub(1).map(|j| points[j].size),
                points.get(first_win).map(|p| p.size),
            ) else {
                let threshold = match first_win {
                    0 => Threshold::AtOrBelow(points[0].size),
                    _ => Threshold::Above(points[points.len() - 1].size),
                };
                return (points, threshold);
            };
            if hi - lo <= 1 || hi as f64 <= lo as f64 * (1.0 + tolerance) {
                return (points, Threshold::At(hi));
            }
            let mid = ((lo as f64 * hi as f64).sqrt().round() as usize).clamp(lo + 1, hi - 1);
            let point = self.measure(meter, mid);
            eprintln!("{}", self.row(&point));
            points.push(point);
        }
    }

    /// The header of the table of [`Crossover::row`]s, in Markdown.
    pub fn header(&self, meter: &Meter) -> String {
        let unit = meter.unit();
        format!(
            "| {} | {} {unit} | {} {unit} | ratio | {} bytes | {} bytes | ratio |\n|---|---|---|---|---|---|---|",
            self.unit, self.below.name, self.above.name, self.below.name, self.above.name
        )
    }

    /// One point as a row of the table, in Markdown.
    pub fn row(&self, p: &Point) -> String {
        format!(
            "| {}{} | {} | {} | {:.3} | {} | {} | {:.3} |",
            p.size,
            (self.note)(p.size),
            p.below.units,
            p.above.units,
            p.ratio(),
            p.below.bytes,
            p.above.bytes,
            p.bytes_ratio()
        )
    }
}

/// The work of each of `methods` on each of `inputs`, `work[i][m]` for input `i` and method
/// `m`, after checking that every method gives the first method's output on every input: for a
/// setting with a few possible values, one method per value.
pub fn settings<I, O: PartialEq + Debug>(
    meter: &mut Meter,
    inputs: &[I],
    methods: &[Method<'_, I, O>],
) -> Vec<Vec<Work>> {
    inputs
        .iter()
        .enumerate()
        .map(|(i, x)| {
            let expected = methods.first().map(|m| (m.run)(x));
            methods
                .iter()
                .map(|m| {
                    assert!(
                        Some((m.run)(x)) == expected,
                        "{} gives a different output from {} on input {i}",
                        m.name,
                        methods[0].name
                    );
                    least(meter, || drop(black_box((m.run)(x))))
                })
                .collect()
        })
        .collect()
}

/// The least work and the least bytes of `RUNS` runs of `f`.
pub fn least(meter: &mut Meter, f: impl Fn()) -> Work {
    (0..RUNS)
        .map(|_| meter.work(&f))
        .reduce(|a, b| Work {
            units: a.units.min(b.units),
            bytes: a.bytes.min(b.bytes),
        })
        .expect("at least one run")
}

/// The load average over 1, 5 and 15 minutes, as the system reports it, and the platform, for
/// the head of each table.
pub fn conditions() -> String {
    let load = std::fs::read_to_string("/proc/loadavg")
        .ok()
        .and_then(|s| {
            let fields: Vec<&str> = s.split_whitespace().take(3).collect();
            (fields.len() == 3).then(|| fields.join(" "))
        })
        .unwrap_or_else(|| "not known".into());
    format!(
        "platform {}-{}, load {load}",
        std::env::consts::ARCH,
        std::env::consts::OS
    )
}
