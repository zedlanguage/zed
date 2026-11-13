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
//! after every change to the code of either method, or to the code generation, that changes
//! its speed, resetting each threshold whose crossover moved by more than the spread of
//! repeated runs. The work is counted in instructions where the hardware counts them
//! ([`zed_tests::scaling::Meter`]), which load does not change, in the build the tests use (the
//! `dev` profile); the load is printed with each table all the same.
//!
//! [`Crossover`] is for a threshold on the size of the input: it measures at given sizes, then
//! halves the interval in which the faster method changes until it is narrower than a given
//! fraction, and reports the least measured size from which the second method is never slower
//! at any measured size. [`settings`] is for a setting with a few possible values (a leaf width,
//! say): it measures each value on each input and checks that every value gives the same
//! output. Both judge the threshold as built by a [`Verdict`]: at every size measured, the
//! method the code takes must do at most the work of the method the measured crossover takes
//! there times the spread of repeated runs. Where a constant of a cost model decides and not a
//! size, [`Constant::steps`] and [`Steps::fit`] find the values of the constant that best match
//! the measurements.
//! The binary `crossover` runs the benchmarks one by one, or all of them (`crossover all`);
//! COMPLEXITY.md section "Crossovers" records what they measured.

use std::fmt::Debug;
use std::hint::black_box;

use zed_tests::scaling::{Meter, Work};

/// How many runs each measurement takes: the least is the measurement, and the most over the
/// least is the spread of repeated runs. Instruction counts of the same run differ by a
/// fraction of a percent, mostly in the first run, which finds the allocator cold.
pub const RUNS: usize = 3;

/// The work of [`RUNS`] runs of the same code.
#[derive(Clone, Copy, Debug)]
pub struct Runs {
    /// The least work and the least bytes.
    pub least: Work,
    /// The most work, in the meter's unit.
    pub most: u64,
}

impl Runs {
    /// The most work over the least, at least 1.
    pub fn spread(&self) -> f64 {
        self.most as f64 / self.least.units as f64
    }
}

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
    /// The greater of the two methods' spreads of repeated runs here.
    pub spread: f64,
    /// Whether the code as built takes the second method at this size.
    pub takes_above: bool,
    /// The value of the benchmark's cost constant at which the code changes method here
    /// ([`Constant::flip`]), when it has one and it decides here.
    pub flip: Option<f64>,
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

    /// The work of the method the code takes over that of the method `threshold` takes here.
    pub fn taken_over(&self, threshold: Threshold) -> f64 {
        match (self.takes_above, threshold.takes_above(self.size)) {
            (true, false) => self.ratio(),
            (false, true) => 1.0 / self.ratio(),
            _ => 1.0,
        }
    }

    /// The least work of the two methods here.
    pub fn least(&self) -> u64 {
        self.below.units.min(self.above.units)
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

impl Threshold {
    /// Whether the second method is taken at `size` with this threshold.
    pub fn takes_above(self, size: usize) -> bool {
        match self {
            Threshold::AtOrBelow(_) => true,
            Threshold::At(s) => size >= s,
            Threshold::Above(_) => false,
        }
    }

    /// Whether `size` lies within `tolerance` of this threshold, where the measured crossover
    /// is not known more closely: `s / (1 + tolerance) <= size <= s (1 + tolerance)`.
    pub fn near(self, size: usize, tolerance: f64) -> bool {
        match self {
            Threshold::At(s) => {
                let (s, size) = (s as f64, size as f64);
                size * (1.0 + tolerance) >= s && size <= s * (1.0 + tolerance)
            }
            _ => false,
        }
    }
}

impl std::fmt::Display for Threshold {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Threshold::AtOrBelow(s) => write!(f, "at or below {s}"),
            Threshold::At(s) => write!(f, "{s}"),
            Threshold::Above(s) => write!(f, "above {s}"),
        }
    }
}

/// Whether a threshold as built sits at the measured crossover: at each size measured, the
/// work of the method the code takes over the other's, the worst of them, against the spread
/// of repeated runs.
#[derive(Clone, Copy, Debug)]
pub struct Verdict {
    /// The greatest work of the method taken over the other's, at any size measured.
    pub worst: f64,
    /// The size where it is.
    pub at: usize,
    /// The greatest spread of repeated runs at any size measured.
    pub spread: f64,
}

impl Verdict {
    /// Whether the code's method is never slower than the other by more than the spread of
    /// repeated runs: if it is, the crossover has moved away from the threshold.
    pub fn holds(&self) -> bool {
        self.worst <= self.spread
    }

    /// The verdict over the points of a [`Crossover`] whose measured crossover is `threshold`:
    /// at each size measured, the work of the method the code takes over that of the method
    /// the measured crossover takes ([`Point::taken_over`]), at least 1. Sizes within
    /// `tolerance` of the measured crossover are not judged, as it is known only to that
    /// width. Where the faster method changes more than once, the code may do better than any
    /// one threshold, which gives a ratio below 1 and does not count against it.
    pub fn of(points: &[Point], threshold: Threshold, tolerance: f64) -> Verdict {
        let mut v = Verdict {
            worst: 1.0,
            at: points.first().map_or(0, |p| p.size),
            spread: 1.0,
        };
        for p in points {
            v.spread = v.spread.max(p.spread);
            if threshold.near(p.size, tolerance) {
                continue;
            }
            let r = p.taken_over(threshold);
            if r > v.worst {
                (v.worst, v.at) = (r, p.size);
            }
        }
        v
    }

    /// The line `crossover all` collects for a benchmark: its name, the threshold as built,
    /// the measured crossover, the worst ratio with where it is (`at`), the spread, and the
    /// verdict, separated by tabs.
    pub fn line(&self, name: &str, built: &str, measured: &str, at: &str) -> String {
        let mark = match self.holds() {
            true => "at the crossover",
            false => "MOVED",
        };
        format!(
            "RESULT\t{name}\t{built}\t{measured}\t{:.4} {at}\t{:.4}\t{mark}",
            self.worst, self.spread
        )
    }
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
    /// Whether the code as built takes the second method for an input, the first at a size.
    pub takes_above: &'a dyn Fn(&I) -> bool,
    /// The cost constant that decides between the methods, where a cost model and not a size
    /// threshold decides: its value is then fitted to the measurements
    /// ([`Constant::steps`], [`Steps::fit`]).
    pub constant: Option<Constant<'a, I>>,
}

/// A constant of a cost model that decides between two methods: the code takes the first
/// method for an input when the constant is at most a value the input gives, its flip, or at
/// least it, as `below_at_most` says. Such a constant has no size at which it is set; it is
/// set at the value that best matches the measured costs at every size.
pub struct Constant<'a, I> {
    /// Its name and value as built, for the tables ("TOOM_COST 6.8").
    pub name: &'static str,
    /// Its value as built.
    pub built: f64,
    /// The value of the constant at which the code changes method for an input; `None` where
    /// the constant does not decide (another threshold does).
    pub flip: &'a dyn Fn(&I) -> Option<f64>,
    /// Whether the code takes the first method when the constant is at most the flip (else at
    /// least the flip).
    pub below_at_most: bool,
}

/// The values of a [`Constant`] that best match the measurements: from `lo` to `hi`, the code
/// takes a method with at most `worst` times the least work of the two at every size measured.
#[derive(Clone, Copy, Debug)]
pub struct Fit {
    /// The least value of the range; 0 if it has no lower end.
    pub lo: f64,
    /// The greatest value of the range; infinite if it has no upper end.
    pub hi: f64,
    /// The greatest work of the method taken over the least of the two, at any size measured,
    /// for a value in the range.
    pub worst: f64,
}

impl Fit {
    /// The value to set: the geometric mean of the ends, or the end there is, to two digits.
    pub fn value(&self) -> f64 {
        let v = match (self.lo > 0.0, self.hi.is_finite()) {
            (true, true) => (self.lo * self.hi).sqrt(),
            (true, false) => self.lo,
            (false, true) => self.hi,
            (false, false) => 1.0,
        };
        let scale = 10f64.powf(v.log10().floor() - 1.0);
        (v / scale).round() * scale
    }
}

impl std::fmt::Display for Fit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = self.value();
        let digits = (1.0 - v.log10().floor()).max(0.0) as usize;
        write!(
            f,
            "{:.4} to {:.4}, worst {:.4}, set {v:.digits$}",
            self.lo, self.hi, self.worst
        )
    }
}

/// The worst work, over the sizes of one or more benchmarks, of the method a [`Constant`]
/// takes over the least of the two, for each range of its values: a step function, as the
/// choice at a size changes only where the constant passes that size's flip.
#[derive(Clone, Debug)]
pub struct Steps {
    /// The constant's name.
    pub name: String,
    /// Its value as built.
    pub built: f64,
    /// The worst work at the value as built.
    pub built_worst: f64,
    /// The greatest spread of repeated runs at any size measured.
    pub spread: f64,
    /// The ranges in order, `(lo, hi, worst)`, from 0 to infinity, each ending where the next
    /// begins.
    pub steps: Vec<(f64, f64, f64)>,
}

impl Steps {
    /// The worst work at `c`, for `c` inside a range (not at an end).
    fn at(&self, c: f64) -> f64 {
        self.steps
            .iter()
            .find(|&&(_, hi, _)| c < hi)
            .map_or(1.0, |s| s.2)
    }

    /// The first run of ranges with the least worst work.
    pub fn fit(&self) -> Fit {
        let least = self.steps.iter().map(|s| s.2).fold(f64::INFINITY, f64::min);
        let first = self
            .steps
            .iter()
            .position(|s| s.2 == least)
            .expect("a range");
        let last = first
            + self.steps[first..]
                .iter()
                .take_while(|s| s.2 == least)
                .count()
            - 1;
        Fit {
            lo: self.steps[first].0,
            hi: self.steps[last].1,
            worst: least,
        }
    }

    /// Whether the value as built does at most the work of the best fit times the spread.
    pub fn holds(&self) -> bool {
        self.built_worst <= self.fit().worst * self.spread
    }

    /// The line `crossover all` collects: `FIT`, the name, the value as built, its worst work,
    /// the spread, then `lo:hi:worst` for each range, separated by tabs.
    pub fn line(&self) -> String {
        let steps: Vec<String> = self
            .steps
            .iter()
            .map(|(lo, hi, w)| format!("{lo}:{hi}:{w}"))
            .collect();
        format!(
            "FIT\t{}\t{}\t{}\t{}\t{}",
            self.name,
            self.built,
            self.built_worst,
            self.spread,
            steps.join("\t")
        )
    }

    /// The [`Steps`] of a [`Steps::line`], or `None` if it is not one.
    pub fn parse(line: &str) -> Option<Steps> {
        let mut fields = line.strip_prefix("FIT\t")?.split('\t');
        let name = fields.next()?.to_string();
        let mut num = || fields.next()?.parse::<f64>().ok();
        let (built, built_worst, spread) = (num()?, num()?, num()?);
        let steps = fields
            .map(|s| {
                let v: Vec<f64> = s.split(':').filter_map(|x| x.parse().ok()).collect();
                (v.len() == 3).then(|| (v[0], v[1], v[2]))
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Steps {
            name,
            built,
            built_worst,
            spread,
            steps,
        })
    }

    /// The steps of the same constant over several benchmarks: at each value, the worst of
    /// theirs. The ends of all their ranges, sorted, bound the joint ranges: n log n for n
    /// ends, each range found by a scan here as the benchmarks have a few dozen ranges each.
    pub fn joint(all: &[Steps]) -> Steps {
        let mut ends: Vec<f64> = all
            .iter()
            .flat_map(|s| s.steps.iter().map(|r| r.1))
            .filter(|e| e.is_finite())
            .collect();
        ends.sort_by(f64::total_cmp);
        ends.dedup();
        let mut lo = 0.0;
        let mut steps = Vec::new();
        for hi in ends.into_iter().chain([f64::INFINITY]) {
            let c = inside(lo, hi);
            let w = all.iter().map(|s| s.at(c)).fold(1.0, f64::max);
            match steps.last_mut() {
                Some((_, h, last)) if *last == w => *h = hi,
                _ => steps.push((lo, hi, w)),
            }
            lo = hi;
        }
        Steps {
            name: all.first().map_or(String::new(), |s| s.name.clone()),
            built: all.first().map_or(0.0, |s| s.built),
            built_worst: all.iter().map(|s| s.built_worst).fold(1.0, f64::max),
            spread: all.iter().map(|s| s.spread).fold(1.0, f64::max),
            steps,
        }
    }
}

/// A value inside the range from `lo` to `hi`, either end missing (0 or infinite).
fn inside(lo: f64, hi: f64) -> f64 {
    match (lo > 0.0, hi.is_finite()) {
        (true, true) => (lo + hi) / 2.0,
        (true, false) => lo * 2.0,
        (false, true) => hi / 2.0,
        (false, false) => 1.0,
    }
}

impl<I> Constant<'_, I> {
    /// Whether the code takes the second method at `p` when the constant is `c`.
    fn takes_above(&self, p: &Point, c: f64) -> bool {
        match p.flip {
            None => p.takes_above,
            Some(f) => match self.below_at_most {
                true => c > f,
                false => c < f,
            },
        }
    }

    /// The worst, over `points`, of the work of the method taken with the constant at `c`
    /// over the least of the two.
    fn worst(&self, points: &[Point], c: f64) -> f64 {
        points
            .iter()
            .map(|p| {
                let taken = match self.takes_above(p, c) {
                    true => p.above.units,
                    false => p.below.units,
                };
                taken as f64 / p.least() as f64
            })
            .fold(1.0, f64::max)
    }

    /// The worst work over `points` for each range of the constant's values. The choice at
    /// each point changes only at a flip, so one value between each two flips in order, and
    /// one beyond each end, stands for every value there: n log n for the sort of n flips,
    /// then n for each of the n + 1 ranges, as a benchmark measures a few dozen sizes.
    pub fn steps(&self, points: &[Point]) -> Steps {
        // A flip at or below 0 leaves the choice the same at every value of the constant.
        let mut flips: Vec<f64> = points
            .iter()
            .filter_map(|p| p.flip)
            .filter(|&f| f > 0.0)
            .collect();
        flips.sort_by(f64::total_cmp);
        flips.dedup();
        let mut lo = 0.0;
        let mut steps = Vec::new();
        for hi in flips.into_iter().chain([f64::INFINITY]) {
            steps.push((lo, hi, self.worst(points, inside(lo, hi))));
            lo = hi;
        }
        Steps {
            name: self.name.to_string(),
            built: self.built,
            built_worst: self.worst(points, self.built),
            spread: points.iter().map(|p| p.spread).fold(1.0, f64::max),
            steps,
        }
    }
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
        let below = runs(meter, || drop(black_box((self.below.run)(x))));
        let above = runs(meter, || drop(black_box((self.above.run)(x))));
        Point {
            size,
            below: below.least,
            above: above.least,
            spread: below.spread().max(above.spread()),
            takes_above: (self.takes_above)(x),
            flip: self.constant.as_ref().and_then(|c| (c.flip)(x)),
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
            "| {} | {} {unit} | {} {unit} | ratio | {} bytes | {} bytes | ratio | spread | built takes |\n|---|---|---|---|---|---|---|---|---|",
            self.unit, self.below.name, self.above.name, self.below.name, self.above.name
        )
    }

    /// One point as a row of the table, in Markdown.
    pub fn row(&self, p: &Point) -> String {
        format!(
            "| {}{} | {} | {} | {:.3} | {} | {} | {:.3} | {:.4} | {} |",
            p.size,
            (self.note)(p.size),
            p.below.units,
            p.above.units,
            p.ratio(),
            p.below.bytes,
            p.above.bytes,
            p.bytes_ratio(),
            p.spread,
            match p.takes_above {
                true => self.above.name,
                false => self.below.name,
            }
        )
    }

    /// [`Crossover::find`] over `sizes`, the table printed, and the line of `crossover all`
    /// for the benchmark `name` of the constants `constants` (their names and values as
    /// built): where the code as built takes the second method among the sizes measured, the
    /// measured crossover, and the [`Verdict`].
    pub fn report(
        &self,
        meter: &mut Meter,
        name: &str,
        constants: &str,
        sizes: &[usize],
        tolerance: f64,
    ) -> Verdict {
        println!("{name}: {constants}, {}", conditions());
        let (points, threshold) = self.find(meter, sizes, tolerance);
        println!("{}", self.header(meter));
        for p in &points {
            println!("{}", self.row(p));
        }
        // Where a constant decides, the sizes it decides at are judged by its fit, over every
        // benchmark of the constant (`crossover all`); the rest by the measured crossover.
        let judged: Vec<Point> = points
            .iter()
            .filter(|p| self.constant.is_none() || p.flip.is_none())
            .copied()
            .collect();
        let verdict = Verdict::of(&judged, threshold, tolerance);
        let built = taken_from(&points);
        println!(
            "built: {} from {built} {unit}; measured crossover: {threshold} {unit}",
            self.above.name,
            unit = self.unit
        );
        let mut measured = format!("{threshold} {}", self.unit);
        if let Some(c) = &self.constant {
            let steps = c.steps(&points);
            let fit = steps.fit();
            println!(
                "{} as built {}, worst {:.4}; best fit over these sizes: {fit}",
                c.name, c.built, steps.built_worst
            );
            println!("{}", steps.line());
            measured = format!("{measured}; {} {fit}", c.name);
        }
        println!("{}", conditions());
        println!(
            "{}",
            verdict.line(
                name,
                &format!("{constants}: from {built}"),
                &measured,
                &format!("at {} {}", verdict.at, self.unit)
            )
        );
        verdict
    }
}

/// Where the code as built takes the second method among `points`, in order of size: the
/// least measured size from which it takes it at every size measured.
pub fn taken_from(points: &[Point]) -> Threshold {
    match points.iter().rposition(|p| !p.takes_above) {
        None => Threshold::AtOrBelow(points[0].size),
        Some(j) if j + 1 == points.len() => Threshold::Above(points[j].size),
        Some(j) => Threshold::At(points[j + 1].size),
    }
}

/// The work of each of `methods` on each of `inputs`, `work[i][m]` for input `i` and method
/// `m`, after checking that every method gives the first method's output on every input: for a
/// setting with a few possible values, one method per value.
pub fn settings<I, O: PartialEq + Debug>(
    meter: &mut Meter,
    inputs: &[I],
    methods: &[Method<'_, I, O>],
) -> Vec<Vec<Runs>> {
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
                    runs(meter, || drop(black_box((m.run)(x))))
                })
                .collect()
        })
        .collect()
}

/// For the work of [`settings`]: each setting's work summed over the inputs, each input's as
/// a multiple of the least of any setting there; the setting of least sum; and the
/// [`Verdict`] on the setting `built`, the value as built: its sum over the least sum, `at`
/// the index of the setting of least sum. A setting is judged by its sum, as no one setting
/// need be the least at every input.
pub fn least_setting(work: &[Vec<Runs>], built: usize) -> (Vec<f64>, usize, Verdict) {
    let best: Vec<u64> = work
        .iter()
        .map(|row| row.iter().map(|w| w.least.units).min().expect("a setting"))
        .collect();
    let settings = work.first().map_or(0, Vec::len);
    let sums: Vec<f64> = (0..settings)
        .map(|m| {
            (0..work.len())
                .map(|i| work[i][m].least.units as f64 / best[i] as f64)
                .sum()
        })
        .collect();
    let chosen = (0..settings)
        .min_by(|&x, &y| sums[x].total_cmp(&sums[y]))
        .expect("a setting");
    let spread = work.iter().flatten().map(Runs::spread).fold(1.0, f64::max);
    let verdict = Verdict {
        worst: sums[built] / sums[chosen],
        at: chosen,
        spread,
    };
    (sums, chosen, verdict)
}

/// A setting with a few possible values, measured by [`settings`] and judged by
/// [`least_setting`].
pub struct Setting<'a, I, O> {
    /// The benchmark's name, for the line of `crossover all`.
    pub name: &'static str,
    /// The setting's name and value as built ("LEAF_DIGITS 1024").
    pub constant: String,
    /// What the values count ("digits").
    pub unit: &'static str,
    /// The values, one per method, in order.
    pub values: Vec<String>,
    /// The index in `values` of the value as built.
    pub built: usize,
    /// A label for each input, in order.
    pub labels: Vec<String>,
    /// The inputs.
    pub inputs: Vec<I>,
    /// One method per value.
    pub methods: Vec<Method<'a, I, O>>,
}

impl<I, O: PartialEq + Debug> Setting<'_, I, O> {
    /// Every value on every input, the table printed in Markdown, and the line of `crossover
    /// all`.
    pub fn report(&self, meter: &mut Meter) -> Verdict {
        println!("{}: {}, {}", self.name, self.constant, conditions());
        let work = settings(meter, &self.inputs, &self.methods);
        let (sums, chosen, verdict) = least_setting(&work, self.built);
        let unit = meter.unit();
        print!("| {} |", self.unit);
        for label in &self.labels {
            print!(" {label}, {unit} | bytes |");
        }
        println!(" sum of work over the least at each input |");
        println!("|---|{}---|", "---|---|".repeat(self.labels.len()));
        for (m, value) in self.values.iter().enumerate() {
            print!("| {value} |");
            for row in &work {
                print!(" {} | {} |", row[m].least.units, row[m].least.bytes);
            }
            println!(" {:.4} |", sums[m]);
        }
        println!(
            "built: {} {unit}; least work: {} {unit}, {:.4} times the least at each input, summed",
            self.values[self.built],
            self.values[chosen],
            sums[chosen],
            unit = self.unit
        );
        println!("{}", conditions());
        println!(
            "{}",
            verdict.line(
                self.name,
                &format!("{}: {}", self.constant, self.values[self.built]),
                &format!("{} {}", self.values[chosen], self.unit),
                &format!("against {}", self.values[chosen])
            )
        );
        verdict
    }
}

/// The least work and bytes, and the most work, of [`RUNS`] runs of `f`.
pub fn runs(meter: &mut Meter, f: impl Fn()) -> Runs {
    let mut all = (0..RUNS).map(|_| meter.work(&f));
    let first = all.next().expect("at least one run");
    all.fold(
        Runs {
            least: first,
            most: first.units,
        },
        |r, w| Runs {
            least: Work {
                units: r.least.units.min(w.units),
                bytes: r.least.bytes.min(w.bytes),
            },
            most: r.most.max(w.units),
        },
    )
}

/// The least work and the least bytes of [`RUNS`] runs of `f`.
pub fn least(meter: &mut Meter, f: impl Fn()) -> Work {
    runs(meter, f).least
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
