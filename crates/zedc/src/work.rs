//! The work of a compilation by stage, unit and definition (plan item TIME-report): the
//! instructions retired and the bytes allocated, which `zedc --report <command> …` writes to
//! standard error after the command. The port to Zed (row S) is compared with these numbers.
//!
//! The compiler marks each stage with [`stage`], naming the definition it works on where it
//! works on one at a time, and each unit with [`unit()`]; a recorder installed by [`with`] counts
//! the work between the marks. With no recorder installed on the thread, a mark only calls its
//! closure, so a compilation that is not reported does no more than read a thread-local cell
//! per mark.
//!
//! A row's work is its own: the work of the stages marked inside it is in their rows and not
//! in its. The work outside every mark, the reading of the command line and of files, the
//! recorder's own bookkeeping, is the row of [`Stage::Other`]. So the rows sum to the total
//! exactly, both counts being sums that only grow: the work inside a mark is the count after it
//! less the count before it, and each mark's interval holds the intervals of the marks inside
//! it.
//!
//! A row that a query takes from its cache (step L1.30) and does not compute is counted by
//! [`cached`]: its work is zero, and the lookup of the cache is in the row around it.
//!
//! The recorder does not read the counters itself: [`with`] takes a counter from its caller.
//! The `zedc` executable gives one that reads the instructions of the thread from
//! `perf_event_open` and its bytes from the global allocator of `zed-alloc-count`; the tests give
//! their own. This crate is linked into executables that `zedc build` makes, which must keep
//! the system allocator, so it cannot link `zed-alloc-count` itself.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::ops::{Add, AddAssign, Sub};

/// An amount of work: instructions retired and bytes allocated.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct Work {
    /// Instructions retired, in user mode.
    pub instructions: u64,
    /// Bytes allocated; freeing subtracts nothing.
    pub bytes: u64,
}

impl Add for Work {
    type Output = Work;
    fn add(self, o: Work) -> Work {
        Work {
            instructions: self.instructions + o.instructions,
            bytes: self.bytes + o.bytes,
        }
    }
}

impl AddAssign for Work {
    fn add_assign(&mut self, o: Work) {
        *self = *self + o;
    }
}

impl Sub for Work {
    type Output = Work;
    /// The work between two readings of a counter, `self` read after `o`; each count only grows,
    /// so neither part underflows.
    fn sub(self, o: Work) -> Work {
        Work {
            instructions: self.instructions - o.instructions,
            bytes: self.bytes - o.bytes,
        }
    }
}

/// The stages of the compiler, in the order a compilation meets them.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Stage {
    /// Everything outside the other stages: the command line, reading files, the recorder.
    Other,
    /// Checking the bytes of a unit's file as text (`source::load`).
    Load,
    /// The lexer.
    Lex,
    /// The parser.
    Parse,
    /// The statements built from the parse tree, with their errors.
    Syntax,
    /// Name resolution.
    Resolve,
    /// The checks of doc comments.
    Docs,
    /// The type checker, over the whole unit: it checks a function where its uses need it, not
    /// one definition at a time.
    Check,
    /// Elaboration to kernel terms.
    Elaborate,
    /// The linear questions of a function (step L1.38).
    Linear,
    /// `main`'s ports, read from its header.
    Program,
    /// The rows of a definition's test table, and the waves of `main`'s.
    Test,
    /// A wave of `main`.
    Run,
    /// Lowering `main` to ZIR (`zedc build`).
    Lower,
    /// Native code generation (`zedc build`).
    Codegen,
    /// Linking the executable (`zedc build`). The linker is a child process: its instructions
    /// count where the counter counts child processes, as `perf_event_open` does, and its
    /// bytes do not count.
    Link,
}

impl Stage {
    /// The stage's name in the report.
    pub fn name(self) -> &'static str {
        match self {
            Stage::Other => "other",
            Stage::Load => "load",
            Stage::Lex => "lex",
            Stage::Parse => "parse",
            Stage::Syntax => "syntax",
            Stage::Resolve => "resolve",
            Stage::Docs => "docs",
            Stage::Check => "check",
            Stage::Elaborate => "elaborate",
            Stage::Linear => "linear",
            Stage::Program => "program",
            Stage::Test => "test",
            Stage::Run => "run",
            Stage::Lower => "lower",
            Stage::Codegen => "codegen",
            Stage::Link => "link",
        }
    }
}

/// A reading of the counters.
pub type Counter = Box<dyn FnMut() -> Work>;

/// One row of a report: the work of a stage on a unit and, where the stage works on one at a
/// time, a definition.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Row {
    /// The stage.
    pub stage: Stage,
    /// The unit, as the command named its file; `None` for work outside every unit.
    pub unit: Option<Box<str>>,
    /// The definition; `None` for work on the whole unit.
    pub definition: Option<Box<str>>,
    /// The work, not counting the stages marked inside this one.
    pub work: Work,
    /// How many times the stage ran.
    pub computed: u64,
    /// How many times it was taken from a cache instead, at no work.
    pub cached: u64,
}

/// The rows of one recording, in the order each was first met, and the total.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Report {
    /// The rows.
    pub rows: Vec<Row>,
    /// The work from the start of the recording to its end: the sum of the rows.
    pub total: Work,
}

/// A stage being counted.
struct Frame {
    /// Its row.
    row: usize,
    /// The counters when it began.
    start: Work,
    /// The work of the stages marked inside it.
    inner: Work,
}

/// The key of a row: stage, unit number, definition number.
type RowKey = (Stage, Option<u32>, Option<u32>);

/// The recorder of one thread.
struct Recorder {
    counter: Counter,
    /// The units' names, by number.
    units: Names,
    /// The definitions' names, by number.
    definitions: Names,
    /// The current unit.
    unit: Option<u32>,
    rows: Vec<(RowKey, Work, u64, u64)>,
    index: HashMap<RowKey, usize>,
    frames: Vec<Frame>,
}

/// Names, each given a number when first met, so that a row's key is three small numbers and
/// finding the row of a name met before allocates nothing.
#[derive(Default)]
struct Names {
    numbers: HashMap<Box<str>, u32>,
    names: Vec<Box<str>>,
}

impl Names {
    fn number(&mut self, name: &str) -> u32 {
        if let Some(&n) = self.numbers.get(name) {
            return n;
        }
        let n = u32::try_from(self.names.len()).expect("fewer than 2^32 names in one report");
        self.numbers.insert(name.into(), n);
        self.names.push(name.into());
        n
    }
}

impl Recorder {
    fn row(&mut self, stage: Stage, definition: Option<&str>) -> usize {
        let key = (
            stage,
            self.unit,
            definition.map(|d| self.definitions.number(d)),
        );
        let rows = &mut self.rows;
        *self.index.entry(key).or_insert_with(|| {
            rows.push((key, Work::default(), 0, 0));
            rows.len() - 1
        })
    }

    /// Opens a frame on the row of `stage` and `definition`. The counters are read last, so
    /// the bookkeeping is in the frame around this one.
    fn enter(&mut self, stage: Stage, definition: Option<&str>) {
        let row = self.row(stage, definition);
        self.frames.push(Frame {
            row,
            start: Work::default(),
            inner: Work::default(),
        });
        let start = (self.counter)();
        self.frames.last_mut().expect("the frame just pushed").start = start;
    }

    /// Closes the innermost frame and gives its work with the work of the frames inside it.
    /// The counters are read first, so the bookkeeping is in the frame around this one.
    fn exit(&mut self) -> Work {
        let end = (self.counter)();
        let f = self.frames.pop().expect("a frame for each mark");
        let all = end - f.start;
        let row = &mut self.rows[f.row];
        row.1 += all - f.inner;
        row.2 += 1;
        if let Some(outer) = self.frames.last_mut() {
            outer.inner += all;
        }
        all
    }

    fn into_report(self, total: Work) -> Report {
        let Recorder {
            units,
            definitions,
            rows,
            ..
        } = self;
        let name = |names: &Names, n: Option<u32>| n.map(|n| names.names[n as usize].clone());
        Report {
            rows: rows
                .into_iter()
                .map(|((stage, unit, definition), work, computed, cached)| Row {
                    stage,
                    unit: name(&units, unit),
                    definition: name(&definitions, definition),
                    work,
                    computed,
                    cached,
                })
                .collect(),
            total,
        }
    }
}

thread_local! {
    static RECORDER: RefCell<Option<Recorder>> = const { RefCell::new(None) };
}

/// Runs `f`, counting its work on this thread by stage, unit and definition with `counter`, and
/// gives its result and the report. A recording already running on the thread is set aside
/// while `f` runs, and its counts do not include `f`'s stages, which are in the row of the
/// stage around this call.
pub fn with<R>(counter: Counter, f: impl FnOnce() -> R) -> (R, Report) {
    let recorder = Recorder {
        counter,
        units: Names::default(),
        definitions: Names::default(),
        unit: None,
        rows: Vec::new(),
        index: HashMap::new(),
        frames: Vec::new(),
    };
    let outer = RECORDER.replace(Some(recorder));
    RECORDER.with_borrow_mut(|r| {
        r.as_mut()
            .expect("the recorder just installed")
            .enter(Stage::Other, None)
    });
    let out = f();
    let mut recorder = RECORDER
        .replace(outer)
        .expect("the recorder installed by `with`");
    let total = recorder.exit();
    debug_assert!(
        recorder.frames.is_empty(),
        "every mark inside `with` closed"
    );
    (out, recorder.into_report(total))
}

/// Makes `name` the unit of the stages that follow, until the next call.
pub fn unit(name: &str) {
    RECORDER.with_borrow_mut(|r| {
        if let Some(r) = r {
            r.unit = Some(r.units.number(name));
        }
    });
}

/// Runs `f` as the work of `stage` on the current unit and `definition`.
pub fn stage<R>(stage: Stage, definition: Option<&str>, f: impl FnOnce() -> R) -> R {
    let on = RECORDER.with_borrow_mut(|r| match r {
        Some(r) => {
            r.enter(stage, definition);
            true
        }
        None => false,
    });
    let out = f();
    if on {
        RECORDER.with_borrow_mut(|r| r.as_mut().expect("the recorder of the mark").exit());
    }
    out
}

/// Counts a row of `stage` on the current unit and `definition` taken from a cache, at no work.
pub fn cached(stage: Stage, definition: Option<&str>) {
    RECORDER.with_borrow_mut(|r| {
        if let Some(r) = r {
            let row = r.row(stage, definition);
            r.rows[row].3 += 1;
        }
    });
}

impl fmt::Display for Report {
    /// A header, a line per row in the order the rows were first met, and the total, in columns:
    /// stage, unit, definition, instructions, bytes, computed, cached. A missing unit or
    /// definition is `-`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = [
            "stage",
            "unit",
            "definition",
            "instructions",
            "bytes",
            "computed",
            "cached",
        ];
        let cells = |r: &Row| {
            [
                r.stage.name().to_string(),
                r.unit.as_deref().unwrap_or("-").to_string(),
                r.definition.as_deref().unwrap_or("-").to_string(),
                r.work.instructions.to_string(),
                r.work.bytes.to_string(),
                r.computed.to_string(),
                r.cached.to_string(),
            ]
        };
        let total = [
            "total".to_string(),
            String::new(),
            String::new(),
            self.total.instructions.to_string(),
            self.total.bytes.to_string(),
            String::new(),
            String::new(),
        ];
        let lines: Vec<[String; 7]> = std::iter::once(head.map(str::to_string))
            .chain(self.rows.iter().map(cells))
            .chain(std::iter::once(total))
            .collect();
        let mut width = [0; 7];
        for l in &lines {
            for (w, c) in width.iter_mut().zip(l) {
                *w = (*w).max(c.chars().count());
            }
        }
        for l in &lines {
            // Names to the left, numbers to the right.
            let line = format!(
                "{:<w0$}  {:<w1$}  {:<w2$}  {:>w3$}  {:>w4$}  {:>w5$}  {:>w6$}",
                l[0],
                l[1],
                l[2],
                l[3],
                l[4],
                l[5],
                l[6],
                w0 = width[0],
                w1 = width[1],
                w2 = width[2],
                w3 = width[3],
                w4 = width[4],
                w5 = width[5],
                w6 = width[6],
            );
            writeln!(f, "{}", line.trim_end())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::rc::Rc;

    /// A counter that reads `clock` as instructions and twice it as bytes, and the clock, which
    /// the test moves to stand for work done.
    fn clock() -> (Counter, Rc<Cell<u64>>) {
        let c = Rc::new(Cell::new(0));
        let read = Rc::clone(&c);
        let counter = move || Work {
            instructions: read.get(),
            bytes: 2 * read.get(),
        };
        (Box::new(counter), c)
    }

    fn work(n: u64) -> Work {
        Work {
            instructions: n,
            bytes: 2 * n,
        }
    }

    fn row<'a>(r: &'a Report, stage: Stage, definition: Option<&str>) -> &'a Row {
        r.rows
            .iter()
            .find(|x| x.stage == stage && x.definition.as_deref() == definition)
            .unwrap_or_else(|| panic!("no row {stage:?} {definition:?} in\n{r}"))
    }

    #[test]
    fn each_row_holds_its_own_work_and_the_rows_sum_to_the_total() {
        let (counter, c) = clock();
        let tick = |n| c.set(c.get() + n);
        let ((), r) = with(counter, || {
            tick(1);
            unit("a.zed");
            stage(Stage::Check, None, || {
                tick(10);
                stage(Stage::Test, Some("f"), || tick(100));
                tick(10);
                stage(Stage::Test, Some("g"), || tick(1000));
                stage(Stage::Test, Some("f"), || tick(100));
            });
            tick(1);
        });
        assert_eq!(row(&r, Stage::Other, None).work, work(2));
        assert_eq!(row(&r, Stage::Check, None).work, work(20));
        let f = row(&r, Stage::Test, Some("f"));
        assert_eq!((f.work, f.computed, f.cached), (work(200), 2, 0));
        assert_eq!(row(&r, Stage::Test, Some("g")).work, work(1000));
        assert_eq!(f.unit.as_deref(), Some("a.zed"));
        assert_eq!(r.total, work(1222));
        let sum = r.rows.iter().fold(Work::default(), |s, x| s + x.work);
        assert_eq!(sum, r.total);
    }

    #[test]
    fn a_cached_row_counts_no_work() {
        let (counter, c) = clock();
        let ((), r) = with(counter, || {
            cached(Stage::Test, Some("f"));
            c.set(c.get() + 5);
            cached(Stage::Test, Some("f"));
        });
        let f = row(&r, Stage::Test, Some("f"));
        assert_eq!((f.work, f.computed, f.cached), (Work::default(), 0, 2));
        assert_eq!(row(&r, Stage::Other, None).work, work(5));
    }

    #[test]
    fn units_keep_their_rows_apart() {
        let (counter, c) = clock();
        let ((), r) = with(counter, || {
            for (u, n) in [("a.zed", 3), ("b.zed", 7), ("a.zed", 3)] {
                unit(u);
                stage(Stage::Lex, None, || c.set(c.get() + n));
            }
        });
        let lex: Vec<_> = r
            .rows
            .iter()
            .filter(|x| x.stage == Stage::Lex)
            .map(|x| (x.unit.as_deref(), x.work.instructions, x.computed))
            .collect();
        assert_eq!(lex, [(Some("a.zed"), 6, 2), (Some("b.zed"), 7, 1)]);
    }

    #[test]
    fn with_no_recorder_a_mark_only_runs_its_closure() {
        assert_eq!(stage(Stage::Lex, Some("f"), || 7), 7);
        cached(Stage::Lex, None);
        unit("a.zed");
        RECORDER.with_borrow(|r| assert!(r.is_none()));
    }

    #[test]
    fn a_recording_inside_another_is_counted_in_the_outer_stage_around_it() {
        let (outer, c) = clock();
        let (inner_report, r) = with(outer, || {
            stage(Stage::Run, None, || {
                let (inner, d) = clock();
                let ((), inner_report) = with(inner, || {
                    stage(Stage::Lex, None, || d.set(4));
                    c.set(c.get() + 9);
                });
                inner_report
            })
        });
        assert_eq!(inner_report.total.instructions, 4);
        assert!(r.rows.iter().all(|x| x.stage != Stage::Lex), "{r}");
        assert_eq!(row(&r, Stage::Run, None).work, work(9));
    }

    #[test]
    fn the_report_is_a_table_with_a_total() {
        let (counter, c) = clock();
        let ((), r) = with(counter, || {
            unit("a.zed");
            stage(Stage::Test, Some("f"), || c.set(12));
        });
        assert_eq!(
            r.to_string(),
            "stage  unit   definition  instructions  bytes  computed  cached\n\
             other  -      -                      0      0         1       0\n\
             test   a.zed  f                     12     24         1       0\n\
             total                               12     24\n"
        );
    }
}
