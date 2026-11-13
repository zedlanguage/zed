//! One row of a test table, run (step L1.21): a row of a function's table, whose call must
//! equal the expected value, and a row of `main`'s table, a wave. The test runner
//! (`crate::testing`) and the mutation pass (`crate::mutate`, step L25.8) both run rows here,
//! the second with a definition swapped for a mutant.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use zed_kernel::{Evaluator, Lookup, Shared, Term, Value, World};

use crate::elab::{Cones, MAIN_KEY, Test};
use crate::interp;
use crate::run::{PortKind, Program, Through};

/// A definition of the unit and the term that replaces its own (step L25.8, a mutant): its
/// position in the unit and the term.
pub(crate) type Swap<'a> = Option<(usize, &'a Shared)>;

/// The value of `term` under the definitions it reaches, with `swap`, and the prelude.
fn value(
    cones: &Cones<'_>,
    swap: Swap<'_>,
    term: &Term,
    map: &Through<'_>,
) -> Result<Value, String> {
    map(
        &interp::prelude(cones.close_with(term.clone(), swap)),
        &mut Evaluator::new(World::new()),
    )
}

/// Checks a row of a function's table, with `swap`.
pub(crate) fn row(
    cones: &Cones<'_>,
    swap: Swap<'_>,
    t: &Test,
    map: &Through<'_>,
) -> Result<(), String> {
    match value(cones, swap, &t.check, map)? {
        Value::Bool(true) => Ok(()),
        _ => {
            let Term::Prim(_, sides) = &t.check else {
                unreachable!("a check is `call == want`")
            };
            Err(format!(
                "the result is {}",
                value(cones, swap, &sides[0], map)?
            ))
        }
    }
}

/// Checks a row of `main`'s table: runs the wave its key gives, and compares the writes. With
/// `swap`, the wave runs `main` closed under the unit with `swap`.
pub(crate) fn wave(
    cones: &Cones<'_>,
    swap: Swap<'_>,
    program: &Program,
    t: &Test,
    map: &Through<'_>,
) -> Result<(), String> {
    // The name a field of `MainArgs` has in this program: `m.stdin`, or `stdin` in `main()`.
    let named = |f: &str| match program.param() {
        Some(p) if f != "files()" => format!("{p}.{f}"),
        _ => f.to_string(),
    };
    // The key gives the inputs by field (`MAIN_KEY`), so a row means the same whichever fields
    // the body reads, and each item is checked whether the body reads it or not; an input the
    // key leaves out is empty.
    let mut stdin: Arc<[u8]> = Arc::from(&b""[..]);
    let mut args = Vec::new();
    let mut lookups: HashMap<&str, Arc<dyn Lookup>> = HashMap::new();
    for (f, arg) in MAIN_KEY.iter().zip(&t.args) {
        match *f {
            "stdin" => match value(cones, swap, arg, map)? {
                Value::Str(s) => stdin = Arc::from(s.flat().as_bytes()),
                v => {
                    return Err(format!(
                        "the `Lines` port `{}` is given as a String, not {v}",
                        named(f)
                    ));
                }
            },
            "args" => match value(cones, swap, arg, map)? {
                Value::Str(s) => args = given_args(&s.flat()),
                v => {
                    return Err(format!(
                        "the `CommandLine` port `{}` is given as a String, one argument per \
                         line, not {v}",
                        named(f)
                    ));
                }
            },
            _ => {
                let given = Given(interp::prelude(cones.close_with(arg.clone(), swap)));
                lookups.insert(f, Arc::new(given));
            }
        }
    }
    let mut lines = BTreeMap::new();
    let mut files: BTreeMap<&str, Arc<dyn Lookup>> = BTreeMap::new();
    for (name, kind) in program.inputs() {
        match kind {
            PortKind::Lines => {
                lines.insert(name.clone(), Arc::clone(&stdin));
            }
            PortKind::Files | PortKind::Env => {
                let given = lookups.get(field(name)).cloned();
                files.insert(name, given.unwrap_or_else(|| Arc::new(NotFound)));
            }
            PortKind::CommandLine => {}
        }
    }
    let wave = match swap {
        None => program.run_through(&lines, &args, |name| files[name].clone(), map)?,
        Some(_) => {
            let main = program.unit.defs.iter().find(|d| d.name == "main");
            let main = Term::Var(main.expect("`main` was elaborated").kernel.clone());
            let main = cones.close_with(main, swap);
            program.run_main_through(&main, &lines, &args, |name| files[name].clone(), map)?
        }
    };
    // The value is standard output, or `(stdout, stderr)`, or `(stdout, stderr, status)`;
    // what it leaves out is `""`, and the status 0.
    let wants = match value(cones, swap, &t.want, map)? {
        Value::Tuple(xs) if (2..=3).contains(&xs.len()) => xs.into_vec(),
        v @ Value::Tuple(_) => {
            return Err(format!(
                "the expected value of a row of `main` is the standard output of the run, as a \
                 String, or the tuple `(stdout, stderr)` or `(stdout, stderr, status)`, not {v}"
            ));
        }
        v => vec![v],
    };
    // The first write to each port, by the field it is.
    let mut written: HashMap<&str, &[u8]> = HashMap::new();
    for (p, b) in &wave.writes {
        written.entry(field(p)).or_insert(&b[..]);
    }
    for (f, want) in MAIN_OUTPUTS.iter().zip(&wants) {
        let name = named(f);
        let got = written.get(f).copied().unwrap_or_default();
        let Value::Str(want) = want else {
            return Err(format!(
                "the expected value of `{name}` is a String, not {want}"
            ));
        };
        if got != want.flat().as_bytes() {
            let got = Value::str(&String::from_utf8_lossy(got));
            return Err(format!("`{name}` writes {got}"));
        }
    }
    let status = match wants.get(2) {
        None => 0,
        Some(Value::Int(n)) if (0..=255).contains(n) => *n,
        Some(v) => {
            return Err(format!(
                "the expected status of a row of `main` is an int from 0 to 255, not {v}"
            ));
        }
    };
    if i64::from(wave.status) != status {
        return Err(format!("the run exits with status {}", wave.status));
    }
    Ok(())
}

/// The output fields of `MainArgs` in the order a row's value gives them.
const MAIN_OUTPUTS: [&str; 2] = ["stdout", "stderr"];

/// The field of `MainArgs` the port `name` of `main` is, as `stdin` for `m.stdin`, or
/// `files()`.
fn field(name: &str) -> &str {
    name.rsplit_once('.').map_or(name, |(_, f)| f)
}

/// The `Files` or environment port of an input a row's key leaves out: every read is
/// `#notFound`.
#[derive(Debug)]
struct NotFound;

impl Lookup for NotFound {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(Value::atom("notFound"))
    }
}

/// The arguments a test gives a `CommandLine` port as the `String` `s`, one per line, the
/// lines read as a `Lines` input's are: a line ends at `\n`, at `\r\n` or at a lone `\r`, and a
/// last line needs no line end.
fn given_args(s: &str) -> Vec<String> {
    let mut lines = Vec::new();
    zed_kernel::lines::LineReader::whole(s.as_bytes(), |l| {
        // A cut of UTF-8 text at `\r` or `\n`, which are never part of another character's
        // encoding, is UTF-8.
        lines.push(String::from_utf8_lossy(l).into_owned());
    });
    lines
}

/// A `Files` port a test gives as a function from path to contents.
#[derive(Debug)]
struct Given(Term);

impl Lookup for Given {
    fn get(&self, key: &Value) -> Result<Value, String> {
        let read = Term::App(Shared::new(self.0.clone()), vec![Term::Lit(key.clone())]);
        Evaluator::new(World::new())
            .run(&read)
            .map_err(|e| e.to_string())
    }
}
