//! One row of a test table, run (step L1.21): a row of a function's table, whose call must
//! equal the expected value, and a row of `main`'s table, a wave. The test runner
//! (`crate::testing`) and the mutation pass (`crate::mutate`, step L25.8) both run rows here,
//! the second with a definition swapped for a mutant.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use zed_kernel::{Evaluator, Lookup, Shared, Term, Value, World};

use crate::elab::{Cones, Test};
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
    let mut lines = BTreeMap::new();
    let mut files: BTreeMap<&str, Arc<dyn Lookup>> = BTreeMap::new();
    // The arguments the first `CommandLine` port is given, and its name.
    let mut args: Option<(&str, Vec<String>)> = None;
    for ((name, kind), arg) in program.inputs().iter().zip(&t.args) {
        match kind {
            PortKind::Lines => match value(cones, swap, arg, map)? {
                Value::Str(s) => {
                    lines.insert(name.clone(), Arc::from(s.flat().as_bytes()));
                }
                v => {
                    return Err(format!(
                        "the `Lines` port `{name}` is given as a String, not {v}"
                    ));
                }
            },
            PortKind::Files | PortKind::Env => {
                files.insert(
                    name,
                    Arc::new(Given(interp::prelude(cones.close_with(arg.clone(), swap)))),
                );
            }
            PortKind::CommandLine => match value(cones, swap, arg, map)? {
                Value::Str(s) => {
                    let given = given_args(&s.flat());
                    match &args {
                        Some((first, a)) if *a != given => {
                            return Err(format!(
                                "the `CommandLine` ports `{first}` and `{name}` are given \
                                 different arguments; a run has one command line"
                            ));
                        }
                        Some(_) => {}
                        None => args = Some((name, given)),
                    }
                }
                v => {
                    return Err(format!(
                        "the `CommandLine` port `{name}` is given as a String, one argument \
                         per line, not {v}"
                    ));
                }
            },
        }
    }
    let args = args.map(|(_, a)| a).unwrap_or_default();
    let wave = match swap {
        None => program.run_through(&lines, &args, |name| files[name].clone(), map)?,
        Some(_) => {
            let main = program.unit.defs.iter().find(|d| d.name == "main");
            let main = Term::Var(main.expect("`main` was elaborated").kernel.clone());
            let main = cones.close_with(main, swap);
            program.run_main_through(&main, &lines, &args, |name| files[name].clone(), map)?
        }
    };
    let outputs = program.outputs();
    let wants = match (outputs.len(), value(cones, swap, &t.want, map)?) {
        (1, v) => vec![v],
        (n, Value::Tuple(xs)) if xs.len() == n => xs.into_vec(),
        (n, v) => {
            return Err(format!(
                "the expected value is a String for each of the {n} output ports, not {v}"
            ));
        }
    };
    // The first write to each port.
    let mut written: HashMap<&str, &[u8]> = HashMap::new();
    for (p, b) in &wave.writes {
        written.entry(&**p).or_insert(&b[..]);
    }
    for (name, want) in outputs.iter().zip(wants) {
        let Value::Str(want) = want else {
            return Err(format!(
                "the expected value of port `{name}` is a String, not {want}"
            ));
        };
        let got = written.get(&**name).copied().unwrap_or(&[]);
        if got != want.flat().as_bytes() {
            let got = Value::str(&String::from_utf8_lossy(got));
            return Err(format!("port `{name}` writes {got}"));
        }
    }
    Ok(())
}

/// The arguments a test gives a `CommandLine` port as the `String` `s`, one per line, the
/// lines read as a `Lines` input's are: a line ends at `\n`, a `\r` before it is dropped, and a
/// last line needs no `\n`.
fn given_args(s: &str) -> Vec<String> {
    let mut lines: Vec<&str> = s.split('\n').collect();
    if lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    lines
        .into_iter()
        .map(|l| l.strip_suffix('\r').unwrap_or(l).to_string())
        .collect()
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
