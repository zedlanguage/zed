//! A run with n variables that reads each of them does work O(n log n): the variables are
//! taken once into a sorted map, and each read is one lookup in it.

use std::ffi::OsString;

use zed_tests::scaling::{self, FACTOR};

use super::{dir_program, run_words, zedc};

/// A program that reads the variables `V0` to `V{n-1}` and writes their values on one line,
/// joined by `|`.
fn reader(n: usize) -> String {
    let holes: Vec<String> = (0..n)
        .map(|k| format!("${{m.env[\"V{k}\"] else \"-\"}}"))
        .collect();
    format!(
        "main(m: MainArgs) {{\n  m.stdout <- \"{}\";\n}}\n",
        holes.join("|")
    )
}

#[test]
fn a_run_reading_n_variables_scales() {
    let n = 200;
    // The programs and the environments of both sizes are made before the runs are measured.
    let input = |m: usize| -> (Vec<OsString>, Vec<(OsString, OsString)>) {
        let prog = dir_program(&format!("scaling{m}"), &reader(m));
        let env = (0..m)
            .map(|k| {
                (
                    OsString::from(format!("V{k}")),
                    OsString::from(format!("{k:05}")),
                )
            })
            .collect();
        (run_words(&prog, &[]), env)
    };
    let (small, large) = (input(n), input(FACTOR * n));
    scaling::check("`zedc run` reading n environment variables", n, |m| {
        let (words, env) = if m == n { &small } else { &large };
        let out = zedc(words, env.clone());
        assert_eq!(out.status, 0, "{}", out.stderr);
        // Each value is five digits, and a `|` or the last `\n` follows each.
        assert_eq!(out.stdout.len(), 6 * m);
    });
}

#[test]
fn taking_n_variables_and_reading_each_scales() {
    use zed_kernel::{Lookup, Value};
    use zedc::run::Environment;
    let n = 20_000;
    // The variables and the names of both sizes are made before the runs are measured.
    let input = |m: usize| -> (Vec<(OsString, OsString)>, Vec<Value>) {
        let env = (0..m)
            .map(|k| {
                (
                    OsString::from(format!("V{k}")),
                    OsString::from(format!("{k}")),
                )
            })
            .collect();
        (env, (0..m).map(|k| Value::str(&format!("V{k}"))).collect())
    };
    let (small, large) = (input(n), input(FACTOR * n));
    scaling::check("an environment of n variables, each read once", n, |m| {
        let (env, names) = if m == n { &small } else { &large };
        let env = Environment::new(env.iter().cloned());
        for name in names {
            assert!(matches!(env.get(name), Ok(Value::Str(_))));
        }
    });
}
