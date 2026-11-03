//! Every type printed while checking the corpus, the fences, their ✗ variants and the units of
//! the step folders parses back, as type syntax, to the type printed (OSP-diag, DESIGN.md
//! "Printed types are syntax").

use std::path::PathBuf;

use zed_kernel::types::Type as KType;
use zed_kernel::{Rat, Value};
use zed_tests::scaling;
use zedc::check::read::parse_type;
use zedc::check::ty::{Carrier, Ty, Vars, printed};

/// Each program the check reads: its place and text.
fn programs() -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = Vec::new();
    for (p, _) in zed_tests::oracle::corpus() {
        out.push((p.display().to_string(), read(&p)));
    }
    out.extend(zed_tests::fences::all().into_iter().map(|f| (f.at, f.text)));
    out.extend(
        zed_tests::fences::variants()
            .into_iter()
            .map(|v| (v.name, v.text)),
    );
    let steps = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("steps");
    let mut dirs = vec![steps];
    while let Some(d) = dirs.pop() {
        for e in std::fs::read_dir(&d).expect("a step directory") {
            let p = e.expect("an entry").path();
            if p.is_dir() {
                dirs.push(p);
            } else if p.extension().is_some_and(|e| e == "zed") {
                out.push((p.display().to_string(), read(&p)));
            }
        }
    }
    out
}

fn read(p: &std::path::Path) -> String {
    std::fs::read_to_string(p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
}

/// The types printed while checking `text`, each with its text, and the rendered diagnostics.
fn printed_by(text: &str) -> (Vec<(Ty, String)>, String) {
    printed::start();
    let out = zedc::run::load(text.as_bytes()).err().unwrap_or_default();
    (printed::take(), out)
}

/// What type syntax states of `t`: the atoms a named family holds, the payloads the atoms were
/// built with, a positional parameter's name, a default, a body's needs, the variables a
/// signature binds and whether it is a family are not written in a type.
fn stated(t: &Ty) -> Ty {
    let mut t = t.clone();
    let mut stack = vec![&mut t];
    while let Some(t) = stack.pop() {
        t.family = KType::empty();
        t.payloads.clear();
        for cs in t.tuples.iter_mut() {
            stack.extend(cs.iter_mut());
        }
        for s in t.fns.iter_mut() {
            let s = std::sync::Arc::make_mut(s);
            for p in s.params.iter_mut() {
                if p.positional {
                    p.name = "".into();
                }
                p.default = None;
            }
            s.needs.clear();
            s.own.clear();
            s.data = false;
            for a in s.arrows.iter_mut() {
                stack.extend(a.params.iter_mut());
                stack.push(&mut a.result);
            }
        }
    }
    t
}

/// Whether `t` holds a class variable of the solver, `$k`: a text printed with one is a
/// placeholder the checker replaces once the class is solved, and is checked in its final form.
fn unsolved(t: &Ty) -> bool {
    let mut vars = Vars::default();
    t.vars_in(&mut vars);
    vars.order.iter().any(|v| v.starts_with('$'))
}

/// Why the type `t`, printed as `text`, does not parse back to itself.
fn mismatch(t: &Ty, text: &str) -> Option<String> {
    match parse_type(text) {
        Err(why) => Some(why),
        Ok(back) if stated(&back) == stated(t) => None,
        Ok(_) => Some(format!("`{text}` parses back to another type")),
    }
}

#[test]
fn every_printed_type_parses_back_to_itself() {
    let mut failures = Vec::new();
    let mut count = 0;
    for (at, text) in programs() {
        let (seen, out) = printed_by(&text);
        if let Some(i) = out
            .find('$')
            .filter(|i| out[i + 1..].starts_with(|c: char| c.is_ascii_digit()))
        {
            failures.push(format!(
                "{at}: a diagnostic names a class of the solver: {}",
                &out[i..]
            ));
        }
        for (t, shown) in seen.into_iter().filter(|(t, _)| !unsolved(t)) {
            count += 1;
            if let Some(why) = mismatch(&t, &shown) {
                failures.push(format!("{at}: {why}"));
            }
        }
    }
    failures.sort();
    failures.dedup();
    println!("{count} printed types");
    assert!(
        failures.is_empty(),
        "{}\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The type `text` reads back to, or why it does not.
fn back(text: &str) -> Ty {
    parse_type(text).unwrap_or_else(|why| panic!("{why}"))
}

#[test]
fn the_forms_of_layer_l1_read_back() {
    assert_eq!(
        back("int | String"),
        Ty::carrier(Carrier::Int).union(&Ty::carrier(Carrier::Str))
    );
    assert_eq!(
        back("(int, bool)"),
        Ty::tuple(vec![Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool)])
    );
    assert_eq!(back("#ioError"), Ty::set(KType::atom("ioError")));
    assert_eq!(back("()"), Ty::tuple(Vec::new()));
    let f = back("(int, name: String) -> ()");
    assert_eq!(f.fns[0].to_string(), "(int, name: String) -> ()");
}

#[test]
fn the_three_leaves_of_layer_l10_read_back() {
    assert_eq!(back("_"), Ty::dynamic());
    assert_eq!(back("!_"), Ty::empty());
    assert_eq!(
        back("\"a\" | -1 | 2.5r"),
        Ty::union_all(&[
            Ty::lit(&Value::str("a")),
            Ty::lit(&Value::int((-1).into())),
            Ty::lit(&Value::rat(Rat::decimal("2.5").expect("a decimal"))),
        ])
    );
    assert_eq!(
        back("int \\ 0"),
        Ty::carrier(Carrier::Int).diff(&Ty::lit(&Value::int(0.into())))
    );
}

#[test]
fn a_bound_clause_reads_back_onto_its_signature() {
    let t = back("(w: T, h: T) -> T for T in int | f64 | rat");
    let mask = Carrier::Int.bit() | Carrier::F64.bit() | Carrier::Rat.bit();
    assert_eq!(t.fns.len(), 1);
    assert_eq!(t.fns[0].bounds, [("T".into(), mask)].into());
    // A signature bounded inside a tuple: the clause ends at its group's parenthesis.
    let t = back("(((T) -> T for T in int | rat), int)");
    assert_eq!(t.tuples[0][0].fns[0].bounds.len(), 1);
    assert_eq!(t.to_string(), "(((T) -> T for T in int | rat), int)");
}

#[test]
fn what_is_no_printed_type_is_an_error() {
    let cases = [
        ("$0", "`$0`: no token starts with '$' (U+0024)"),
        ("!int", "`!int`: `!` stands before no `_`"),
        ("#e(int)", "`#e(int)` holds a form of layer L2"),
        ("[int]", "`[int]` holds a form of layer L3"),
        (
            "(T) -> T for T in widget",
            "`(T) -> T for T in widget`: `widget` in the bound of `T` is no carrier",
        ),
        (
            "(T) -> T for T int",
            "`(T) -> T for T int`: the bound `T int` has no ` in `",
        ),
        (
            "int for U in int",
            "`int for U in int`: the bound of `U` is on no signature that names it",
        ),
    ];
    for (text, want) in cases {
        assert_eq!(parse_type(text).err().as_deref(), Some(want), "{text}");
    }
    assert!(
        parse_type("class T")
            .unwrap_err()
            .starts_with("`class T` is not a type: expected")
    );
}

/// The printed text of a union of `n` atoms and a tuple of `n` components, built once.
fn wide(n: usize) -> (String, String) {
    let union = (0..n)
        .map(|i| format!("#a{i}"))
        .collect::<Vec<_>>()
        .join(" | ");
    let tuple = format!("({})", vec!["int"; n].join(", "));
    (union, tuple)
}

#[test]
fn reading_a_printed_type_back_scales() {
    let n = 400;
    let inputs = [(n, wide(n)), (8 * n, wide(8 * n))];
    let input = |size: usize| {
        &inputs
            .iter()
            .find(|(m, _)| *m == size)
            .expect("a built size")
            .1
    };
    scaling::check(
        "reading back a union of n atoms and a tuple of n components",
        n,
        |size| {
            let (union, tuple) = input(size);
            assert_eq!(back(union).set.to_string().matches('#').count(), size);
            assert_eq!(back(tuple).tuples[0].len(), size);
        },
    );
}
