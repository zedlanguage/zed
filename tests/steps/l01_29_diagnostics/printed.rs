//! Every type printed while checking the corpus, the fences, their ✗ variants and the units of
//! the step folders parses back, as type syntax, to the type printed (OSP-diag, DESIGN.md
//! "Printed types are syntax").

use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::Arc;

use zed_kernel::types::Type as KType;
use zed_kernel::{Rat, Value};
use zed_tests::scaling;
use zedc::check::read::parse_type;
use zedc::check::ty::{Carrier, OTHER, Shape, Ty, Vars, printed};

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

/// What type syntax states of `t`: the atoms a named family holds, a positional parameter's name,
/// a default, a body's needs, the variables a signature binds and whether it is a family are
/// not written in a type. The payloads of atoms are (L29-print). A type variable is written
/// only with a bound of carriers: one that no signature around it bounds so, or whose bound
/// holds other values, is `_` (DESIGN.md L1.26).
fn stated(t: &Ty) -> Ty {
    let mut t = t.clone();
    // Each part to read, with the variables the signatures around it bound by carriers.
    let mut stack = vec![(&mut t, Arc::new(HashSet::<Arc<str>>::new()))];
    while let Some((t, scope)) = stack.pop() {
        t.family = KType::empty();
        let free = t.vars.iter().any(|v| !scope.contains(v));
        t.vars.retain(|v| scope.contains(v));
        t.dynamic |= free;
        for s in t.payloads.values_mut().flatten().flatten() {
            stack.extend(s.items.iter_mut().map(|t| (t, scope.clone())));
            stack.extend(s.fields.values_mut().map(|t| (t, scope.clone())));
        }
        for cs in t.tuples.iter_mut() {
            stack.extend(cs.iter_mut().map(|t| (t, scope.clone())));
        }
        for s in t.fns.iter_mut() {
            let s = Arc::make_mut(s);
            s.bounds.retain(|_, m| *m & OTHER == 0);
            // Its own variables bounded by carriers are written by name; its other own ones are `_`.
            let scope = if s.bounds.is_empty() && s.own.iter().all(|v| !scope.contains(v)) {
                scope.clone()
            } else {
                let mut inner = (*scope).clone();
                inner.retain(|v| !s.own.contains(v));
                inner.extend(s.bounds.keys().cloned());
                Arc::new(inner)
            };
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
                stack.extend(a.params.iter_mut().map(|t| (t, scope.clone())));
                stack.push((&mut a.result, scope.clone()));
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

/// A port's failure is printed with its payload type, as DESIGN.md sec:ports writes it, and
/// reads back to the atom with that payload: not to the bare `#ioError`, which has none.
#[test]
fn an_atom_with_a_payload_reads_back() {
    let io = "#ioError(op: String, path: String, why: String)";
    let fields = ["op", "path", "why"]
        .into_iter()
        .map(|f| (f.into(), Ty::carrier(Carrier::Str)))
        .collect();
    let mut want = Ty::set(KType::atom_with("ioError", &KType::top()));
    want.payloads.insert(
        "ioError".into(),
        Some(vec![Shape {
            items: Vec::new(),
            fields,
        }]),
    );
    assert_eq!(back(io), want);
    assert_eq!(back(io).to_string(), io);
    assert_ne!(back(io), back("#ioError"));
    // Components by position, then fields by name, and a payload within a payload.
    let t = back("#pair(int, #box(String), tag: #a)");
    assert_eq!(t.to_string(), "#pair(int, #box(String), tag: #a)");
    assert_eq!(
        t.payloads["pair"].as_ref().expect("a known payload")[0]
            .items
            .len(),
        2
    );
    // What the checker prints for a lookup in a `Files` port, and for the lines of a `Lines`
    // port, reads back to the type printed.
    for src in [
        "main(fs: Files) -> (stdout: Lines) {\n  stdout <- fs[\"a\"] else #notFound -> \"\";\n}\n",
        "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin;\n}\n",
    ] {
        let (seen, out) = printed_by(src);
        assert!(out.contains(io), "{src}: {out}");
        let io: Vec<_> = seen
            .iter()
            .filter(|(_, s)| s.contains("#ioError"))
            .collect();
        assert!(!io.is_empty(), "{src}: no printed #ioError");
        for (t, s) in io {
            assert_eq!(mismatch(t, s), None, "{src}");
        }
    }
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
        ("{x: int}", "`{x: int}` holds a form of layer L2"),
        ("[int]", "`[int]` holds a form of layer L3"),
        (
            "(T) -> T for T in widget",
            "`(T) -> T for T in widget`: `widget` in the bound of `T` is no carrier",
        ),
        (
            "(T) -> T for T int",
            "`(T) -> T for T int` is not a type: expected 'in'",
        ),
        (
            "int for U in int",
            "`int for U in int`: the bound of `U` is on no signature that names it",
        ),
        (
            "(T) -> T for T in int | #a",
            "`(T) -> T for T in int | #a`: `#a` in the bound of `T` is no carrier",
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

/// Printing a union of `n` atoms, each with its payload type, and reading the text back, each
/// timed alone: the printer takes the payload atoms out of the kernel set in one difference.
#[test]
fn printing_atoms_with_payloads_scales() {
    let n = 400;
    let built = |n: usize| {
        let text = (0..n)
            .map(|i| format!("#a{i}(int, f: String)"))
            .collect::<Vec<_>>()
            .join(" | ");
        back(&text)
    };
    let inputs = [n, 8 * n].map(|m| {
        let t = built(m);
        let text = t.to_string();
        (m, t, text)
    });
    let input = |size: usize| {
        inputs
            .iter()
            .find(|(m, ..)| *m == size)
            .expect("a built size")
    };
    scaling::check("printing a union of n atoms with payloads", n, |size| {
        let text = input(size).1.to_string();
        assert_eq!(text.matches("(int, f: String)").count(), size);
    });
    scaling::check("reading back a union of n atoms with payloads", n, |size| {
        let (_, t, text) = input(size);
        assert_eq!(&back(text), t);
    });
}
