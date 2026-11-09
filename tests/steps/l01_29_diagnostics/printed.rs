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
use zedc::check::ty::{Carrier, EVERY, OTHER, Shape, Ty, Vars, mask_text, printed};

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
    stated_in(t, Arc::default())
}

/// [`stated`] of `t` inside signatures that bound the variables `scope` by carriers.
fn stated_in(t: &Ty, scope: Arc<HashSet<Arc<str>>>) -> Ty {
    let mut t = t.clone();
    // Each part to read, with the variables the signatures around it bound by carriers.
    let mut stack = vec![(&mut t, scope)];
    while let Some((t, scope)) = stack.pop() {
        t.family = KType::empty();
        let free = t.vars.iter().any(|v| !scope.contains(v));
        t.vars.retain(|v| scope.contains(v));
        t.dynamic |= free;
        // A payload shape and a row are shared and keep a hash of what they hold, so they are
        // made again.
        for s in t.payloads.values_mut().flatten().flatten() {
            *s = Shape::new(
                s.items
                    .iter()
                    .map(|c| stated_in(c, scope.clone()))
                    .collect(),
                (s.fields.iter())
                    .map(|(n, c)| (n.clone(), stated_in(c, scope.clone())))
                    .collect(),
            );
        }
        for cs in t.tuples.iter_mut() {
            *cs = cs.iter().map(|c| stated_in(c, scope.clone())).collect();
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
pub(super) fn unsolved(t: &Ty) -> bool {
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
        if let Some(name) = super::kernel_names::kernel_name(&out) {
            failures.push(format!("{at}: a diagnostic names a kernel binder: {name}"));
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
    want.payloads
        .insert("ioError".into(), Some(vec![Shape::new(Vec::new(), fields)]));
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

/// Failures that merge are printed `#errs(E ->? E)`, the family that maps each distinct
/// failure to itself, with `E` written out and no `#errs` in it, and read back to the type
/// printed (ERRS-precise).
#[test]
fn a_merged_failure_reads_back() {
    let text = "p(positional n: int) = if n > 0 { n } else { #syntaxError(n) };\n\
                f(positional x: int | #notFound, positional y: int | #invalid) = x + y;\n\
                g(positional x: int | #a, positional y: int | #b, positional z: int | #c) = (x + y) + z;\n\
                h(positional a: int, positional b: int) = p(a) + p(b);\n";
    // Item PRINT-fmt-audit: the set of failures, used twice, gets a definition placed first.
    // Before, it was written at each use: `#errs(#invalid | #notFound ->? #invalid | #notFound)`.
    // An atom with a payload is written by the compiler, not the kernel, so it gets none.
    for (name, def, want) in [
        ("f", "type T1 = #invalid | #notFound;\n", "#errs(T1 ->? T1)"),
        ("g", "type T1 = #a | #b | #c;\n", "#errs(T1 ->? T1)"),
        ("h", "", "#errs(#syntaxError(int) ->? #syntaxError(int))"),
    ] {
        let s = zed_tests::step_helpers::l01_26_type_resolution::sig_of(text, name);
        let t = Ty::func(s.clone());
        let shown = s.to_string();
        assert!(shown.starts_with(def) && shown.contains(want), "{shown}");
        assert_eq!(shown.matches("#errs").count(), 1, "{shown}");
        assert_eq!(mismatch(&t, &shown), None, "{shown}");
        let alone = &s.arrows[0].result;
        assert_eq!(mismatch(alone, &alone.to_string()), None, "{alone}");
    }
    assert_eq!(
        back("#errs(#a | #b ->? #a | #b)").payloads["errs"]
            .as_ref()
            .map(Vec::len),
        Some(1)
    );
}

/// A partial map `K ->? V` is the function type whose lookup is `V | #notFound`
/// (sec:type_language), printed `K ->? V` as `#morphism` of sec:introspection writes it, which reads back to it; an `#errs`
/// family reads back through the same rule, its lookup `E | #notFound`.
#[test]
fn a_partial_map_reads_back_with_its_miss() {
    let partial = back("String ->? int");
    assert_eq!(partial, back("(String) -> int | #notFound"));
    assert_eq!(partial.to_string(), "String ->? int");
    assert_ne!(partial, back("String -> int"));
    let built = zedc::check::ty::errs_of(back("#a | #b"));
    let shown = built.to_string();
    // Item PRINT-fmt-audit: `#a | #b`, used twice, gets a definition placed first. Before:
    // `#errs(#a | #b ->? #a | #b)`.
    assert_eq!(shown, "type T1 = #a | #b;\n#errs(T1 ->? T1)");
    assert_eq!(mismatch(&built, &shown), None, "{shown}");
    let errs = back(&shown);
    let family = &errs.payloads["errs"].as_ref().expect("a payload")[0].items[0].fns[0];
    assert_eq!(
        family.arrows[0].result,
        back("#a | #b | #notFound"),
        "{family}"
    );
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
            Ty::lit(&Value::rat(
                Rat::decimal("2.5").unwrap().expect("a decimal")
            )),
        ])
    );
    assert_eq!(
        back("int \\ 0"),
        Ty::carrier(Carrier::Int).diff(&Ty::lit(&Value::int(0.into())))
    );
}

/// Each set of carriers a class or a use can hold is printed as type syntax that reads back to
/// it: a set that may take other values is `_`, since `int | _` is `_` (DESIGN.md L1.26), and
/// the empty set is `Never` (BOUNDS-other).
#[test]
fn every_set_of_carriers_prints_as_a_type_that_reads_back() {
    for m in 0..=EVERY {
        let want = if m & OTHER != 0 {
            Ty::dynamic()
        } else {
            let carriers: Vec<Ty> = Carrier::of_mask(m).map(Ty::carrier).collect();
            Ty::union_all(&carriers)
        };
        let text = mask_text(m);
        assert_eq!(back(&text), want, "mask {m:#08b} printed `{text}`");
    }
    assert_eq!(mask_text(0), "Never");
    assert_eq!(mask_text(OTHER | Carrier::Int.bit()), "_");
    assert_eq!(
        mask_text(Carrier::Int.bit() | Carrier::F64.bit()),
        "int | f64"
    );
}

#[test]
fn a_bound_clause_reads_back_onto_its_signature() {
    let t = back("(w: T, h: T) -> T for T in int | f64 | rat");
    let mask = Carrier::Int.bit() | Carrier::F64.bit() | Carrier::Rat.bit();
    assert_eq!(t.fns.len(), 1);
    assert_eq!(t.fns[0].bounds, [("T".into(), mask)].into());
    // A signature bounded inside a tuple, before a comma: parenthesized, so the clause ends
    // where a reader sees it end.
    let t = back("(((T) -> T for T in int | rat), int)");
    assert_eq!(t.tuples[0][0].fns[0].bounds.len(), 1);
    let shown = t.to_string();
    assert_eq!(shown, "(((T) -> T for T in int | rat), int)");
    assert_eq!(mismatch(&t, &shown), None, "{shown}");
}

/// An intersection of function types is one function's list of arrows, an overload, as the
/// checker prints a signature of several arrows (DESIGN.md sec:type_language, "Relation to
/// semantic subtyping" (2)): `show` here is defined at least on `int` and at least on `f64`.
#[test]
fn an_intersection_of_function_types_reads_back_as_one_overload() {
    let text = "((x: int) -> String) & ((x: f64) -> String)";
    let show = back(text);
    assert_eq!(show.fns.len(), 1);
    assert_eq!(show.fns[0].arrows.len(), 2);
    assert_eq!(show.fns[0].to_string(), text);
    // Positional parameters, as an operator's arrows are printed.
    let text = "((int, int) -> int) & ((f64, f64) -> f64) & ((rat, rat) -> rat)";
    let plus = back(text);
    assert_eq!(plus.fns[0].arrows.len(), 3);
    assert_eq!(plus.fns[0].to_string(), text);
    // Each arrow's variable is bounded on the one signature.
    let text = "((x: T, n: int) -> T) & ((x: U, n: int) -> U) for T in int | rat, U in f64";
    let scale = back(text);
    assert_eq!(scale.fns.len(), 1);
    assert_eq!(scale.fns[0].to_string(), text);
    let both = Carrier::Int.bit() | Carrier::Rat.bit();
    assert_eq!(
        scale.fns[0].bounds,
        [("T".into(), both), ("U".into(), Carrier::F64.bit())].into()
    );
    // One variable may stand in several arrows: they are one function's, which a call binds,
    // as the checker prints a generic function that takes its parameter's atoms.
    let text = "((T) -> \"big\" | \"small\") & ((#_ | T) -> \"big\" | \"small\" | #_) \
                for T in int | f64 | rat";
    let r = back(text);
    assert_eq!(r.fns.len(), 1);
    assert_eq!(r.fns[0].arrows.len(), 2);
    assert_eq!(r.fns[0].to_string(), text);
    // An overload in a tuple reads as one too.
    let pair = back("(((x: int) -> int) & ((x: f64) -> f64), int)");
    assert_eq!(pair.tuples[0][0].fns[0].arrows.len(), 2);
}

/// The arrows of one function share its parameter list, so an intersection of function types
/// whose parameters differ in number, name or `positional` mark is no type.
#[test]
fn an_intersection_of_function_types_with_different_parameters_is_an_error() {
    let cases = [
        (
            "((x: int) -> int) & ((y: f64) -> f64)",
            "the arrows of an intersection of function types share one parameter list, but one \
             takes (x) and another (y)",
        ),
        (
            "((x: T) -> T) & ((y: U) -> U) for T in int, U in f64",
            "the arrows of an intersection of function types share one parameter list, but one \
             takes (x) and another (y)",
        ),
        (
            "((x: int) -> int) & ((x: int, n: int) -> int)",
            "the arrows of an intersection of function types share one parameter list, but one \
             takes (x) and another (x, n)",
        ),
        (
            "((int) -> int) & ((x: int) -> int)",
            "the arrows of an intersection of function types share one parameter list, but one \
             takes (_) and another (x)",
        ),
    ];
    for (text, want) in cases {
        assert_eq!(
            parse_type(text).err(),
            Some(format!("`{text}`: {want}")),
            "{text}"
        );
    }
}

/// An overload in parentheses inside another is read with the other's arrows, in written
/// order, and its parameter list is compared with theirs: `abs` on three carriers, written as
/// an overload on two and one more.
#[test]
fn an_overload_in_parentheses_reads_back_with_the_other_arrows() {
    let flat = "((x: int) -> int) & ((x: f64) -> f64) & ((x: rat) -> rat)";
    for text in [
        "(((x: int) -> int) & ((x: f64) -> f64)) & ((x: rat) -> rat)",
        "((x: int) -> int) & (((x: f64) -> f64) & ((x: rat) -> rat))",
        "((x: int) -> int) & ((((x: f64) -> f64)) & (((x: rat) -> rat)))",
    ] {
        let abs = back(text);
        assert_eq!(abs.fns.len(), 1, "{text}");
        assert_eq!(abs.fns[0].to_string(), flat, "{text}");
    }
    let text = "(((x: int) -> int) & ((x: f64) -> f64)) & ((y: rat) -> rat)";
    assert_eq!(
        parse_type(text).err(),
        Some(format!(
            "`{text}`: the arrows of an intersection of function types share one parameter \
             list, but one takes (x) and another (y)"
        ))
    );
    // A bounds clause around the inner overload would bound its variables on part of the
    // function.
    let text = "((((x: T) -> T) & ((x: int) -> int)) for T in f64) & ((x: rat) -> rat)";
    assert_eq!(
        parse_type(text).err(),
        Some(format!(
            "`{text}`: a bounds clause stands around an intersection of function types that is \
             part of another; write the clause once, after the whole intersection"
        ))
    );
}

/// The arrows of one function share its bounds: two arrows may each bound a variable of one
/// name by the same carriers, in any order, and not by different ones.
#[test]
fn arrows_that_bound_one_variable_bound_it_alike() {
    let text = "(((x: T) -> T) for T in int | rat) & (((x: T) -> int) for T in rat | int)";
    let t = back(text);
    assert_eq!(t.fns.len(), 1);
    assert_eq!(
        t.fns[0].bounds,
        [("T".into(), Carrier::Int.bit() | Carrier::Rat.bit())].into()
    );
    let text = "(((x: T) -> T) for T in int) & (((x: T) -> T) for T in f64)";
    assert_eq!(
        parse_type(text).err(),
        Some(format!(
            "`{text}`: the type variable `T` is bounded by int on one arrow of an intersection \
             of function types and by f64 on another, but the arrows of one function share its \
             bounds"
        ))
    );
}

/// A call passes a positional parameter by place, so its name is not compared: the arrows of
/// `(+)` may name their positional operands differently.
#[test]
fn the_names_of_positional_parameters_are_not_compared() {
    let t = back("((positional x: int) -> int) & ((positional y: f64) -> f64)");
    assert_eq!(t.fns[0].to_string(), "((int) -> int) & ((f64) -> f64)");
    let t = back("((positional x: int) -> int) & ((int) -> f64)");
    assert_eq!(t.fns[0].to_string(), "((int) -> int) & ((int) -> f64)");
}

#[test]
fn what_is_no_printed_type_is_an_error() {
    let cases = [
        (
            "$0",
            "`$0`: the character `$` (U+0024) starts no name, number, operator or other part of a Zed program. Remove it, or, if it is meant as text, write it inside a string, as `\"$\"`.",
        ),
        ("!int", "`!int`: `!` stands before no `_`"),
        (
            "{x: int}",
            "`{x: int}` holds a record type or a type applied to arguments, which the checker never prints",
        ),
        (
            "[int]",
            "`[int]` holds an array type, which the checker never prints",
        ),
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

/// Reading back an intersection of `n` function types of one parameter list: the parameter
/// lists are compared with the first once each, and the arrows joined into one signature.
#[test]
fn reading_an_overload_of_many_arrows_back_scales() {
    let n = 200;
    let overload = |m: usize| {
        (0..m)
            .map(|i| format!("((x: #a{i}) -> #b{i})"))
            .collect::<Vec<_>>()
            .join(" & ")
    };
    let inputs = [(n, overload(n)), (8 * n, overload(8 * n))];
    scaling::check("reading back an overload of n arrows", n, |size| {
        let text = &inputs
            .iter()
            .find(|(m, _)| *m == size)
            .expect("a built size")
            .1;
        let ty = back(text);
        assert_eq!(ty.fns.len(), 1);
        assert_eq!(ty.fns[0].arrows.len(), size);
    });
}

/// Reading back an overload of `n` arrows nested `n` deep in parentheses, to the left and to
/// the right: each intersection is read once, with the one around it, so the cost is linear
/// and not a walk of the inner arrows at each depth.
#[test]
fn reading_an_overload_nested_in_parentheses_back_scales() {
    let n = 100;
    let arrow = |i: usize| format!("((x: #a{i}) -> #b{i})");
    let left = |m: usize| (1..m).fold(arrow(0), |inner, i| format!("({inner}) & {}", arrow(i)));
    let right = |m: usize| (1..m).fold(arrow(0), |inner, i| format!("{} & ({inner})", arrow(i)));
    for (side, build) in [
        ("left", &left as &dyn Fn(usize) -> String),
        ("right", &right),
    ] {
        let inputs = [(n, build(n)), (8 * n, build(8 * n))];
        scaling::check(
            &format!("reading back an overload of n arrows nested n deep to the {side}"),
            n,
            |size| {
                let text = &inputs
                    .iter()
                    .find(|(m, _)| *m == size)
                    .expect("a built size")
                    .1;
                let ty = back(text);
                assert_eq!(ty.fns.len(), 1);
                assert_eq!(ty.fns[0].arrows.len(), size);
            },
        );
    }
}

/// A morphism type is printed as sec:introspection's `#morphism` writes it: `K ->? V` when its
/// guarantee is empty, `L .. U -> V` when its bounds differ, and each text reads back to the
/// same type as an argument, a union member, a tuple component, a key and a value.
#[test]
fn morphism_types_print_as_written_and_read_back_in_every_position() {
    for (text, shown) in [
        ("String ->? int", "String ->? int"),
        ("(String) -> int | #notFound", "String ->? int"),
        ("(String) -> #notFound", "(String) -> #notFound"),
        ("(String ->? int) | int", "int | (String ->? int)"),
        ("(String ->? int, int)", "(String ->? int, int)"),
        ("int ->? (String ->? int)", "int ->? String ->? int"),
        ("(int ->? int) ->? int", "(int ->? int) ->? int"),
        ("((int, int)) ->? int", "((int, int)) ->? int"),
        ("((int) -> int) ->? int", "((int) -> int) ->? int"),
        (
            "(k: String) -> int | #notFound",
            "(k: String) -> int | #notFound",
        ),
        ("T ->? T for T in int | f64", "T ->? T for T in int | f64"),
        ("int .. int | String -> bool", "int .. int | String -> bool"),
        ("#a .. #a | #b -> int", "#a .. #a | #b -> int"),
        ("int .. int -> bool", "(int) -> bool"),
        ("Never .. int -> bool", "int ->? bool"),
        (
            "((int) -> bool) & ((int | String) -> bool | #notFound)",
            "int .. int | String -> bool",
        ),
        (
            "((int) -> bool) & ((String) -> bool | #notFound)",
            "((int) -> bool) & ((String) -> bool | #notFound)",
        ),
        (
            "(int .. int | String -> bool, int)",
            "(int .. int | String -> bool, int)",
        ),
        // Item PRINT-fmt-audit: `int | String`, used twice, gets a definition placed first.
        // Before: `int .. int | String -> int .. int | String -> bool`.
        (
            "int .. int | String -> (int .. int | String -> bool)",
            "type T1 = int | String;\nint .. T1 -> int .. T1 -> bool",
        ),
        (
            "(x: int .. int | String -> bool) -> int",
            "(x: int .. int | String -> bool) -> int",
        ),
    ] {
        let t = back(text);
        assert_eq!(t.to_string(), shown, "{text}");
        assert_eq!(mismatch(&t, shown), None, "{text}");
    }
}

/// A function type is printed with the parentheses the grammar needs and no others (DESIGN.md
/// sec:grammar): bare where a whole type stands, as a tuple component, a parameter, a payload
/// and an arrow's result; parenthesized as an operand of `|` and `&` and as the key of `->?`,
/// and as a result when it has a bounds clause. Each text reads back to the type printed.
#[test]
fn function_types_print_with_only_the_parentheses_the_grammar_needs() {
    for (text, shown) in [
        // In a tuple.
        ("(((int) -> int), String)", "((int) -> int, String)"),
        ("(((int) -> int),)", "((int) -> int,)"),
        // In a union, alone and inside a tuple.
        ("((int) -> int) | String", "String | ((int) -> int)"),
        (
            "((int) -> int) | ((String) -> String)",
            "((int) -> int) | ((String) -> String)",
        ),
        (
            "(((int) -> int) | String, bool)",
            "(String | ((int) -> int), bool)",
        ),
        // As a result: `->` groups to the right.
        ("(int) -> ((String) -> bool)", "(int) -> (String) -> bool"),
        ("((int) -> (String) -> bool)", "(int) -> (String) -> bool"),
        // As a parameter, alone, with another, and by name.
        ("(((int) -> Never)) -> Never", "((int) -> Never) -> Never"),
        (
            "(((int) -> Never), int) -> Never",
            "((int) -> Never, int) -> Never",
        ),
        ("(f: ((int) -> int)) -> int", "(f: (int) -> int) -> int"),
        // Nested functions, to the left and to the right.
        (
            "(((((int) -> int)) -> int)) -> int",
            "(((int) -> int) -> int) -> int",
        ),
        (
            "(((int) -> int)) -> ((int) -> ((int) -> int))",
            "((int) -> int) -> (int) -> (int) -> int",
        ),
        // A union inside a function's result, of plain types and with a function.
        ("(int) -> (int | String)", "(int) -> int | String"),
        (
            "(int) -> (((int) -> int) | String)",
            "(int) -> String | ((int) -> int)",
        ),
        // A payload.
        ("#a(((int) -> int))", "#a((int) -> int)"),
        ("#a(f: ((int) -> int))", "#a(f: (int) -> int)"),
        // An intersection of arrows: each arrow parenthesized, the whole bare where it stands.
        (
            "(((int) -> int) & ((String) -> String), bool)",
            "(((int) -> int) & ((String) -> String), bool)",
        ),
        (
            "(((int) -> int) & ((String) -> String)) | bool",
            "bool | ((int) -> int) & ((String) -> String)",
        ),
        // A bounds clause: bare where a whole type stands with no comma after it, parenthesized
        // as a result and before a comma.
        (
            "((T) -> T for T in int | f64, int)",
            "(((T) -> T for T in int | f64), int)",
        ),
        (
            "(int) -> ((T) -> T for T in int | f64)",
            "(int) -> ((T) -> T for T in int | f64)",
        ),
        // The key of `->?`: a function and a tuple of other than one component parenthesized.
        ("((int) -> int) ->? int", "((int) -> int) ->? int"),
        ("((int, int)) ->? int", "((int, int)) ->? int"),
        ("(int,) ->? int", "(int,) ->? int"),
        ("int ->? (int ->? int)", "int ->? int ->? int"),
        // A union as the key: each operand as in any union.
        (
            "(((int, int)) | String) ->? int",
            "String | (int, int) ->? int",
        ),
        (
            "(((int) -> int) | String) ->? int",
            "String | ((int) -> int) ->? int",
        ),
        // A bounds clause as the value of `->?`, and in a list of parameters before another.
        (
            "int ->? ((T) -> T for T in int | f64)",
            "int ->? ((T) -> T for T in int | f64)",
        ),
        (
            "(((T) -> T for T in int | f64), int) -> int",
            "(((T) -> T for T in int | f64), int) -> int",
        ),
    ] {
        let t = back(text);
        assert_eq!(t.to_string(), shown, "{text}");
        assert_eq!(mismatch(&t, shown), None, "{text}");
    }
}

/// A function type with a bounds clause is parenthesized wherever a comma follows it: as a
/// tuple component other than the last and as the one component of `(T,)`, as a parameter
/// other than the last, positional or named, and as a payload other than the last. In `((T) ->
/// T for T in int, int)` a reader cannot tell at the comma whether another bound, `U in f64`,
/// follows; the grammar reads it only by looking past the next name. Where a closing
/// parenthesis follows, the clause ends there and the text stays bare. Each text written either
/// way reads back to the type printed, and the printed text prints itself again.
#[test]
fn a_bounds_clause_before_a_comma_is_parenthesized() {
    for (text, shown) in [
        // A tuple: first, only and last component, and two bounded components.
        (
            "((T) -> T for T in int | f64, int)",
            "(((T) -> T for T in int | f64), int)",
        ),
        (
            "(((T) -> T for T in int | f64), int)",
            "(((T) -> T for T in int | f64), int)",
        ),
        (
            "(((T) -> T for T in int | f64),)",
            "(((T) -> T for T in int | f64),)",
        ),
        (
            "(int, (T) -> T for T in int | f64)",
            "(int, (T) -> T for T in int | f64)",
        ),
        (
            "(int, ((T) -> T for T in int | f64))",
            "(int, (T) -> T for T in int | f64)",
        ),
        (
            "((T) -> T for T in int | f64, (U) -> U for U in String | bool)",
            "(((T) -> T for T in int | f64), (U) -> U for U in String | bool)",
        ),
        // The same places with no bounds clause: no parentheses added.
        ("((int) -> int, int)", "((int) -> int, int)"),
        ("(((int) -> int),)", "((int) -> int,)"),
        ("((int) -> int, int) -> int", "((int) -> int, int) -> int"),
        ("#a((int) -> int, int)", "#a((int) -> int, int)"),
        // Parameters: before another, last, alone, and by name.
        (
            "((T) -> T for T in int | f64, int) -> int",
            "(((T) -> T for T in int | f64), int) -> int",
        ),
        (
            "(int, (T) -> T for T in int | f64) -> int",
            "(int, (T) -> T for T in int | f64) -> int",
        ),
        (
            "(((T) -> T for T in int | f64)) -> int",
            "((T) -> T for T in int | f64) -> int",
        ),
        (
            "(f: (T) -> T for T in int | f64, n: int) -> int",
            "(f: ((T) -> T for T in int | f64), n: int) -> int",
        ),
        (
            "(n: int, f: (T) -> T for T in int | f64) -> int",
            "(n: int, f: (T) -> T for T in int | f64) -> int",
        ),
        // Payloads: positional and by name, before another and last.
        (
            "#a((T) -> T for T in int | f64, int)",
            "#a(((T) -> T for T in int | f64), int)",
        ),
        (
            "#a(int, (T) -> T for T in int | f64)",
            "#a(int, (T) -> T for T in int | f64)",
        ),
        (
            "#a(f: (T) -> T for T in int | f64, n: int)",
            "#a(f: ((T) -> T for T in int | f64), n: int)",
        ),
        // Nested: a bounded function whose result is a bounded function, in a tuple, as a
        // parameter, and as the result of one in a tuple.
        (
            "((T) -> ((U) -> U for U in String | bool) for T in int | f64, int)",
            "(((T) -> ((U) -> U for U in String | bool) for T in int | f64), int)",
        ),
        (
            "((T) -> ((U) -> U for U in String | bool) for T in int | f64, int) -> int",
            "(((T) -> ((U) -> U for U in String | bool) for T in int | f64), int) -> int",
        ),
        (
            "((int) -> ((T) -> T for T in int | f64, int), bool)",
            "((int) -> (((T) -> T for T in int | f64), int), bool)",
        ),
    ] {
        let t = back(text);
        assert_eq!(t.to_string(), shown, "{text}");
        assert_eq!(mismatch(&t, shown), None, "{text}");
        assert_eq!(back(shown).to_string(), shown, "{shown}");
    }
}

/// The empty type prints as the prelude name `Never` (DESIGN.md, the L1 row of "Defined words
/// by layer"), never as its L10 form `!_`, and reads back to itself: alone, as a function's
/// result, and not at all inside a union, where it adds nothing.
#[test]
fn the_empty_type_prints_as_never_and_reads_back() {
    assert_eq!(Ty::empty().to_string(), "Never");
    assert_eq!(back("Never"), Ty::empty());
    assert_eq!(back("Never"), back("!_"));
    let union = back("int | Never");
    assert_eq!(union, Ty::carrier(Carrier::Int));
    assert_eq!(union.to_string(), "int");
    let f = back("(int) -> Never");
    let shown = f.to_string();
    assert_eq!(shown, "(int) -> Never");
    assert_eq!(mismatch(&f, &shown), None, "{shown}");
    assert_eq!(back(&shown), f);
}

/// A rejection whose types hold the empty type writes it `Never`, and each type it prints
/// reads back to the type printed.
#[test]
fn a_rejection_writes_the_empty_type_as_never() {
    let (seen, out) = printed_by("take(positional x: Never) = x;\nr = take(1);\n");
    assert_eq!(
        out,
        "2:5: `take` does not take (1): these are the types of its arguments here, and `take` \
has no arrow that takes them all
  [1] 2:10: this literal, 1, is 1
      2 | r = take(1);
        |     ^^^^^^^ [2]
        |          ^ [1]
  [2] 2:5: `take` takes (Never) -> Never
  [3] 1:1: `take` is declared here with no type written for its result; the type the checker found \
for `take` is `(Never) -> Never`
      1 | take(positional x: Never) = x;
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
    );
    assert!(!out.contains("!_"), "{out}");
    assert!(seen.iter().any(|(_, s)| s.contains("Never")), "{seen:?}");
    for (t, shown) in &seen {
        assert_eq!(mismatch(t, shown), None, "{shown}");
    }
}

/// A tuple with an empty component is the empty type: written, nested or in a union, it reads
/// back as `Never` or without the tuple, and prints so.
#[test]
fn an_empty_product_prints_as_never_and_reads_back() {
    for text in [
        "(Never, int)",
        "(int, Never)",
        "((Never, int), bool)",
        "(bool, (int, Never))",
    ] {
        let t = back(text);
        assert_eq!(t, Ty::empty(), "{text}");
        assert_eq!(t.to_string(), "Never", "{text}");
    }
    assert_eq!(
        Ty::tuple(vec![Ty::empty(), Ty::carrier(Carrier::Int)]),
        Ty::empty()
    );
    let union = back("(int, Never) | bool");
    assert_eq!(union, Ty::carrier(Carrier::Bool));
    assert_eq!(union.to_string(), "bool");
    let f = back("(int) -> (Never, int)");
    let shown = f.to_string();
    assert_eq!(shown, "(int) -> Never");
    assert_eq!(mismatch(&f, &shown), None, "{shown}");
    assert_eq!(back(&shown), f);
}

/// A rejection at a parameter whose type is an empty product writes that type `Never`, and each
/// type it prints reads back to the type printed.
#[test]
fn a_rejection_writes_an_empty_product_as_never() {
    let (seen, out) = printed_by("f(positional x: (Never, int)) = x;\nr = f((1, 2));\n");
    assert_eq!(
        out,
        "2:5: `f` does not take ((1, 2)): these are the types of its arguments here, and `f` \
has no arrow that takes them all
  [1] 2:7: this expression gives (1, 2)
      2 | r = f((1, 2));
        |     ^^^^^^^^^ [4]
        |       ^^^^^^ [1]
        |        ^ [2]
        |           ^ [3]
  [2] 2:8: this literal, 1, is 1
  [3] 2:11: this literal, 2, is 2
  [4] 2:5: `f` takes (Never) -> Never
  [5] 1:1: `f` is declared here with no type written for its result; the type the checker found for \
`f` is `(Never) -> Never`
      1 | f(positional x: (Never, int)) = x;
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [5]
        |                 ^^^^^^^^^^^^ [6]
  [6] 1:17: this tuple type has no value, since its component 0, `Never`, has none, so it is \
`Never`"
    );
    // The source line quoted shows the type as written; no type printed does.
    for (_, shown) in &seen {
        assert!(
            !shown.contains("Never,") && !shown.contains(", Never"),
            "{shown}"
        );
    }
    for (t, shown) in &seen {
        assert_eq!(mismatch(t, shown), None, "{shown}");
    }
}

/// Item PRINT-group-site-defs: a signature printed alone declares the part it uses twice on a
/// line of its own, as a program declares it, and the text reads back as the signature (zed
/// DOCS-TODO 55); with no part used twice it is one line.
#[test]
fn a_signature_printed_alone_declares_its_shared_part_a_line_before() {
    use zed_tests::step_helpers::l01_26_type_resolution::sig_of;
    let s = sig_of("f(positional p: (int | #x, int | #x)) = 0;\n", "f");
    let shown = s.to_string();
    assert_eq!(shown, "type T1 = int | #x;\n((T1, T1)) -> 0");
    assert_eq!(mismatch(&Ty::func(s), &shown), None, "{shown}");
    let g = sig_of("g(positional p: (int | #x, int | #y)) = 0;\n", "g");
    assert_eq!(g.to_string(), "((int | #x, int | #y)) -> 0");
}
