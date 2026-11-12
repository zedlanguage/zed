//! Loading and resolving a package at the rule of low complexity (DESIGN.md Part G): linear
//! in its units, its imports and its names, for many units each importing the two before it, a
//! long chain of imports, one unit importing many, one import of many names, and many empty
//! units given as roots. Each package's files are built before timing; the work measured is the
//! loader's, from reading each file to resolving each unit.
//!
//! Ordering the units and reporting their cycles is also timed alone, on import graphs built
//! with no file (many cycles of two, one long cycle, a chain of cycles, a dense component and a
//! complete one): loading a unit costs so much more that a cost per pair of units there would
//! not show in the loading tests.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use zed_tests::scaling;
use zedc::lex::Span;
use zedc::query::Db;
use zedc::unit::{Loaded, Memory, Package, load, order};

use super::{files, mistakes};

/// The package of the `(file, text)` pairs `fs`.
fn memory(fs: Vec<(String, String)>) -> Memory {
    let refs: Vec<(&str, &str)> = fs.iter().map(|(f, t)| (f.as_str(), t.as_str())).collect();
    files(&refs)
}

/// Checks that loading the package `make(k)` from `main` is linear in `k`, from `k` = `n`, and
/// that each package has no mistake but the forms of later steps.
fn linear(what: &str, n: usize, make: impl Fn(usize) -> Vec<(String, String)>) {
    let pkgs: HashMap<usize, Memory> = [n, 8 * n]
        .into_iter()
        .map(|k| (k, memory(make(k))))
        .collect();
    for fs in pkgs.values() {
        let p = load(&mut Db::new(), fs, &["main"]);
        assert_eq!(mistakes(&p), Vec::<String>::new(), "{what}");
    }
    scaling::check_order(what, n, 1, |k| {
        std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
    });
}

/// `k` units `u0` … `u{k-1}`, each importing the two before it, like a ledger whose each day
/// reads the two before; `main` imports the last.
fn ladder(k: usize) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = (0..k)
        .map(|i| {
            let text = match i {
                0 => "v0 = 1;\n".to_string(),
                1 => "import u0.{v0};\nv1 = v0 + 1;\n".to_string(),
                _ => format!(
                    "import u{a}.{{v{a}}};\nimport u{b}.{{v{b}}};\nv{i} = v{a} + v{b};\n",
                    a = i - 1,
                    b = i - 2
                ),
            };
            (format!("u{i}.zed"), text)
        })
        .collect();
    out.push((
        "main.zed".into(),
        format!("import u{l}.{{v{l}}};\ntotal = v{l};\n", l = k - 1),
    ));
    out
}

/// A chain of `k` units, each importing the one before it: the depth-first search goes `k`
/// deep, on its own stack.
fn chain(k: usize) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = (0..k)
        .map(|i| {
            let text = match i {
                0 => "step0 = 0;\n".to_string(),
                _ => format!(
                    "import c{p}.{{step{p}}};\nstep{i} = step{p} + 1;\n",
                    p = i - 1
                ),
            };
            (format!("c{i}.zed"), text)
        })
        .collect();
    out.push((
        "main.zed".into(),
        format!("import c{l}.{{step{l}}};\nlast = step{l};\n", l = k - 1),
    ));
    out
}

/// `main` imports `k` units of one rate each and adds them up.
fn fan(k: usize) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = (0..k)
        .map(|i| (format!("rates/r{i}.zed"), format!("rate{i} = {i};\n")))
        .collect();
    let imports: String = (0..k)
        .map(|i| format!("import rates.r{i}.{{rate{i}}};\n"))
        .collect();
    let sum: Vec<String> = (0..k).map(|i| format!("rate{i}")).collect();
    out.push((
        "main.zed".into(),
        format!("{imports}total = {};\n", sum.join(" + ")),
    ));
    out
}

/// One unit of `k` constants, which `main` imports by name in one import and uses each of.
fn names(k: usize) -> Vec<(String, String)> {
    let consts: String = (0..k).map(|i| format!("c{i} = {i};\n")).collect();
    let listed: Vec<String> = (0..k).map(|i| format!("c{i}")).collect();
    let used: String = (0..k).map(|i| format!("d{i} = c{i} + 1;\n")).collect();
    vec![
        ("table.zed".into(), consts),
        (
            "main.zed".into(),
            format!("import table.{{{}}};\n{used}", listed.join(", ")),
        ),
    ]
}

/// One lambda of `k` tuple-destructuring parameters, like a fold over `k` running pairs, whose
/// body reads every name they bind: each name is bound and found once.
fn pairs(k: usize) -> Vec<(String, String)> {
    let params: Vec<String> = (0..k).map(|i| format!("(s{i}, b{i})")).collect();
    let body: Vec<String> = (0..k).map(|i| format!("max(s{i}, b{i})")).collect();
    vec![(
        "main.zed".into(),
        format!("f = ({}) -> {};\n", params.join(", "), body.join(" + ")),
    )]
}

#[test]
fn many_units_each_importing_two_load_in_linear_time() {
    linear("a ladder of units", 200, ladder);
}

#[test]
fn a_long_chain_of_imports_loads_in_linear_time() {
    linear("a chain of units", 200, chain);
}

#[test]
fn a_unit_importing_many_units_loads_in_linear_time() {
    linear("a fan of imports", 200, fan);
}

#[test]
fn an_import_of_many_names_loads_in_linear_time() {
    linear("an import of many names", 500, names);
}

/// Checks that loading the package `make(k)` from `main` is linear in `k`, from `k` = `n`, and
/// that `expect(k, mistakes)` holds of its mistakes at each size: the cycles it reports.
fn rejected(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> Vec<(String, String)>,
    expect: impl Fn(usize, &[String]),
) {
    let pkgs: HashMap<usize, Memory> = [n, 8 * n]
        .into_iter()
        .map(|k| (k, memory(make(k))))
        .collect();
    for (&k, fs) in &pkgs {
        expect(k, &mistakes(&load(&mut Db::new(), fs, &["main"])));
    }
    scaling::check_order(what, n, 1, |k| {
        std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
    });
}

/// The steps of the cycle the message `m` names, each `` `a` imports `b` at file:line:col ``.
fn steps(m: &str) -> usize {
    m.matches("` imports `").count()
}

/// [`chain`] of `k` units with `c0` also importing the unit `c{to}`, closing a cycle of
/// `to + 1` units.
fn closed(k: usize, to: usize) -> Vec<(String, String)> {
    let mut fs = chain(k);
    fs[0].1 = format!("import c{to}.{{step{to}}};\nstep0 = 0;\n");
    fs
}

#[test]
fn a_lambda_of_many_tuple_parameters_resolves_in_linear_time() {
    linear("a lambda of many tuple parameters", 2000, pairs);
}

/// One unit of `k` functions, each built of the forms of step L3.2 and L5.1, whose children are
/// resolved: a `for` binding its pattern in its `where` and its body, displays, a range, an `in`
/// test, a reduction and a sort key.
fn later_forms(k: usize) -> Vec<(String, String)> {
    let text: String = (0..k)
        .map(|i| {
            format!(
                "h{i}(m, g) = for k -> v in m where k in 0..<v {{ [v, k, {{v -> k}}] >< max }} + g(desc m);\n"
            )
        })
        .collect();
    vec![("main.zed".into(), text)]
}

/// One function of `k` `for`s, each nested in the body of the one before and reading its source
/// from the binder of that one: the scopes open `k` deep, on the resolver's own stack.
fn nested_fors(k: usize) -> Vec<(String, String)> {
    let mut text = "f(m) = ".to_string();
    for i in 0..k {
        let from = if i == 0 {
            "m".to_string()
        } else {
            format!("a{}", i - 1)
        };
        text.push_str(&format!("for a{i} in {from} {{ "));
    }
    text.push_str(&format!("a{}", k - 1));
    text.push_str(&" }".repeat(k));
    text.push_str(";\n");
    vec![("main.zed".into(), text)]
}

#[test]
fn many_functions_of_later_forms_resolve_in_linear_time() {
    linear("many functions of later forms", 500, later_forms);
}

#[test]
fn fors_nested_deep_resolve_in_linear_time() {
    linear("fors nested deep", 500, nested_fors);
}

#[test]
fn a_long_cycle_is_named_whole_in_linear_time() {
    // The chain closed into a cycle: `c0` imports the last unit.
    rejected(
        "a cycle of units",
        200,
        |k| closed(k, k - 1),
        |k, m| {
            assert_eq!(m.len(), 1, "{m:?}");
            let l = k - 1;
            assert!(
                m[0].starts_with(&format!(
                    "c0.zed:1:1: the unit `c{l}` cannot be imported: the imports form a cycle, so \
                     its units have no order to be resolved in: `c0` imports `c{l}` at \
                     c0.zed:1:1, `c{l}` imports `c{}` at c{l}.zed:1:1, ",
                    l - 1
                )),
                "{}",
                m[0]
            );
            assert!(
                m[0].ends_with("`c1` imports `c0` at c1.zed:1:1."),
                "{}",
                m[0]
            );
            assert_eq!(steps(&m[0]), k);
        },
    );
}

#[test]
fn a_chain_with_one_import_back_is_named_in_linear_time() {
    // `c0` imports the middle of the chain: a cycle of half the units, the rest outside it.
    rejected(
        "a chain with one import back",
        200,
        |k| closed(k, k / 2),
        |k, m| {
            assert_eq!(m.len(), 1, "{m:?}");
            let h = k / 2;
            assert!(
                m[0].starts_with(&format!("c0.zed:1:1: the unit `c{h}` cannot be imported: ")),
                "{}",
                m[0]
            );
            assert!(
                m[0].ends_with("`c1` imports `c0` at c1.zed:1:1."),
                "{}",
                m[0]
            );
            assert_eq!(steps(&m[0]), h + 1);
        },
    );
}

#[test]
fn many_imports_back_into_a_long_cycle_are_named_once_in_linear_time() {
    // Each unit of the cycle also imports its last unit: k imports, each on a cycle, of which
    // a report per import naming its cycle would write O(k²) text. The component is named
    // once, by its shortest cycle through `c0`, which is the whole chain.
    rejected(
        "many imports back into a cycle",
        200,
        |k| {
            let mut fs = closed(k, k - 1);
            let l = k - 1;
            for (i, (_, text)) in fs.iter_mut().enumerate().take(l).skip(1) {
                *text = format!("import c{l}.{{step{l}}};\n{text}step{i}b = step{l};\n");
            }
            fs
        },
        |k, m| {
            assert_eq!(m.len(), 1, "{m:?}");
            assert!(m[0].starts_with("c0.zed:1:1: "), "{}", m[0]);
            assert_eq!(steps(&m[0]), k);
        },
    );
}

#[test]
fn many_disjoint_cycles_are_each_named_in_linear_time() {
    // `k` pairs of units that import each other, as a package split into many halves that
    // still lean on each other; `main` imports one unit of each pair.
    rejected(
        "many cycles of two",
        200,
        |k| {
            let mut fs: Vec<(String, String)> = (0..k)
                .flat_map(|i| {
                    [
                        (
                            format!("p{i}/a.zed"),
                            format!("import p{i}.b.{{b{i}}};\na{i} = 1;\n"),
                        ),
                        (
                            format!("p{i}/b.zed"),
                            format!("import p{i}.a.{{a{i}}};\nb{i} = a{i};\n"),
                        ),
                    ]
                })
                .collect();
            let imports: String = (0..k)
                .map(|i| format!("import p{i}.a.{{a{i}}};\n"))
                .collect();
            fs.push(("main.zed".into(), format!("{imports}total = 0;\n")));
            fs
        },
        |k, m| {
            assert_eq!(m.len(), k, "{m:?}");
            for line in m {
                let file = line.split(':').next().unwrap();
                let i = &file[1..file.len() - "/a.zed".len()];
                assert_eq!(
                    line,
                    &format!(
                        "p{i}/a.zed:1:1: the unit `p{i}.b` cannot be imported: the imports form a \
                         cycle, so its units have no order to be resolved in: `p{i}.a` imports \
                         `p{i}.b` at p{i}/a.zed:1:1, `p{i}.b` imports `p{i}.a` at p{i}/b.zed:1:1."
                    )
                );
            }
        },
    );
}

/// `k` units `u0` … `u{k-1}`, each a new empty file, all given as roots, as when every unit of
/// a package just laid out is checked at once. An empty unit costs little to read, parse and
/// resolve (6,500 instructions; a unit of one comment costs 200,000), so the work of finding a
/// unit among those read so far is what would grow with `k`.
fn placeholders(k: usize) -> (Memory, Vec<String>) {
    let fs = (0..k)
        .map(|i| (format!("u{i}.zed"), String::new()))
        .collect();
    (memory(fs), (0..k).map(|i| format!("u{i}")).collect())
}

#[test]
fn many_roots_load_in_linear_time() {
    // Each unit is looked up among those read when it is added (`unit::add`); a linear scan
    // there in place of `Package::index` makes this 47.2 times the work at 1,000 and 8,000
    // units (measured), while the other tests here pass with it: a unit of the fan costs
    // 540,000 instructions to read, parse and resolve, against the scan's 32 per unit compared.
    let pkgs: HashMap<usize, (Memory, Vec<String>)> = [1000, 8000]
        .into_iter()
        .map(|k| (k, placeholders(k)))
        .collect();
    for (k, (fs, roots)) in &pkgs {
        let roots: Vec<&str> = roots.iter().map(String::as_str).collect();
        let p = load(&mut Db::new(), fs, &roots);
        assert_eq!(p.units.len(), *k);
        assert_eq!(mistakes(&p), Vec::<String>::new());
    }
    scaling::check_order("many roots", 1000, 1, |k| {
        let (fs, roots) = &pkgs[&k];
        let roots: Vec<&str> = roots.iter().map(String::as_str).collect();
        std::hint::black_box(load(&mut Db::new(), fs, &roots));
    });
}

/// A package with no file read, and the import graph edges [`order`] reads.
type Graph = (Package, Vec<Vec<(usize, Span)>>);

/// The package of units `u0` … `u{k-1}`, unit `i` importing the units `imports[i]` in that
/// order, one import a line, with each import graph edge at its line: what [`order`] reads,
/// built with no file read or parsed, so that a test times the ordering and the cycles'
/// reports alone. Loading a unit costs about 510,000 instructions, which hides a cost below
/// about 1,000 instructions for each pair of units in the tests above that load packages.
fn graph(imports: &[Vec<usize>]) -> Graph {
    let mut pkg = Package::default();
    let mut edges = Vec::with_capacity(imports.len());
    for (i, names) in imports.iter().enumerate() {
        let mut text = String::new();
        let mut out = Vec::with_capacity(names.len());
        for &j in names {
            let line = format!("import u{j}.{{v{j}}};\n");
            out.push((
                j,
                Span {
                    start: text.len(),
                    end: text.len() + line.len() - 1,
                },
            ));
            text.push_str(&line);
        }
        text.push_str(&format!("v{i} = {i};\n"));
        let path: Arc<str> = format!("u{i}").into();
        pkg.index.insert(path.clone(), i);
        pkg.units.push(Loaded {
            path,
            file: format!("u{i}.zed"),
            text: Some(Ok(text.into())),
            parsed: None,
            resolved: None,
        });
        edges.push(out);
    }
    (pkg, edges)
}

/// Checks that ordering the import graph `make(k)` and reporting its cycles is linear in its
/// units and imports, from `k` = `n`, with no file read; `expect(k, messages)` holds of the
/// messages of its cycles at each size.
fn ordered(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> Vec<Vec<usize>>,
    expect: impl Fn(usize, &[String]),
) {
    let graphs: HashMap<usize, Mutex<Graph>> = [n, 8 * n]
        .into_iter()
        .map(|k| (k, Mutex::new(graph(&make(k)))))
        .collect();
    for (&k, g) in &graphs {
        let (pkg, edges) = &mut *g.lock().unwrap();
        order(pkg, edges, None);
        assert_eq!(pkg.order.len(), pkg.units.len());
        let messages: Vec<String> = pkg
            .problems
            .iter()
            .map(|p| p.error.message.clone())
            .collect();
        expect(k, &messages);
    }
    scaling::check_order(what, n, 1, |k| {
        let (pkg, edges) = &mut *graphs[&k].lock().unwrap();
        pkg.order.clear();
        pkg.problems.clear();
        std::hint::black_box(order(pkg, edges, None));
    });
}

#[test]
fn many_disjoint_cycles_are_ordered_and_reported_in_linear_time_with_no_file_read() {
    // `k` pairs `u{2i}` and `u{2i+1}` importing each other: `k` components, each searched for
    // its cycle once. Clearing or allocating the search's arrays, of the size of the package,
    // for each component makes this quadratic and fails here (measured, COMPLEXITY.md F84);
    // the loading tests above passed under the allocation, since loading a unit costs far more.
    ordered(
        "many cycles of two, ordered",
        4000,
        |k| (0..2 * k).map(|i| vec![i ^ 1]).collect(),
        |k, m| {
            assert_eq!(m.len(), k);
            assert!(
                m.iter().all(|m| m.matches("` imports `").count() == 2),
                "{m:?}"
            );
        },
    );
}

#[test]
fn one_long_cycle_is_ordered_and_reported_in_linear_time_with_no_file_read() {
    ordered(
        "one cycle, ordered",
        2000,
        |k| (0..k).map(|i| vec![(i + 1) % k]).collect(),
        |k, m| {
            assert_eq!(m.len(), 1);
            assert_eq!(m[0].matches("` imports `").count(), k);
        },
    );
}

#[test]
fn a_dense_component_is_searched_once_in_linear_time_with_no_file_read() {
    // Each unit imports the 16 after it around a ring: one component of `16k` imports. Its
    // shortest cycle through `u0` is found by one breadth-first search over the component,
    // not one from each unit; a search from each unit would take `k` times as long.
    ordered(
        "a dense component, ordered",
        500,
        |k| {
            (0..k)
                .map(|i| (1..=16).map(|d| (i + d) % k).collect())
                .collect()
        },
        |k, m| {
            assert_eq!(m.len(), 1);
            // From `u0`, the units 16 on at each step reach back around the ring.
            assert_eq!(m[0].matches("` imports `").count(), k.div_ceil(16));
        },
    );
}

#[test]
fn a_chain_of_cycles_is_ordered_in_linear_time_with_no_file_read() {
    // Pairs that import each other, each pair's first unit also importing the next pair's:
    // `k` components, each put after the one it imports, the depth-first search `k` deep.
    ordered(
        "a chain of cycles, ordered",
        4000,
        |k| {
            (0..2 * k)
                .map(|i| {
                    let mut to = vec![i ^ 1];
                    if i % 2 == 0 && i + 2 < 2 * k {
                        to.push(i + 2);
                    }
                    to
                })
                .collect()
        },
        |k, m| assert_eq!(m.len(), k),
    );
}

#[test]
fn a_complete_component_is_searched_once_in_time_linear_in_its_imports() {
    // Every unit imports every other: `k(k-1)` imports. The sizes 40 and 113 give 1,560 and
    // 12,656 imports, 8.1 times as many, held to the limit for 8 times.
    let complete = |k: usize| -> Vec<Vec<usize>> {
        (0..k)
            .map(|i| (0..k).filter(|&j| j != i).collect())
            .collect()
    };
    let graphs: HashMap<usize, Mutex<Graph>> = [40, 113]
        .into_iter()
        .map(|k| (k, Mutex::new(graph(&complete(k)))))
        .collect();
    for g in graphs.values() {
        let (pkg, edges) = &mut *g.lock().unwrap();
        order(pkg, edges, None);
        assert_eq!(pkg.problems.len(), 1);
        // `u0` imports `u1` first, and `u1` imports `u0` first.
        assert!(
            pkg.problems[0]
                .error
                .message
                .ends_with("`u0` imports `u1` at u0.zed:1:1, `u1` imports `u0` at u1.zed:1:1"),
            "{}",
            pkg.problems[0].error.message
        );
    }
    let run = |k: usize| {
        let (pkg, edges) = &mut *graphs[&k].lock().unwrap();
        pkg.order.clear();
        pkg.problems.clear();
        std::hint::black_box(order(pkg, edges, None));
    };
    scaling::compare(
        "a complete component, ordered: 40 and 113 units",
        &format!(
            "the 1,560 and 12,656 imports, 8.1 times as many; for work of order n log n in \
             them the rule of low complexity allows at most {:.1} times (DESIGN.md Part G)",
            scaling::limit(40 * 39, 113 * 112, 1)
        ),
        scaling::limit(40 * 39, 113 * 112, 1),
        || run(40),
        || run(113),
    );
}
