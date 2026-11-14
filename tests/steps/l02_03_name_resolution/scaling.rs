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
//!
//! The benchmarks in `bench/scaling.rs` hold the time of each; here each package and graph is
//! loaded or ordered at small sizes, with the checks the benchmarks made of their inputs.

use std::sync::Arc;

use zedc::lex::Span;
use zedc::query::Db;
use zedc::unit::{Loaded, Memory, Package, load, order};

use super::{files, mistakes};

/// The package of the `(file, text)` pairs `fs`.
pub(super) fn memory(fs: Vec<(String, String)>) -> Memory {
    let refs: Vec<(&str, &str)> = fs.iter().map(|(f, t)| (f.as_str(), t.as_str())).collect();
    files(&refs)
}

/// The mistakes of loading the package `fs` from `main`.
fn loaded(fs: &Memory) -> Vec<String> {
    mistakes(&load(&mut Db::new(), fs, &["main"]))
}

/// `k` units `u0` … `u{k-1}`, each importing the two before it, like a ledger whose each day
/// reads the two before; `main` imports the last.
pub(super) fn ladder(k: usize) -> Vec<(String, String)> {
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
pub(super) fn chain(k: usize) -> Vec<(String, String)> {
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
pub(super) fn fan(k: usize) -> Vec<(String, String)> {
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
pub(super) fn names(k: usize) -> Vec<(String, String)> {
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
pub(super) fn pairs(k: usize) -> Vec<(String, String)> {
    let params: Vec<String> = (0..k).map(|i| format!("(s{i}, b{i})")).collect();
    let body: Vec<String> = (0..k).map(|i| format!("max(s{i}, b{i})")).collect();
    vec![(
        "main.zed".into(),
        format!("f = ({}) -> {};\n", params.join(", "), body.join(" + ")),
    )]
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

/// One unit of `k` functions, each built of the forms of step L3.2 and L5.1, whose children are
/// resolved: a `for` binding its pattern in its `where` and its body, displays, a range, an `in`
/// test, a reduction and a sort key.
pub(super) fn later_forms(k: usize) -> Vec<(String, String)> {
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
pub(super) fn nested_fors(k: usize) -> Vec<(String, String)> {
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

/// Each package that loads with no mistake but the forms of later steps, at small sizes.
#[test]
fn each_package_that_loads_has_no_mistake_at_small_sizes() {
    for (what, make) in [
        (
            "a ladder of units",
            ladder as fn(usize) -> Vec<(String, String)>,
        ),
        ("a chain of units", chain),
        ("a fan of imports", fan),
        ("an import of many names", names),
        ("a lambda of many tuple parameters", pairs),
        ("many functions of later forms", later_forms),
        ("fors nested deep", nested_fors),
    ] {
        for k in [1, 2, 9] {
            assert_eq!(
                loaded(&memory(make(k))),
                Vec::<String>::new(),
                "{what}, {k}"
            );
        }
    }
}

/// The chain closed into a cycle: `c0` imports the last unit.
pub(super) fn long_cycle(k: usize) -> Vec<(String, String)> {
    closed(k, k - 1)
}

/// The cycle of [`long_cycle`] is named whole.
fn names_the_long_cycle(k: usize, m: &[String]) {
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
}

/// `c0` imports the middle of the chain: a cycle of half the units, the rest outside it.
pub(super) fn chain_back(k: usize) -> Vec<(String, String)> {
    closed(k, k / 2)
}

fn names_the_cycle_back(k: usize, m: &[String]) {
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
}

/// Each unit of the cycle also imports its last unit: k imports, each on a cycle, of which a
/// report per import naming its cycle would write O(k²) text. The component is named once, by
/// its shortest cycle through `c0`, which is the whole chain.
pub(super) fn imports_back(k: usize) -> Vec<(String, String)> {
    let mut fs = closed(k, k - 1);
    let l = k - 1;
    for (i, (_, text)) in fs.iter_mut().enumerate().take(l).skip(1) {
        *text = format!("import c{l}.{{step{l}}};\n{text}step{i}b = step{l};\n");
    }
    fs
}

fn names_the_component_once(k: usize, m: &[String]) {
    assert_eq!(m.len(), 1, "{m:?}");
    assert!(m[0].starts_with("c0.zed:1:1: "), "{}", m[0]);
    assert_eq!(steps(&m[0]), k);
}

/// `k` pairs of units that import each other, as a package split into many halves that still
/// lean on each other; `main` imports one unit of each pair.
pub(super) fn cycles_of_two(k: usize) -> Vec<(String, String)> {
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
}

fn names_each_cycle_of_two(k: usize, m: &[String]) {
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
}

/// Each package of cycles, loaded at small sizes, reports its cycles as its benchmark's inputs
/// did at n and 8n.
#[test]
fn each_package_of_cycles_names_its_cycles_at_small_sizes() {
    for k in [3, 4, 9] {
        names_the_long_cycle(k, &loaded(&memory(long_cycle(k))));
        names_the_cycle_back(k, &loaded(&memory(chain_back(k))));
        names_the_component_once(k, &loaded(&memory(imports_back(k))));
        names_each_cycle_of_two(k, &loaded(&memory(cycles_of_two(k))));
    }
}

/// `k` units `u0` … `u{k-1}`, each a new empty file, all given as roots, as when every unit of
/// a package just laid out is checked at once. An empty unit costs little to read, parse and
/// resolve (6,500 instructions; a unit of one comment costs 200,000), so the work of finding a
/// unit among those read so far is what would grow with `k`.
pub(super) fn placeholders(k: usize) -> (Memory, Vec<String>) {
    let fs = (0..k)
        .map(|i| (format!("u{i}.zed"), String::new()))
        .collect();
    (memory(fs), (0..k).map(|i| format!("u{i}")).collect())
}

/// Each unit is looked up among those read when it is added (`unit::add`), so each root is one
/// unit and none is a mistake.
#[test]
fn a_few_roots_load_each_once() {
    for k in [1, 2, 9] {
        let (fs, roots) = placeholders(k);
        let roots: Vec<&str> = roots.iter().map(String::as_str).collect();
        let p = load(&mut Db::new(), &fs, &roots);
        assert_eq!(p.units.len(), k);
        assert_eq!(mistakes(&p), Vec::<String>::new());
    }
}

/// A package with no file read, and the import graph edges [`order`] reads.
pub(super) type Graph = (Package, Vec<Vec<(usize, Span)>>);

/// The package of units `u0` … `u{k-1}`, unit `i` importing the units `imports[i]` in that
/// order, one import a line, with each import graph edge at its line: what [`order`] reads,
/// built with no file read or parsed, so that a test times the ordering and the cycles'
/// reports alone. Loading a unit costs about 510,000 instructions, which hides a cost below
/// about 1,000 instructions for each pair of units in the tests above that load packages.
pub(super) fn graph(imports: &[Vec<usize>]) -> Graph {
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

/// Orders the import graph `g` and gives the messages of its cycles; every unit is put in the
/// order.
fn ordered(g: &mut Graph) -> Vec<String> {
    let (pkg, edges) = g;
    order(pkg, edges, None);
    assert_eq!(pkg.order.len(), pkg.units.len());
    pkg.problems
        .iter()
        .map(|p| p.error.message.clone())
        .collect()
}

/// `k` pairs `u{2i}` and `u{2i+1}` importing each other: `k` components, each searched for its
/// cycle once.
pub(super) fn pairs_of_units(k: usize) -> Vec<Vec<usize>> {
    (0..2 * k).map(|i| vec![i ^ 1]).collect()
}

/// One cycle through all `k` units.
pub(super) fn ring(k: usize) -> Vec<Vec<usize>> {
    (0..k).map(|i| vec![(i + 1) % k]).collect()
}

/// Each unit imports the 16 after it around a ring: one component of `16k` imports. Its
/// shortest cycle through `u0` is found by one breadth-first search over the component, not one
/// from each unit.
pub(super) fn dense(k: usize) -> Vec<Vec<usize>> {
    (0..k)
        .map(|i| (1..=16).map(|d| (i + d) % k).collect())
        .collect()
}

/// Pairs that import each other, each pair's first unit also importing the next pair's: `k`
/// components, each put after the one it imports, the depth-first search `k` deep.
pub(super) fn chain_of_cycles(k: usize) -> Vec<Vec<usize>> {
    (0..2 * k)
        .map(|i| {
            let mut to = vec![i ^ 1];
            if i % 2 == 0 && i + 2 < 2 * k {
                to.push(i + 2);
            }
            to
        })
        .collect()
}

/// Every unit imports every other: `k(k-1)` imports.
pub(super) fn complete(k: usize) -> Vec<Vec<usize>> {
    (0..k)
        .map(|i| (0..k).filter(|&j| j != i).collect())
        .collect()
}

/// Each import graph, ordered at small sizes with no file read, reports its cycles as its
/// benchmark's inputs did at n and 8n.
#[test]
fn each_import_graph_is_ordered_and_its_cycles_reported_at_small_sizes() {
    for k in [3, 4, 9] {
        let m = ordered(&mut graph(&pairs_of_units(k)));
        assert_eq!(m.len(), k);
        assert!(
            m.iter().all(|m| m.matches("` imports `").count() == 2),
            "{m:?}"
        );
        let m = ordered(&mut graph(&ring(k)));
        assert_eq!(m.len(), 1);
        assert_eq!(m[0].matches("` imports `").count(), k);
        assert_eq!(ordered(&mut graph(&chain_of_cycles(k))).len(), k);
        let m = ordered(&mut graph(&complete(k)));
        assert_eq!(m.len(), 1);
        // `u0` imports `u1` first, and `u1` imports `u0` first.
        assert!(
            m[0].ends_with("`u0` imports `u1` at u0.zed:1:1, `u1` imports `u0` at u1.zed:1:1"),
            "{}",
            m[0]
        );
    }
    // From `u0`, the units 16 on at each step reach back around the ring; below 17 units a unit
    // imports itself.
    for k in [17, 32, 40] {
        let m = ordered(&mut graph(&dense(k)));
        assert_eq!(m.len(), 1);
        assert_eq!(m[0].matches("` imports `").count(), k.div_ceil(16));
    }
}

/// An imported unit `tool` with its own `main` and `k` helpers, each reading `main::files`,
/// half in parentheses, and `main` reading it too; `main` imports one helper.
pub(super) fn own_main(k: usize) -> Vec<(String, String)> {
    let mut text = String::new();
    for i in 0..k {
        let of = if i % 2 == 0 { "main" } else { "(main)" };
        text.push_str(&format!("h{i}(positional p) = {of}::files[p] else \"\";\n"));
    }
    text.push_str(
        "main(m: MainArgs) {\n  fs = main::files;\n  m.stdout <- fs[\"a\"] else \"\";\n}\n",
    );
    vec![
        ("tool.zed".into(), text),
        ("main.zed".into(), "import tool.{h0};\nmain() {\n}\n".into()),
    ]
}

/// Each read of `main::files` in a unit with its own `main` is found among the unit's uses in one
/// pass (QUESTIONS Q54), the reads in parentheses by the builder's walk before the build.
#[test]
fn a_few_reads_of_main_files_in_a_unit_with_its_own_main_are_each_rejected() {
    for k in [1, 2, 9] {
        assert_eq!(loaded(&memory(own_main(k))).len(), k + 1, "{k}");
    }
}
