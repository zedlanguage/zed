//! Loading and resolving a package at the rule of low complexity (DESIGN.md Part G): linear
//! in its units, its imports and its names, for many units each importing the two before it, a
//! long chain of imports, one unit importing many, one import of many names, and many empty
//! units given as roots. Each package's files are built before timing; the work measured is the
//! loader's, from reading each file to resolving each unit.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::query::Db;
use zedc::unit::{Memory, load};

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
                m[0].ends_with("`c1` imports `c0` at c1.zed:1:1"),
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
                m[0].ends_with("`c1` imports `c0` at c1.zed:1:1"),
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
                         `p{i}.b` at p{i}/a.zed:1:1, `p{i}.b` imports `p{i}.a` at p{i}/b.zed:1:1"
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
