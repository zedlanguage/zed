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

#[test]
fn a_long_cycle_is_named_whole_in_linear_time() {
    // The chain closed into a cycle: `c0` imports the last unit.
    let make = |k: usize| {
        let mut fs = chain(k);
        fs[0].1 = format!("import c{l}.{{step{l}}};\nstep0 = 0;\n", l = k - 1);
        fs
    };
    let pkgs: HashMap<usize, Memory> = [200, 1600]
        .into_iter()
        .map(|k| (k, memory(make(k))))
        .collect();
    let p = load(&mut Db::new(), &pkgs[&200], &["main"]);
    let m = mistakes(&p);
    assert_eq!(m.len(), 1, "{m:?}");
    assert!(m[0].starts_with("c0.zed:1:1: "), "{}", m[0]);
    assert!(
        m[0].ends_with("`c0` imports `c199` at c0.zed:1:1"),
        "{}",
        m[0]
    );
    scaling::check_order("a cycle of units", 200, 1, |k| {
        std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
    });
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
