//! Syntax-error recovery across a package (step L1.29d, plan row L1.29d-package): one build
//! reports every unit's syntax errors, and the resolution errors of the declarations that
//! parse, each once, in its own file; an importer does not repeat a unit's syntax error, and a
//! statement that uses a name a broken declaration of another unit would define is not
//! checked, as within a unit, at any distance and through any number of units. A unit that
//! compiles alone (it imports nothing and sees no prelude unit) has its type errors reported
//! too. Batch and single-file checking agree, and the cost is linear in the units.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use zedc::query::Db;
use zedc::suppress::Suppress;
use zedc::unit::{Memory, Package, load};

/// The files `fs`, each a name under the root and its text.
fn memory(fs: &[(&str, &str)]) -> Memory {
    Memory(
        fs.iter()
            .map(|&(name, text)| (name.to_string(), Arc::from(text)))
            .collect::<HashMap<_, _>>(),
    )
}

/// The headline of each problem of `p`, but for the imports a later step links (L2.4).
fn headlines(p: &Package) -> Vec<String> {
    p.report(Path::new(""))
        .into_iter()
        .map(|m| m.lines().next().unwrap_or_default().to_string())
        .filter(|m| !zed_tests::is_not_yet(m))
        .collect()
}

/// The package of `fs` that the unit `main` reaches.
fn package(fs: &[(&str, &str)]) -> Package {
    load(&mut Db::new(), &memory(fs), &["main"])
}

/// A package of four units: `geo` has two declarations that do not parse, and imports
/// `helpers`, which has an error of its own; `stats` has one; `main` imports names that
/// `geo` and `stats` would define.
const SHOP: &[(&str, &str)] = &[
    ("zed.manifest", "// the shop\n"),
    (
        "main.zed",
        "import geo.{area, perimeter, later, side};\nimport stats.{mean, var};\n\
         a = area(1, 2) + nosuch;\nb = later(3) + var(1, 2) + nosuch;\nc = mean(1, 2) + side;\n\
         d = undefinedHere;\n",
    ),
    (
        "geo.zed",
        "import helpers.{sq};\nperimeter(w, h) = 2 * (w + h\narea(w, h) = w * * h;\n\
         side = sq(2);\nlater(x) = perimeter(x, x) + 1;\nbad = nosuch + 1;\n",
    ),
    ("helpers.zed", "sq(x) = x * x;\nalsobad = 1 + \"a\";\n"),
    (
        "stats.zed",
        "mean(a, b) = (a + b) / 2;\nvar(a, b = a * a;\n",
    ),
];

#[test]
fn one_build_reports_every_units_syntax_errors_each_once_in_its_own_file() {
    let p = package(SHOP);
    assert_eq!(
        headlines(&p),
        [
            "geo.zed:3:1: Syntax error at `area`. Try `perimeter(w, h) = 2 * (w + h);` instead.",
            "geo.zed:3:18: Syntax error at `*`. Try `area(w, h) = w * h;` instead.",
            "geo.zed:6:7: `nosuch` is not defined.",
            "helpers.zed:2:11: `+` does not take (1, \"a\"): no arrow of `+` takes these types.",
            // `a` and `b` use names `geo` and `stats` would define, and `later`, which uses
            // `perimeter`: they are not checked, so their `nosuch` is not reported. `c` uses
            // only names that are defined, and `d` none: both are checked.
            "main.zed:6:5: `undefinedHere` is not defined.",
            "stats.zed:2:17: Syntax error at `;`.",
        ]
    );
}

#[test]
fn an_importer_does_not_repeat_the_syntax_error_of_a_unit_it_imports() {
    let p = package(SHOP);
    let all = p.report(Path::new(""));
    assert!(
        all.iter()
            .all(|m| !m.starts_with("main.zed") || !m.contains("parse")),
        "{all:?}"
    );
    for syntax in ["geo.zed:3:1:", "geo.zed:3:18:", "stats.zed:2:17:"] {
        let n = all.iter().filter(|m| m.starts_with(syntax)).count();
        assert_eq!(n, 1, "{syntax} in {all:?}");
    }
}

#[test]
fn a_statement_that_uses_a_broken_import_is_not_checked_whatever_else_it_holds() {
    // Each statement of `main` that reads `area` holds an error of its own; none is reported,
    // since a repair of `area` may change them. The last statement is checked.
    let p = package(&[
        ("geo.zed", "area(w, h) = w * * h;\n"),
        (
            "main.zed",
            "import geo.{area};\nx = area(1, 2) + nosuch;\ny = x + alsoNot;\n\
             z(n: Missing) = area(n, n);\nw = stillNot;\n",
        ),
    ]);
    assert_eq!(
        headlines(&p),
        [
            "geo.zed:1:18: Syntax error at `*`. Try `area(w, h) = w * h;` instead.",
            "main.zed:5:5: `stillNot` is not defined.",
        ]
    );
}

#[test]
fn the_names_dropped_in_one_unit_are_dropped_in_the_units_that_import_them() {
    // `mid.twice` uses `low.half`, which does not parse, so `twice` is not checked in `mid`,
    // and `top`'s use of it is not checked either, two imports away from the error.
    let p = package(&[
        ("low.zed", "half(x) = x / ;\n"),
        (
            "mid.zed",
            "import low.{half};\ntwice(x) = half(x) * 4;\nown = 1;\n",
        ),
        (
            "main.zed",
            "import mid.{twice, own};\nt = twice(2) + nosuch;\no = own + other;\n",
        ),
    ]);
    assert_eq!(
        headlines(&p),
        [
            "low.zed:1:15: Syntax error at `;`.",
            "main.zed:3:11: `other` is not defined.",
        ]
    );
}

#[test]
fn a_qualified_use_of_a_broken_name_is_not_checked_and_of_a_missing_one_is() {
    let p = package(&[
        ("geo.zed", "area(w, h) = w * * h;\nside = 2;\n"),
        (
            "main.zed",
            "import geo;\nw = geo.area(1, 2) + nosuch;\nv = geo.nothere;\nu = geo.side;\n",
        ),
    ]);
    assert_eq!(
        headlines(&p),
        [
            "geo.zed:1:18: Syntax error at `*`. Try `area(w, h) = w * h;` instead.",
            "main.zed:3:5: the unit `geo` defines no `nothere`.",
        ]
    );
}

#[test]
fn a_type_a_broken_declaration_would_define_is_not_checked_where_imported() {
    let p = package(&[
        ("shapes.zed", "struct Point { x: f64, y: }\n"),
        (
            "main.zed",
            "import shapes.{Point};\nnorm(p: Point) = p.x + nosuch;\nok = notThere;\n",
        ),
    ]);
    let h = headlines(&p);
    assert_eq!(h.len(), 2, "{h:?}");
    assert!(
        h[0].starts_with("main.zed:3:6: `notThere` is not defined"),
        "{h:?}"
    );
    assert!(h[1].starts_with("shapes.zed:1:"), "{h:?}");
    assert!(h[1].contains("Syntax error"), "{h:?}");
}

#[test]
fn a_unit_that_does_not_lex_hides_every_name_it_imports_with_no_error_at_the_importer() {
    // A unit that does not lex has no declarations to read: every name an import brings in
    // from it is unknown, and the statements that use them are not checked.
    let p = package(&[
        ("odd.zed", "f(x) = x + 1;\ns = \"open;\n"),
        (
            "main.zed",
            "import odd.{f, g};\nimport odd;\na = f(1) + g(2) + nosuch;\nb = odd.h + nosuch;\n\
             c = notThere;\n",
        ),
    ]);
    let h = headlines(&p);
    assert_eq!(h.len(), 2, "{h:?}");
    assert_eq!(h[0], "main.zed:5:5: `notThere` is not defined.", "{h:?}");
    assert!(h[1].starts_with("odd.zed:2:"), "{h:?}");
}

#[test]
fn a_unit_that_compiles_alone_has_its_syntax_and_type_errors_reported_together() {
    let p = package(&[
        (
            "calc.zed",
            "half(x) = x / ;\nsum = 1 + \"a\";\nuse = half(2) + true;\n",
        ),
        ("main.zed", "import calc.{sum};\nmain(m: MainArgs) {}\n"),
    ]);
    assert_eq!(
        headlines(&p),
        [
            "calc.zed:1:15: Syntax error at `;`.",
            "calc.zed:2:7: `+` does not take (1, \"a\"): no arrow of `+` takes these types.",
        ]
    );
}

/// The directory `name` under this process's scratch directory, holding the files `fs`.
fn package_dir(name: &str, fs: &[(&str, &str)]) -> PathBuf {
    let d = zed_tests::step_helpers::scratch(format!("l01_29_package/{name}"));
    for (file, text) in fs {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    d
}

/// The problems of `report`, the text `zedc` prints, each a headline that starts with `root`
/// and the lines after it, by the file each lies in, in the order printed.
fn by_file(root: &str, report: &str) -> BTreeMap<String, Vec<String>> {
    let mut out: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut last: Option<String> = None;
    for line in report.lines() {
        if let Some(rest) = line.strip_prefix(root) {
            let file = rest.split(':').next().unwrap().to_string();
            out.entry(file.clone()).or_default().push(line.to_string());
            last = Some(file);
        } else if let Some(f) = &last {
            let p = out.get_mut(f).unwrap().last_mut().unwrap();
            p.push('\n');
            p.push_str(line);
        }
    }
    out
}

#[test]
fn batch_and_single_file_checking_agree_on_every_unit() {
    let d = package_dir("shop", SHOP);
    let root = format!("{}/", d.display());
    let units = ["main", "geo", "helpers", "stats"];
    let batch = load(&mut Db::new(), &zedc::unit::Dir(d.clone()), &units);
    let batch = batch.report_on_disk(&d, &mut Suppress::default());
    let batch = by_file(&root, &batch.join("\n"));
    assert_eq!(batch.len(), 4, "{batch:?}");
    for unit in units {
        let file = d.join(format!("{unit}.zed"));
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let status = zedc::run::command(
            &["run", file.to_str().unwrap()],
            &mut "".as_bytes(),
            &mut out,
            &mut err,
        );
        let err = String::from_utf8(err).unwrap();
        assert_eq!(status, 1, "{err}");
        let alone = by_file(&root, &err);
        assert!(!alone.is_empty(), "`zedc run {unit}`: {err}");
        for (f, problems) in &alone {
            assert_eq!(Some(problems), batch.get(f), "`zedc run {unit}`, file {f}");
        }
    }
}

/// `k` units `u0` … `u{k-1}`, each importing two names of the one before it, each with a
/// declaration that does not parse, a declaration that uses the broken name it imports, which
/// is dropped, and one error of its own; `u0` compiles alone, so its error is a type error.
/// `main` imports from the last.
fn broken_chain(k: usize) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = (0..k)
        .map(|i| {
            let text = match i {
                0 => "step0(x) = (x + ;\nvia0(x) = step0(x);\nbad0 = 1 + \"a\";\n".to_string(),
                _ => format!(
                    "import u{p}.{{step{p}, via{p}}};\nstep{i}(x) = (x + ;\n\
                     via{i}(x) = step{p}(x) + via{p}(x) + nosuch;\nbad{i} = nosuch{i};\n",
                    p = i - 1
                ),
            };
            (format!("u{i}.zed"), text)
        })
        .collect();
    out.push((
        "main.zed".into(),
        format!(
            "import u{l}.{{via{l}}};\ntotal = via{l}(1) + nosuch;\n",
            l = k - 1
        ),
    ));
    out
}

/// [`broken_chain`]`(k)` in memory.
pub(super) fn a_broken_chain(k: usize) -> Memory {
    let fs = broken_chain(k);
    let refs: Vec<(&str, &str)> = fs.iter().map(|(f, t)| (f.as_str(), t.as_str())).collect();
    memory(&refs)
}

#[test]
fn reporting_the_errors_of_a_chain_of_broken_units() {
    for k in [1, 2, 6] {
        let p = load(&mut Db::new(), &a_broken_chain(k), &["main"]);
        // Each unit's syntax error and its own error (at `u0`, which compiles alone, its type
        // error), nothing for the dropped declarations.
        let h = headlines(&p);
        let odd: Vec<&String> = h
            .iter()
            .filter(|m| !m.contains("Syntax error") && !m.contains("`nosuch"))
            .collect();
        assert_eq!(h.len(), 2 * k, "{odd:?}");
        assert_eq!(odd.len(), 1, "{odd:?}");
        assert!(h.iter().all(|m| !m.contains("`nosuch`")), "{h:?}");
    }
}
