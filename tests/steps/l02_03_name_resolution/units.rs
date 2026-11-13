//! Units as files: `local`, a unit with no file, a unit that does not parse, the import graph's
//! order and its cycles, and the file a unit path names.

use super::{errors, mistakes, package, use_of};
use zedc::unit::{file_of, unit_of};

#[test]
fn a_local_declaration_is_visible_in_its_unit_and_not_through_an_import() {
    let p = package(&[
        (
            "billing.zed",
            "local taxRate = 0.2;\ntotal(net: f64) = net * (1.0 + taxRate);\n",
        ),
        (
            "main.zed",
            "import billing.{total, taxRate};\ndue = total(100.0);\n",
        ),
    ]);
    // In its unit the name resolves; the importer is refused it, with the import named.
    assert_eq!(
        use_of(&p, "billing", "taxRate", 1),
        ["binding taxRate = 0.2;"]
    );
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:1:1: `taxRate` is declared `local` in the unit `billing`, so no other unit \
          sees it.\n  \
          [1] 1:1: the import of the unit `billing`\n      \
          1 | import billing.{total, taxRate};\n        \
          | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
        ]
    );
    let billing = p.unit("billing").unwrap().resolved.as_ref().unwrap();
    assert_eq!(billing.res.local.len(), 1);
    assert!(billing.res.exports.get("taxRate").unwrap().local);
    assert!(!billing.res.exports.get("total").unwrap().local);
}

#[test]
fn local_is_a_node_of_the_syntax_tree_that_prints_as_written() {
    let text = "local taxRate = 0.2;\n";
    let tokens = zedc::lex::lex(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    assert!(matches!(stmts[0].kind, zedc::ast::StmtKind::Local(_)));
    assert_eq!(zedc::format::format(text, &tokens, &stmts), text);
}

#[test]
fn local_marks_a_top_level_definition_only() {
    assert_eq!(
        errors("f(x) = {\n  local y = x;\n  y\n};\n"),
        [
            "`local` keeps a declaration from other units, and a declaration in a block is seen \
             by no other unit already, so `local` stands only at a unit's top level or in a \
             loop body. Remove the `local`. [local y = x;]"
        ]
    );
    assert_eq!(
        errors("import billing;\nlocal import billing;\n"),
        [
            "the unit `billing` cannot be imported: no manifest `zed.manifest` marks a package \
             root at or above this unit, so it imports no unit [import billing;]",
            "`local` stands before an import, whose names are not definitions of the unit, and \
             `local` marks only a binding, a function, a struct, a type or a method. Remove the \
             `local`, or write it before one of those. [local import billing;]",
        ]
    );
}

#[test]
fn an_import_of_a_unit_with_no_file_names_the_file_looked_for() {
    let p = package(&[(
        "main.zed",
        "import geometry.solids.{volume};\nv = volume(1.0);\n",
    )]);
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:1:1: the unit `geometry.solids` cannot be imported: there is no file \
          `geometry/solids.zed` under the root."
        ]
    );
}

#[test]
fn a_unit_that_does_not_parse_reports_its_own_error_and_its_importer_none() {
    // The syntax error is reported once, in its own file; the importer's use of `x`, which
    // the broken declaration would define, is not checked (step L1.29d).
    let p = package(&[
        ("broken.zed", "x = ;\n"),
        ("main.zed", "import broken.{x};\ny = x;\n"),
    ]);
    let m = mistakes(&p);
    assert_eq!(m.len(), 1, "{m:?}");
    assert!(
        m[0].starts_with("broken.zed:1:5: Syntax error at `;`."),
        "{m:?}"
    );
}

#[test]
fn a_cycle_is_rejected_once_at_the_import_of_its_first_unit_naming_every_unit_on_it() {
    let p = package(&[
        ("main.zed", "import orders.{place};\nrun = place(1);\n"),
        (
            "orders.zed",
            "import stock.{reserve};\nplace(n) = reserve(n);\n",
        ),
        ("stock.zed", "\nimport orders.{place};\nreserve(n) = n;\n"),
    ]);
    assert_eq!(
        mistakes(&p),
        [
            "orders.zed:1:1: the unit `stock` cannot be imported: the imports form a cycle, so its \
          units have no order to be resolved in: `orders` imports `stock` at orders.zed:1:1, \
          `stock` imports `orders` at stock.zed:2:1."
        ]
    );
    // The order puts each unit after the units it imports outside its component, and the units
    // of the cycle together, in order of their paths.
    let order: Vec<&str> = p.order.iter().map(|&i| &*p.units[i].path).collect();
    assert_eq!(order, ["orders", "stock", "main"]);
}

#[test]
fn a_unit_that_imports_itself_is_a_cycle_of_one() {
    let p = package(&[("main.zed", "import main.{x};\nx = 1;\n")]);
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:1:1: the unit `main` cannot be imported: the imports form a cycle, so its \
          units have no order to be resolved in: `main` imports `main` at main.zed:1:1."
        ]
    );
}

#[test]
fn a_diamond_is_no_cycle_and_each_unit_is_read_once() {
    let p = package(&[
        (
            "main.zed",
            "import left.{l};\nimport right.{r};\nboth = l + r;\n",
        ),
        ("left.zed", "import base.{b};\nl = b + 1;\n"),
        ("right.zed", "import base.{b};\nr = b + 2;\n"),
        ("base.zed", "b = 10;\n"),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(p.units.len(), 4);
    let order: Vec<&str> = p.order.iter().map(|&i| &*p.units[i].path).collect();
    assert_eq!(order.last(), Some(&"main"));
    assert_eq!(order.iter().position(|u| *u == "base"), Some(0));
}

#[test]
fn a_root_with_no_file_is_reported() {
    let p = package(&[]);
    assert_eq!(
        mistakes(&p),
        ["main.zed: there is no unit `main`: no file `main.zed` under the root"]
    );
}

#[test]
fn a_unit_path_names_a_file_under_the_root_and_back() {
    assert_eq!(file_of("geometry.shapes"), "geometry/shapes.zed");
    assert_eq!(unit_of("geometry/shapes.zed").unwrap(), "geometry.shapes");
    assert_eq!(
        unit_of("geometry/my-shapes.zed").unwrap_err(),
        "the file `geometry/my-shapes.zed` names no unit: `my-shapes` is not a name, and each \
         directory under the package root and the file's stem must be one"
    );
    assert_eq!(
        unit_of("notes.txt").unwrap_err(),
        "the file `notes.txt` is not a unit: its name does not end in `.zed`"
    );
}

/// A unit with its own `main` and a helper that read `main::files` (QUESTIONS Q54).
const OWN_MAIN: &str = "size(positional p) = main::files[p] else \"none\";\n\
                        main(m: MainArgs) {\n  fs = main::files;\n  \
                        m.stdout <- size(\"a\") ++ (fs[\"b\"] else \"\");\n}\n";

#[test]
fn main_files_in_a_unit_with_its_own_main_is_rejected_unless_the_unit_is_the_root() {
    // Imported, the unit's `main` never runs, so each read, in its `main` and outside it,
    // names that `main`; at the root it is the program's own.
    let p = package(&[
        ("tool.zed", OWN_MAIN),
        ("main.zed", "import tool.{size};\nmain() {\n}\n"),
    ]);
    // The second read's listing gives the lines the first one showed by their ranges.
    let shown = "      2 | main(m: MainArgs) {\n        | ^^^^^^^^^^^^^^^^^";
    let got = mistakes(&p);
    assert_eq!(got.len(), 2, "{got:#?}");
    for (g, (at, step, line)) in got.iter().zip([
        ("1:22", "2:1", shown),
        ("3:8", "2:1 to 2:17", "      line 2 is shown above"),
    ]) {
        let want = format!(
            "tool.zed:{at}: `main::files` names this unit's own `main`, and this unit is not the \
             program's root.\n  [1] {step}: the unit's `main`, which never runs: only the root \
             unit's `main` runs, and every other unit reads its files\n{line}\n  [2] {step}: \
             repair: rename this `main`; `main::files` then names the program's entry point"
        );
        assert_eq!(g, &want);
    }
    let root = zedc::unit::load(
        &mut zedc::query::Db::new(),
        &super::files(&[("tool.zed", OWN_MAIN)]),
        &["tool"],
    );
    assert_eq!(mistakes(&root), Vec::<String>::new());
    // A unit with no `main` of its own reads the program's port, imported or not.
    let p = package(&[
        (
            "lib.zed",
            "size(positional p) = main::files[p] else \"none\";\n",
        ),
        ("main.zed", "import lib.{size};\nmain() {\n}\n"),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
}
