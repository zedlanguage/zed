//! Import cycles reported the same whatever the order of the roots: each strongly connected
//! component of the import graph once, at the import of its first unit by path that begins the
//! shortest cycle through it, the cycle written from that unit; each self-import at the unit's
//! first import of itself; and the problems in order of their files.

use super::{files, mistakes};
use zedc::query::Db;
use zedc::unit::load;

/// Every order of `items`.
fn orders<'a>(items: &[&'a str]) -> Vec<Vec<&'a str>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut out = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let first = rest.remove(i);
        for mut o in orders(&rest) {
            o.insert(0, first);
            out.push(o);
        }
    }
    out
}

/// The mistakes of the package `fs` loaded from the roots `roots`, checked to be byte for byte
/// the same for every order of the roots.
fn every_order(fs: &[(&str, &str)], roots: &[&str]) -> Vec<String> {
    let files = files(fs);
    let all = orders(roots);
    let first = mistakes(&load(&mut Db::new(), &files, &all[0]));
    for o in &all[1..] {
        assert_eq!(
            mistakes(&load(&mut Db::new(), &files, o)),
            first,
            "roots {o:?} against {:?}",
            all[0]
        );
    }
    first
}

/// Checks that the package `fs`, one strongly connected component, reports the same from each
/// of its units alone as from all of them: the batch and the single unit agree.
fn each_alone_agrees(fs: &[(&str, &str)], roots: &[&str], batch: &[String]) {
    let files = files(fs);
    for r in roots {
        assert_eq!(
            mistakes(&load(&mut Db::new(), &files, &[r])),
            batch,
            "the unit `{r}` alone"
        );
    }
}

#[test]
fn a_cycle_of_two_is_reported_at_the_same_import_from_either_unit() {
    let fs = [
        (
            "orders.zed",
            "import stock.{reserve};\nplace(n) = reserve(n);\n",
        ),
        (
            "stock.zed",
            "\nimport orders.{place};\nreserve(n) = n;\nrestock(n) = place(n);\n",
        ),
    ];
    let m = every_order(&fs, &["orders", "stock"]);
    // `orders` comes first by path; `stock`'s import is rejected with no error of its own, and
    // its use of `place` is not reported, since the import binds it.
    assert_eq!(
        m,
        [
            "orders.zed:1:1: the unit `stock` cannot be imported: the imports form a cycle, so its \
          units have no order to be resolved in: `orders` imports `stock` at orders.zed:1:1, \
          `stock` imports `orders` at stock.zed:2:1"
        ]
    );
    each_alone_agrees(&fs, &["orders", "stock"], &m);
}

#[test]
fn two_disjoint_cycles_are_each_reported_once() {
    let fs = [
        ("catalog.zed", "import pricing.{price};\nitem = price(1);\n"),
        ("pricing.zed", "import catalog.{item};\nprice(n) = n * 2;\n"),
        ("invoices.zed", "import payments.{paid};\ndue = 1;\n"),
        ("payments.zed", "import invoices.{due};\npaid = due;\n"),
    ];
    let m = every_order(&fs, &["invoices", "pricing", "payments", "catalog"]);
    assert_eq!(
        m,
        [
            "catalog.zed:1:1: the unit `pricing` cannot be imported: the imports form a cycle, so \
             its units have no order to be resolved in: `catalog` imports `pricing` at \
             catalog.zed:1:1, `pricing` imports `catalog` at pricing.zed:1:1",
            "invoices.zed:1:1: the unit `payments` cannot be imported: the imports form a cycle, \
             so its units have no order to be resolved in: `invoices` imports `payments` at \
             invoices.zed:1:1, `payments` imports `invoices` at payments.zed:1:1",
        ]
    );
    // A unit alone reaches its own cycle only, reported as in the batch.
    let files = files(&fs);
    for (root, line) in [("pricing", 0), ("payments", 1)] {
        assert_eq!(
            mistakes(&load(&mut Db::new(), &files, &[root])),
            [m[line].as_str()]
        );
    }
}

#[test]
fn a_cycle_of_three_with_a_chord_is_reported_once_by_its_shortest_cycle() {
    // `cart` reaches `stock` both through `orders` and directly, and `stock` imports `cart`:
    // two cycles in one component, of which the one through the direct import is shorter.
    let fs = [
        (
            "cart.zed",
            "import orders.{place};\nimport stock.{reserve};\ncheckout(n) = place(reserve(n));\n",
        ),
        (
            "orders.zed",
            "import stock.{reserve};\nplace(n) = reserve(n);\n",
        ),
        ("stock.zed", "import cart.{checkout};\nreserve(n) = n;\n"),
    ];
    let roots = ["cart", "orders", "stock"];
    let m = every_order(&fs, &roots);
    assert_eq!(
        m,
        [
            "cart.zed:2:1: the unit `stock` cannot be imported: the imports form a cycle, so its \
          units have no order to be resolved in: `cart` imports `stock` at cart.zed:2:1, `stock` \
          imports `cart` at stock.zed:1:1"
        ]
    );
    each_alone_agrees(&fs, &roots, &m);
}

#[test]
fn of_two_shortest_cycles_the_one_whose_import_comes_first_in_the_text_is_reported() {
    let others = [
        ("auth.zed", "import app.{name};\nuser = 1;\n"),
        ("db.zed", "import app.{name};\nrows = 2;\n"),
    ];
    for (app, at, first) in [
        (
            "import auth.{user};\nimport db.{rows};\nname = 0;\n",
            1,
            "auth",
        ),
        (
            "import db.{rows};\nimport auth.{user};\nname = 0;\n",
            1,
            "db",
        ),
        (
            "name = 0;\nimport db.{rows};\nimport auth.{user};\n",
            2,
            "db",
        ),
    ] {
        let fs = [("app.zed", app), others[0], others[1]];
        let roots = ["app", "auth", "db"];
        let m = every_order(&fs, &roots);
        assert_eq!(
            m,
            [format!(
                "app.zed:{at}:1: the unit `{first}` cannot be imported: the imports form a cycle, \
                 so its units have no order to be resolved in: `app` imports `{first}` at \
                 app.zed:{at}:1, `{first}` imports `app` at {first}.zed:1:1"
            )],
            "{app}"
        );
        each_alone_agrees(&fs, &roots, &m);
    }
}

#[test]
fn a_unit_that_imports_itself_on_a_cycle_is_reported_for_both() {
    let fs = [
        (
            "ledger.zed",
            "import audit.{check};\nimport ledger.{post};\nimport ledger.{post};\n\
             post(x) = check(x);\n",
        ),
        ("audit.zed", "import ledger.{post};\ncheck(x) = x;\n"),
    ];
    let m = every_order(&fs, &["ledger", "audit"]);
    // The component of `audit` and `ledger` once, from `audit`; the self-import once, at the
    // first of `ledger`'s two imports of itself.
    assert_eq!(
        m,
        [
            "audit.zed:1:1: the unit `ledger` cannot be imported: the imports form a cycle, so its \
             units have no order to be resolved in: `audit` imports `ledger` at audit.zed:1:1, \
             `ledger` imports `audit` at ledger.zed:1:1",
            "ledger.zed:2:1: the unit `ledger` cannot be imported: the imports form a cycle, so \
             its units have no order to be resolved in: `ledger` imports `ledger` at \
             ledger.zed:2:1",
        ]
    );
    each_alone_agrees(&fs, &["ledger", "audit"], &m);
}

#[test]
fn units_outside_cycles_are_ordered_and_reported_the_same_for_every_order_of_the_roots() {
    // Two units that do not parse, a cycle, and units that import them: the problems come in
    // order of their files, and the units in one order, whatever the roots' order.
    let fs = [
        ("report.zed", "import sales.{total};\nshown = total;\n"),
        ("sales.zed", "import tax.{rate};\ntotal = rate;\n"),
        ("tax.zed", "rate = ;\n"),
        ("draft.zed", "x = ;\n"),
        ("left.zed", "import right.{r};\nl = 1;\n"),
        ("right.zed", "import left.{l};\nr = 2;\n"),
    ];
    let roots = ["report", "draft", "left", "tax"];
    let m = every_order(&fs, &roots);
    let files_of: Vec<&str> = m.iter().map(|l| l.split(':').next().unwrap()).collect();
    assert_eq!(
        files_of,
        ["draft.zed", "left.zed", "sales.zed", "tax.zed"],
        "{m:?}"
    );
    let files = files(&fs);
    let unit_order = |roots: &[&str]| -> Vec<String> {
        let p = load(&mut Db::new(), &files, roots);
        p.order
            .iter()
            .map(|&i| p.units[i].path.to_string())
            .collect()
    };
    let first = unit_order(&roots);
    for o in orders(&roots) {
        assert_eq!(unit_order(&o), first, "roots {o:?}");
    }
    assert_eq!(
        first,
        ["draft", "left", "right", "tax", "sales", "report"],
        "each unit after the units it imports"
    );
}
