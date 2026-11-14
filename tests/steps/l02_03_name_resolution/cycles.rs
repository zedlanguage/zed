//! Import cycles reported the same whatever the order of the roots: each strongly connected
//! component of the import graph once, at the import of its first unit by path that begins the
//! shortest cycle through it, the cycle written from that unit; each self-import at the unit's
//! first import of itself; and the problems in order of their files.

use std::collections::HashMap;
use std::path::Path;

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
          `stock` imports `orders` at stock.zed:2:1."
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
             catalog.zed:1:1, `pricing` imports `catalog` at pricing.zed:1:1.",
            "invoices.zed:1:1: the unit `payments` cannot be imported: the imports form a cycle, \
             so its units have no order to be resolved in: `invoices` imports `payments` at \
             invoices.zed:1:1, `payments` imports `invoices` at payments.zed:1:1.",
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
          imports `cart` at stock.zed:1:1."
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
                 app.zed:{at}:1, `{first}` imports `app` at {first}.zed:1:1."
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
             `ledger` imports `audit` at ledger.zed:1:1.",
            "ledger.zed:2:1: the unit `ledger` cannot be imported: the imports form a cycle, so \
             its units have no order to be resolved in: `ledger` imports `ledger` at \
             ledger.zed:2:1.",
        ]
    );
    each_alone_agrees(&fs, &["ledger", "audit"], &m);
}

#[test]
fn units_outside_cycles_are_ordered_and_reported_the_same_for_every_order_of_the_roots() {
    // Two units that do not parse, a cycle, and units that import them: the problems come in
    // order of their files, and the units in one order, whatever the roots' order. `sales`
    // imports a name of `tax`, which does not parse, and is given no error for it (L1.29d).
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
    assert_eq!(files_of, ["draft.zed", "left.zed", "tax.zed"], "{m:?}");
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

/// The lines of `batch` that a check of the units `reached` alone gives as well: those of the
/// files of those units and of the manifest, but for the error of a root with no file that is
/// not `root`. Each file's lines keep their order.
fn restricted(batch: &[String], reached: &[String], root: &str) -> Vec<String> {
    let files: Vec<String> = reached.iter().map(|u| file_of(u)).collect();
    batch
        .iter()
        .filter(|l| {
            let file = l.split(':').next().unwrap();
            (file == "zed.manifest" || files.iter().any(|f| f == file))
                && !(l.contains(": there is no unit `") && !l.contains(&format!("unit `{root}`")))
        })
        .cloned()
        .collect()
}

/// The file of the unit `path`.
fn file_of(path: &str) -> String {
    format!("{}.zed", path.replace('.', "/"))
}

/// The name the generated unit `path` defines.
fn defined(path: &str) -> String {
    format!("v{}", path.replace('.', "_"))
}

/// A generator of numbers, seeded, so that each case can be run again by its seed.
struct Rng(u64);

impl Rng {
    /// A number below `n` (splitmix64).
    fn below(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        ((z ^ (z >> 31)) % n as u64) as usize
    }
}

/// A package [`generate`] made: its files, its roots, its prelude, and each unit's imports in
/// order with the line of each, for the units with a file that parses.
type Generated = (
    Vec<(String, String)>,
    Vec<&'static str>,
    Option<&'static str>,
    HashMap<&'static str, Vec<(&'static str, usize)>>,
);

/// The paths of the generated units; `zz` never has a file.
const PATHS: [&str; 8] = ["a", "b", "c", "d", "e", "g.x", "g.y", "zz"];

/// A small package, made from `seed`: units of [`PATHS`], each importing up to four of them
/// (itself, a unit with no file and the same unit twice among them), some not parsing, some
/// with a definition before their imports, and sometimes a prelude; with roots, one of which
/// may name no file.
fn generate(seed: u64) -> Generated {
    let mut rng = Rng(seed);
    let mut fs = Vec::new();
    let mut graph = HashMap::new();
    // `zz` never has a file.
    for &u in &PATHS[..7] {
        if rng.below(8) == 0 {
            continue;
        }
        if rng.below(8) == 0 {
            fs.push((file_of(u), format!("{} = ;\n", defined(u))));
            continue;
        }
        let mut text = String::new();
        let mut line = 1;
        if rng.below(3) == 0 {
            text.push_str(&format!("{} = 1;\n", defined(u)));
            line += 1;
        }
        let mut imports = Vec::new();
        for _ in 0..rng.below(5) {
            let to = PATHS[rng.below(PATHS.len())];
            text.push_str(&format!("import {to}.{{{}}};\n", defined(to)));
            imports.push((to, line));
            line += 1;
        }
        if !text.starts_with('v') {
            text.push_str(&format!("{} = 1;\n", defined(u)));
        }
        fs.push((file_of(u), text));
        graph.insert(u, imports);
    }
    let prelude = (rng.below(4) == 0).then(|| PATHS[rng.below(7)]);
    if let Some(p) = prelude {
        fs.push(("zed.manifest".into(), format!("prelude = \"{p}\";\n")));
    }
    let mut roots: Vec<&str> = Vec::new();
    for _ in 0..1 + rng.below(4) {
        let r = PATHS[rng.below(PATHS.len())];
        if !roots.contains(&r) {
            roots.push(r);
        }
    }
    (fs, roots, prelude, graph)
}

/// The units the units `from` reach by `graph`, those with no file and those that do not parse
/// among them, in order of their paths.
fn reach(graph: &HashMap<&str, Vec<(&str, usize)>>, from: &[&str]) -> Vec<String> {
    let mut seen: Vec<&str> = Vec::new();
    let mut todo: Vec<&str> = from.to_vec();
    while let Some(u) = todo.pop() {
        if seen.contains(&u) {
            continue;
        }
        seen.push(u);
        todo.extend(graph.get(u).into_iter().flatten().map(|&(v, _)| v));
    }
    seen.sort_unstable();
    seen.into_iter().map(String::from).collect()
}

/// The messages of the import cycles of the units `units` by `graph`, found by brute force: each
/// self-import at its first line; and for each strongly connected component of two units or
/// more, every simple cycle through its first unit by path that goes through another unit, the
/// least by its length and then by the positions of its imports in their units, in order along
/// it, written from that unit.
fn expected_cycles(graph: &HashMap<&str, Vec<(&str, usize)>>, units: &[String]) -> Vec<String> {
    let reaches = |a: &str, b: &str| reach(graph, &[a]).iter().any(|u| u == b);
    let mut out = Vec::new();
    let step = |from: &str, to: &str, line: usize| {
        format!("`{from}` imports `{to}` at {}:{line}:1", file_of(from))
    };
    let message = |steps: &[(&str, &str, usize)]| {
        let (from, to, line) = steps[0];
        let named: Vec<String> = steps.iter().map(|&(f, t, l)| step(f, t, l)).collect();
        format!(
            "{}:{line}:1: the unit `{to}` cannot be imported: the imports form a cycle, so its \
             units have no order to be resolved in: {}.",
            file_of(from),
            named.join(", ")
        )
    };
    for u in units {
        let imports = graph.get(u.as_str()).map_or(&[][..], Vec::as_slice);
        if let Some(&(_, line)) = imports.iter().find(|&&(v, _)| v == u) {
            out.push(message(&[(u, u, line)]));
        }
        // `u` is the first unit by path of its component, of two units or more.
        let comp: Vec<&String> = units
            .iter()
            .filter(|v| reaches(u, v) && reaches(v, u))
            .collect();
        if comp.len() < 2 || comp[0] != u {
            continue;
        }
        // Every simple cycle through `u`, each as its steps and the index of each import.
        type Steps<'a> = Vec<(&'a str, &'a str, usize)>;
        let mut best: Option<(usize, Vec<usize>, Steps)> = None;
        let mut stack: Vec<(&str, Vec<usize>, Steps)> = vec![(u.as_str(), Vec::new(), Vec::new())];
        while let Some((x, idx, steps)) = stack.pop() {
            for (k, &(v, line)) in graph[x].iter().enumerate() {
                if v == x || !comp.iter().any(|c| *c == v) {
                    continue;
                }
                let (mut idx, mut steps) = (idx.clone(), steps.clone());
                idx.push(k);
                steps.push((x, v, line));
                if v == u {
                    let key = (steps.len(), idx);
                    if best.as_ref().is_none_or(|b| key < (b.0, b.1.clone())) {
                        best = Some((key.0, key.1, steps));
                    }
                } else if !steps.iter().any(|&(f, _, _)| f == v) {
                    stack.push((v, idx, steps));
                }
            }
        }
        out.push(message(
            &best.expect("a component has a cycle through each unit").2,
        ));
    }
    out.sort();
    out
}

/// 100 packages from a new seed each run; `ZED_TEST_SEED` repeats one.
#[test]
fn random_packages_report_the_same_cycles_for_every_order_of_the_roots_and_each_unit_alone() {
    let first = zed_tests::seed::seed(
        "random_packages_report_the_same_cycles_for_every_order_of_the_roots_and_each_unit_alone",
    );
    for seed in (0..100).map(|i| first.wrapping_add(i)) {
        let (fs, roots, prelude, graph) = generate(seed);
        let refs: Vec<(&str, &str)> = fs.iter().map(|(f, t)| (f.as_str(), t.as_str())).collect();
        let files = files(&refs);
        let report = |roots: &[&str]| {
            let p = load(&mut Db::new(), &files, roots);
            let order: Vec<String> = p
                .order
                .iter()
                .map(|&i| p.units[i].path.to_string())
                .collect();
            (p.report(Path::new("")), order)
        };
        let all = orders(&roots);
        let (batch, order) = report(&all[0]);
        for o in &all[1..] {
            assert_eq!(
                report(o),
                (batch.clone(), order.clone()),
                "seed {seed}: roots {o:?}"
            );
        }
        // The problems in order of their files.
        let files_of: Vec<&str> = batch.iter().map(|l| l.split(':').next().unwrap()).collect();
        assert!(files_of.is_sorted(), "seed {seed}: {batch:?}");
        // The cycles reported are those the brute force finds.
        let mut from = roots.clone();
        from.extend(prelude);
        let reached = reach(&graph, &from);
        let mut cycles: Vec<String> = batch
            .iter()
            .filter(|l| l.contains("the imports form a cycle"))
            .cloned()
            .collect();
        cycles.sort();
        assert_eq!(
            cycles,
            expected_cycles(&graph, &reached),
            "seed {seed}: {fs:?}"
        );
        // Each unit with a file checked alone gives the batch's problems of the units it reaches.
        for u in reached
            .iter()
            .filter(|u| fs.iter().any(|(f, _)| *f == file_of(u)))
        {
            let mut from = vec![u.as_str()];
            from.extend(prelude);
            assert_eq!(
                report(&[u]).0,
                restricted(&batch, &reach(&graph, &from), u),
                "seed {seed}: the unit `{u}` alone, against roots {roots:?}: {fs:?}"
            );
        }
    }
}

#[test]
fn a_cycle_beside_a_unit_that_does_not_parse_and_a_root_with_no_file_is_reported_the_same() {
    let fs = [
        (
            "orders.zed",
            "import stock.{reserve};\nplace(n) = reserve(n);\n",
        ),
        (
            "stock.zed",
            "import orders.{place};\nimport draft.{x};\nreserve(n) = n;\n",
        ),
        ("draft.zed", "x = ;\n"),
    ];
    let roots = ["stock", "draft", "missing", "orders"];
    let m = every_order(&fs, &roots);
    let cycle = "orders.zed:1:1: the unit `stock` cannot be imported: the imports form a cycle, \
                 so its units have no order to be resolved in: `orders` imports `stock` at \
                 orders.zed:1:1, `stock` imports `orders` at stock.zed:1:1.";
    let files_of: Vec<&str> = m.iter().map(|l| l.split(':').next().unwrap()).collect();
    assert_eq!(
        files_of,
        ["draft.zed", "missing.zed", "orders.zed"],
        "{m:?}"
    );
    assert_eq!(
        m[1],
        "missing.zed: there is no unit `missing`: no file `missing.zed` under the root"
    );
    assert_eq!(m[2], cycle);
    // Either unit of the cycle alone: the cycle and `draft`'s own error; the import of `draft`,
    // which does not parse, is given no error (L1.29d).
    let files = files(&fs);
    for r in ["orders", "stock"] {
        let alone = mistakes(&load(&mut Db::new(), &files, &[r]));
        assert_eq!(alone, [&*m[0], &m[2]], "the unit `{r}` alone");
    }
}

#[test]
fn a_cycle_that_imports_another_cycle_is_reported_once_with_it_from_every_unit() {
    // `billing` and `accounts` import each other, and `accounts` imports `ledger`, which with
    // `audit` is a second cycle: each component once, each from its first unit by path.
    let fs = [
        ("billing.zed", "import accounts.{owner};\nbill = 1;\n"),
        (
            "accounts.zed",
            "import billing.{bill};\nimport ledger.{post};\nowner = post;\n",
        ),
        ("ledger.zed", "import audit.{check};\npost = 2;\n"),
        ("audit.zed", "import ledger.{post};\ncheck = post;\n"),
    ];
    let roots = ["billing", "accounts", "ledger", "audit"];
    let m = every_order(&fs, &roots);
    assert_eq!(
        m,
        [
            "accounts.zed:1:1: the unit `billing` cannot be imported: the imports form a cycle, \
             so its units have no order to be resolved in: `accounts` imports `billing` at \
             accounts.zed:1:1, `billing` imports `accounts` at billing.zed:1:1.",
            "audit.zed:1:1: the unit `ledger` cannot be imported: the imports form a cycle, so \
             its units have no order to be resolved in: `audit` imports `ledger` at \
             audit.zed:1:1, `ledger` imports `audit` at ledger.zed:1:1.",
        ]
    );
    // The importing cycle's units reach both; the imported cycle's units only their own.
    let files = files(&fs);
    for (r, want) in [
        ("billing", &m[..]),
        ("accounts", &m[..]),
        ("ledger", &m[1..]),
        ("audit", &m[1..]),
    ] {
        assert_eq!(
            mistakes(&load(&mut Db::new(), &files, &[r])),
            want,
            "`{r}` alone"
        );
    }
    // The imported cycle is put first, each component's units in order of their paths.
    let p = load(&mut Db::new(), &files, &["billing"]);
    let order: Vec<&str> = p.order.iter().map(|&i| &*p.units[i].path).collect();
    assert_eq!(order, ["audit", "ledger", "accounts", "billing"]);
}

#[test]
fn of_two_shortest_cycles_that_share_their_first_import_the_next_import_in_the_text_decides() {
    // `app` imports `core`, and `core` imports `db` before `cache`; each imports `app`. Both
    // cycles through `app` take three imports and begin with the same one: the one through
    // `db`, which `core` imports first, is reported, though `cache` comes first by path.
    let fs = [
        ("app.zed", "import core.{run};\nname = 0;\n"),
        (
            "core.zed",
            "import db.{rows};\nimport cache.{hit};\nrun = 1;\n",
        ),
        ("cache.zed", "import app.{name};\nhit = 2;\n"),
        ("db.zed", "import app.{name};\nrows = 3;\n"),
    ];
    let roots = ["app", "core", "cache", "db"];
    let m = every_order(&fs, &roots);
    assert_eq!(
        m,
        [
            "app.zed:1:1: the unit `core` cannot be imported: the imports form a cycle, so its \
             units have no order to be resolved in: `app` imports `core` at app.zed:1:1, `core` \
             imports `db` at core.zed:1:1, `db` imports `app` at db.zed:1:1."
        ]
    );
    each_alone_agrees(&fs, &roots, &m);
}

#[test]
fn a_shorter_cycle_wins_over_one_whose_imports_come_first() {
    // `app` imports `menu` first, whose cycle back takes three imports, and `tabs` second,
    // whose cycle takes two: the shorter is reported, at `app`'s second import.
    let fs = [
        (
            "app.zed",
            "import menu.{items};\nimport tabs.{open};\nname = 0;\n",
        ),
        ("menu.zed", "import pane.{draw};\nitems = 1;\n"),
        ("tabs.zed", "import app.{name};\nopen = 2;\n"),
        ("pane.zed", "import app.{name};\ndraw = 3;\n"),
    ];
    let roots = ["app", "menu", "tabs", "pane"];
    let m = every_order(&fs, &roots);
    assert_eq!(
        m,
        [
            "app.zed:2:1: the unit `tabs` cannot be imported: the imports form a cycle, so its \
             units have no order to be resolved in: `app` imports `tabs` at app.zed:2:1, `tabs` \
             imports `app` at tabs.zed:1:1."
        ]
    );
    each_alone_agrees(&fs, &roots, &m);
}

#[test]
fn names_brought_in_on_a_cycle_are_bound_and_other_imports_are_still_checked() {
    // `stock` imports from `orders` on the cycle, a name `orders` does not define among them,
    // which is not reported, as the cycle is; but its import from `tax`, off the cycle, of a
    // name `tax` does not define is, and so is the import from `stock` by `report`, outside
    // the cycle, of a name `stock` does not define; and a use of a name never brought in.
    let fs = [
        (
            "orders.zed",
            "import stock.{reserve};\nplace(n) = reserve(n);\n",
        ),
        (
            "stock.zed",
            "import orders.{place, ghost};\nimport tax.{rate, levy};\nreserve(n) = place(ghost(n)) + rate;\n",
        ),
        ("tax.zed", "rate = 1;\n"),
        (
            "report.zed",
            "import stock.{reserve, refund};\nshown = reserve(1) + missing;\n",
        ),
    ];
    let m = every_order(&fs, &["report", "orders"]);
    assert_eq!(m.len(), 4, "{m:?}");
    assert!(
        m[0].starts_with(
            "orders.zed:1:1: the unit `stock` cannot be imported: the imports form a cycle"
        ),
        "{m:?}"
    );
    assert!(
        m[1].starts_with("report.zed:1:1: the unit `stock` defines no `refund`"),
        "{m:?}"
    );
    assert_eq!(m[2], "report.zed:2:22: `missing` is not defined.");
    assert!(
        m[3].starts_with("stock.zed:2:1: the unit `tax` defines no `levy`"),
        "{m:?}"
    );
}
