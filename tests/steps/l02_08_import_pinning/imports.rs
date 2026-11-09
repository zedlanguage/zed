//! Pins in import statements: written where an import has none, checked where it has one,
//! each import of a unit pinned to the same address, and the address a function of the unit's
//! exports alone.

use zed_tests::is_not_yet;
use zedc::format::format_source;
use zedc::query::{Db, Query};
use zedc::unit::load;

use super::{files, mistakes, package, pin_in};

/// A unit that prices goods, as the shop's units import it.
const PRICING: &str = "net(g: f64) = g / 1.2;\ngross(n: f64) = n * 1.2;\n";

/// The unit `main` that imports `pricing` by `import`, written as `stmt`.
fn main_with(stmt: &str) -> String {
    format!("{stmt}\nmain() -> (stdout: Lines) {{}}\n")
}

/// The pin the build writes into `import pricing;` with `pricing` as `text`.
fn pin_of(text: &str) -> String {
    let p = package(&[
        ("main.zed", &main_with("import pricing;")),
        ("pricing.zed", text),
    ]);
    pin_in(&p.pinned("main").expect("the import is pinned"), 0)
}

#[test]
fn an_unpinned_import_gets_the_address_of_the_unit_it_names() {
    let main = main_with("import pricing;");
    let p = package(&[("main.zed", &main), ("pricing.zed", PRICING)]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    let pinned = p.pinned("main").unwrap();
    let h = pin_in(&pinned, 0);
    assert_eq!(
        pinned,
        main_with(&format!("import pricing @hash(\"{h}\");"))
    );
    // The imported unit imports nothing, so nothing is written into it, and the package has no
    // prelude unit, so no pin file is written.
    assert_eq!(p.pinned("pricing"), None);
    assert_eq!(p.writes.pin_file, None);
}

#[test]
fn a_pinned_import_that_matches_is_checked_and_nothing_is_written() {
    let pinned = package(&[
        ("main.zed", &main_with("import pricing;")),
        ("pricing.zed", PRICING),
    ])
    .pinned("main")
    .unwrap();
    let p = package(&[("main.zed", &pinned), ("pricing.zed", PRICING)]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert!(p.writes.units.is_empty(), "{:?}", p.writes);
    assert_eq!(p.pinned("main"), None);
}

#[test]
fn the_address_follows_the_exports_and_nothing_else() {
    let h = pin_of(PRICING);
    // A comment, the layout, and the names of parameters are not part of the address.
    assert_eq!(pin_of(&format!("// the shop's rates\n{PRICING}")), h);
    assert_eq!(
        pin_of("net(g: f64) =\n    g / 1.2;\n\ngross(n: f64) = n * 1.2;\n"),
        h
    );
    assert_eq!(
        pin_of("net(x: f64) = x / 1.2;\ngross(n: f64) = n * 1.2;\n"),
        h
    );
    // (A `local` declaration is not compiled before a later step, so the case of one that no
    // export uses waits for it.)
    // A changed body, a new export or a removed one is.
    assert_ne!(
        pin_of("net(g: f64) = g / 1.25;\ngross(n: f64) = n * 1.2;\n"),
        h
    );
    assert_ne!(pin_of(&format!("{PRICING}tax(n: f64) = n * 0.2;\n")), h);
    assert_ne!(pin_of("net(g: f64) = g / 1.2;\n"), h);
    // The unit's path is not part of it: the same text at another path has the same address.
    let p = package(&[
        ("main.zed", &main_with("import shop.rates;")),
        ("shop/rates.zed", PRICING),
    ]);
    assert_eq!(pin_in(&p.pinned("main").unwrap(), 0), h);
}

#[test]
fn a_changed_unit_makes_its_pin_stale_and_the_build_stops_with_two_repairs() {
    let pinned = package(&[
        ("main.zed", &main_with("import pricing;")),
        ("pricing.zed", PRICING),
    ])
    .pinned("main")
    .unwrap();
    let old = pin_in(&pinned, 0);
    let changed = "net(g: f64) = g / 1.25;\ngross(n: f64) = n * 1.25;\n";
    let p = package(&[("main.zed", &pinned), ("pricing.zed", changed)]);
    let new = pin_of(changed);
    assert_eq!(
        mistakes(&p),
        vec![format!(
            "main.zed:1:1: the import of the unit `pricing` is pinned to the content address \
             {old}, and the unit now has the address {new}: its exports, or a declaration they \
             use, changed in `pricing.zed` after the pin was written. A pinned import is \
             checked and never resolved again, so the build stops here. Repairs: to build with \
             the unit as it is now, remove the pin, as `import pricing;`, and the next build \
             writes the new address; or, to build with the unit as it was pinned, restore \
             `pricing.zed` to that version."
        )]
    );
    // The stale pin is left as it is written.
    assert!(p.writes.units.is_empty(), "{:?}", p.writes);
    // The first repair: with the pin removed, the build writes the new address and stops at
    // nothing.
    let p = package(&[
        ("main.zed", &main_with("import pricing;")),
        ("pricing.zed", changed),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(pin_in(&p.pinned("main").unwrap(), 0), new);
}

#[test]
fn a_comment_only_change_keeps_the_pin() {
    let pinned = package(&[
        ("main.zed", &main_with("import pricing;")),
        ("pricing.zed", PRICING),
    ])
    .pinned("main")
    .unwrap();
    let commented = format!("// rates of 2026\n{PRICING}// end\n");
    let p = package(&[("main.zed", &pinned), ("pricing.zed", &commented)]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert!(p.writes.units.is_empty());
}

#[test]
fn selective_aliased_and_nested_imports_are_pinned_where_each_is_written() {
    let main = "import pricing.{net};\n\
                import pricing as p;\n\
                total(g: f64) = {\n  import pricing.{gross};\n  gross(net(g)) + p.net(g)\n};\n\
                main() -> (stdout: Lines) {}\n";
    let p = package(&[("main.zed", main), ("pricing.zed", PRICING)]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    let pinned = p.pinned("main").unwrap();
    let h = pin_in(&pinned, 0);
    assert_eq!(
        pinned,
        main.replace(
            "import pricing.{net};",
            &format!("import pricing.{{net}} @hash(\"{h}\");")
        )
        .replace(
            "import pricing as p;",
            &format!("import pricing as p @hash(\"{h}\");")
        )
        .replace(
            "import pricing.{gross};",
            &format!("import pricing.{{gross}} @hash(\"{h}\");")
        )
    );
    // The writes of one unit are in text order, one per import that had no pin.
    let at: Vec<usize> = p.writes.units[0].1.iter().map(|(_, e)| e.at).collect();
    assert_eq!(at.len(), 3);
    assert!(at.windows(2).all(|w| w[0] < w[1]), "{at:?}");
}

#[test]
fn only_the_imports_with_no_pin_are_written() {
    let h = pin_of(PRICING);
    let main = format!(
        "import pricing.{{net}} @hash(\"{h}\");\nimport pricing.{{gross}};\nmain() -> (stdout: Lines) {{}}\n"
    );
    let p = package(&[("main.zed", &main), ("pricing.zed", PRICING)]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(
        p.pinned("main").unwrap(),
        main.replace(
            "import pricing.{gross};",
            &format!("import pricing.{{gross}} @hash(\"{h}\");")
        )
    );
}

#[test]
fn a_comment_before_the_semicolon_stays_after_the_pin() {
    let main = main_with("import pricing // for the till\n;");
    let p = package(&[("main.zed", &main), ("pricing.zed", PRICING)]);
    let pinned = p.pinned("main").unwrap();
    let h = pin_in(&pinned, 0);
    assert_eq!(
        pinned,
        main_with(&format!("import pricing @hash(\"{h}\") // for the till\n;"))
    );
}

#[test]
fn the_formatter_leaves_a_pinned_unit_as_the_build_wrote_it() {
    let main = "import pricing.{net, gross};\n\nmain() -> (stdout: Lines) { }\n";
    assert_eq!(format_source(main.as_bytes()).unwrap(), main);
    let pinned = package(&[("main.zed", main), ("pricing.zed", PRICING)])
        .pinned("main")
        .unwrap();
    assert_eq!(format_source(pinned.as_bytes()).unwrap(), pinned);
}

#[test]
fn a_unit_that_does_not_compile_alone_is_neither_pinned_nor_checked() {
    // `pricing` imports `rates`, so until step L2.4 links units it has no address of its own:
    // `main`'s import of it is not pinned, and a pin written on it is not checked.
    let rates = "rate = 1.2;\n";
    let pricing = "import rates.{rate};\nnet(g: f64) = g / rate;\n";
    let p = package(&[
        ("main.zed", &main_with("import pricing;")),
        ("pricing.zed", pricing),
        ("rates.zed", rates),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(p.pinned("main"), None);
    let pinned = p.pinned("pricing").unwrap();
    pin_in(&pinned, 0);
    let wrong = format!("import pricing @hash(\"{}\");", "0".repeat(64));
    let p = package(&[
        ("main.zed", &main_with(&wrong)),
        ("pricing.zed", &pinned),
        ("rates.zed", rates),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert!(p.writes.units.is_empty(), "{:?}", p.writes);
}

#[test]
fn an_import_of_a_unit_that_is_not_there_or_does_not_parse_is_not_pinned() {
    let p = package(&[("main.zed", &main_with("import pricing;"))]);
    assert!(!mistakes(&p).is_empty());
    assert!(p.writes.units.is_empty());
    let p = package(&[
        ("main.zed", &main_with("import pricing;")),
        ("pricing.zed", "net(g: f64) = ;\n"),
    ]);
    assert!(!mistakes(&p).is_empty());
    assert!(p.writes.units.is_empty());
}

#[test]
fn many_importers_of_one_unit_address_it_once() {
    let fs = files(&[
        (
            "main.zed",
            "import a;\nimport b;\nimport pricing;\nmain() -> (stdout: Lines) {}\n",
        ),
        ("a.zed", "import pricing.{net};\nx = net(1.0);\n"),
        ("b.zed", "import pricing.{gross};\ny = gross(1.0);\n"),
        ("pricing.zed", PRICING),
    ]);
    let mut db = Db::new();
    let p = load(&mut db, &fs, &["main"]);
    assert!(mistakes(&p).is_empty(), "{:?}", mistakes(&p));
    // `a`, `b` and `pricing` are each addressed once, though `pricing` is imported three times.
    assert_eq!(db.computed(Query::Address), 3);
    let h = pin_in(&p.pinned("a").unwrap(), 0);
    assert_eq!(pin_in(&p.pinned("b").unwrap(), 0), h);
    assert_eq!(pin_in(&p.pinned("main").unwrap(), 0), h);
    // A second load in the same database addresses nothing again.
    load(&mut db, &fs, &["main"]);
    assert_eq!(db.computed(Query::Address), 3);
}

#[test]
fn the_pins_of_a_package_do_not_depend_on_its_roots() {
    let fs = files(&[
        (
            "main.zed",
            "import pricing;\nmain() -> (stdout: Lines) {}\n",
        ),
        ("till.zed", "import pricing.{net};\nsale = net(10.0);\n"),
        ("pricing.zed", PRICING),
    ]);
    let both = load(&mut Db::new(), &fs, &["main", "till"]);
    let reversed = load(&mut Db::new(), &fs, &["till", "main"]);
    let main = load(&mut Db::new(), &fs, &["main"]);
    let till = load(&mut Db::new(), &fs, &["till"]);
    for unit in ["main", "till"] {
        let alone = if unit == "main" { &main } else { &till };
        assert_eq!(both.pinned(unit), alone.pinned(unit), "{unit}");
        assert_eq!(reversed.pinned(unit), alone.pinned(unit), "{unit}");
    }
    assert!(
        both.report(std::path::Path::new(""))
            .iter()
            .all(|m| is_not_yet(m))
    );
}
