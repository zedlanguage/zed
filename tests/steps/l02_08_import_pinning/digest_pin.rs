//! The address of a unit whose exports' types hold function types is pinned
//! (TEST-param-digest-pinned): the digest of the names inside those types
//! (`zedc_types::ty::NameDigests`, ADDR-nested-param-names) depends on nothing of the process,
//! neither the addresses of the nodes it keys its memo by nor what was checked before, so the
//! address is the one written here, alone or in a batch. `crates/zed-native`'s test
//! `pins_binary` checks the same address from separate `zedc` processes.

use zedc::query::Db;
use zedc::unit::load;

use super::digest_program::{ADDRESS, BATCH_MAIN, OTHERS, SINGLE_MAIN, UNIT};
use super::{files, mistakes, pin_in};

/// The pin `u`'s import gets in the unit `importer` of the package `fs`, loaded through `db`
/// from `main`, which loads with no mistake.
fn pin_through(db: &mut Db, fs: &[(&str, &str)], importer: &str) -> String {
    let p = load(db, &files(fs), &["main"]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    let text = p.pinned(importer).expect("the import is pinned");
    let line = text.lines().find(|l| l.starts_with("import u "));
    pin_in(
        line.unwrap_or_else(|| panic!("no import of u in\n{text}")),
        0,
    )
}

/// The single-file package: `main` imports `u` alone.
fn single(unit: &str) -> Vec<(&'static str, String)> {
    vec![("main.zed", SINGLE_MAIN.into()), ("u.zed", unit.into())]
}

/// The batch package: `main` imports `a`, `b` and `u`, and `b` imports `u`.
fn batch() -> Vec<(&'static str, String)> {
    let mut fs = vec![("main.zed", BATCH_MAIN.into()), ("u.zed", UNIT.into())];
    fs.extend(OTHERS.iter().map(|&(n, t)| (n, t.to_string())));
    fs
}

/// The package `fs` with each text borrowed.
fn borrowed<'a>(fs: &'a [(&'static str, String)]) -> Vec<(&'static str, &'a str)> {
    fs.iter().map(|(n, t)| (*n, t.as_str())).collect()
}

#[test]
fn the_address_of_function_types_inside_exports_is_pinned() {
    let single = single(UNIT);
    assert_eq!(
        pin_through(&mut Db::new(), &borrowed(&single), "main"),
        ADDRESS
    );
}

/// In a batch, `u` is checked after `a` and beside `b`, in a database that has checked the
/// single-file package first: the address is the same for both importers.
#[test]
fn the_address_is_the_same_in_a_batch_and_alone() {
    let (single, batch) = (single(UNIT), batch());
    let mut db = Db::new();
    assert_eq!(pin_through(&mut db, &borrowed(&single), "main"), ADDRESS);
    assert_eq!(pin_through(&mut db, &borrowed(&batch), "main"), ADDRESS);
    assert_eq!(pin_through(&mut db, &borrowed(&batch), "b"), ADDRESS);
    // And in a fresh database, the batch first.
    assert_eq!(pin_through(&mut Db::new(), &borrowed(&batch), "b"), ADDRESS);
}

/// Each name the pinned address must keep does change it: a renamed parameter of a returned
/// function, of a parameter's function type, of a function in a tuple and of a function type
/// inside it, and of each member of the union. So the pin above covers each of these places.
#[test]
fn each_name_inside_the_pinned_unit_changes_its_address() {
    for (from, to) in [
        ("g(z: f64) = z * k", "g(zz: f64) = zz * k"),
        (
            "(x: f64) -> f64) = f(x: 1.0)",
            "(xx: f64) -> f64) = f(xx: 1.0)",
        ),
        ("g(a: f64) = a + s", "g(aa: f64) = aa + s"),
        ("(c: f64) -> f64) = b(c: s)", "(cc: f64) -> f64) = b(cc: s)"),
        ("g(v: f64) = v;", "g(vv: f64) = vv;"),
        ("h(w: f64) = w * 2.0", "h(ww: f64) = ww * 2.0"),
        ("j(y: f64) = y * 3.0", "j(yy: f64) = yy * 3.0"),
    ] {
        assert!(UNIT.contains(from), "{from}");
        let renamed = single(&UNIT.replace(from, to));
        assert_ne!(
            pin_through(&mut Db::new(), &borrowed(&renamed), "main"),
            ADDRESS,
            "{from} -> {to}"
        );
    }
}
