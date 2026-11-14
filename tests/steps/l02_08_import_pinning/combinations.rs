//! Completeness of step L2.8 (plan row TEST-complete-ports, COMPLETENESS.md beside this file):
//! a pin that is not an address, a stale pin beside an unpinned import, and a stale pin in a
//! nested scope.

use super::{mistakes, package, pin_in};

const PRICING: &str = "net(g: f64) = g / 1.2;\ngross(n: f64) = n * 1.2;\n";
const RATES: &str = "rate(x: f64) = x * 0.2;\n";

/// The address the build writes for `pricing` as `PRICING`.
fn pricing_pin() -> String {
    let p = package(&[
        ("main.zed", "import pricing;\nmain(m: MainArgs) {}\n"),
        ("pricing.zed", PRICING),
    ]);
    pin_in(&p.pinned("main").unwrap(), 0)
}

#[test]
fn a_pin_that_is_no_address_of_the_unit_stops_the_build_and_is_left_as_written() {
    // DESIGN.md sec:units: a pinned import is checked, never resolved again, and a pin that
    // does not match the unit it names stops the build. Text that is no address at all
    // matches no unit.
    let h = pricing_pin();
    for pin in [
        "0".repeat(64),
        h[..63].to_string(),
        format!("{h}0"),
        h.to_uppercase(),
        String::new(),
    ] {
        let main = format!("import pricing @hash(\"{pin}\");\nmain(m: MainArgs) {{}}\n");
        let p = package(&[("main.zed", &main), ("pricing.zed", PRICING)]);
        assert!(!mistakes(&p).is_empty(), "{pin:?} was accepted");
        assert!(p.writes.units.is_empty(), "{pin:?}: {:?}", p.writes);
    }
}

#[test]
fn a_stale_pin_does_not_keep_another_import_from_being_pinned() {
    // DESIGN.md sec:units: the build writes its pins whether or not it stops for another
    // problem.
    let stale = format!("import pricing @hash(\"{}\");", "0".repeat(64));
    let main = format!("{stale}\nimport rates;\nmain(m: MainArgs) {{}}\n");
    let p = package(&[
        ("main.zed", &main),
        ("pricing.zed", PRICING),
        ("rates.zed", RATES),
    ]);
    let report = mistakes(&p);
    assert_eq!(report.len(), 1, "{report:?}");
    assert!(report[0].starts_with("main.zed:1:1: "), "{report:?}");
    let pinned = p.pinned("main").expect("the unpinned import is pinned");
    let r = pin_in(&pinned, 1);
    assert_eq!(
        pinned,
        main.replace("import rates;", &format!("import rates @hash(\"{r}\");"))
    );
}

#[test]
fn a_stale_pin_in_a_nested_scope_is_reported_at_its_import() {
    let main = format!(
        "total(g: f64) = {{\n  import pricing.{{net}} @hash(\"{}\");\n  net(g)\n}};\n\
         main(m: MainArgs) {{}}\n",
        "0".repeat(64)
    );
    let p = package(&[("main.zed", &main), ("pricing.zed", PRICING)]);
    let report = mistakes(&p);
    assert_eq!(report.len(), 1, "{report:?}");
    assert!(report[0].starts_with("main.zed:2:3: "), "{report:?}");
    assert!(p.writes.units.is_empty(), "{:?}", p.writes);
}

#[test]
fn the_pin_file_is_made_when_missing_and_never_written_over_a_change() {
    // `pin::write_file` makes the file when the build found none, and refuses when the file
    // is not as the build read it (it appeared, changed or went away), so the build never
    // writes over an edit made while it ran. The file's name is new in each process, so the
    // case of a missing file runs on every run, not only on a fresh build directory.
    use zedc::pin::write_file;
    let d = zed_tests::step_helpers::scratch("l02_08_pins");
    std::fs::create_dir_all(&d).unwrap();
    let file = d.join(format!("made-{}.pins", std::process::id()));
    let changed = Err("the file changed while zedc was reading it; build again".to_string());
    assert_eq!(write_file(&file, None, "a\n"), Ok(()));
    assert_eq!(std::fs::read_to_string(&file).unwrap(), "a\n");
    assert_eq!(write_file(&file, None, "b\n"), changed, "it appeared");
    assert_eq!(write_file(&file, Some("x\n"), "b\n"), changed, "it changed");
    assert_eq!(write_file(&file, Some("a\n"), "c\n"), Ok(()));
    assert_eq!(std::fs::read_to_string(&file).unwrap(), "c\n");
    std::fs::remove_file(&file).unwrap();
    assert_eq!(
        write_file(&file, Some("c\n"), "d\n"),
        changed,
        "it went away"
    );
    assert!(!file.exists());
}
