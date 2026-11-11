//! The pin file is the toolchain's: a line that is no pin, or a second pin of one kind and key,
//! is reported at its line, and the file is then neither checked nor written.

use zedc::pin::{PIN_FILE, Pins};

use super::{mistakes, package};

/// A package with prelude unit `std` and the pin file `pins`.
fn with_pins(pins: &str) -> zedc::unit::Package {
    package(&[
        ("zed.manifest", "prelude = \"std\";\n"),
        (PIN_FILE, pins),
        ("main.zed", "main(m: MainArgs) {}\n"),
        ("std.zed", "double(x: f64) = x * 2.0;\n"),
    ])
}

#[test]
fn a_line_that_is_no_pin_is_reported_at_its_line() {
    let zeros = "0".repeat(64);
    for line in [
        "prelude std".to_string(),
        format!("prelude {} std", "0".repeat(63)),
        format!("prelude {} std", "0".repeat(63) + "G"),
        format!("Prelude {zeros} std"),
        format!("prelude  {zeros} std"),
        format!("prelude {zeros} "),
    ] {
        let p = with_pins(&format!("// pins\n{line}\n"));
        assert_eq!(
            mistakes(&p),
            vec![format!(
                "zed.pins:2:1: this line of the pin file `zed.pins` is not a pin. A pin is \
                 written as its kind, its content address of 64 lowercase hex digits and its \
                 key, with one space between them, as `prelude {zeros} std.prelude`. zedc \
                 writes this file: delete the line, and the next build writes the pin again."
            )],
            "{line:?}"
        );
        assert_eq!(p.writes.pin_file, None, "{line:?}");
    }
}

#[test]
fn a_kind_and_key_pinned_twice_is_reported_at_the_second_line() {
    let (a, b) = ("1".repeat(64), "2".repeat(64));
    let p = with_pins(&format!("prelude {a} std\nprelude {b} std\n"));
    let report = mistakes(&p);
    assert_eq!(report.len(), 1, "{report:?}");
    assert!(
        report[0].starts_with(
            "zed.pins:2:1: the pin file `zed.pins` pins the prelude `std` twice, and it holds \
             one pin for each. Delete both lines, and the next build writes the pin again."
        ),
        "{report:?}"
    );
    assert!(
        report[0].contains("the prelude `std` is first pinned here"),
        "{report:?}"
    );
    assert_eq!(p.writes.pin_file, None);
}

#[test]
fn a_pin_file_round_trips_in_a_fixed_order() {
    let (a, b) = ("1".repeat(64), "2".repeat(64));
    let text = format!("proof {b} a key with spaces\nprelude {a} std\n");
    let pins = Pins::parse(&text).unwrap();
    assert_eq!(pins.len(), 2);
    let written = pins.text();
    assert!(written.ends_with(&format!("prelude {a} std\nproof {b} a key with spaces\n")));
    assert_eq!(Pins::parse(&written).unwrap(), pins);
    assert_eq!(Pins::parse(&written).unwrap().text(), written);
}
