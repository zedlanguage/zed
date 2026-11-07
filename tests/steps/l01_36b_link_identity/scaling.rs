//! The identity of a toolchain costs the same for every build: two runs of the driver, which
//! do no work, and one hash of the runtime library. Only the object file's hash grows with
//! the program, linearly.

use std::path::Path;

use zed_native::link::Toolchain;
use zed_tests::scaling::{self, FACTOR};

use super::{Link, dir, link, script, toolchain};

/// A program of `n` lines of a price list, each a definition the output uses.
fn price_list(n: usize) -> String {
    let mut src = "main() -> (stdout: Lines) {\n".to_string();
    for k in 1..=n {
        src += &format!("  p{k} = {k} * 3;\n");
    }
    let items: Vec<String> = (1..=n).map(|k| format!("${{p{k}}}")).collect();
    src + &format!("  stdout <- \"{}\";\n}}\n", items.join(" "))
}

/// The first word of each run of the driver logged in `log`, which a build makes empty.
fn runs(log: &Path) -> Vec<String> {
    let words = std::fs::read_to_string(log).unwrap_or_default();
    std::fs::write(log, "").unwrap();
    words.lines().map(str::to_string).collect()
}

#[test]
fn a_build_runs_the_driver_the_same_times_at_every_size() {
    let d = dir("scaling");
    let log = d.join("driver.log");
    let logging = d.join("cc-logging");
    script(
        &logging,
        &format!(
            "printf '%s\\n' \"$1\" >> '{}'\nexec cc \"$@\"\n",
            log.display()
        ),
    );
    let tools = Toolchain {
        linker: logging.into(),
        ..toolchain()
    };
    runs(&log);
    let n = 40;
    for m in [n, FACTOR * n] {
        let src = d.join(format!("prices{m}.zed"));
        std::fs::write(&src, price_list(m)).unwrap();
        let out = d.join(format!("prices{m}"));
        // The first build links, or keeps an output of the run before; the second keeps it.
        let first = link(&src, &out, &tools);
        let identity = ["--version", "-Wl,--version"];
        let expect = |l: Link| -> Vec<&str> {
            match l {
                Link::Ran => [&identity[..], &["-o"]].concat(),
                Link::Kept => identity.to_vec(),
            }
        };
        assert_eq!(runs(&log), expect(first), "the first build at size {m}");
        assert_eq!(link(&src, &out, &tools), Link::Kept);
        assert_eq!(
            runs(&log),
            expect(Link::Kept),
            "the second build at size {m}"
        );
    }
}

#[test]
fn the_key_of_an_object_file_scales() {
    // Only the hash of the object file grows with the program; it allocates nothing.
    let n = 1 << 20;
    let tools = zed_native::link::Identity::of(&toolchain()).unwrap();
    let (small, large) = (vec![7u8; n], vec![7u8; FACTOR * n]);
    scaling::check_instructions_only("the key of an object file of n bytes", n, 1, |m| {
        let object = if m == n { &small } else { &large };
        std::hint::black_box(tools.key(object, &[]));
    });
}
