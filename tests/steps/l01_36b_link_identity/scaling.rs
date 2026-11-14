//! The identity of a toolchain costs the same for every build: two runs of the driver, which
//! do no work, and one hash of the runtime library. Only the object file's hash grows with
//! the program, linearly (`bench.rs`).

use std::path::Path;

use zed_native::link::Toolchain;

use super::{Link, dir, link, script, toolchain};

/// A program of `n` lines of a price list, each a definition the output uses.
fn price_list(n: usize) -> String {
    let mut src = "main(m: MainArgs) {\n".to_string();
    for k in 1..=n {
        src += &format!("  p{k} = {k} * 3;\n");
    }
    let items: Vec<String> = (1..=n).map(|k| format!("${{p{k}}}")).collect();
    src + &format!("  m.stdout <- \"{}\";\n}}\n", items.join(" "))
}

/// The first word of each run of the driver logged in `log`, which a build makes empty.
fn runs(log: &Path) -> Vec<String> {
    let words = std::fs::read_to_string(log).unwrap_or_default();
    std::fs::write(log, "").unwrap();
    words.lines().map(str::to_string).collect()
}

/// Builds a price list of each size in `sizes` twice, in the directory of test `name`, with a
/// driver that logs its runs: each build runs the driver for its two reports and no more, and
/// a build that links runs it once more, to link.
pub(super) fn builds_run_the_driver_the_same_times(name: &str, sizes: &[usize]) {
    let d = dir(name);
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
    for &m in sizes {
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
fn a_build_runs_the_driver_for_its_reports_and_its_link() {
    builds_run_the_driver_the_same_times("driver_runs", &[3]);
}
