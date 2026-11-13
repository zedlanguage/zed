//! An executable reading n files named by its n arguments does work linear in n: its start
//! decodes and plans the program once, and each read is one call through `Files`.

use std::ffi::OsString;

use zed_tests::scaling::{self, FACTOR};

use super::{built, dir, executable};

/// A program that reads the file each of its first `n` arguments names, and writes what each
/// holds on one line, joined by `|`.
fn reader(n: usize) -> String {
    let mut src = "main(m: MainArgs) {\nfs = main::files;\n".to_string();
    for k in 1..=n {
        src += &format!(
            "  r{k} = (fs[m.args[{}] else \"\"] else #notFound -> \"missing\") \
             else #ioError -> \"unreadable\";\n",
            k - 1
        );
    }
    let holes: Vec<String> = (1..=n).map(|k| format!("${{r{k}}}")).collect();
    src + &format!("  m.stdout <- \"{}\";\n}}\n", holes.join("|"))
}

#[test]
fn an_executable_reading_n_files_scales() {
    let d = dir("scaling");
    let n = 200;
    // The programs, their executables, the files and the words of both sizes are made before
    // the runs are measured.
    let words = |m: usize| -> Vec<OsString> {
        let src = d.join(format!("reader{m}.zed"));
        std::fs::write(&src, reader(m)).unwrap();
        built(&src, &d.join(format!("reader{m}")));
        let mut w: Vec<OsString> = vec!["--".into()];
        for i in 0..m {
            let f = d.join(format!("file{i}.txt"));
            std::fs::write(&f, format!("{i:05}")).unwrap();
            w.push(f.into());
        }
        w
    };
    let (small, large) = (words(n), words(FACTOR * n));
    scaling::check("an executable reading n files", n, |m| {
        let w = if m == n { &small } else { &large };
        let ran = executable(&d.join(format!("reader{m}")), w, b"");
        assert_eq!(ran.status, 0, "{}", ran.stderr);
        // Each file holds five digits, and a `|` or the last `\n` follows each.
        assert_eq!(ran.stdout.len(), 6 * m);
    });
}
