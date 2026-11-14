//! Executables at the rule of low complexity (DESIGN.md Part G): the benchmarks of this step,
//! run by `tools/run_tests.sh --bench` and left out of its default run. Each check they make
//! besides the ratio is made at a small size by the correctness test named in its doc.

use std::ffi::OsString;
use std::path::PathBuf;

use zed_native::link::{build_id, runtime_of};
use zed_tests::scaling::{self, FACTOR};
use zedc::zir::lower::lower_sited;

use super::runtime::{library, object_file, of_other_flags};
use super::sites::chain;
use super::{built, dir, executable};

/// Finding the library reads the executable's section headers and each library's symbol
/// index once, and only the member that defines `BUILD`: linear in the symbols of the
/// executable and of the libraries' indexes.
///
/// Small instances: `runtime::a_library_built_with_other_compiler_flags_is_not_picked` and
/// `runtime::the_library_built_with_this_executable_is_picked_over_a_newer_one`.
#[test]
fn finding_the_library_scales() {
    let n = 200_000;
    let id = build_id(&std::env::current_exe().unwrap()).unwrap();
    // Each file of a size, made before the runs are measured: an object file of m symbols
    // holding the build, a library of another build and one of this build, each indexing
    // m - 1 other symbols before `BUILD`.
    let made = |m: usize| -> (PathBuf, PathBuf) {
        let d = dir(&format!("scaling{m}"));
        let symbols: Vec<Vec<u8>> = (1..m)
            .map(|i| format!("_RNvNtCs1b1S38cFQTP_10zed_native4link1f{i}").into_bytes())
            .collect();
        let exe = d.join("exe.o");
        std::fs::write(&exe, object_file(&symbols, Some(&id))).unwrap();
        std::fs::write(
            d.join("libzed_native-0.a"),
            library(&symbols, &of_other_flags(&id)),
        )
        .unwrap();
        std::fs::write(d.join("libzed_native-1.a"), library(&symbols, &id)).unwrap();
        (exe, d)
    };
    let (small, large) = (made(n), made(FACTOR * n));
    scaling::check("finding the runtime library among n symbols", n, |m| {
        let (exe, d) = if m == n { &small } else { &large };
        assert_eq!(runtime_of(exe, d), Ok(d.join("libzed_native-1.a")));
    });
}

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

/// An executable reading n files named by its n arguments does work linear in n: its start
/// decodes and plans the program once, and each read is one call through `Files`. Small
/// instance: `agreement.rs`'s `READER`, three files read, found, missing and unreadable, by the
/// executable and the interpreter.
#[test]
fn an_executable_reading_n_files_scales() {
    let d = dir("scaling");
    let n = 400;
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

/// Small instance: `sites::the_sites_change_neither_the_address_nor_the_zir_text`.
#[test]
fn lowering_with_sites_scales() {
    let n = 5_000;
    let programs = scaling::inputs(n, |m| zedc::run::load(chain(m, "    ").as_bytes()).unwrap());
    let terms = scaling::inputs(n, |m| programs[&m].term());
    scaling::check("lowering n joins with their sites", n, |m| {
        let (g, sites) = lower_sited(&terms[&m], Some(programs[&m].sites())).unwrap();
        assert!(
            sites.len() >= m && sites.len() < 4 * m + 50,
            "{}",
            sites.len()
        );
        drop(g);
    });
}

/// Small instance: `sites::the_sites_change_neither_the_address_nor_the_zir_text`.
#[test]
fn loading_with_sites_scales() {
    // Elaboration marks each node with its site once and the table is frozen in one walk.
    let n = 4_000;
    let sources = scaling::inputs(n, |m| chain(m, "    "));
    scaling::check("loading n joins, with their sites", n, |m| {
        let p = zedc::run::load(sources[&m].as_bytes()).unwrap();
        assert!(p.sites().len() >= m);
    });
}
