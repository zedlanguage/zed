//! Executables at the rule of low complexity (DESIGN.md Part G): the benchmarks of this step,
//! run by `tools/run_tests.sh --bench` and left out of its default run. Each check they make
//! besides the ratio is made at a small size by the correctness test named in its doc.

use std::ffi::OsString;
use std::path::PathBuf;

use zed_native::link::{build_id, runtime_of};
use zed_tests::scaling::{self, FACTOR};
use zedc::zir::lower::{lower_debug, lower_sited};

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
            "  r{k} = (fs[m.args[{}] else #outOfBounds -> \"\"] else #notFound -> \"missing\") \
             else #ioError -> \"unreadable\";\n",
            k - 1
        );
    }
    let holes: Vec<String> = (1..=n).map(|k| format!("${{r{k}}}")).collect();
    src + &format!("  m.stdout <- \"{}\";\n}}\n", holes.join("|"))
}

/// Building an executable reading n files named by its n arguments, and running it, does work
/// linear in n: the build compiles n reads, the start decodes and plans the program once, and
/// each read is one call through `Files`. Small instance: `agreement.rs`'s `READER`, three
/// files read, found, missing and unreadable, by the executable and the interpreter.
#[test]
fn an_executable_reading_n_files_scales() {
    let d = dir("scaling");
    let n = 200;
    // The measured run builds the executable (`link::build`: this process compiles, the linker
    // it starts links) and runs it. The run of the executable alone was the measure before,
    // and under DynamoRIO's zed_icount (the Colab VMs) that counted only this process's start
    // of it and its pipes, 145,484 and 915,752 instructions at 200 and 1600 (job dv52 of
    // b22-free2, 2026-11-26): the client never counts a child process
    // (tools/icount/zed_icount.c, "Threads", case 3), so neither the build nor the executable's
    // own work was measured there, and the linker's and the executable's are not now. Where perf
    // counts with `inherit` the ended children count too. `link::build` of the reader took
    // 5,888,951,454 and 36,561,376,157 instructions at 400 and 3200, 6.21 times, in 7.6 s and
    // 23.3 s on a Colab VM (job dv51), so the sizes are 200 and 1600. Each process makes only
    // the size it runs (`scaling::check_inputs`; FAIL-exe-reader-bench-first-phase).
    let words = |m: usize| -> (usize, Vec<OsString>) {
        std::fs::write(d.join(format!("reader{m}.zed")), reader(m)).unwrap();
        let mut w: Vec<OsString> = vec!["--".into()];
        for i in 0..m {
            let f = d.join(format!("file{i}.txt"));
            std::fs::write(&f, format!("{i:05}")).unwrap();
            w.push(f.into());
        }
        (m, w)
    };
    scaling::check_inputs(
        "building and running an executable reading n files",
        n,
        words,
        |(m, w)| {
            let m = *m;
            let exe = d.join(format!("reader{m}"));
            built(&d.join(format!("reader{m}.zed")), &exe);
            let ran = executable(&exe, w, b"");
            assert_eq!(ran.status, 0, "{}", ran.stderr);
            // Each file holds five digits, and a `|` or the last `\n` follows each.
            assert_eq!(ran.stdout.len(), 6 * m);
        },
    );
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

/// Reading a stored memory plan is linear in its size (plan row EXE-plan-carried): each byte
/// read once and each index checked against a length of the graph. Small instance:
/// `plan_carried::the_stored_plan_is_the_plan_worked_out_again_on_the_corpus`.
#[test]
fn reading_the_stored_plan_scales() {
    // 1,000 and 8,000: at 5,000 and 40,000 a phase under DynamoRIO passed the 20 s cap of a
    // piece on an 8-core VM (job3 of b22-small13); instructions need no larger size.
    let n = 1_000;
    let stored = scaling::inputs(n, |m| {
        let p = zedc::run::load(chain(m, "    ").as_bytes()).unwrap();
        let g = zed_native::legalize(zedc::zir::lower::lower(&p.term()).unwrap());
        let bytes = zedc::zir::memory::plan(g.graph(), true).to_bytes();
        (g, bytes)
    });
    scaling::check("reading the stored plan of n joins", n, |m| {
        let (g, bytes) = &stored[&m];
        let p = zedc::zir::memory::Plan::from_bytes(bytes, g.graph()).unwrap();
        assert!(p.regions.iter().map(|r| r.nodes.len()).sum::<usize>() >= m);
    });
}

/// The start of an executable on the corpus, before EXE-plan-carried (decode the graph,
/// legalize it and plan it) and after (decode, legalize and read the stored plan): the work of
/// each, summed over the 115 graphs, printed, and the start now does less.
#[test]
fn the_start_reads_the_plan_in_less_work_than_planning() {
    use super::plan_carried::corpus;
    use zedc::zir::memory::{Plan, plan};
    let stored: Vec<(Vec<u8>, Vec<u8>)> = (corpus().iter())
        .map(|g| {
            let zir = zedc::zir::strip::encode_stripped(g).unwrap();
            let p = plan(zed_native::legalize(g.clone()).graph(), true);
            (zir, p.to_bytes())
        })
        .collect();
    let decode = |zir: &[u8]| zed_native::legalize(zedc::zir::binary::decode_form(zir).unwrap().0);
    let mut meter = scaling::Meter::new();
    let before = meter.least(
        || {},
        || {
            for (zir, _) in &stored {
                let g = decode(zir);
                std::hint::black_box(plan(g.graph(), true));
            }
        },
    );
    let after = meter.least(
        || {},
        || {
            for (zir, p) in &stored {
                let g = decode(zir);
                std::hint::black_box(Plan::from_bytes(p, g.graph()).unwrap());
            }
        },
    );
    let unit = meter.unit();
    let ratio = before.units as f64 / after.units as f64;
    println!(
        "start on the corpus: planning {unit}={}, reading the plan {unit}={}, ratio {ratio:.2}",
        before.units, after.units
    );
    assert!(
        after.units < before.units,
        "{} {}",
        before.units,
        after.units
    );
}

/// The object file of an executable with its DWARF (plan row DEBUG-dwarf-clif, COMPLEXITY.md
/// rows Z37 and Z38): the line table's rows, the subprograms and the sections are each linear
/// in the code, and each node's line one binary search; the n names the chain binds in
/// `zed_root` are sorted and swept once (DEBUG-dwarf-clif-bindings). The measure is the whole
/// object file, the code generator's work with it. Small instances:
/// `dwarf::the_code_is_the_same_with_and_without_debug_information` and
/// `dwarf::gdb_prints_the_words_the_names_are_bound_to`.
#[test]
fn the_dwarf_of_n_statements_scales() {
    let n = 500;
    // Each process builds only the size it runs (`scaling::check_inputs`). The bench stopped
    // before its count while the location lists' pieces were quadratic in n: the code of no
    // node between ranges split every scope (`dwarf::Runs`; 41,208 pieces for 200 joins in job
    // dv50 of b22-free2, 2026-11-26).
    let made = |m: usize| {
        let p = zedc::run::load(chain(m, "    ").as_bytes()).unwrap();
        let lowered = lower_debug(&p.term(), Some(p.sites())).unwrap();
        (p, lowered)
    };
    scaling::check_inputs(
        "the object file of n statements, with DWARF",
        n,
        made,
        |made| {
            let (p, (g, sited)) = made;
            let object = zed_native::executable_object(
                g.clone(),
                true,
                p.ports(),
                &p.limits(),
                p.address().unwrap(),
                (p.file(), p.text()),
                sited,
                true,
            )
            .unwrap();
            std::hint::black_box(object);
        },
    );
}
