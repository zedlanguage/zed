//! One engine (plan row ENGINE-one): `zedc build` and `zedc run` take one staged program, and
//! a program one of them runs the other runs to the same end, the same stop at the same site
//! with the same exit status. A constant staging folds is written by the form it is kept in,
//! `2^2^100` as a power, so no constant too large to write out refuses a build that a run
//! completes or stops at run time.

use std::path::{Path, PathBuf};

use zed_native::link::build;
use zed_tests::step_helpers::l01_36a_executables::toolchain;

use super::{Ran, dir, executable, interpreter};

/// The program `src` written to a file of test `name`, built, and run with no words and no
/// input by both engines: the build's error or the executable's run, and `zedc run`'s.
fn both(name: &str, src: &str) -> (PathBuf, Result<Ran, (u8, String)>, Ran) {
    let d = dir("one_engine");
    let file = d.join(format!("{name}.zed"));
    std::fs::write(&file, src).unwrap();
    (
        file.clone(),
        native(&file, &d.join(name)),
        interpreter(&file, &[], b""),
    )
}

/// The program in `src` built into `out` and run with no words and no input, or the status and
/// error of its build.
fn native(src: &Path, out: &Path) -> Result<Ran, (u8, String)> {
    build(
        src.to_str().unwrap(),
        out,
        &[],
        &mut Default::default(),
        &toolchain(),
        &mut Vec::new(),
    )?;
    Ok(executable(out, &[], b""))
}

/// Checks that the two engines end `src` alike: the executable's status and standard output
/// are `zedc run`'s, and its standard error is the end of `zedc run`'s, which prints the
/// program's warnings first.
fn agree(name: &str, src: &str) -> Ran {
    let (file, native, run) = both(name, src);
    let native = native.unwrap_or_else(|(s, why)| {
        panic!(
            "{}: `zedc build` refused with status {s}, and `zedc run` ended with status {}: \
             {why}",
            file.display(),
            run.status
        )
    });
    assert_eq!(
        (native.status, &native.stdout),
        (run.status, &run.stdout),
        "{}",
        file.display()
    );
    assert!(
        run.stderr.ends_with(&native.stderr),
        "{}: the executable wrote\n{}\nand zedc run\n{}",
        file.display(),
        native.stderr,
        run.stderr
    );
    native
}

/// The first line of the stop `s` wrote, with `FILE` for the program's path.
fn stop_line(s: &Ran, name: &str) -> String {
    let file = dir("one_engine").join(format!("{name}.zed"));
    s.stderr
        .lines()
        .next()
        .unwrap_or("")
        .replace(&file.display().to_string(), "FILE")
}

#[test]
fn a_folded_constant_too_large_to_write_out_stops_alike() {
    // `g()` stages to the constant 2^2^100, whose digits no memory holds. Before, the build
    // wrote the constant's digits to key its node and refused the program ("one of its
    // constants takes 1267650600228229401496703205378 bytes") while `zedc run` stopped at 4:17.
    let src = "g() = 2^2^100;\nmain(m: MainArgs) {\n    n = 1;\n    \
               m.stdout <- String(g() * n);\n}\n";
    let ran = agree("folded", src);
    assert_eq!(ran.status, 1);
    assert_eq!(
        stop_line(&ran, "folded"),
        "FILE:4:17: `String` must build a number in full, and the system refused the \
         4322886617184547919947741790226 bytes of memory asked for it; the number is exact and \
         has no size limit, but this machine cannot hold its digits."
    );
}

#[test]
fn the_row_s_program_stops_alike() {
    let src = "main(m: MainArgs) {\n    n = 1;\n    m.stdout <- String(2^2^100 * n);\n}\n";
    let ran = agree("row", src);
    assert_eq!(ran.status, 1);
    assert!(stop_line(&ran, "row").starts_with("FILE:3:17: `String` must build a number"));
}

#[test]
fn a_literal_too_large_to_write_out_runs_alike() {
    // The literal is 2^K 5^K for K = 10^20. Before, both engines refused the program for want
    // of the memory to write its digits into the content address.
    let src = "main(m: MainArgs) {\n    m.stdout <- String(1e100000000000000000000r == 0r);\n}\n";
    let ran = agree("literal", src);
    assert_eq!((ran.status, ran.stdout.as_str()), (0, "false\n"));
}

#[test]
fn a_folded_constant_used_without_its_digits_runs_alike() {
    // The folded constant is used only by operations that never build it.
    let src = "g() = 2^2^100;\nh() = 3r^2^80 / 7r^2^90;\nmain(m: MainArgs) {\n    \
               n = 1;\n    m.stdout <- \"${(g() * n) mod 7} ${g() > 0} ${-g() < 0} \
               ${h() > 0r}\";\n}\n";
    let ran = agree("used", src);
    assert_eq!((ran.status, ran.stdout.as_str()), (0, "2 true true true\n"));
}

/// The `.zed` files under `d`, in path order.
fn zed_files(d: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(d) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.map(|e| e.unwrap().path()).collect();
    paths.sort();
    for p in paths {
        if p.is_dir() {
            zed_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "zed") {
            out.push(p);
        }
    }
}

/// The corpus sweep: every program of the repository's `.zed` files and of the fences of
/// DESIGN.md and EXAMPLES.md that loads and has `main`, at any layer, built and run with no
/// words and no input by both engines, ends alike.
#[test]
fn every_program_ends_alike() {
    let d = dir("one_engine_sweep");
    let mut files = Vec::new();
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    zed_files(&repo.join("zed"), &mut files);
    zed_files(&repo.join("tests/steps"), &mut files);
    for (k, f) in zed_tests::fences::all().into_iter().enumerate() {
        if !f.notation {
            let src = d.join(format!("fence{k}.zed"));
            std::fs::write(&src, &f.text).unwrap();
            files.push(src);
        }
    }
    let programs: Vec<PathBuf> = files
        .into_iter()
        .filter(|p| {
            let text = std::fs::read(p).unwrap();
            text.windows(5).any(|w| w == b"main(") && zedc::run::load(&text).is_ok()
        })
        .collect();
    let mut differ = Vec::new();
    for (k, src) in programs.iter().enumerate() {
        let native = native(src, &d.join(format!("program{k}")));
        let run = interpreter(src, &[], b"");
        let same = native.as_ref().is_ok_and(|n| {
            (n.status, &n.stdout) == (run.status, &run.stdout) && run.stderr.ends_with(&n.stderr)
        });
        if !same {
            differ.push(format!("{}: native {native:?}, run {run:?}", src.display()));
        }
    }
    eprintln!("{} programs: {programs:?}", programs.len());
    assert!(differ.is_empty(), "{}", differ.join("\n"));
}

#[test]
fn constants_kept_as_powers_print_and_compare_alike() {
    // Each line holds a constant staging keeps with prime powers, of a size whose digits fit:
    // positive and negative, an integer and a fraction with powers above and below the line,
    // a decimal literal with an exponent (the primes 2 and 5), and comparisons of a kept power
    // with the same number written out, which the executable reads back from its binary form.
    let src = "a() = 2^200;\nb() = -3r^70 / 7r^90;\nc() = 1.5e30r;\n\
               main(m: MainArgs) {\n    n = 1;\n    \
               m.stdout <- \"${a() * n}\\n${b() * rat(n)}\\n${c() * rat(n)}\\n\
               ${a() == 1606938044258990275541962092341162602522202993782792835301376} \
               ${-a() < 0} ${b() < 0r} ${c() == 1500000000000000000000000000000r}\";\n}\n";
    let ran = agree("corners", src);
    assert_eq!(ran.status, 0, "{}", ran.stderr);
    let lines: Vec<&str> = ran.stdout.lines().collect();
    assert_eq!(
        lines[0],
        "1606938044258990275541962092341162602522202993782792835301376"
    );
    assert_eq!(lines[3], "true true true true");
}
