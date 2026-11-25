//! `zedc build`, run as a user runs it (DESIGN.md step L1.36a): it builds an executable that
//! runs, and a missing linker or runtime library, or a wrong command line, is a usage error,
//! status 2, naming what is missing. `crates/zed-native/Cargo.toml` names this test, since
//! only a test of that package can name the executable.
#![cfg(target_os = "linux")]

#[path = "../../src/linker_comment.rs"]
mod linker_comment;
/// This process's scratch directory, as the step tests have it. A test target of zed-native
/// cannot depend on zed-tests, so the module is compiled in; a target may use part of it.
#[allow(dead_code)]
#[path = "../../src/scratch.rs"]
mod scratch;

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A directory of its own for the calling test, under the test target's scratch directory,
/// claimed by `scratch`; files in it are overwritten by each run, never deleted.
fn dir() -> PathBuf {
    scratch::test_dir("l01_36a_binary")
}

/// The runtime library built with `zedc`: of the `libzed_native-<hash>.a` Cargo keeps beside
/// this test, one for each set of features it has built zed-native with, the one holding the
/// symbol `zedc` holds, not the newest.
fn runtime() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    zed_native::link::runtime_of(Path::new(env!("CARGO_BIN_EXE_zedc")), exe.parent().unwrap())
        .unwrap_or_else(|e| panic!("{e}"))
}

/// `zedc build src -o out` with the runtime library and linker `cc` named in the environment,
/// each replaced by `env` where it names one.
fn zedc_build(src: &Path, out: &Path, env: &[(&str, &str)]) -> Output {
    let mut c = Command::new(env!("CARGO_BIN_EXE_zedc"));
    c.arg("build").arg(src).arg("-o").arg(out);
    c.env("ZED_RUNTIME", runtime()).env("CC", "cc");
    for (k, v) in env {
        c.env(k, v);
    }
    c.output().unwrap()
}

/// The working directories of builds of `name` in `d` (`<name>.zed-build.<pid>.<k>`), and the
/// object file that builds before LINK-obj-leftover wrote (`<name>.zed.o`).
fn working(d: &Path, name: &str) -> Vec<String> {
    let (prefix, old) = (format!("{name}.zed-build."), format!("{name}.zed.o"));
    let mut names: Vec<String> = std::fs::read_dir(d)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.starts_with(&prefix) || *n == old)
        .collect();
    names.sort_unstable();
    names
}

/// Writes `bytes` at `path` as a runnable file, in a process of its own: a file this process
/// held open for writing could be inherited by a child that another test thread forks at that
/// moment, and running it would then fail with "Text file busy" (ETXTBSY). As
/// `tests/steps/l01_36b_link_identity`'s `script` does.
fn install(path: &Path, bytes: &[u8]) {
    let text = path.with_extension("bytes");
    std::fs::write(&text, bytes).unwrap();
    let installed = Command::new("install")
        .arg("-m")
        .arg("755")
        .arg(&text)
        .arg(path)
        .status()
        .unwrap();
    assert!(
        installed.success(),
        "install {}: {installed}",
        path.display()
    );
}

/// The status and standard error of `out`, and that it wrote nothing to standard output.
fn failed(out: &Output) -> (Option<i32>, String) {
    assert_eq!(String::from_utf8_lossy(&out.stdout), "");
    (
        out.status.code(),
        String::from_utf8(out.stderr.clone()).unwrap(),
    )
}

#[test]
fn a_built_executable_runs() {
    let d = dir();
    let src = d.join("hello.zed");
    std::fs::write(
        &src,
        "main(m: MainArgs) {\n  \
         m.stdout <- \"Hello, ${m.args[0] else #outOfBounds -> \"world\"}!\";\n}\n",
    )
    .unwrap();
    let exe = d.join("hello");
    let out = zedc_build(&src, &exe, &[]);
    assert_eq!(failed(&out), (Some(0), String::new()));
    let ran = Command::new(&exe).args(["--", "Ann"]).output().unwrap();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "Hello, Ann!\n".to_string())
    );
    // The directory the link works in, with the object file it reads, is not left behind.
    assert_eq!(working(&d, "hello"), Vec::<String>::new());
}

/// Plan row RT-internal-fault: a fault in the code zedc made that no rule of the language
/// explains is reported as a bug in zedc, with the program's content address and the site of
/// the node whose code faulted, status 3, never as an error of the program. The fault is
/// injected by the test build of `zedc build` (`ZED_TEST_FAULT`, which this test's `zedc` reads
/// since zed-native's tests build it with the feature `counts`): a read of address 0 before
/// the code of each `+`. Control: the same program built with no fault runs.
#[test]
fn an_injected_fault_is_reported_as_a_bug_in_zedc() {
    let d = dir();
    let src = d.join("fault.zed");
    std::fs::write(
        &src,
        "main(m: MainArgs) {\n    n = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> \
         1;\n    m.stdout <- String(n + 1);\n}\n",
    )
    .unwrap();
    let exe = d.join("fault");
    let run = || Command::new(&exe).args(["--", "4"]).output().unwrap();
    assert_eq!(
        failed(&zedc_build(&src, &exe, &[])),
        (Some(0), String::new())
    );
    let ran = run();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "5\n".to_string())
    );
    let built = zedc_build(&src, &exe, &[("ZED_TEST_FAULT", "+")]);
    assert_eq!(failed(&built), (Some(0), String::new()));
    let (status, err) = failed(&run());
    assert_eq!(status, Some(3), "{err}");
    assert!(
        err.starts_with(
            "the run stopped because of a bug in zedc, not in your program. The machine code \
             zedc made for the program reached memory or an instruction that no rule of the \
             language lets it reach.\nPlease report it at "
        ),
        "{err}"
    );
    let tail = format!("\n  signal: SIGSEGV\n  site: {}:3:24\n", src.display());
    assert!(err.ends_with(&tail), "{err}");
    // The program's content address, 64 hexadecimal digits, on the line before.
    let address = err[..err.len() - tail.len()]
        .rsplit_once("\nDetails for the report:\n  program: ")
        .map(|(_, a)| a);
    assert!(
        address.is_some_and(|a| a.len() == 64 && a.bytes().all(|b| b.is_ascii_hexdigit())),
        "{err}"
    );
}

/// The bytes of the section `.comment` of the executable `exe`, where LLD writes
/// `Linker: [<vendor> ]LLD <version>` and GNU ld writes nothing of its own.
fn comment(exe: &Path) -> Vec<u8> {
    use object::{Object as _, ObjectSection as _};
    let bytes = std::fs::read(exe).unwrap();
    let elf = object::File::parse(&*bytes).unwrap();
    elf.section_by_name(".comment")
        .map(|s| s.data().unwrap().to_vec())
        .unwrap_or_default()
}

/// LLD is told from GNU ld by the `.comment` strings each leaves, as `readelf -p .comment`
/// printed them for `int main(void){return 0;}` linked by `cc -fuse-ld=lld` and by GNU ld, on
/// Fedora 44 (LLD 22.1.8, GCC 16.2.1) and on Ubuntu 24.04 (a Colab VM: LLD 18.1.3, GCC 13.3.0),
/// 2026-11-22. The section holds NUL-ended strings; LLD's executables also hold GCC's.
#[test]
fn lld_is_told_by_its_comment_with_or_without_a_vendor() {
    let names = linker_comment::names_lld;
    let fedora_gcc = b"GCC: (GNU) 16.2.1 20261029 (Red Hat 16.2.1-3)\0\
                       GCC: (GNU) 16.2.1 20260819 (Red Hat 16.2.1-2)\0";
    assert!(names(
        &[b"\0Linker: LLD 22.1.8\0".as_slice(), fedora_gcc].concat()
    ));
    assert!(!names(fedora_gcc));
    let ubuntu_gcc = b"GCC: (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0\0";
    assert!(names(
        &[ubuntu_gcc.as_slice(), b"Linker: Ubuntu LLD 18.1.3\0"].concat()
    ));
    assert!(!names(ubuntu_gcc));
    assert!(!names(b""));
    // Two words before LLD, or none and a space, are not LLD's string.
    assert!(!names(b"Linker: GNU ld LLD\0"));
    assert!(!names(b"Linker:  LLD 1\0"));
}

/// `zedc build` links with LLD when `ld.lld` is on `PATH`, and with the driver's own linker
/// when the user's `PATH` holds no `ld.lld` (LINK-lld-when-present): here a directory holding
/// only `cc`, `ld` and `dd`, which a link needs. The two executables say the same.
#[test]
fn a_path_without_lld_links_with_the_drivers_linker() {
    let d = dir().join("no_lld");
    let bin = d.join("bin");
    std::fs::create_dir_all(&bin).unwrap();
    let path = std::env::var_os("PATH").expect("a PATH");
    let on_path = |name: &str| {
        std::env::split_paths(&path)
            .map(|dir| dir.join(name))
            .find(|p| p.is_file())
            .unwrap_or_else(|| panic!("no {name} on PATH"))
    };
    assert_eq!(
        zed_native::link::Ld::from_env(),
        zed_native::link::Ld::Lld,
        "ld.lld is on PATH (Fedora package lld), as the default build here needs"
    );
    for name in ["cc", "ld", "dd"] {
        match std::os::unix::fs::symlink(on_path(name), bin.join(name)) {
            Err(e) if e.kind() != std::io::ErrorKind::AlreadyExists => panic!("{name}: {e}"),
            _ => {}
        }
    }
    let src = d.join("greet.zed");
    std::fs::write(
        &src,
        "main(m: MainArgs) {\n  m.stdout <- \"Good ${m.args[0] else #outOfBounds -> \"day\"}\";\n}\n",
    )
    .unwrap();
    let (lld, gnu) = (d.join("greet-lld"), d.join("greet-gnu"));
    assert_eq!(
        failed(&zedc_build(&src, &lld, &[])),
        (Some(0), String::new())
    );
    let no_lld = [("PATH", bin.to_str().unwrap())];
    assert_eq!(
        failed(&zedc_build(&src, &gnu, &no_lld)),
        (Some(0), String::new())
    );
    let by_lld = |exe: &Path| linker_comment::names_lld(&comment(exe));
    assert_eq!((by_lld(&lld), by_lld(&gnu)), (true, false));
    let says = |exe: &Path| {
        let ran = Command::new(exe).args(["--", "evening"]).output().unwrap();
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap())
    };
    assert_eq!(says(&gnu), (Some(0), "Good evening\n".to_string()));
    assert_eq!(says(&lld), says(&gnu));
}

#[test]
fn a_missing_tool_is_a_usage_error_naming_it() {
    let d = dir();
    let src = d.join("quiet.zed");
    std::fs::write(&src, "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n").unwrap();
    let out = d.join("quiet");
    let missing = d.join("no-such-runtime.a");
    assert_eq!(
        failed(&zedc_build(
            &src,
            &out,
            &[("ZED_RUNTIME", missing.to_str().unwrap())]
        )),
        (
            Some(2),
            format!(
                "zedc cannot build an executable: the runtime library {}, which every executable \
                 is linked with, is missing. Repairs: build it with `cargo build -p zed-native`, \
                 which writes it beside zedc, or name its path in the environment variable \
                 ZED_RUNTIME\n",
                missing.display()
            )
        )
    );
    assert_eq!(
        failed(&zedc_build(&src, &out, &[("CC", "no-such-cc")])),
        (
            Some(2),
            "zedc cannot link an executable: the linker `no-such-cc` is missing. Repairs: \
             install a C compiler, or name one in the environment variable CC\n"
                .to_string()
        )
    );
    // A failed link leaves no object file.
    assert_eq!(working(&d, "quiet"), Vec::<String>::new());
}

/// A runtime library that is not the one built with `zedc` (here an archive holding nothing,
/// so not `zedc`'s build) is a usage error naming it:
/// linking it would join code generated by one build to a runtime of another.
#[test]
fn a_runtime_library_of_another_build_is_a_usage_error() {
    let d = dir();
    let src = d.join("other.zed");
    std::fs::write(&src, "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n").unwrap();
    let other = d.join("libzed_native-other.a");
    std::fs::write(&other, b"!<arch>\n").unwrap();
    let out = d.join("other");
    assert_eq!(
        failed(&zedc_build(
            &src,
            &out,
            &[("ZED_RUNTIME", other.to_str().unwrap())]
        )),
        (
            Some(2),
            format!(
                "zedc cannot build an executable: the runtime library {} comes from another build \
                 of zed-native than this zedc, {}, and code one build makes does not run with \
                 another's library. Repairs: build both again with `cargo build -p zed-native`, \
                 or name the library built with this zedc in ZED_RUNTIME\n",
                other.display(),
                env!("CARGO_BIN_EXE_zedc")
            )
        )
    );
    assert!(!out.exists());
    assert_eq!(working(&d, "other"), Vec::<String>::new());
}

/// The executable `bytes` with its symbol table taken out, as `strip` leaves it.
fn strip(bytes: &[u8]) -> Vec<u8> {
    let mut elf = object::build::elf::Builder::read(bytes).unwrap();
    for s in &mut elf.sections {
        if [&b".symtab"[..], b".strtab"].contains(&&*s.name) {
            s.delete = true;
        }
    }
    for s in &mut elf.symbols {
        s.delete = true;
    }
    let mut stripped = Vec::new();
    elf.write(&mut stripped).unwrap();
    stripped
}

/// `zedc` with its symbol table removed, as `strip` removes it, still builds: the build it
/// holds is read from its section `.zed_native.build`, which stays (NATIVE-build-id). The
/// copy is stripped here with the `object` crate, so the test needs no `strip` program. The
/// executable it builds, stripped as well, passes `zedc check-exe` (plan row
/// EXE-plan-carried-recheck), which finds the program by its section `.zed_program`, not by
/// the symbol `zed_program` that stripping takes out, and runs as it did.
#[test]
fn a_stripped_zedc_builds() {
    use object::Object as _;
    let d = dir();
    let bytes = std::fs::read(env!("CARGO_BIN_EXE_zedc")).unwrap();
    let stripped = strip(&bytes);
    // No symbol is left, so `link::build`'s, which named the build before, is gone too.
    assert_eq!(
        object::File::parse(&*stripped).unwrap().symbols().count(),
        0
    );
    let zedc = d.join("zedc-stripped");
    install(&zedc, &stripped);
    let src = d.join("stripped.zed");
    std::fs::write(
        &src,
        "main(m: MainArgs) {\n  m.stdout <- \"stripped\";\n}\n",
    )
    .unwrap();
    let exe = d.join("stripped");
    // The copy lies in another folder than zedc, so a build with `-C prefer-dynamic` whose
    // rpaths are relative (`$ORIGIN`, `$ORIGIN/deps`, as job.sh's dylib retry links it) finds
    // no workspace library from there when the test binary runs outside cargo, which sets
    // LD_LIBRARY_PATH: "libzed_rt.so: cannot open shared object file"
    // (FAIL-stripped-zedc-libzed-rt-missing). The loader searches LD_LIBRARY_PATH before
    // RUNPATH, so naming zedc's own folders first finds the libraries the original finds;
    // a statically linked zedc ignores them.
    let built = Path::new(env!("CARGO_BIN_EXE_zedc")).parent().unwrap();
    let mut libs = vec![built.to_path_buf(), built.join("deps")];
    libs.extend(std::env::split_paths(
        &std::env::var_os("LD_LIBRARY_PATH").unwrap_or_default(),
    ));
    let out = Command::new(&zedc)
        .arg("build")
        .arg(&src)
        .arg("-o")
        .arg(&exe)
        .env("LD_LIBRARY_PATH", std::env::join_paths(libs).unwrap())
        .env("ZED_RUNTIME", runtime())
        .env("CC", "cc")
        .output()
        .unwrap();
    assert_eq!(failed(&out), (Some(0), String::new()));
    let ran = Command::new(&exe).output().unwrap();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "stripped\n".to_string())
    );
    let exe_stripped = d.join("stripped-exe");
    install(&exe_stripped, &strip(&std::fs::read(&exe).unwrap()));
    let checked = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("check-exe")
        .arg(&exe_stripped)
        .output()
        .unwrap();
    assert_eq!(failed(&checked), (Some(0), String::new()));
    let ran = Command::new(&exe_stripped).output().unwrap();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "stripped\n".to_string())
    );
}

#[test]
fn a_wrong_command_line_is_a_usage_error() {
    let usage = (Some(2), format!("{}\n", zed_native::link::USAGE));
    for words in [
        &["build"][..],
        &["build", "a.zed"],
        &["build", "a.zed", "-x", "out"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
            .args(words)
            .output()
            .unwrap();
        assert_eq!(failed(&out), usage, "{words:?}");
    }
}

#[test]
fn a_rejected_program_builds_nothing() {
    let d = dir();
    let src = d.join("rejected.zed");
    std::fs::write(&src, "main(m: MainArgs) {\n  m.stdout <- nothing;\n}\n").unwrap();
    let out = d.join("rejected");
    let (status, stderr) = failed(&zedc_build(&src, &out, &[]));
    assert_eq!(status, Some(1), "{stderr}");
    assert!(stderr.starts_with(src.to_str().unwrap()), "{stderr}");
    assert!(!out.exists());
}

/// A build stopped by SIGKILL while its linker runs leaves its working directory, with the
/// object file in it; the next build to the same output succeeds and removes it
/// (LINK-obj-leftover). The driver here stands for a slow linker: in the link of the program,
/// the one call that reads `killed.o` from the working directory, it says when the link has
/// begun, and waits until the build that ran it has ended, then fails. Every other call, the
/// version reports and the prelink of the runtime, it passes to `cc`. Before
/// (FAIL-build-killed-link-no-working-dir), it waited in every call but the version reports,
/// and so in the prelink, which runs before the working directory is made, whenever no
/// prelinked runtime of this library and key was there yet: after each new build of the
/// library, and after LINK-lld-when-present gave LLD a key of its own. The build was then
/// killed with no working directory, and the test failed or passed by the order its tests ran
/// in. `a_build_killed_while_prelinking_blocks_no_later_build` kills a build in the prelink.
#[test]
fn a_build_killed_while_linking_blocks_no_later_build() {
    let d = dir();
    let src = d.join("killed.zed");
    std::fs::write(&src, "main(m: MainArgs) {\n  m.stdout <- \"again\";\n}\n").unwrap();
    let (out, linking) = (d.join("killed"), d.join("killed.linking"));
    // An executable of the run before records the key, and the build would not link.
    for f in [&out, &linking] {
        match std::fs::remove_file(f) {
            Err(e) if e.kind() != std::io::ErrorKind::NotFound => panic!("{}: {e}", f.display()),
            _ => {}
        }
    }
    let waits = d.join("cc-waits");
    install(
        &waits,
        format!(
            "#!/bin/sh\nfor a in \"$@\"; do\n  case \"$a\" in */killed.o)\n    : > '{}'\n    \
             while kill -0 \"$PPID\" 2>/dev/null; do sleep 0.01; done\n    exit 1 ;;\n  \
             esac\ndone\nexec cc \"$@\"\n",
            linking.display()
        )
        .as_bytes(),
    );
    let mut build = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("build")
        .arg(&src)
        .arg("-o")
        .arg(&out)
        .env("ZED_RUNTIME", runtime())
        .env("CC", &waits)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap();
    while !linking.exists() {
        if let Some(status) = build.try_wait().unwrap() {
            panic!("the build ended before its link began: {status}");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    build.kill().unwrap();
    build.wait().unwrap();
    let left = working(&d, "killed");
    assert_eq!(left.len(), 1, "{left:?}");
    assert!(d.join(&left[0]).join("killed.o").is_file(), "{left:?}");
    assert!(!out.exists());

    assert_eq!(
        failed(&zedc_build(&src, &out, &[])),
        (Some(0), String::new())
    );
    let ran = Command::new(&out).output().unwrap();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "again\n".to_string())
    );
    assert_eq!(working(&d, "killed"), Vec::<String>::new());
}

/// The prelinked runtimes in `d` made from the library named `library`, finished
/// (`<library>.<hash>.<key>.o`) or unfinished (that and `.<pid>`), by name.
fn prelinked_in(d: &Path, library: &str) -> Vec<String> {
    let prefix = format!("{library}.");
    let mut names: Vec<String> = std::fs::read_dir(d)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.starts_with(&prefix) && (n.ends_with(".o") || n.contains(".o.")))
        .collect();
    names.sort_unstable();
    names
}

/// A build stopped by SIGKILL while the driver makes the prelinked runtime, which comes before
/// the build has a working directory, leaves none, and leaves only the prelink's unfinished
/// file; the next build to the same output prelinks again, removes that file, and succeeds
/// (FAIL-build-killed-link-no-working-dir). The runtime library is linked (`symlink(2)`) into a
/// directory of this test's own, which `zed_native::link::prelinked` looks in first, so the
/// build prelinks there whatever other tests have made beside the library itself; the
/// prelinked runtimes a run before left there are removed first, and the one this run makes
/// is removed at the end, since it is as large as the part of the library a program reaches.
#[test]
fn a_build_killed_while_prelinking_blocks_no_later_build() {
    let d = dir().join("killed-prelinking");
    std::fs::create_dir_all(&d).unwrap();
    let library = runtime();
    let name = library.file_name().unwrap().to_str().unwrap().to_string();
    let linked = d.join(&name);
    // A symbolic link, not a hard link: tools/run_tests.sh mounts the run's copy of the build
    // over the profile folder, so the library and this directory are on two mounts, and
    // link(2) between mounts fails (EXDEV) even on one file system. `ZED_RUNTIME` is used as
    // given, not resolved (link.rs, `Toolchain`), so the build looks for the prelinked object
    // in this directory. The link a run before left may name another path; it is made again.
    match std::fs::remove_file(&linked) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => {
            panic!("{}: {e}", linked.display())
        }
        _ => {}
    }
    std::os::unix::fs::symlink(&library, &linked).unwrap();
    for f in prelinked_in(&d, &name) {
        std::fs::remove_file(d.join(f)).unwrap();
    }
    let src = d.join("killed.zed");
    std::fs::write(&src, "main(m: MainArgs) {\n  m.stdout <- \"again\";\n}\n").unwrap();
    let (out, prelinking) = (d.join("killed"), d.join("killed.prelinking"));
    for f in [&out, &prelinking] {
        match std::fs::remove_file(f) {
            Err(e) if e.kind() != std::io::ErrorKind::NotFound => panic!("{}: {e}", f.display()),
            _ => {}
        }
    }
    // The prelink is the one call whose first argument is `-r` (`PRELINK_FLAGS`).
    let waits = d.join("cc-waits");
    install(
        &waits,
        format!(
            "#!/bin/sh\ncase \"$1\" in -r)\n  : > '{}'\n  \
             while kill -0 \"$PPID\" 2>/dev/null; do sleep 0.01; done\n  exit 1 ;;\n\
             esac\nexec cc \"$@\"\n",
            prelinking.display()
        )
        .as_bytes(),
    );
    let mut build = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("build")
        .arg(&src)
        .arg("-o")
        .arg(&out)
        .env("ZED_RUNTIME", &linked)
        .env("CC", &waits)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap();
    while !prelinking.exists() {
        if let Some(status) = build.try_wait().unwrap() {
            panic!("the build ended before its prelink began: {status}");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    build.kill().unwrap();
    build.wait().unwrap();
    assert_eq!(working(&d, "killed"), Vec::<String>::new());
    let left = prelinked_in(&d, &name);
    assert!(
        left.len() == 1 && left[0].ends_with(&format!(".o.{}", build.id())),
        "{left:?}"
    );
    assert!(!out.exists());

    let linked_text = linked.to_str().unwrap();
    assert_eq!(
        failed(&zedc_build(&src, &out, &[("ZED_RUNTIME", linked_text)])),
        (Some(0), String::new())
    );
    let ran = Command::new(&out).output().unwrap();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "again\n".to_string())
    );
    assert_eq!(working(&d, "killed"), Vec::<String>::new());
    let made = prelinked_in(&d, &name);
    assert!(made.len() == 1 && made[0].ends_with(".o"), "{made:?}");
    std::fs::remove_file(d.join(&made[0])).unwrap();
}
