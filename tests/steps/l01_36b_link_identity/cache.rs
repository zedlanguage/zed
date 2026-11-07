//! A build links again exactly when the key of its link changes: after an edit of the program,
//! or with another release of the driver or of the linker; the same driver and runtime library
//! reached by other paths keep the executable as it is.

use std::os::unix::fs::MetadataExt as _;
use std::path::{Path, PathBuf};

use zed_native::link::{Toolchain, recorded};

use super::{Link, dir, driver, executable, link, sign, toolchain};

/// The line the executable `exe` writes when run with no words.
fn says(exe: &Path) -> String {
    let ran = executable(exe, &[], b"");
    assert_eq!(ran.status, 0, "{}", ran.stderr);
    ran.stdout
}

/// The path of the program `name` that the shell would run: the first directory of `PATH`
/// holding it.
fn on_path(name: &str) -> PathBuf {
    let path = std::env::var_os("PATH").expect("a PATH");
    std::env::split_paths(&path)
        .map(|d| d.join(name))
        .find(|p| p.is_file())
        .unwrap_or_else(|| panic!("no {name} on PATH"))
}

#[test]
fn an_edited_program_links_again() {
    let d = dir("edited");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    let tools = toolchain();
    std::fs::write(&src, sign("open")).unwrap();
    // Linked, or kept from the run before: either way it says "open".
    link(&src, &out, &tools);
    assert_eq!(says(&out), "open\n");
    let open = recorded(&out).expect("a built executable records its key");
    assert_eq!(open.len(), 32, "the key is a BLAKE3 hash");

    std::fs::write(&src, sign("closed")).unwrap();
    assert_eq!(link(&src, &out, &tools), Link::Ran);
    assert_eq!(says(&out), "closed\n");
    assert_ne!(recorded(&out).unwrap(), open);

    std::fs::write(&src, sign("open")).unwrap();
    assert_eq!(link(&src, &out, &tools), Link::Ran);
    assert_eq!(says(&out), "open\n");
    assert_eq!(
        recorded(&out).unwrap(),
        open,
        "the key is a function of the inputs"
    );
}

#[test]
fn another_release_of_the_driver_or_the_linker_links_again() {
    let d = dir("releases");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("sale")).unwrap();
    let (gcc_next, ld_next) = (d.join("gcc-next"), d.join("ld-next"));
    driver(&gcc_next, Some("cc (GCC) 99.1.0"), None);
    driver(&ld_next, None, Some("GNU ld version 9.99"));
    let system = toolchain();
    let with = |linker: &Path| Toolchain {
        linker: linker.into(),
        ..system.clone()
    };
    link(&src, &out, &system);
    assert_eq!(
        link(&src, &out, &with(&gcc_next)),
        Link::Ran,
        "another driver release"
    );
    assert_eq!(
        link(&src, &out, &with(&ld_next)),
        Link::Ran,
        "another linker release under the same driver"
    );
    assert_eq!(link(&src, &out, &system), Link::Ran, "the system's again");
    // Each driver linked with `cc` itself, so each executable runs alike.
    assert_eq!(says(&out), "sale\n");
}

#[test]
fn the_same_toolchain_on_other_paths_keeps_the_executable() {
    let d = dir("paths");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("welcome")).unwrap();
    let system = toolchain();
    link(&src, &out, &system);
    let before = std::fs::metadata(&out).unwrap();
    // The runtime library in another directory, through a symbolic link: the same bytes at no
    // copying cost. Its name is the library's, which Cargo makes from the build's hash, so a
    // link left by a run before names this library.
    let elsewhere = d.join("lib").join(
        system
            .runtime
            .file_name()
            .expect("a runtime library's name"),
    );
    std::fs::create_dir_all(elsewhere.parent().unwrap()).unwrap();
    match std::os::unix::fs::symlink(&system.runtime, &elsewhere) {
        Err(e) if e.kind() != std::io::ErrorKind::AlreadyExists => {
            panic!("{}: {e}", elsewhere.display())
        }
        _ => {}
    }
    let moved = Toolchain {
        linker: on_path("cc").into(),
        runtime: elsewhere,
        env: zed_native::link::driver_env(),
    };
    assert_ne!(moved.linker, system.linker);
    assert_eq!(link(&src, &out, &moved), Link::Kept);
    let after = std::fs::metadata(&out).unwrap();
    assert_eq!(
        (after.ino(), after.mtime(), after.mtime_nsec()),
        (before.ino(), before.mtime(), before.mtime_nsec()),
        "a kept executable is not written"
    );
    assert_eq!(says(&out), "welcome\n");
}

#[test]
fn a_file_of_the_users_at_the_output_is_replaced() {
    let d = dir("replaced");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("back soon")).unwrap();
    std::fs::write(&out, "notes for the sign\n").unwrap();
    assert_eq!(recorded(&out), None, "a text file records no key");
    assert_eq!(link(&src, &out, &toolchain()), Link::Ran);
    assert_eq!(says(&out), "back soon\n");
}

#[test]
fn one_program_built_at_two_outputs_records_one_key() {
    let d = dir("two_outputs");
    let src = d.join("sign.zed");
    std::fs::write(&src, sign("fresh bread")).unwrap();
    let (one, two) = (d.join("sign"), d.join("bakery").join("sign"));
    std::fs::create_dir_all(two.parent().unwrap()).unwrap();
    let tools = toolchain();
    link(&src, &one, &tools);
    link(&src, &two, &tools);
    assert_eq!(recorded(&one), recorded(&two));
    assert_eq!(
        std::fs::read(&one).unwrap(),
        std::fs::read(&two).unwrap(),
        "the output's path enters neither the key nor the bytes"
    );
}
