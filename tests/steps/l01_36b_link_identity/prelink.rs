//! A build links a prelinked runtime (PERF-link-archive): one object file made from the
//! runtime library once for each toolchain, kept beside the library, or beside the output when
//! the library's directory cannot be written. A build that makes it removes the prelinked
//! objects of other bytes of the library and the unfinished files of stopped builds, and keeps
//! those of other toolchains with the same library; a prelinked object made again has the same
//! bytes.

use std::path::{Path, PathBuf};

use zed_native::link::{Identity, Toolchain};

use super::{Link, dir, executable, link, sign, toolchain};

/// The system's toolchain with its runtime library reached through a symbolic link in `lib`,
/// so the prelinked object and its lock are made there, in a directory of this test's.
fn linked_from(lib: &Path) -> Toolchain {
    let system = toolchain();
    let runtime = lib.join(
        system
            .runtime
            .file_name()
            .expect("a runtime library's name"),
    );
    std::fs::create_dir_all(lib).unwrap();
    match std::os::unix::fs::symlink(&system.runtime, &runtime) {
        Err(e) if e.kind() != std::io::ErrorKind::AlreadyExists => {
            panic!("{}: {e}", runtime.display())
        }
        _ => {}
    }
    Toolchain { runtime, ..system }
}

/// The path of the prelinked object of `tools` in `dir`.
fn prelinked_in(dir: &Path, tools: &Toolchain) -> PathBuf {
    let identity = Identity::of(tools).unwrap();
    let mut name = tools.runtime.file_name().unwrap().to_owned();
    name.push(format!(
        ".{}.{}.o",
        identity.runtime.to_hex(),
        identity.prelink_key().to_hex()
    ));
    dir.join(name)
}

/// Removes the file at `path` if it is there.
fn removed(path: &Path) {
    match std::fs::remove_file(path) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => panic!("{}: {e}", path.display()),
        _ => {}
    }
}

/// Builds the sign saying `text` in `d` as `out` with `tools`, links it, and checks it runs.
fn built(d: &Path, out: &str, text: &str, tools: &Toolchain) {
    let (src, out) = (d.join(format!("{out}.zed")), d.join(out));
    std::fs::write(&src, sign(text)).unwrap();
    // The text names the time of the run, so the output is linked, not kept from a run before.
    assert_eq!(link(&src, &out, tools), Link::Ran);
    let ran = executable(&out, &[], b"");
    assert_eq!(ran.status, 0, "{}", ran.stderr);
    assert_eq!(ran.stdout, format!("{text}\n"));
}

#[test]
fn a_build_prelinks_the_runtime_once_beside_it_and_removes_stale_ones() {
    let d = dir("prelink");
    let lib = d.join("lib");
    let tools = linked_from(&lib);
    let object = prelinked_in(&lib, &tools);
    let name = object.file_name().unwrap().to_str().unwrap();
    let library = tools.runtime.file_name().unwrap().to_str().unwrap();
    let key = &name[library.len() + 66..name.len() - 2];
    // Made from other bytes of the library: removed.
    let stale = lib.join(format!("{library}.{}.{key}.o", "0".repeat(64)));
    // Made from these bytes for another toolchain: kept.
    let other = lib.join(format!(
        "{}.{}.o",
        &name[..library.len() + 65],
        "1".repeat(64)
    ));
    let mut unfinished = object.as_os_str().to_owned();
    unfinished.push(".4242");
    let unfinished = PathBuf::from(unfinished);
    // A user's file whose name starts as the library's does not match the pattern and stays.
    let mut kept = tools.runtime.file_name().unwrap().to_owned();
    kept.push(".notes.o");
    let kept = lib.join(kept);
    removed(&object);
    for path in [&stale, &other, &unfinished, &kept] {
        std::fs::write(path, "left by another build").unwrap();
    }
    built(
        &d,
        "first",
        &format!("first {:?}", std::time::SystemTime::now()),
        &tools,
    );
    assert!(object.is_file(), "{} made", object.display());
    assert!(!stale.exists(), "{} removed", stale.display());
    assert!(!unfinished.exists(), "{} removed", unfinished.display());
    assert!(kept.exists(), "{} kept", kept.display());
    assert!(other.exists(), "{} kept", other.display());
    let bytes = std::fs::read(&object).unwrap();
    // A second build reads the object as it is.
    let made = std::fs::metadata(&object).unwrap().modified().unwrap();
    built(
        &d,
        "second",
        &format!("second {:?}", std::time::SystemTime::now()),
        &tools,
    );
    assert_eq!(
        std::fs::metadata(&object).unwrap().modified().unwrap(),
        made
    );
    // Made again, it has the same bytes.
    removed(&object);
    built(
        &d,
        "third",
        &format!("third {:?}", std::time::SystemTime::now()),
        &tools,
    );
    assert!(
        std::fs::read(&object).unwrap() == bytes,
        "a prelink gives the same bytes"
    );
}

#[test]
fn a_runtime_in_a_directory_that_cannot_be_written_is_prelinked_beside_the_output() {
    use std::os::unix::fs::PermissionsExt as _;
    let d = dir("prelink_read_only");
    let lib = d.join("lib");
    let tools = linked_from(&lib);
    let object = prelinked_in(&d, &tools);
    removed(&object);
    std::fs::set_permissions(&lib, std::fs::Permissions::from_mode(0o555)).unwrap();
    let writable = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(lib.join("probe"))
        .is_ok();
    let result = std::panic::catch_unwind(|| {
        built(
            &d,
            "sign",
            &format!("read-only {:?}", std::time::SystemTime::now()),
            &tools,
        )
    });
    std::fs::set_permissions(&lib, std::fs::Permissions::from_mode(0o755)).unwrap();
    if let Err(e) = result {
        std::panic::resume_unwind(e);
    }
    // Run as root, the directory can be written all the same, and the object goes there.
    let at = if writable {
        prelinked_in(&lib, &tools)
    } else {
        object
    };
    assert!(at.is_file(), "{} made", at.display());
}
