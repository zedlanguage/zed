//! The identity of a toolchain (`zed_native::link::Identity`) names the runtime library by its
//! bytes and the linker by its driver's reports, and the key of a link changes with each of
//! them and with the object file. A driver that cannot be run, fails, or reports nothing is
//! refused, each with its own message.

use zed_native::link::{Identity, Toolchain};

use super::{dir, script};

/// The system's driver with the runtime library `runtime` in the directory of test `name`,
/// holding `bytes`. The identity reads a library's bytes and nothing else, so a small file
/// stands for one.
fn with_runtime(name: &str, runtime: &str, bytes: &str) -> Toolchain {
    let path = dir(name).join(runtime);
    std::fs::write(&path, bytes).unwrap();
    Toolchain {
        linker: "cc".into(),
        runtime: path,
    }
}

/// The identity of `tools`, which must have one.
fn identity(tools: &Toolchain) -> Identity {
    Identity::of(tools).unwrap_or_else(|(status, why)| panic!("status {status}: {why}"))
}

#[test]
fn the_runtime_library_is_named_by_its_bytes_not_its_path() {
    let monday = identity(&with_runtime(
        "bytes",
        "libmonday.a",
        "the runtime of Monday",
    ));
    let copy = identity(&with_runtime("bytes", "libcopy.a", "the runtime of Monday"));
    let tuesday = identity(&with_runtime(
        "bytes",
        "libtuesday.a",
        "the runtime of Tuesday",
    ));
    assert_eq!(monday, copy);
    assert_ne!(monday, tuesday);
    let object = b"the object file of a program";
    assert_eq!(monday.key(object), copy.key(object));
    assert_ne!(monday.key(object), tuesday.key(object));
}

#[test]
fn the_object_file_is_named_by_its_bytes() {
    let tools = identity(&with_runtime("object", "libzed.a", "a runtime"));
    let object = b"price = 120".to_vec();
    let mut edited = object.clone();
    *edited.last_mut().unwrap() = b'5';
    assert_eq!(tools.key(&object), tools.key(&object.clone()));
    assert_ne!(tools.key(&object), tools.key(&edited));
}

#[test]
fn the_linker_is_named_by_its_drivers_reports() {
    let d = dir("reports");
    let tools = with_runtime("reports", "libzed.a", "a runtime");
    let system = identity(&tools);
    assert!(
        system.linker.iter().all(|r| !r.is_empty()),
        "cc reports its version and its linker's"
    );
    let report = d.join("cc-report");
    script(&report, "printf '%s\\n' \"report for $1\"\n");
    let reported = identity(&Toolchain {
        linker: report.into(),
        ..tools
    });
    assert_eq!(
        reported.linker,
        [
            b"report for --version\n".to_vec(),
            b"report for -Wl,--version\n".to_vec()
        ]
    );
    assert_eq!(reported.runtime, system.runtime);
    assert_ne!(reported.key(b"o"), system.key(b"o"));
}

#[test]
fn a_driver_that_gives_no_version_is_refused() {
    let d = dir("refused");
    let tools = with_runtime("refused", "libzed.a", "a runtime");
    let of = |linker: &std::path::Path| {
        Identity::of(&Toolchain {
            linker: linker.into(),
            ..tools.clone()
        })
        .expect_err("refused")
    };
    let failing = d.join("cc-failing");
    script(&failing, "echo 'cc: unknown option' >&2\nexit 3\n");
    let (status, why) = of(&failing);
    assert_eq!(status, 1);
    let failing = failing.display();
    assert_eq!(
        why,
        format!(
            "the linker `{failing}` gave no version: `{failing} --version` failed (exit \
             status: 3):\ncc: unknown option"
        )
    );

    let silent = d.join("cc-silent");
    script(&silent, "exit 0\n");
    let (status, why) = of(&silent);
    assert_eq!(status, 1);
    let silent = silent.display();
    assert_eq!(
        why,
        format!(
            "the linker `{silent}` wrote nothing for `{silent} --version`, so its links cannot \
             be told from another linker's: name a C compiler that gives its version in CC"
        )
    );

    let (status, why) = of(&d.join("no-such-cc"));
    assert_eq!(status, 2, "a missing linker is a usage error");
    assert!(
        why.ends_with("is missing: install a C compiler, or name one in CC"),
        "{why}"
    );
}

#[test]
fn a_missing_runtime_library_is_named() {
    let tools = Toolchain {
        linker: "cc".into(),
        runtime: dir("missing").join("libnone.a"),
    };
    let (status, why) = Identity::of(&tools).expect_err("no library");
    assert_eq!(status, 1);
    assert_eq!(
        why,
        format!(
            "{}: No such file or directory (os error 2)",
            tools.runtime.display()
        )
    );
}
