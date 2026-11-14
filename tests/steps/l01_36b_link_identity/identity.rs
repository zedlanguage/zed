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
        env: zed_native::link::driver_env(),
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
    assert_eq!(monday.key(object, &[]), copy.key(object, &[]));
    assert_ne!(monday.key(object, &[]), tuesday.key(object, &[]));
}

#[test]
fn the_object_file_is_named_by_its_bytes() {
    let tools = identity(&with_runtime("object", "libzed.a", "a runtime"));
    let object = b"price = 120".to_vec();
    let mut edited = object.clone();
    *edited.last_mut().unwrap() = b'5';
    assert_eq!(tools.key(&object, &[]), tools.key(&object.clone(), &[]));
    assert_ne!(tools.key(&object, &[]), tools.key(&edited, &[]));
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
    assert_ne!(reported.key(b"o", &[]), system.key(b"o", &[]));
}

/// The key names the files the link read and the driver's environment, each read without
/// linking: no files and one, another file, one more file, the same files in another order,
/// and a variable unset, set empty and set to a value each give a key of their own.
#[test]
fn the_key_names_the_files_read_and_the_environment() {
    let tools = identity(&with_runtime("inputs", "libzed.a", "a runtime"));
    let (a, b) = (blake3::hash(b"libc.so"), blake3::hash(b"libm.so"));
    let object = b"the object file of a program";
    let keys: Vec<_> = [&[][..], &[a], &[b], &[a, b], &[b, a], &[a, a]]
        .iter()
        .map(|inputs| tools.key(object, inputs))
        .collect();
    for (i, k) in keys.iter().enumerate() {
        assert_eq!(
            keys.iter().filter(|o| *o == k).count(),
            1,
            "inputs case {i}"
        );
    }
    assert_eq!(
        tools.key(object, &[a, b]),
        keys[3],
        "the same files, the same key"
    );
    let name = zed_native::link::DRIVER_ENV[0];
    let with = |value: Option<&str>| {
        let mut changed = tools.clone();
        changed.env = vec![(name, value.map(Into::into))];
        changed.key(object, &[])
    };
    let env = [with(None), with(Some("")), with(Some("/opt/gcc"))];
    assert!(
        env[0] != env[1] && env[1] != env[2] && env[0] != env[2],
        "{name} unset, empty and set give three keys"
    );
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
            "zedc cannot use the linker `{failing}`: `{failing} --version` failed (exit \
             status: 3), and zedc needs the linker's version to tell its links from another \
             linker's. Repair: name in CC a C compiler that gives its version. The linker \
             printed:\ncc: unknown option"
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
            "zedc cannot use the linker `{silent}`: it wrote nothing for `{silent} --version`, \
             so its links cannot be told from another linker's. Repair: name in CC a C \
             compiler that gives its version"
        )
    );

    let (status, why) = of(&d.join("no-such-cc"));
    assert_eq!(status, 2, "a missing linker is a usage error");
    assert!(
        why.ends_with(
            "is missing. Repairs: install a C compiler, or name one in the environment \
             variable CC"
        ),
        "{why}"
    );
}

#[test]
fn a_missing_runtime_library_is_named() {
    let tools = Toolchain {
        linker: "cc".into(),
        runtime: dir("missing").join("libnone.a"),
        env: zed_native::link::driver_env(),
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
