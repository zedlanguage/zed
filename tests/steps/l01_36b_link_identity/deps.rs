//! The key of a link names every file the linker read, by its bytes, and the environment of the
//! driver (LINK-key-deps): a library the link read that a system update changes, or another
//! `LIBRARY_PATH`, links again under the same driver release. The linker lists the files it
//! read (`--dependency-file`), and the build keeps that list beside the executable,
//! `<out>.zed-link` (`zed_native::link::Record`), with the hash of the executable's bytes, so
//! a stripped or edited executable, which keeps its build ID, links again too.

use std::os::unix::fs::MetadataExt as _;
use std::path::{Path, PathBuf};

use zed_native::link::{Inputs, Record, Toolchain, dependencies, recorded};

use super::{Link, at_once, copied, dir, executable, link, script, sign, toolchain};

/// The line the executable `exe` writes when run with no words.
fn says(exe: &Path) -> String {
    let ran = executable(exe, &[], b"");
    assert_eq!(ran.status, 0, "{}", ran.stderr);
    ran.stdout
}

/// The system's toolchain with its driver at `path`: a script that runs `cc` with `-L lib`
/// first, so that the linker finds `-lutil` in `lib` before the system's directories. Its
/// reports for `--version` and `-Wl,--version` are `cc`'s, so it stands for the system's
/// toolchain after an update that changed one library and not the driver's release.
fn with_lib(path: &Path, lib: &Path) -> Toolchain {
    script(path, &format!("exec cc -L'{}' \"$@\"\n", lib.display()));
    Toolchain {
        linker: path.into(),
        ..toolchain()
    }
}

/// `libutil`, as a linker script with no commands: since glibc 2.34 the functions of
/// `libutil` are in `libc`, and the system's `libutil.a` is an empty archive. `note` is its
/// comment, so two notes give two files that link alike.
fn libutil(lib: &Path, note: &str) -> PathBuf {
    std::fs::create_dir_all(lib).unwrap();
    let at = lib.join("libutil.so");
    std::fs::write(&at, format!("/* {note} */\n")).unwrap();
    at
}

/// The time `path` was last written, to the nanosecond, and its inode.
fn written(path: &Path) -> (u64, i64, i64) {
    let m = std::fs::metadata(path).unwrap();
    (m.ino(), m.mtime(), m.mtime_nsec())
}

/// The two notes of `libutil` in the test below: the library as the system ships it, and
/// after an update.
const SHIPPED: &str = "libutil: its functions are in libc";
const UPDATED: &str = "libutil, after a system update";

/// The library changes, and changes back. Each change has a directory of its own, with its own
/// `libutil` and driver, and runs at once with the other: `from` is the library the output is
/// first linked with (linked, or kept from the run before), `to` the one a copy of it is linked
/// with after.
#[test]
fn a_changed_library_the_link_read_links_again() {
    let d = dir("library");
    let src = d.join("sign.zed");
    std::fs::write(&src, sign("today's special")).unwrap();
    let change = |name: &str, from: &str, to: &str| {
        let d = d.join(name);
        let (out, lib) = (d.join("sign"), d.join("lib"));
        let util = libutil(&lib, from);
        let tools = with_lib(&d.join("cc-lib"), &lib);
        link(&src, &out, &tools);
        let record = Record::read(&out).expect("a link leaves its record");
        assert!(
            record.inputs.iter().any(|p| p == &util),
            "the record names the libutil the linker read: {:?}",
            record.inputs
        );
        assert!(
            record.inputs.iter().any(|p| p
                .file_name()
                .is_some_and(|n| n.to_string_lossy().starts_with("libc.so"))),
            "and the system's libc: {:?}",
            record.inputs
        );
        let before = (written(&out), written(&Record::path(&out)));
        assert_eq!(link(&src, &out, &tools), Link::Kept, "nothing changed");
        assert_eq!(
            (written(&out), written(&Record::path(&out))),
            before,
            "a kept executable and its record are not written"
        );
        let changed = d.join("changed");
        copied(&out, &changed);
        libutil(&lib, to);
        assert_eq!(
            link(&src, &changed, &tools),
            Link::Ran,
            "{from} became {to}"
        );
        assert_eq!(says(&changed), "today's special\n");
        assert_eq!(link(&src, &changed, &tools), Link::Kept);
    };
    at_once(&[&|| change("updated", SHIPPED, UPDATED), &|| {
        change("changed_back", UPDATED, SHIPPED)
    }]);
}

/// The system's toolchain with the environment variable `name` of [`zed_native::link::DRIVER_ENV`]
/// set to `value`, or removed for `None`, on its driver's runs.
fn with_env(name: &str, value: Option<&std::ffi::OsStr>) -> Toolchain {
    let mut tools = toolchain();
    let at = tools.env.iter_mut().find(|(n, _)| *n == name);
    at.unwrap_or_else(|| panic!("{name} is in DRIVER_ENV")).1 = value.map(Into::into);
    tools
}

/// The output `out` of `src` linked with the driver's environment `from` (linked, or kept from
/// the run before), then a copy of it at `changed` linked with `to`, which links again. Each
/// build after the first that changes nothing keeps the executable.
fn relinks(src: &Path, out: &Path, changed: &Path, from: &Toolchain, to: &Toolchain, what: &str) {
    link(src, out, from);
    assert_eq!(link(src, out, from), Link::Kept, "{what}: nothing changed");
    copied(out, changed);
    assert_eq!(link(src, changed, to), Link::Ran, "{what}");
    assert_eq!(
        link(src, changed, to),
        Link::Kept,
        "{what}: nothing changed"
    );
}

/// `LIBRARY_PATH` set, changed and unset, each on an output of its own, at once.
#[test]
fn another_library_path_links_again() {
    let d = dir("library_path");
    let (src, empty) = (d.join("sign.zed"), d.join("empty"));
    std::fs::create_dir_all(&empty).unwrap();
    std::fs::write(&src, sign("closed on Sunday")).unwrap();
    let with = |value: Option<&Path>| with_env("LIBRARY_PATH", value.map(Path::as_os_str));
    let change = |name: &str, from: Option<&Path>, to: Option<&Path>| {
        let (out, changed) = (d.join(name), d.join(format!("{name}_changed")));
        relinks(&src, &out, &changed, &with(from), &with(to), name);
        assert_eq!(says(&changed), "closed on Sunday\n");
    };
    at_once(&[
        &|| change("set", None, Some(&empty)),
        &|| change("changed", Some(&empty), Some(&d)),
        &|| change("unset", Some(&d), None),
    ]);
}

/// The executable `out` stripped in place by binutils' `strip`, which comes with the GNU ld
/// that `cc` runs. (The `object` crate's ELF builder, which `build_binary` strips with, is a
/// feature this test crate does not build `object` with.)
fn strip(out: &Path) {
    let size = std::fs::metadata(out).unwrap().len();
    let stripped = std::process::Command::new("strip")
        .arg(out)
        .status()
        .unwrap();
    assert!(stripped.success(), "strip {}: {stripped}", out.display());
    assert!(
        std::fs::metadata(out).unwrap().len() < size,
        "a symbol table was removed"
    );
}

#[test]
fn a_stripped_executable_links_again() {
    let d = dir("stripped");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("half price")).unwrap();
    let tools = toolchain();
    link(&src, &out, &tools);
    let key = recorded(&out).unwrap();
    strip(&out);
    assert_eq!(
        recorded(&out),
        Some(key.clone()),
        "strip keeps the build ID"
    );
    assert_eq!(link(&src, &out, &tools), Link::Ran);
    assert_eq!(recorded(&out), Some(key));
    assert_eq!(link(&src, &out, &tools), Link::Kept);
    assert_eq!(says(&out), "half price\n");
}

#[test]
fn an_edited_executable_links_again() {
    use object::{Object as _, ObjectSection as _};
    let d = dir("edited_bytes");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("sold out")).unwrap();
    let tools = toolchain();
    link(&src, &out, &tools);
    // One byte of the `.comment` section, the compilers' names, which the program never reads.
    let mut bytes = std::fs::read(&out).unwrap();
    let (at, _) = object::File::parse(&*bytes)
        .unwrap()
        .section_by_name(".comment")
        .expect("a .comment section")
        .file_range()
        .unwrap();
    bytes[at as usize] ^= 0x20;
    std::fs::write(&out, &bytes).unwrap();
    assert_eq!(link(&src, &out, &tools), Link::Ran);
    assert_eq!(link(&src, &out, &tools), Link::Kept);
    assert_eq!(says(&out), "sold out\n");
}

#[test]
fn an_executable_without_its_record_links_again() {
    let d = dir("no_record");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("ring the bell")).unwrap();
    let tools = toolchain();
    link(&src, &out, &tools);
    std::fs::write(Record::path(&out), "notes\n").unwrap();
    assert_eq!(Record::read(&out), None, "not a record");
    assert_eq!(link(&src, &out, &tools), Link::Ran);
    assert_eq!(link(&src, &out, &tools), Link::Kept);
}

/// A build in a directory whose name holds a space, linked by LLD, which escapes the space in
/// the list of the files it read; the build reads the list back and keeps the executable.
#[test]
fn lld_s_list_is_read_with_its_escapes() {
    let d = dir("lld").join("shop window");
    std::fs::create_dir_all(&d).unwrap();
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("open #1")).unwrap();
    let lld = d.join("cc-lld");
    script(&lld, "exec cc -fuse-ld=lld \"$@\"\n");
    let tools = Toolchain {
        linker: lld.into(),
        ..toolchain()
    };
    link(&src, &out, &tools);
    assert_eq!(link(&src, &out, &tools), Link::Kept);
    assert_eq!(says(&out), "open #1\n");
}

#[test]
fn the_list_of_either_linker_is_read() {
    let d = dir("lists").join("a #1 b");
    std::fs::create_dir_all(&d).unwrap();
    let (spaced, plain) = (d.join("lib c.a"), d.join("libd.a"));
    std::fs::write(&spaced, "").unwrap();
    std::fs::write(&plain, "").unwrap();
    let (spaced_s, plain_s) = (spaced.display(), plain.display());
    let gnu = format!("out: \\\n  {spaced_s} \\\n  {plain_s}\n\n{spaced_s}:\n\n{plain_s}:\n");
    let escape = |p: &Path| {
        p.display()
            .to_string()
            .replace('#', "\\#")
            .replace(' ', "\\ ")
    };
    let (spaced_e, plain_e) = (escape(&spaced), escape(&plain));
    let lld = format!("out: \\\n {spaced_e} \\\n {plain_e}\n\n{spaced_e}:\n\n{plain_e}:\n");
    for list in [gnu, lld] {
        assert_eq!(
            dependencies(list.as_bytes()).collect::<Vec<_>>(),
            [spaced.clone(), plain.clone()],
            "{list}"
        );
    }
    assert_eq!(
        dependencies(b"out:\n").count(),
        0,
        "a link that read nothing"
    );
    assert_eq!(dependencies(b"").count(), 0);
}

#[test]
fn each_file_is_hashed_once() {
    let d = dir("once");
    let (a, b, skipped) = (d.join("liba.a"), d.join("libb.a"), d.join("program.o"));
    std::fs::write(&a, "a").unwrap();
    std::fs::write(&b, "b").unwrap();
    std::fs::write(&skipped, "o").unwrap();
    let a_again = d.join(".").join("liba.a");
    let inputs = Inputs::of(
        [a.clone(), skipped.clone(), b.clone(), a_again, a.clone()],
        &[&skipped],
    )
    .unwrap();
    assert_eq!(inputs.paths, [a, b]);
    assert_eq!(
        inputs.hashes,
        [blake3::hash(b"a"), blake3::hash(b"b")],
        "the hash of each file's bytes"
    );
}

/// A driver at `path` that runs `cc` with `args` changed by the shell command `edit`, run on
/// each argument `$a` in turn, which passes it on with `set -- "$@" ...`; after each run of
/// `cc` that succeeds, `after` runs, with `$list` the path of the list of files the linker
/// read, empty for a run that is not a link.
fn wrapping(path: &Path, edit: &str, after: &str) {
    script(
        path,
        &format!(
            "list=\nfor a do\n  shift\n  case \"$a\" in --dependency-file=*) \
             list=\"${{a#--dependency-file=}}\" ;; esac\n  {edit}\ndone\ncc \"$@\" || exit\n\
             {after}\n"
        ),
    );
}

/// Building `src` into `out` with the driver at `driver`, which must fail; the status and
/// message.
fn refused(src: &Path, out: &Path, driver: &Path) -> (u8, String) {
    let tools = Toolchain {
        linker: driver.into(),
        ..toolchain()
    };
    zed_native::link::build(
        src.to_str().unwrap(),
        out,
        &[],
        &mut Default::default(),
        &tools,
        &mut Vec::new(),
    )
    .expect_err("refused")
}

#[test]
fn a_linker_that_lists_no_files_is_refused() {
    let d = dir("no_list");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("no list")).unwrap();
    let driver = d.join("cc-no-list");
    wrapping(
        &driver,
        "case \"$a\" in -Xlinker | --dependency-file=*) ;; *) set -- \"$@\" \"$a\" ;; esac",
        "",
    );
    let (status, why) = refused(&src, &out, &driver);
    assert_eq!(status, 1);
    assert_eq!(
        why,
        format!(
            "zedc could not finish {}: the linker `{}` wrote no list of the files it read (No \
             such file or directory (os error 2)), and zedc needs that list to tell when the \
             executable must be linked again. Repair: name in CC a C compiler whose linker \
             takes --dependency-file, as GNU ld 2.35 and later and LLD do",
            out.display(),
            driver.display()
        )
    );
}

#[test]
fn a_listed_file_that_cannot_be_read_is_refused() {
    let d = dir("gone");
    let (src, out, gone) = (d.join("sign.zed"), d.join("sign"), d.join("libgone.so"));
    std::fs::write(&src, sign("gone")).unwrap();
    let driver = d.join("cc-gone");
    wrapping(
        &driver,
        "set -- \"$@\" \"$a\"",
        &format!(
            "[ -z \"$list\" ] || printf 'out: \\\\\\n  %s\\n' '{}' > \"$list\"",
            gone.display()
        ),
    );
    let (status, why) = refused(&src, &out, &driver);
    assert_eq!(status, 1);
    assert_eq!(
        why,
        format!(
            "zedc could not finish {}: the linker `{}` read a file that cannot be read now ({}: \
             No such file or directory (os error 2)), and zedc reads every file a link read to \
             tell when the executable must be linked again. Repair: build again, after putting \
             back the file if it was moved or removed",
            out.display(),
            driver.display(),
            gone.display()
        )
    );
}

#[test]
fn a_linker_that_writes_no_build_id_is_refused() {
    let d = dir("no_build_id");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("no id")).unwrap();
    let driver = d.join("cc-no-id");
    wrapping(
        &driver,
        "case \"$a\" in -Wl,--build-id=*) set -- \"$@\" -Wl,--build-id=none ;; \
         *) set -- \"$@\" \"$a\" ;; esac",
        "",
    );
    let (status, why) = refused(&src, &out, &driver);
    assert_eq!(status, 1);
    assert_eq!(
        why,
        format!(
            "zedc could not finish {}: the linker `{}` wrote it without the build ID zedc gave \
             it, where zedc records which files the executable was linked from. Repair: name \
             in CC a C compiler whose linker takes --build-id",
            out.display(),
            driver.display()
        )
    );
}

/// An output may have any name, those the build once gave its object file and its other files
/// in the working directory among them (`program.o`, `read.d`, `record`): the link did not
/// overwrite its own input, and the record is not lost. The five builds run at once, beside
/// the source and each other.
#[test]
fn an_output_may_take_any_name() {
    let d = dir("any_name");
    let src = d.join("sign.zed");
    std::fs::write(&src, sign("any name")).unwrap();
    let tools = toolchain();
    let named = |name: &str| {
        let out = d.join(name);
        // An output that records no key, so the build links even where the run before left
        // the executable.
        std::fs::write(&out, "not yet built\n").unwrap();
        assert_eq!(link(&src, &out, &tools), Link::Ran, "{name}");
        assert_eq!(link(&src, &out, &tools), Link::Kept, "{name}");
        assert_eq!(says(&out), "any name\n", "{name}");
    };
    at_once(&[
        &|| named("program.o"),
        &|| named("read.d"),
        &|| named("record"),
        &|| named("sign.o"),
        &|| named("sign.zed-link"),
    ]);
}

/// GNU ld's default input object format, `GNUTARGET`, set to the format the link reads anyway:
/// the executable is the same program, and the key differs, since another value could change
/// how the linker reads its inputs. Set and unset, each on an output of its own, at once.
#[test]
fn another_input_format_links_again() {
    let d = dir("gnutarget");
    let src = d.join("sign.zed");
    std::fs::write(&src, sign("formats")).unwrap();
    let elf = Some(std::ffi::OsStr::new("elf64-x86-64"));
    let change = |name: &str, from, to| {
        let (out, changed) = (d.join(name), d.join(format!("{name}_changed")));
        let (from, to) = (with_env("GNUTARGET", from), with_env("GNUTARGET", to));
        relinks(&src, &out, &changed, &from, &to, name);
        assert_eq!(says(&changed), "formats\n");
    };
    at_once(&[&|| change("set", None, elf), &|| change("unset", elf, None)]);
}

/// A `$` in a path is written `$$` in the list, as in a makefile, and read back as one `$`.
#[test]
fn a_dollar_sign_in_a_listed_path_is_read() {
    let d = dir("dollar");
    let lib = d.join("lib$e.a");
    std::fs::write(&lib, "").unwrap();
    let doubled = lib.display().to_string().replace('$', "$$");
    let list = format!("out: \\\n {doubled}\n\n{doubled}:\n");
    assert_eq!(dependencies(list.as_bytes()).collect::<Vec<_>>(), [lib]);
}

/// A record of a link that read no file besides its object file and the runtime library reads
/// back with no paths.
#[test]
fn a_record_naming_no_files_reads_back() {
    let out = dir("empty_record").join("sign");
    let record = Record {
        output: blake3::hash(b"an executable"),
        inputs: Vec::new(),
    };
    std::fs::write(Record::path(&out), record.to_bytes()).unwrap();
    assert_eq!(Record::read(&out), Some(record));
}

/// A record naming a file that is gone since the link, the executable and every other input
/// as they were: the output is not kept, and the build links again, after which it is kept.
#[test]
fn a_record_naming_a_file_that_is_gone_links_again() {
    let d = dir("gone");
    let (src, out, copy) = (d.join("sign.zed"), d.join("sign"), d.join("sign-copy"));
    std::fs::write(&src, sign("closed")).unwrap();
    let tools = toolchain();
    link(&src, &out, &tools);
    copied(&out, &copy);
    let mut record = Record::read(&copy).expect("a link leaves its record");
    record.inputs.push(d.join("no-such-library.a"));
    std::fs::write(Record::path(&copy), record.to_bytes()).unwrap();
    assert_eq!(link(&src, &copy, &tools), Link::Ran);
    assert_eq!(link(&src, &copy, &tools), Link::Kept);
    assert_eq!(says(&copy), "closed\n");
}
