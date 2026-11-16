//! A build links with LLD when `ld.lld` is on `PATH`, and with the driver's own linker, GNU ld,
//! when it is not (LINK-lld-when-present, `zed_native::link::Ld`). Each linker's executables
//! give the same output, record a key of their own as their build ID, are the same bytes when
//! built twice, and are kept by a build that would link them again.

use std::path::Path;

use zed_native::link::{Identity, Ld, Toolchain, recorded};
use zed_tests::oracle;

use super::{Link, at_once, copied, dir, executable, link, script, sign, toolchain};

/// The system's toolchain with the linker `ld`.
fn with(ld: Ld) -> Toolchain {
    Toolchain { ld, ..toolchain() }
}

/// Whether the executable `exe` was linked by LLD, which writes `Linker: LLD <version>` in the
/// section `.comment`; GNU ld writes nothing there of its own.
fn by_lld(exe: &Path) -> bool {
    let bytes = std::fs::read(exe).unwrap();
    bytes
        .windows(b"Linker: LLD".len())
        .any(|w| w == b"Linker: LLD")
}

#[test]
fn lld_is_found_only_as_a_runnable_file_in_a_directory_of_the_path() {
    let d = dir("ld_on_path");
    let (with_lld, without, not_runnable, a_directory) = (
        d.join("with"),
        d.join("without"),
        d.join("not_runnable"),
        d.join("a_directory"),
    );
    for dir in [&with_lld, &without, &not_runnable, &a_directory] {
        std::fs::create_dir_all(dir).unwrap();
    }
    script(&with_lld.join("ld.lld"), "exec /usr/bin/ld.lld \"$@\"\n");
    std::fs::write(not_runnable.join("ld.lld"), "not a program\n").unwrap();
    std::fs::create_dir_all(a_directory.join("ld.lld")).unwrap();
    let path = |dirs: &[&Path]| std::env::join_paths(dirs).unwrap();
    let on = |dirs: &[&Path]| Ld::on_path(Some(&path(dirs)));
    assert_eq!(Ld::on_path(None), Ld::Driver, "no PATH");
    assert_eq!(Ld::on_path(Some("".as_ref())), Ld::Driver, "an empty PATH");
    assert_eq!(on(&[&without]), Ld::Driver);
    assert_eq!(on(&[&not_runnable, &a_directory]), Ld::Driver);
    assert_eq!(
        on(&[&without, &with_lld]),
        Ld::Lld,
        "found in a later directory"
    );
    // An empty entry, the working directory to a shell, is skipped, whatever it holds.
    assert_eq!(on(&[Path::new(""), &without]), Ld::Driver);
    // This machine has LLD, so the tests of this step link with both linkers; without it they
    // would link with one twice and test nothing of the other.
    assert_eq!(
        Ld::from_env(),
        Ld::Lld,
        "ld.lld is on PATH (Fedora package lld), as the tests of both linkers need"
    );
}

/// Each linker's prelinked runtime has a key of its own, so both are kept beside one library,
/// and the driver's own linker has the key it had before LLD was chosen.
#[test]
fn each_linker_has_its_own_identity() {
    let (lld, gnu) = (
        Identity::of(&with(Ld::Lld)).unwrap(),
        Identity::of(&with(Ld::Driver)).unwrap(),
    );
    assert_eq!(lld.runtime, gnu.runtime);
    assert_ne!(
        lld.linker[1], gnu.linker[1],
        "-Wl,--version names the linker"
    );
    assert!(
        String::from_utf8_lossy(&lld.linker[1]).contains("LLD"),
        "{}",
        String::from_utf8_lossy(&lld.linker[1])
    );
    assert_ne!(lld.prelink_key(), gnu.prelink_key());
    // The reports alike, the flag alone tells the keys apart.
    let reported_alike = Identity {
        ld: Ld::Driver,
        ..lld.clone()
    };
    assert_ne!(reported_alike.prelink_key(), lld.prelink_key());
    assert_ne!(reported_alike.key(b"o", &[]), lld.key(b"o", &[]));
}

/// For each linker at once: one program built at two outputs at once gives the same bytes and
/// the same key; a build that would link it again keeps it; an edit on a copy links again with
/// another key. The two linkers' executables say the same, and record different keys.
#[test]
fn both_linkers_build_reproducibly_and_keep_their_builds() {
    let d = dir("linkers");
    let src = d.join("sign.zed");
    std::fs::write(&src, sign("open late")).unwrap();
    let edited_src = d.join("edited.zed");
    std::fs::write(&edited_src, sign("closed")).unwrap();
    let (lld, gnu) = (with(Ld::Lld), with(Ld::Driver));
    let each = |name: &str, tools: &Toolchain| {
        let (one, two, edited) = (
            d.join(format!("{name}-one")),
            d.join(format!("{name}-two")),
            d.join(format!("{name}-edited")),
        );
        at_once(&[&|| link(&src, &one, tools), &|| link(&src, &two, tools)]);
        assert_eq!(
            std::fs::read(&one).unwrap(),
            std::fs::read(&two).unwrap(),
            "{name}: two builds, the same bytes"
        );
        let key = recorded(&one).expect("a build ID");
        assert_eq!(recorded(&two).as_ref(), Some(&key));
        assert_eq!(
            link(&src, &one, tools),
            Link::Kept,
            "{name}: nothing changed"
        );
        copied(&one, &edited);
        assert_eq!(
            link(&edited_src, &edited, tools),
            Link::Ran,
            "{name}: edited"
        );
        assert_ne!(recorded(&edited).as_ref(), Some(&key));
        assert_eq!(executable(&edited, &[], b"").stdout, "closed\n");
        (executable(&one, &[], b""), key, by_lld(&one))
    };
    let ran = at_once(&[&|| each("lld", &lld), &|| each("gnu", &gnu)]);
    let ((lld_ran, lld_key, lld_by), (gnu_ran, gnu_key, gnu_by)) = (&ran[0], &ran[1]);
    assert_eq!(
        (lld_ran.status, lld_ran.stdout.as_str()),
        (0, "open late\n")
    );
    assert_eq!(lld_ran, gnu_ran, "both linkers' executables say the same");
    assert_ne!(lld_key, gnu_key, "each linker's link has a key of its own");
    assert_eq!(
        (*lld_by, *gnu_by),
        (true, false),
        "each linked by its linker"
    );
}

/// The step program fahrenheit, linked by each linker, gives the same output and exit status
/// on every corpus input.
#[test]
fn both_linkers_executables_agree_on_the_corpus() {
    let d = dir("linkers_corpus");
    let src = oracle::step_units()
        .into_iter()
        .find(|p| p.file_stem().is_some_and(|s| s == "fahrenheit"))
        .unwrap();
    let (lld, gnu) = (d.join("fahrenheit-lld"), d.join("fahrenheit-gnu"));
    at_once(&[&|| link(&src, &lld, &with(Ld::Lld)), &|| {
        link(&src, &gnu, &with(Ld::Driver))
    }]);
    assert_eq!((by_lld(&lld), by_lld(&gnu)), (true, false));
    let corpus = oracle::corpus();
    assert_eq!(corpus.len(), 31);
    std::thread::scope(|s| {
        for (c, _) in &corpus {
            let (lld, gnu) = (&lld, &gnu);
            s.spawn(move || {
                let input = std::fs::read(oracle::corpus_file(c, "in")).unwrap();
                assert_eq!(
                    executable(lld, &[], &input),
                    executable(gnu, &[], &input),
                    "{}",
                    c.display()
                );
            });
        }
    });
}
