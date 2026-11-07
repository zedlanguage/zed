//! The runtime library a build links with is the one built with the executable that generates
//! the code (`zed_native::link::runtime_of`). Cargo keeps a `libzed_native-<hash>.a` for each
//! set of features it has built zed-native with (this test binary's, `zedc`'s, one with
//! `short-addresses`), and one for each set of compiler flags, so the newest of them, or the
//! first by name, can be another build's. Each file names its build in the section
//! `.zed_native.build` (`zed_native::link::BUILD`), which `strip` keeps (NATIVE-build-id).

use std::path::{Path, PathBuf};

use object::write::{Object, StandardSection, Symbol, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, SectionKind, SymbolFlags, SymbolKind, SymbolScope,
};
use zed_native::link::{BUILD, SECTION, Toolchain, build, build_id, runtime_of};
use zed_tests::scaling::{self, FACTOR};

use super::dir;

/// `zed_native::link::BUILD`'s name in an archive's symbol index, as Rust mangles it.
const BUILD_SYMBOL: &[u8] = b"_RNvNtCs1b1S38cFQTP_10zed_native4link5BUILD";

/// A GNU archive of the one member `member`, whose symbol table names `symbols`, each in it.
fn archive(symbols: &[Vec<u8>], member: &[u8]) -> Vec<u8> {
    let header = |name: &str, size: usize| {
        format!("{name:<16}{:<12}{:<6}{:<6}{:<8}{size:<10}`\n", 0, 0, 0, 644)
    };
    let mut table = u32::try_from(symbols.len()).unwrap().to_be_bytes().to_vec();
    let names: usize = symbols.iter().map(|s| s.len() + 1).sum();
    let size = 4 + 4 * symbols.len() + names;
    // The member follows the magic, the table's header and the table, padded to an even size.
    let at = u32::try_from(8 + 60 + size + size % 2).unwrap();
    for _ in symbols {
        table.extend(at.to_be_bytes());
    }
    for s in symbols {
        table.extend(s);
        table.push(0);
    }
    let mut a = b"!<arch>\n".to_vec();
    a.extend(header("/", size).as_bytes());
    a.extend(table);
    if size % 2 == 1 {
        a.push(b'\n');
    }
    a.extend(header("m.o/", member.len()).as_bytes());
    a.extend(member);
    a
}

/// An ELF object file defining `symbols` in its text section and, given a build, holding it in
/// `.zed_native.build` under `BUILD`'s symbol.
fn object_file(symbols: &[Vec<u8>], build: Option<&[u8]>) -> Vec<u8> {
    let mut o = Object::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
    let text = o.section_id(StandardSection::Text);
    o.append_section_data(text, &[0xc3], 1);
    let symbol = |name: &[u8], kind, section| Symbol {
        name: name.to_vec(),
        value: 0,
        size: 1,
        kind,
        scope: SymbolScope::Linkage,
        weak: false,
        section: SymbolSection::Section(section),
        flags: SymbolFlags::None,
    };
    for name in symbols {
        o.add_symbol(symbol(name, SymbolKind::Text, text));
    }
    if let Some(id) = build {
        let s = o.add_section(Vec::new(), SECTION.as_bytes().to_vec(), SectionKind::Data);
        o.append_section_data(s, id, 8);
        o.add_symbol(symbol(BUILD_SYMBOL, SymbolKind::Data, s));
    }
    o.write().unwrap()
}

/// A runtime library holding the build `id`, its index naming `others` before `BUILD`.
fn library(others: &[Vec<u8>], id: &[u8]) -> Vec<u8> {
    let mut symbols = others.to_vec();
    symbols.push(BUILD_SYMBOL.to_vec());
    archive(&symbols, &object_file(&[], Some(id)))
}

/// The build `id` with its byte `at` changed: the crate's hash for `at` below 16, the
/// compiler's flags above (`zed_native::link::Build`).
fn changed(id: &[u8], at: usize) -> Vec<u8> {
    let mut other = id.to_vec();
    other[at] ^= 1;
    other
}

/// Another build than `id`: the same features and dependencies, other compiler flags.
fn of_other_flags(id: &[u8]) -> Vec<u8> {
    changed(id, id.len() - 1)
}

/// This test executable, the runtime library built with it, and a directory holding a link to
/// that library and a newer library of `other`'s build that sorts before it by name.
fn with_a_newer_library(
    name: &str,
    other: fn(&[u8]) -> Vec<u8>,
) -> (PathBuf, PathBuf, PathBuf, PathBuf) {
    let exe = std::env::current_exe().unwrap();
    let own = runtime_of(&exe, exe.parent().unwrap()).unwrap();
    let d = dir(name);
    let ours = d.join("libzed_native-ffffffffffffffff.a");
    // The link of an earlier run is replaced, so it names this build's library.
    match std::fs::remove_file(&ours) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => panic!("{}: {e}", ours.display()),
        _ => {}
    }
    std::os::unix::fs::symlink(&own, &ours).unwrap();
    let decoy = d.join("libzed_native-0000000000000000.a");
    std::fs::write(&decoy, library(&[], &other(&build_id(&exe).unwrap()))).unwrap();
    // The link reads as its library, which is older than the one just written.
    let time = |p: &Path| std::fs::metadata(p).unwrap().modified().unwrap();
    assert!(time(&decoy) > time(&ours));
    (exe, d, ours, decoy)
}

#[test]
fn this_executable_holds_its_build() {
    let id = build_id(&std::env::current_exe().unwrap()).unwrap();
    assert_eq!(id.len(), std::mem::size_of_val(&BUILD));
}

#[test]
fn the_library_built_with_this_executable_is_picked_over_a_newer_one() {
    let (exe, d, ours, _) = with_a_newer_library("newer", |id| changed(id, 0));
    assert_eq!(runtime_of(&exe, &d), Ok(ours));
}

#[test]
fn a_library_built_with_other_compiler_flags_is_not_picked() {
    let (exe, d, ours, _) = with_a_newer_library("flags", of_other_flags);
    assert_eq!(runtime_of(&exe, &d), Ok(ours));
}

#[test]
fn a_build_refuses_a_library_of_another_build() {
    for (name, other) in [
        ("refused", (|id| changed(id, 0)) as fn(&[u8]) -> Vec<u8>),
        ("refused-flags", of_other_flags),
    ] {
        let (exe, d, _, decoy) = with_a_newer_library(name, other);
        let src = d.join("quiet.zed");
        std::fs::write(&src, "main() -> (stdout: Lines) {\n  stdout <- \"x\";\n}\n").unwrap();
        let out = d.join("quiet");
        let tools = Toolchain {
            linker: "cc".into(),
            runtime: decoy.clone(),
            env: zed_native::link::driver_env(),
        };
        assert_eq!(
            build(
                src.to_str().unwrap(),
                &out,
                &mut Default::default(),
                &tools,
                &mut Vec::new()
            ),
            Err((
                2,
                format!(
                    "the runtime library {} is from another build of zed-native than {}: build \
                     both with `cargo build -p zed-native`, or name the matching one in ZED_RUNTIME",
                    decoy.display(),
                    exe.display()
                )
            ))
        );
        assert!(!out.exists());
    }
}

#[test]
fn no_library_of_this_build_is_an_error_naming_the_directory() {
    let exe = std::env::current_exe().unwrap();
    let d = dir("none");
    let id = build_id(&exe).unwrap();
    std::fs::write(
        d.join("libzed_native-0000000000000000.a"),
        library(&[], &of_other_flags(&id)),
    )
    .unwrap();
    // A library whose index names no `BUILD`, as one from before NATIVE-build-id.
    std::fs::write(
        d.join("libzed_native-1111111111111111.a"),
        archive(&[b"main".to_vec()], &object_file(&[b"main".to_vec()], None)),
    )
    .unwrap();
    assert_eq!(
        runtime_of(&exe, &d),
        Err(format!(
            "no runtime library in {} was built with {}: build it with `cargo build -p zed-native`",
            d.display(),
            exe.display()
        ))
    );
}

#[test]
fn a_build_without_symbols_is_read_by_its_section() {
    let d = dir("stripped");
    let id = build_id(&std::env::current_exe().unwrap()).unwrap();
    let mut o = Object::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
    let s = o.add_section(Vec::new(), SECTION.as_bytes().to_vec(), SectionKind::Data);
    o.append_section_data(s, &id, 8);
    let exe = d.join("stripped.o");
    std::fs::write(&exe, o.write().unwrap()).unwrap();
    assert_eq!(build_id(&exe), Ok(id.clone()));
    std::fs::write(d.join("libzed_native-0.a"), library(&[], &id)).unwrap();
    assert_eq!(runtime_of(&exe, &d), Ok(d.join("libzed_native-0.a")));
}

#[test]
fn a_file_without_the_section_is_an_error_naming_it() {
    let d = dir("no-section");
    let exe = d.join("plain.o");
    std::fs::write(&exe, object_file(&[b"main".to_vec()], None)).unwrap();
    assert_eq!(
        build_id(&exe),
        Err(format!(
            "{} has no section .zed_native.build, which names the build of zed-native it \
             holds, so the runtime library built with it cannot be found: it does not hold \
             zed-native",
            exe.display()
        ))
    );
}

/// Finding the library reads the executable's section headers and each library's symbol
/// index once, and only the member that defines `BUILD`: linear in the symbols of the
/// executable and of the libraries' indexes.
#[test]
fn finding_the_library_scales() {
    let n = 20_000;
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
