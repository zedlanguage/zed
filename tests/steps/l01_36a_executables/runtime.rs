//! The runtime library a build links with is the one built with the executable that generates
//! the code (`zed_native::link::runtime_of`). Cargo keeps a `libzed_native-<hash>.a` for each
//! set of features it has built zed-native with (this test binary's, `zedc`'s, one with
//! `short-addresses`), so the newest of them, or the first by name, can be another build's.

use std::path::{Path, PathBuf};

use object::write::{Object, StandardSection, Symbol, SymbolSection};
use object::{Architecture, BinaryFormat, Endianness, SymbolFlags, SymbolKind, SymbolScope};
use zed_native::link::{Toolchain, build, build_symbol, runtime_of};
use zed_tests::scaling::{self, FACTOR};

use super::dir;

/// A GNU archive whose symbol table names `symbols`, each in its one empty member.
fn archive(symbols: &[Vec<u8>]) -> Vec<u8> {
    let header = |name: &str, size: usize| {
        format!("{name:<16}{:<12}{:<6}{:<6}{:<8}{size:<10}`\n", 0, 0, 0, 644)
    };
    let mut table = u32::try_from(symbols.len()).unwrap().to_be_bytes().to_vec();
    let names: usize = symbols.iter().map(|s| s.len() + 1).sum();
    let size = 4 + 4 * symbols.len() + names;
    // The member follows the magic, the table's header and the table, padded to an even size.
    let member = u32::try_from(8 + 60 + size + size % 2).unwrap();
    for _ in symbols {
        table.extend(member.to_be_bytes());
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
    a.extend(header("m.o/", 0).as_bytes());
    a
}

/// An ELF object file defining `symbols` in its text section.
fn object_file(symbols: &[Vec<u8>]) -> Vec<u8> {
    let mut o = Object::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
    let text = o.section_id(StandardSection::Text);
    o.append_section_data(text, &[0xc3], 1);
    for name in symbols {
        o.add_symbol(Symbol {
            name: name.clone(),
            value: 0,
            size: 1,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
    }
    o.write().unwrap()
}

/// `zed_native::link::build`'s symbol as a build of zed-native with another hash names it.
fn of_another_build(own: &[u8]) -> Vec<u8> {
    let mut other = own.to_vec();
    // The last character of the hash: before `_10zed_native…` in Rust's own mangling, before
    // the closing `E` in the older one.
    let at = if own.starts_with(b"_RNvNtCs") {
        own.len() - b"_10zed_native4link5build".len() - 1
    } else {
        own.len() - 2
    };
    other[at] = if other[at] == b'0' { b'1' } else { b'0' };
    other
}

/// This test executable, the runtime library built with it, and a directory holding a link to
/// that library and a newer library of another build that sorts before it by name.
fn with_a_newer_library_of_another_build(name: &str) -> (PathBuf, PathBuf, PathBuf, PathBuf) {
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
    let other = d.join("libzed_native-0000000000000000.a");
    let symbol = build_symbol(&exe).unwrap();
    std::fs::write(&other, archive(&[of_another_build(&symbol)])).unwrap();
    // The link reads as its library, which is older than the one just written.
    let time = |p: &Path| std::fs::metadata(p).unwrap().modified().unwrap();
    assert!(time(&other) > time(&ours));
    (exe, d, ours, other)
}

#[test]
fn the_library_built_with_this_executable_is_picked_over_a_newer_one() {
    let (exe, d, ours, _) = with_a_newer_library_of_another_build("newer");
    assert_eq!(runtime_of(&exe, &d), Ok(ours));
}

#[test]
fn a_build_refuses_a_library_of_another_build() {
    let (exe, d, _, other) = with_a_newer_library_of_another_build("refused");
    let src = d.join("quiet.zed");
    std::fs::write(&src, "main() -> (stdout: Lines) {\n  stdout <- \"x\";\n}\n").unwrap();
    let out = d.join("quiet");
    let tools = Toolchain {
        linker: "cc".into(),
        runtime: other.clone(),
    };
    assert_eq!(
        build(src.to_str().unwrap(), &out, &tools, &mut Vec::new()),
        Err((
            2,
            format!(
                "the runtime library {} is from another build of zed-native than {}: build \
                 both with `cargo build -p zed-native`, or name the matching one in ZED_RUNTIME",
                other.display(),
                exe.display()
            )
        ))
    );
    assert!(!out.exists());
}

#[test]
fn no_library_of_this_build_is_an_error_naming_the_directory() {
    let exe = std::env::current_exe().unwrap();
    let d = dir("none");
    let symbol = build_symbol(&exe).unwrap();
    std::fs::write(
        d.join("libzed_native-0000000000000000.a"),
        archive(&[of_another_build(&symbol)]),
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
fn an_executable_without_the_symbol_is_an_error_naming_it() {
    let d = dir("stripped");
    let exe = d.join("stripped.o");
    std::fs::write(&exe, object_file(&[b"main".to_vec()])).unwrap();
    assert_eq!(
        build_symbol(&exe),
        Err(format!(
            "{} has no symbol for zed_native::link::build, so the runtime library built with \
             it cannot be found: it was stripped, or it does not hold zed-native",
            exe.display()
        ))
    );
}

/// Finding the library reads each symbol table once: linear in the symbols of the executable
/// and of the libraries.
#[test]
fn finding_the_library_scales() {
    let n = 20_000;
    let own = b"_RNvNtCs1b1S38cFQTP_10zed_native4link5build".to_vec();
    // Each file of a size, made before the runs are measured: an object file and an archive
    // of m symbols, `build`'s last, and an archive of another build's m symbols before it.
    let made = |m: usize| -> (PathBuf, PathBuf) {
        let d = dir(&format!("scaling{m}"));
        let mut symbols: Vec<Vec<u8>> = (1..m)
            .map(|i| format!("_RNvNtCs1b1S38cFQTP_10zed_native4link1f{i}").into_bytes())
            .collect();
        let mut others = symbols.clone();
        others.push(of_another_build(&own));
        symbols.push(own.clone());
        let exe = d.join("exe.o");
        std::fs::write(&exe, object_file(&symbols)).unwrap();
        std::fs::write(d.join("libzed_native-0.a"), archive(&others)).unwrap();
        std::fs::write(d.join("libzed_native-1.a"), archive(&symbols)).unwrap();
        (exe, d)
    };
    let (small, large) = (made(n), made(FACTOR * n));
    scaling::check("finding the runtime library among n symbols", n, |m| {
        let (exe, d) = if m == n { &small } else { &large };
        assert_eq!(runtime_of(exe, d), Ok(d.join("libzed_native-1.a")));
    });
}
