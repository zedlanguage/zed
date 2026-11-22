//! Which linker made an executable, from the string LLD writes in its section `.comment`. Shared
//! by the test target `build_binary` of zed-native (tests/steps/l01_36a_executables/binary.rs,
//! which includes this file by `#[path]`, as zed-native cannot depend on zed-tests) and by step
//! L1.36b (tests/steps/l01_36b_link_identity/linkers.rs, through `zed_tests::linker_comment`).

/// Whether `bytes` (an executable, or its section `.comment`) holds LLD's linker string:
/// `Linker: LLD <version>` from an LLVM build (Fedora 44: `Linker: LLD 22.1.8`, measured the same
/// way), or
/// `Linker: <vendor> LLD <version>` from a distribution's build (Ubuntu 24.04:
/// `Linker: Ubuntu LLD 18.1.3`, read with `readelf -p .comment` on a Colab VM, b22-farm1
/// 2026-11-22, where `ld.lld --version` printed `Ubuntu LLD 18.1.3 (compatible with GNU
/// linkers)`). The vendor is one word of letters, digits, `-` or `_`. Before this, the tests
/// asked for the bytes `Linker: LLD` and read Ubuntu's LLD executables as GNU ld's
/// (build_binary at binary.rs:168 and l01_36b at linkers.rs:140, merge check of 2026-11-22). GNU
/// ld writes no `Linker:` string: the `.comment` of its executables holds only the compilers'
/// `GCC: (...) <version>`, so they read false.
pub fn names_lld(bytes: &[u8]) -> bool {
    const HEAD: &[u8] = b"Linker: ";
    (0..bytes.len())
        .filter(|&i| bytes[i..].starts_with(HEAD))
        .any(|i| {
            let rest = &bytes[i + HEAD.len()..];
            let word = rest
                .iter()
                .take_while(|b| b.is_ascii_alphanumeric() || **b == b'-' || **b == b'_')
                .count();
            rest.starts_with(b"LLD") || (word > 0 && rest[word..].starts_with(b" LLD"))
        })
}
