//! Writes two files into `OUT_DIR` for `link::BUILD`, which together with the crate's own hash
//! name the build of this crate:
//!
//! - `rustflags.rs`: a hash of the flags Cargo passes to the compiler (`CARGO_ENCODED_RUSTFLAGS`,
//!   which holds `RUSTFLAGS` and `build.rustflags`). The crate's own hash, which Cargo computes
//!   from its features, its dependencies' builds, the profile, the target and the compiler,
//!   leaves those flags out (measured with Cargo 1.99), so two builds that differ only in them
//!   are told apart by this.
//! - `sources.rs`: the BLAKE3 hash of the sources of this crate and of the workspace crates it
//!   depends on (`sources::of`, RUNTIME-build-src). The crate's own hash leaves out the contents
//!   of every source file, so two builds that differ only in them are told apart by this. The
//!   compiler's grammar, which `zedc-syntax`'s build script reads from the spec's DESIGN.md
//!   outside the workspace, is read here the same way and added (`sources::with_grammar`).

#[path = "src/sources.rs"]
mod sources;

#[path = "../zedc-syntax/spec_grammar.rs"]
mod spec_grammar;

fn main() {
    let flags = std::env::var_os("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default();
    // FNV-1a, 64 bits: fixed by its definition, so the same flags give the same bytes with
    // any compiler.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for b in flags.as_encoded_bytes() {
        hash = (hash ^ u64::from(*b)).wrapping_mul(0x0100_0000_01b3);
    }
    let out_dir = std::path::PathBuf::from(
        std::env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR for a build script"),
    );
    let write = |name: &str, text: String| {
        let out = out_dir.join(name);
        std::fs::write(&out, text).unwrap_or_else(|e| panic!("{}: {e}", out.display()));
    };
    write("rustflags.rs", format!("{:?}", hash.to_le_bytes()));

    let krate = std::path::PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"),
    );
    let sources = sources::of(&krate).unwrap_or_else(|e| panic!("the sources of zed-native: {e}"));
    println!("cargo::rerun-if-env-changed={}", spec_grammar::VAR);
    let grammar = spec_grammar::read(&krate).unwrap_or_else(|e| panic!("{e}"));
    println!("cargo::rerun-if-changed={}", grammar.design.display());
    let hash = sources::with_grammar(sources.hash, &[&grammar.syntax, &grammar.notation]);
    write("sources.rs", format!("{hash:?}"));
    // Cargo runs this script in a directory of its own for each set of compiler flags
    // (measured with Cargo 1.99, with and without `--target`), so for the flags it need not
    // run again; for the sources it runs again when a file read changes, or a file is added
    // to a directory listed. `sources.read` holds this script and `src/sources.rs`.
    for path in &sources.read {
        println!("cargo::rerun-if-changed={}", path.display());
    }
}
