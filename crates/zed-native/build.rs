//! Writes `rustflags.rs` into `OUT_DIR`: a hash of the flags Cargo passes to the compiler
//! (`CARGO_ENCODED_RUSTFLAGS`, which holds `RUSTFLAGS` and `build.rustflags`), for
//! `link::BUILD`. The crate's own hash, which Cargo computes from its features, its
//! dependencies' builds, the profile, the target and the compiler, leaves those flags out
//! (measured with Cargo 1.99), so two builds that differ only in them are told apart by this.

fn main() {
    let flags = std::env::var_os("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default();
    // FNV-1a, 64 bits: fixed by its definition, so the same flags give the same bytes with
    // any compiler.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for b in flags.as_encoded_bytes() {
        hash = (hash ^ u64::from(*b)).wrapping_mul(0x0100_0000_01b3);
    }
    let out = std::path::PathBuf::from(
        std::env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR for a build script"),
    )
    .join("rustflags.rs");
    std::fs::write(&out, format!("{:?}", hash.to_le_bytes()))
        .unwrap_or_else(|e| panic!("{}: {e}", out.display()));
    // Cargo runs this script in a directory of its own for each set of compiler flags
    // (measured with Cargo 1.99, with and without `--target`), so it need not run again
    // unless it changes.
    println!("cargo::rerun-if-changed=build.rs");
}
