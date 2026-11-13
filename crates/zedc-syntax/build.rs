//! Reads the syntactic grammar and the documentation notation from the spec's DESIGN.md
//! (`spec_grammar.rs`) and writes them into `OUT_DIR` as `syntax.peg` and `notation.peg`, which
//! `parse::tree::grammar` embeds. Nothing is written inside the repository: the spec is kept
//! only in its own repository. Without the spec the build fails, naming `ZED_SPEC_DIR`.

#[path = "spec_grammar.rs"]
mod spec_grammar;

fn main() {
    let krate = std::path::PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"),
    );
    println!("cargo::rerun-if-env-changed={}", spec_grammar::VAR);
    let grammar = spec_grammar::read(&krate).unwrap_or_else(|e| panic!("{e}"));
    println!("cargo::rerun-if-changed={}", grammar.design.display());
    let out_dir = std::path::PathBuf::from(
        std::env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR for a build script"),
    );
    for (name, text) in [
        ("syntax.peg", &grammar.syntax),
        ("notation.peg", &grammar.notation),
    ] {
        let out = out_dir.join(name);
        std::fs::write(&out, text).unwrap_or_else(|e| panic!("{}: {e}", out.display()));
    }
}
