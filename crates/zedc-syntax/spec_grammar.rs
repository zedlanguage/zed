//! The compiler's grammar, read from the spec when the compiler is built. The spec repository
//! (DESIGN.md) is not part of this repository and no copy of it is kept here, so the build
//! scripts of `zedc-syntax`, which embeds the grammar, and of `zed-native`, whose hash of the
//! sources a build is made from must change with it, each compile this file as a module of its
//! own and read the grammar in place.
//!
//! The spec is the directory named by `ZED_SPEC_DIR` when that is set, and otherwise the first
//! directory `zed` holding DESIGN.md beside the crate's workspace or beside one of its
//! ancestors: the walk of `zed_tests::spec::locate`, written again here because a build script
//! cannot use the test crate. Its grammars are the second and third ```` ```peg ```` fences of
//! DESIGN.md (sec:grammar: the syntactic grammar and the documentation notation), found as
//! `zed_tools::spec::fence_texts` finds them; `zed-tools` cannot be used either, since it
//! depends on `zedc`.

use std::path::{Path, PathBuf};

/// The environment variable that names the spec repository.
pub const VAR: &str = "ZED_SPEC_DIR";

/// The grammar of the spec, and the file it was read from.
pub struct SpecGrammar {
    /// The DESIGN.md read, which a build script names to Cargo with `cargo::rerun-if-changed`.
    pub design: PathBuf,
    /// The syntactic grammar, with a final newline.
    pub syntax: String,
    /// The documentation notation, with a final newline.
    pub notation: String,
}

/// Reads the grammar of the spec for the crate in directory `krate`; the error says, in full,
/// what was looked for and how to name the spec.
pub fn read(krate: &Path) -> Result<SpecGrammar, String> {
    let design = locate(std::env::var_os(VAR), krate)?;
    let text = std::fs::read_to_string(&design)
        .map_err(|e| format!("{}: {e}", design.display()))?
        .replace("\r\n", "\n")
        .replace('\r', "\n");
    let mut pegs = peg_fences(&text).into_iter().skip(1);
    let (Some(syntax), Some(notation)) = (pegs.next(), pegs.next()) else {
        return Err(format!(
            "{} has fewer than three ```peg fences, so it holds no grammar for the compiler; \
             set {VAR} to the spec repository",
            design.display()
        ));
    };
    Ok(SpecGrammar {
        design,
        syntax: syntax + "\n",
        notation: notation + "\n",
    })
}

/// The DESIGN.md of the spec, given `var`, the value of [`VAR`]: in that directory where it is
/// set, and otherwise in the first `zed` directory beside `krate` or one of its ancestors.
fn locate(var: Option<std::ffi::OsString>, krate: &Path) -> Result<PathBuf, String> {
    if let Some(var) = var {
        let design = PathBuf::from(&var).join("DESIGN.md");
        return if design.is_file() {
            Ok(design)
        } else {
            Err(format!(
                "the compiler's grammar is read from the spec repository, and {VAR}={var:?}, but \
                 {} is not a file; set {VAR} to the directory holding DESIGN.md",
                design.display()
            ))
        };
    }
    let mut tried = Vec::new();
    for up in krate.ancestors().skip(1) {
        let design = up.join("zed/DESIGN.md");
        if design.is_file() {
            return Ok(design);
        }
        tried.push(design.display().to_string());
    }
    Err(format!(
        "the compiler's grammar is read from the spec repository, and none was found: {VAR} is \
         not set, and none of {} is a file; set {VAR} to the directory holding DESIGN.md",
        tried.join(", ")
    ))
}

/// The text of each ```` ```peg ```` fence of `text`, in order: the lines between a line
/// ```` ```peg ```` and the next line ```` ``` ````, each delimiter read with the white space
/// around it trimmed. An unclosed fence is not counted. One pass over `text`.
fn peg_fences(text: &str) -> Vec<String> {
    fn trim(l: &str) -> &str {
        l.trim_matches(|c: char| c.is_whitespace() || ('\x1c'..='\x1f').contains(&c))
    }
    let mut out = Vec::new();
    let mut body: Option<Vec<&str>> = None;
    for l in text.split('\n') {
        match &mut body {
            None if trim(l) == "```peg" => body = Some(Vec::new()),
            None => {}
            Some(b) if trim(l) == "```" => {
                out.push(b.join("\n"));
                body = None;
            }
            Some(b) => b.push(l),
        }
    }
    out
}
