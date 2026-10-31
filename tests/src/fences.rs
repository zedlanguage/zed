//! The documentation's fences, copied from the spec into `zed/fences/` by
//! `tools/bin/sync.dart` (step L1.7), and the hand-written fixtures of their commented ✗ variants.

use std::path::PathBuf;

use zedc::fence;

/// A fence of DESIGN.md or EXAMPLES.md, with what `tools/bin/sync.dart` recorded about it.
#[derive(Clone, Debug)]
pub struct DocFence {
    /// The document and line of its ```` ```zed ````: `DESIGN.md:196`.
    pub at: String,
    /// The layer from which it is parsed, checked and run.
    pub layer: u32,
    /// The lowest ring of sec:grammar at which it parses.
    pub ring: u32,
    /// Whether it parses only under the documentation notation of sec:grammar.
    pub notation: bool,
    /// Its text.
    pub text: String,
}

/// A rejected variant: a fence with one commented ✗ line made live.
#[derive(Clone, Debug)]
pub struct Variant {
    /// The fixture's file name, without `.zed`.
    pub name: String,
    /// The commented line of the fence it is a variant of, trimmed.
    pub of: String,
    /// The fixture's text, its first line, `// variant: …`, included.
    pub text: String,
}

/// The directory `zed/fences/`.
pub fn dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/fences")
}

/// The fences of the copy `file` (`design.md` or `examples.md`), in order.
pub fn of(file: &str) -> Vec<DocFence> {
    let md = std::fs::read_to_string(dir().join(file)).expect("the fence copy is readable");
    fence::extract(&md)
        .into_iter()
        .map(|f| {
            let head = f
                .before
                .strip_prefix("<!-- ")
                .unwrap_or_else(|| panic!("no header before the fence at line {}", f.line));
            let (at, rest) = head.split_once(" layer L").expect("a layer");
            let layer = rest[..rest.find(':').expect("a `:`")]
                .parse()
                .expect("a layer number");
            let ring = head
                .split_once(": ring L")
                .and_then(|(_, r)| r[..r.find(',')?].parse().ok())
                .expect("a ring");
            DocFence {
                at: at.into(),
                layer,
                ring,
                notation: head.ends_with(", documentation notation -->"),
                text: f.text,
            }
        })
        .collect()
}

/// Every fence: DESIGN.md's, then EXAMPLES.md's.
pub fn all() -> Vec<DocFence> {
    let mut out = of("design.md");
    out.extend(of("examples.md"));
    out
}

/// Every variant fixture, by name.
pub fn variants() -> Vec<Variant> {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(dir().join("variants"))
        .expect("the variants directory")
        .map(|e| e.expect("an entry").path())
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|p| {
            let text = std::fs::read_to_string(&p).expect("a readable fixture");
            let of = text
                .lines()
                .next()
                .and_then(|l| l.strip_prefix("// variant: "))
                .unwrap_or_else(|| panic!("{} has no `// variant:` line", p.display()))
                .into();
            Variant {
                name: p.file_stem().expect("a name").to_string_lossy().into(),
                of,
                text,
            }
        })
        .collect()
}
