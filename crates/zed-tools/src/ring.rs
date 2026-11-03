//! `ring SPEC_DIR FILE.zed ...` prints the lowest ring at which each file parses as a `Unit`:
//! `FILE Lk`, or `FILE FAIL reason`. It fails if any file does.

use zedc::parse::TOP;

use crate::spec::Spec;
use crate::syntax::{Tokens, Tree, lex, parse};
use crate::text::read_text;
use crate::{Outcome, arg, say};

/// A text parsed at the full ring: the lowest ring it parses at, its tree and its tokens.
#[derive(Clone, Debug)]
pub struct Ringed {
    /// The lowest ring.
    pub ring: u32,
    /// The tree at the full ring.
    pub tree: Tree,
    /// The tokens.
    pub toks: Tokens,
}

/// The lowest ring of `text` as a `Unit`, or the reason it has none.
pub fn ring_of(spec: &Spec, text: &str) -> Result<Ringed, String> {
    let toks = lex(&spec.lexical, &text.replace('…', "elided")).map_err(|e| format!("LEX {e}"))?;
    let (syn, lexical) = (&spec.syntactic, &spec.lexical);
    let tree = parse(syn, lexical, &toks, TOP, "Unit")?;
    for ring in 1..=TOP {
        if let Ok(t) = parse(syn, lexical, &toks, ring, "Unit") {
            if !t.same(&tree) {
                return Err(format!("TREE CHANGES between L{ring} and L{TOP}"));
            }
            return Ok(Ringed { ring, tree, toks });
        }
    }
    Err("no ring".into())
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let spec = Spec::open(arg(args, 0, "ring SPEC_DIR FILE.zed ...")?)?;
    let mut bad = 0;
    for f in &args[1..] {
        match ring_of(&spec, &read_text(f)?) {
            Ok(r) => say!(out, "{f} L{}", r.ring),
            Err(why) => {
                say!(out, "{f} FAIL {why}");
                bad += 1;
            }
        }
    }
    Ok(bad == 0)
}
