//! Expected output of the signatures and top-level types the checker prints (plan row
//! TESTS-STACK-big-tests-deep-ops, item TY-write-stack). Commit 81f3d848 made `Denote::ty`, the
//! drop of a signature, `Sig::facts` and `Sig::digest` work on an explicit stack, and found the
//! printed types and signatures byte-identical to the old code once, by a comparison that was
//! not kept. The old code is gone, so these snapshots are written from the code as it stands:
//! they catch a later change to what is printed, not a difference from the recursive code.

use std::fmt::Write;

use zed_tests::{deep, oracle};

/// [`deep::statements`] of `text`, with the error that stops it as text in place of a panic.
fn statements(text: &str) -> Result<Vec<zedc::ast::Stmt>, String> {
    let tokens = zedc::lex::lex_fence(text).map_err(|e| format!("{e:?}"))?;
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP)
        .map_err(|e| format!("{e:?}"))?;
    zedc::ast::unit(text, &tokens, &tree).map_err(|e| format!("{e:?}"))
}

/// The signature of each declared function, by binder, the type of each top-level name bound by
/// `=`, sorted by name, and the number of type errors, of the unit `text`; or the message of
/// the first error that stops it before the checker (a corpus program written with a form this
/// zedc does not take yet), or that it does not resolve alone (a corpus program that imports
/// units of its package).
fn printed(text: &str) -> String {
    let stmts = match statements(text) {
        Ok(stmts) => stmts,
        Err(message) => return format!("  does not parse: {message}\n"),
    };
    let Ok(res) = zedc::resolve::resolve(&stmts) else {
        return "  does not resolve alone\n".into();
    };
    let info = zedc::check::walk::check(&stmts, &res);
    let mut out = String::new();
    for (binder, sig) in &info.sigs {
        writeln!(out, "  sig {binder}: {sig}").expect("a String takes any write");
    }
    let mut tops: Vec<_> = info.tops.iter().collect();
    tops.sort_by(|a, b| a.0.cmp(b.0));
    for (name, ty) in tops {
        writeln!(out, "  {name}: {ty}").expect("a String takes any write");
    }
    writeln!(out, "  {} type errors", info.errors.len()).expect("a String takes any write");
    out
}

/// Each corpus program, read by its main file's text alone.
#[test]
fn signatures_and_types_of_the_corpus_programs() {
    let mut out = String::new();
    for (path, layer) in oracle::corpus() {
        let text =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let name = oracle::corpus_name(&path);
        writeln!(out, "{name} (L{layer}):").expect("a String takes any write");
        out += &printed(&text);
    }
    insta::assert_snapshot!(out);
}

/// Each shape of [`deep::programs`], 4 and 12 deep: nested function types, tuples and lambdas
/// are what the explicit stacks of 81f3d848 walk.
#[test]
fn signatures_and_types_of_the_deep_programs() {
    let mut out = String::new();
    for n in [4, 12] {
        for p in deep::programs(n) {
            writeln!(out, "{} ({n} deep):", p.shape).expect("a String takes any write");
            out += &printed(&p.text);
        }
    }
    insta::assert_snapshot!(out);
}
