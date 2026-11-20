//! No two expressions of a syntax tree share a span (TEST-read-fit-span-unique). The checker
//! keys what it learns of an expression by its span (`Info::fits` and `Ck::read_by` in
//! zedc-check, PROOF-read-fit-single-writer): two expressions at one span would read as one,
//! and the fit one of them needs would be refused as a second fit, or replaced, at the other.
//!
//! Every expression the builder makes has its own text, so the claim holds by construction;
//! these tests check it over every desugaring the builder makes and over the programs of the
//! repository, so that a desugaring that copies a span fails here. The desugarings, each in
//! [`DESUGARINGS`]: an infix call `a ~f~ b` (the call, its callee at the name and its operands
//! at theirs, ast/infix.rs); a section `(+)` (the section and the lambda it stands for are one
//! expression, the checker walks the lambda in its place, so the lambda shares its span and is
//! not counted apart; the lambda's body is at the text between the parentheses and its two
//! names at the parentheses, `section_lambda` in ast/mod.rs); `main`'s inputs and outputs
//! (`m.stdin`, `m.stdout` passed whole, a name at the member's text or at the whole argument,
//! ast/builder.rs); a sort key (`desc`, at its own argument); `is`, `in`, ranges, `else`,
//! reductions `><`, remaps `as … into …` (a remap that changes nothing is its operand, not a
//! second expression), records and named arguments written `x:` (one name at the label), and a
//! negative literal in a pattern (a pattern, not walked: the walk lists the expressions that
//! are run, the ones an operator or a call reads).

use super::{expr_kids, expr_kids_mut, stmts_exprs_mut};
use crate::ast::{Expr, ExprKind, Stmt, unit};
use crate::lex::{Span, lex};
use crate::parse::{TOP, parse_unit};
use crate::seed::Rng;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Programs that make each desugaring of the builder (see the module's comment).
const DESUGARINGS: &[&str] = &[
    "f(a: int, b: int) = a + b;\nx = 1 ~f~ 2;\ny = 3 ~f~ 4 ~f~ 5;",
    "s = [1, 2, 3] >< (+);\nt = [1, 2] >< (*) else 1;\nu = [(+), (-)];",
    "main(m: MainArgs) {\n  w = m.stdin.concat(\" \");\n  m.stdout <- [w];\n}",
    "xs = [3, 1, 2];\nys = xs.sort(desc);\nzs = xs.sort();",
    "v = 2;\na = v is int;\nb = v is not f64;\nc = v in {1, 2};\nd = v not in {3};",
    "r = 1..=5;\nq = 0..<4;\ne = [1][0] else 0;",
    "t = [1, 2];\nu = t as (k -> v) into (v -> k);\nw = t as (k -> v) into (k -> v);",
    "x = 1;\ny = 2;\nr = {x:, y: y + 1};\nf(x: int) = x;\nz = f(x:);",
    "g(n: int) = match n { -1 -> 0, 0 -> 1, k -> k };\nh = g(-1) + -2;",
    "l = for n in 1..=3 where n != 2 { n * 2 };\nk = (n -> n + 1)(1);\nj = ((a, b) -> a + b)(1, 2);",
    "p = \"a ${1 + 2} b ${[1] >< (+)}\";\nq = !(1 == 2);\nr = -(-1);",
];

/// The span of each expression of `stmts`, the expressions of a section's lambda counted as
/// the section's own (the section is the lambda's span, and the checker walks the lambda in
/// its place). Walked on a work list, as [`expr_kids_mut`] is.
fn spans(stmts: &mut [Stmt]) -> Vec<Span> {
    let mut work: Vec<&mut Expr> = Vec::new();
    stmts_exprs_mut(stmts, &mut work);
    let mut out = Vec::new();
    while let Some(e) = work.pop() {
        out.push(e.span);
        let Expr { kind, .. } = e;
        if let ExprKind::Section(_, lambda) = kind {
            expr_kids_mut(&mut lambda.kind, &mut work);
        } else {
            expr_kids_mut(kind, &mut work);
        }
    }
    out
}

/// The first span two expressions of `text` share, or `None`; an error if `text` does not
/// build.
fn shared_span(text: &str) -> Result<Option<String>, String> {
    let tokens = lex(text).map_err(|e| format!("lexing: {e:?}"))?;
    let (tree, errors) = parse_unit(text, &tokens, TOP);
    if !errors.is_empty() {
        return Err(format!("parsing: {errors:?}"));
    }
    let mut stmts = unit(text, &tokens, &tree).map_err(|e| format!("building: {e:?}"))?;
    let mut seen = HashSet::new();
    Ok(spans(&mut stmts)
        .into_iter()
        .find(|s| !seen.insert(*s))
        .map(|s| {
            let shown = &text[s.start..s.end];
            format!("`{shown}` at {s:?} is the span of two expressions")
        }))
}

#[test]
fn each_desugaring_gives_each_expression_its_own_span() {
    for text in DESUGARINGS {
        match shared_span(text) {
            Ok(None) => {}
            Ok(Some(why)) => panic!("{why}, in\n{text}"),
            Err(e) => panic!("{e}, in\n{text}"),
        }
    }
}

/// A seeded generator of random expressions that nest the desugarings of [`DESUGARINGS`]
/// inside each other, for [`random_programs_give_each_expression_its_own_span`], drawing from
/// the shared [`Rng`].
struct Gen(Rng);

impl Gen {
    fn below(&mut self, n: u64) -> u64 {
        self.0.below_u64(n)
    }

    /// An operand of `depth` levels at most: a leaf at depth 0, else a form in parentheses, so
    /// that it is one operand whatever the precedence of the form around it (an infix call next
    /// to `-` is an error). The parentheses give the form a span of their own text, so a form
    /// is also written bare, as a definition's whole right side ([`Self::program`]): a
    /// desugaring that copies a span shows only there, as the chain `3 ~f~ 4 ~f~ 5` of
    /// [`DESUGARINGS`] does.
    fn operand(&mut self, depth: u32) -> String {
        if depth == 0 {
            return match self.below(4) {
                0 => "a".into(),
                1 => "b".into(),
                2 => format!("{}", self.below(100)),
                _ => format!("(-{})", self.below(10)),
            };
        }
        format!("({})", self.form(depth))
    }

    /// A form of `depth` levels at most (at least 1), its operands of fewer, written bare.
    fn form(&mut self, depth: u32) -> String {
        let d = depth - 1;
        match self.below(17) {
            0 => format!("{} + {}", self.operand(d), self.operand(d)),
            1 => format!("{} * {}", self.operand(d), self.operand(d)),
            2 => format!("{} ~f~ {}", self.operand(d), self.operand(d)),
            3 => format!(
                "{} ~f~ {} ~f~ {}",
                self.operand(d),
                self.operand(d),
                self.operand(d)
            ),
            4 => format!("[{}, {}] >< (+)", self.operand(d), self.operand(d)),
            5 => format!("[{}] >< (*) else {}", self.operand(d), self.operand(d)),
            6 => format!("{} is int", self.operand(d)),
            7 => format!("{} in {{1, 2}}", self.operand(d)),
            8 => format!("[{}][0] else {}", self.operand(d), self.operand(d)),
            9 => format!("(n -> n + {})({})", self.operand(d), self.operand(d)),
            10 => format!("\"s ${{{}}} t\"", self.operand(d)),
            11 => format!("!({} == {})", self.operand(d), self.operand(d)),
            12 => format!("-{}", self.operand(d)),
            13 => format!("f(x: {}, y: {})", self.operand(d), self.operand(d)),
            14 => format!("[{}, 2].sort(desc)", self.operand(d)),
            15 => format!(
                "for n in 1..={} where n != {} {{ n * 2 }}",
                self.operand(d),
                self.operand(d)
            ),
            _ => format!(
                "if {} == 1 {{ {} }} else {{ {} }}",
                self.operand(d),
                self.operand(d),
                self.operand(d)
            ),
        }
    }

    /// A program of a few definitions, each a random expression.
    fn program(&mut self) -> String {
        let mut text = String::from("f(x: int, y: int) = x + y;\na = 1;\nb = 2;\n");
        for i in 0..1 + self.below(4) {
            let depth = 1 + self.below(4) as u32;
            text.push_str(&format!("v{i} = {};\n", self.form(depth)));
        }
        text
    }
}

/// TEST-read-fit-span-cross-file, part 2: random programs that nest the desugarings in each
/// other, from fixed seeds, build and give each expression its own span. Asserted for every
/// draw: each program builds (the generator writes only forms the parser takes) and no span
/// is shared.
#[test]
fn random_programs_give_each_expression_its_own_span() {
    for seed in 0..400u64 {
        let text = Gen(Rng::new(seed)).program();
        match shared_span(&text) {
            Ok(None) => {}
            Ok(Some(why)) => panic!("seed {seed}: {why}, in\n{text}"),
            Err(e) => panic!("seed {seed}: {e}, in\n{text}"),
        }
    }
}

/// The first expression of `text` whose children [`expr_kids`] and [`expr_kids_mut`] list
/// differently, or `None`; a block, whose statements `expr_kids` leaves to its caller, is
/// skipped. `text` must build.
fn kids_differ(text: &str) -> Option<String> {
    let tokens = lex(text).expect("lexes");
    let (tree, errors) = parse_unit(text, &tokens, TOP);
    assert!(errors.is_empty(), "parses: {errors:?}");
    let mut stmts = unit(text, &tokens, &tree).expect("builds");
    let mut work: Vec<&mut Expr> = Vec::new();
    stmts_exprs_mut(&mut stmts, &mut work);
    while let Some(e) = work.pop() {
        let mut read = Vec::new();
        expr_kids(&e.kind, &mut |k| read.push(k.span));
        let at = work.len();
        let block = matches!(e.kind, ExprKind::Block(_));
        let span = e.span;
        let Expr { kind, .. } = e;
        expr_kids_mut(kind, &mut work);
        let written: Vec<Span> = work[at..].iter().map(|k| k.span).collect();
        if !block && read != written {
            return Some(format!(
                "at {span:?}: expr_kids gives {read:?}, expr_kids_mut {written:?}"
            ));
        }
    }
    None
}

/// DRY-text-shared job 10: the read-only and the changing walk list the same children, in
/// the same order, over every desugaring and the random programs of the tests above.
#[test]
fn the_read_only_walk_lists_the_children_the_changing_one_does() {
    for text in DESUGARINGS {
        assert_eq!(kids_differ(text), None, "in\n{text}");
    }
    let block = "f(n: int) = { m = n + 1; if m > 2 { [m, 3] } else { [0] } };";
    assert_eq!(kids_differ(block), None, "in\n{block}");
    for seed in 0..400u64 {
        let text = Gen(Rng::new(seed)).program();
        assert_eq!(kids_differ(&text), None, "seed {seed}, in\n{text}");
    }
}

/// The `.zed` files under `dir`, sorted.
fn zed_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
        .map(|d| d.expect("a directory entry").path())
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            zed_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "zed") {
            out.push(p);
        }
    }
}

#[test]
fn no_program_of_the_repository_has_two_expressions_at_one_span() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    zed_files(&root.join("zed"), &mut files);
    zed_files(&root.join("tests/steps"), &mut files);
    let mut built = 0;
    let mut not_built = Vec::new();
    for f in &files {
        let text = std::fs::read_to_string(f).expect("a .zed file reads");
        match shared_span(&text) {
            Ok(None) => built += 1,
            Ok(Some(why)) => panic!("{why}, in {}", f.display()),
            Err(e) => not_built.push(format!("{}: {e}", f.display())),
        }
    }
    eprintln!("{built} of {} files built and checked", files.len());
    for n in &not_built {
        eprintln!("not built: {n}");
    }
    assert!(built > 0, "no .zed file built");
}
