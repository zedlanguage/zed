//! The build constant (step L2.8d, DESIGN.md "Build modes"): `build.target`, the target the
//! build is for, and `build.options.<name>`, whether the build turns the option `<name>` on.
//! The options a build may turn on are those the package's manifest lists in its entry
//! `options`, and the command line turns each on with `--option <name>`.
//!
//! Each read is replaced, in the unit's statements and after resolution, by the literal it
//! reads, at the read's text: a string literal for the target and a `bool` literal for an
//! option. So the checker checks the branch of every target, and the build, which evaluates a
//! condition on literals (step L1.28), keeps the branch of the build's target alone.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::ast::{self, BinaryOp, Expr, ExprKind, Note, Stmt, StrPart};
use crate::lex::Span;
use crate::resolve::{Ref, Resolution};

/// The targets a build may be for, each `<architecture>-<system>` (DESIGN.md L28.4 and S.12).
pub const TARGETS: &[&str] = &[
    "x86_64-linux",
    "aarch64-linux",
    "riscv64-linux",
    "x86_64-macos",
    "aarch64-macos",
    "x86_64-windows",
    "aarch64-windows",
];

/// What a program reads of its build: the target and each option the package declares, with
/// whether it is on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Build {
    target: String,
    /// The options the package declares, in the order its manifest writes them.
    declared: Vec<String>,
    /// Each option the package declares, with whether the build turns it on.
    options: BTreeMap<String, bool>,
}

impl Default for Build {
    /// The build for the machine zedc runs on, of a package that declares no option.
    fn default() -> Self {
        Build {
            target: format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS),
            declared: Vec::new(),
            options: BTreeMap::new(),
        }
    }
}

impl Build {
    /// The build for `target` of a package that declares the options `declared`, with those
    /// of `on` turned on; or why an option of `on` is not one of `declared`, which lists them.
    /// O((d + o) log d) for d options declared and o turned on.
    pub fn new(target: &str, declared: &[String], on: &[&str]) -> Result<Build, String> {
        let mut options: BTreeMap<String, bool> =
            declared.iter().map(|o| (o.clone(), false)).collect();
        for &o in on {
            match options.get_mut(o) {
                Some(v) => *v = true,
                None => {
                    return Err(format!(
                        "`--option {o}`: the package {}. Declare it in the manifest, as \
                         `options = \"{}\";`, or remove `--option {o}`.",
                        declares(declared),
                        with(declared, o)
                    ));
                }
            }
        }
        Ok(Build {
            target: target.to_string(),
            declared: declared.to_vec(),
            options,
        })
    }

    /// The build for the machine zedc runs on of the package whose manifest lies above the
    /// place `place`, with the options of `on` turned on; or why the manifest cannot be read
    /// or an option of `on` is not one it lists, with the status of the command: 1 for a manifest
    /// that does not parse, 2 for one that cannot be read and for an option it does not list.
    pub fn at(place: &crate::place::Place, on: &[&str]) -> Result<Build, (u8, String)> {
        let host = Build::default();
        let declared = match place {
            crate::place::Place::Loose(_) => Vec::new(),
            crate::place::Place::Unit { root, .. } => {
                let path = root.join(crate::place::MANIFEST);
                match std::fs::read(&path) {
                    Ok(bytes) => {
                        let text = crate::source::load(&bytes).map_err(|e| {
                            (1, format!("{}: {}", path.display(), e.render(&bytes)))
                        })?;
                        crate::unit::manifest(&text)
                            .map_err(|es| {
                                (
                                    1,
                                    es.iter()
                                        .map(|e| {
                                            let (l, c) = crate::source::line_col(
                                                text.as_bytes(),
                                                e.span.start,
                                            );
                                            format!("{}:{l}:{c}: {}", path.display(), e.message)
                                        })
                                        .collect::<Vec<_>>()
                                        .join("\n"),
                                )
                            })?
                            .options
                    }
                    Err(e) => {
                        return Err((2, crate::run::unreadable(&path.display().to_string(), &e)));
                    }
                }
            }
        };
        Build::new(&host.target, &declared, on).map_err(|why| (2, why))
    }

    /// The target the build is for.
    pub fn target(&self) -> &str {
        &self.target
    }

    /// This build with every option off: the build a unit's pins are taken at, so that the
    /// options a build turns on leave the pins as they are.
    pub fn pinned(&self) -> Build {
        Build {
            target: self.target.clone(),
            declared: self.declared.clone(),
            options: self.options.keys().map(|o| (o.clone(), false)).collect(),
        }
    }

    /// The build as bytes, for a query's key: no two builds share them. O(the bytes).
    pub fn bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let mut part = |b: &[u8]| {
            out.extend_from_slice(&(b.len() as u64).to_le_bytes());
            out.extend_from_slice(b);
        };
        part(self.target.as_bytes());
        // In the manifest's order, which the messages follow.
        for o in &self.declared {
            part(o.as_bytes());
            part(&[u8::from(self.options.get(o) == Some(&true))]);
        }
        out
    }
}

/// The options each `--option <name>` of `words` turns on, in order, and the other words; or
/// why `--option` is the last word. O(the words).
pub fn take<'a>(words: &[&'a str]) -> Result<(Vec<&'a str>, Vec<&'a str>), String> {
    let mut on = Vec::new();
    let mut rest = Vec::with_capacity(words.len());
    let mut words = words.iter();
    while let Some(&w) = words.next() {
        if w != "--option" {
            rest.push(w);
            continue;
        }
        let o = words.next().ok_or_else(|| {
            "`--option` is the last word of the command line, and it needs the name of the \
             option to turn on after it, one the manifest's entry `options` lists. Write \
             `--option <name>`, or remove `--option`."
                .to_string()
        })?;
        on.push(*o);
    }
    Ok((on, rest))
}

/// What the package declares, for a message: "declares the options `a` and `b`" or "declares
/// no option".
fn declares(declared: &[String]) -> String {
    let names: Vec<String> = declared.iter().map(|o| format!("`{o}`")).collect();
    match &names[..] {
        [] => "declares no option".into(),
        [one] => format!("declares the one option {one}"),
        [init @ .., last] => format!("declares the options {} and {last}", init.join(", ")),
    }
}

/// The list of the entry `options` with `o` added at its end.
fn with(declared: &[String], o: &str) -> String {
    let mut names: Vec<&str> = declared.iter().map(String::as_str).collect();
    names.push(o);
    names.join(", ")
}

/// The targets, for a message: "`x86_64-linux`, …, and `aarch64-windows`".
fn targets() -> String {
    let names: Vec<String> = TARGETS.iter().map(|t| format!("`{t}`")).collect();
    match &names[..] {
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
        [] => String::new(),
    }
}

/// What a use of `build` reads.
enum Read<'a> {
    /// `build.target`.
    Target,
    /// `build.options.<name>`.
    Option(&'a str),
}

/// Whether `e` is the prelude word `build`, by its resolution `res`.
fn is_build(e: &Expr, res: &Resolution) -> bool {
    matches!(&e.kind, ExprKind::Name(_))
        && matches!(res.uses.get(&e.span), Some(Ref::Prelude(w)) if w == "build")
}

/// What `e` reads of the build, if it is `build.target` or `build.options.<name>`.
fn read_of<'a>(e: &'a Expr, res: &Resolution) -> Option<Read<'a>> {
    let ExprKind::Member {
        of,
        name,
        safe: false,
    } = &e.kind
    else {
        return None;
    };
    if is_build(of, res) && name == "target" {
        return Some(Read::Target);
    }
    match &of.kind {
        ExprKind::Member {
            of: inner,
            name: options,
            safe: false,
        } if options == "options" && is_build(inner, res) => Some(Read::Option(name)),
        _ => None,
    }
}

/// An error at `span` with the repair `repair`, a line of rewritten code.
fn error(span: Span, message: String, repair: Option<String>) -> ast::Error {
    ast::Error {
        span,
        message,
        notes: repair
            .map(|text| Note {
                span,
                text: format!("repair: {text}"),
            })
            .into_iter()
            .collect(),
        menu: String::new(),
        row: None,
    }
}

/// Replaces each read of the build `build` in `stmts`, whose resolution is `res`, by the
/// literal it reads, at the read's text, and drops the uses its text held from `res`; or
/// gives every use of `build` that is no read, every option read that the build does not
/// declare, and every comparison of `build.target` with a string literal that is no target.
///
/// A walk with an explicit stack over the expressions, each met once; a read's uses are
/// dropped by a range of the map. O(n + u log u) for n nodes and u uses.
pub(crate) fn read(stmts: &mut [Stmt], res: &mut Resolution, build: &Build) -> Vec<ast::Error> {
    let mut errors = Vec::new();
    // The texts of the reads: their uses are dropped after the walk, which borrows `res`.
    let mut read_spans = Vec::new();
    let target = Arc::new(build.target.clone());
    let mut stack = Vec::new();
    ast::stmts_exprs_mut(stmts, &mut stack);
    while let Some(e) = stack.pop() {
        if let ExprKind::Binary(BinaryOp::Eq | BinaryOp::Ne, a, b) = &e.kind {
            for (r, s) in [(&**a, &**b), (&**b, &**a)] {
                if matches!(read_of(r, res), Some(Read::Target))
                    && let Some(t) = literal(s)
                    && !TARGETS.contains(&t.as_str())
                {
                    errors.push(error(
                        s.span,
                        format!("`{t}` is no target: `build.target` is one of {}", targets()),
                        None,
                    ));
                }
            }
        }
        let kind = match read_of(e, res) {
            Some(Read::Target) => ExprKind::Str(vec![StrPart::Text(Arc::clone(&target))]),
            Some(Read::Option(o)) => match build.options.get(o) {
                Some(&on) => ExprKind::Bool(on),
                None => {
                    errors.push(error(
                        e.span,
                        format!(
                            "`build.options.{o}` names no option: the package {}",
                            declares(&build.declared)
                        ),
                        Some(format!(
                            "declare it in the manifest `zed.manifest`, as `options = \"{}\";`",
                            with(&build.declared, o)
                        )),
                    ));
                    continue;
                }
            },
            None => {
                if let Some(why) = misuse(e, res) {
                    errors.push(why);
                    continue;
                }
                ast::expr_kids_mut(&mut e.kind, &mut stack);
                continue;
            }
        };
        read_spans.push(e.span);
        // The old kind holds `build` and its members only, and is dropped here.
        e.kind = kind;
    }
    errors.sort_by_key(|e| e.span);
    for span in read_spans {
        let inside: Vec<Span> = res
            .uses
            .range(
                Span {
                    start: span.start,
                    end: 0,
                }..,
            )
            .take_while(|(s, _)| s.start < span.end)
            .filter(|(s, _)| s.end <= span.end)
            .map(|(s, _)| *s)
            .collect();
        for s in inside {
            res.uses.remove(&s);
        }
    }
    errors
}

/// The text of `e` when it is a string literal with no hole.
fn literal(e: &Expr) -> Option<String> {
    let ExprKind::Str(parts) = &e.kind else {
        return None;
    };
    parts
        .iter()
        .map(|p| match p {
            StrPart::Text(t) => Some(t.as_str()),
            StrPart::Hole(_) => None,
        })
        .collect()
}

/// Why `e` misuses `build`, when it is `build` read other than as `build.target` or
/// `build.options.<name>`: `build` alone, `build.options` alone, another member of either, or
/// either read with `?.`.
fn misuse(e: &Expr, res: &Resolution) -> Option<ast::Error> {
    const READS: &str = "`build` is read as `build.target` or `build.options.<name>`";
    if is_build(e, res) {
        return Some(error(
            e.span,
            format!("`build` alone is no value: {READS}"),
            Some("`build.target == \"x86_64-linux\"`".into()),
        ));
    }
    let ExprKind::Member { of, name, safe } = &e.kind else {
        return None;
    };
    let dot = if *safe { "?." } else { "." };
    if is_build(of, res) {
        let message = match (name.as_str(), safe) {
            ("options", false) => {
                format!("`build.options` alone is no value: {READS}, one option at a time")
            }
            ("target" | "options", true) => {
                format!("`build{dot}{name}` reads no atom, so it takes `.`: {READS}")
            }
            _ => format!("`build{dot}{name}`: `build` has no member `{name}`: {READS}"),
        };
        return Some(error(e.span, message, None));
    }
    match &of.kind {
        ExprKind::Member {
            of: inner,
            name: options,
            safe: inner_safe,
        } if options == "options" && is_build(inner, res) => {
            let first = if *inner_safe { "?." } else { "." };
            Some(error(
                e.span,
                format!("`build{first}options{dot}{name}` reads no atom, so it takes `.`: {READS}"),
                Some(format!("`build.options.{name}`")),
            ))
        }
        _ => None,
    }
}
