//! The source formatter (step L1.13): a unit's statements written back as text, in one layout.
//!
//! Two spaces per level of indentation and one statement per line. A block is written on one
//! line, `{ e }`, when it holds only its export and no comment; otherwise it has one statement
//! per line, its export last, so a block reads top-down to its result (DESIGN.md, "Blocks
//! bind; `return` exports"). A function's body block is always on several lines, and its
//! `test` cases are one table on one line, indented under it. An export of one value is the
//! trailing expression, of several `return a, b;`. Binary operators have a space each side,
//! `x: T` has none before the colon, a named argument `x: x` is written `x:`, and parentheses
//! are written only where the grammar needs them. A literal is written as it was spelled.
//!
//! Comments are kept. A comment on its own line stays before the statement after it; one after
//! a statement, on its line, stays after it; one inside a statement but in none of its blocks
//! moves to the end of the statement. One blank line is kept where the source had one or more
//! between two statements, or before the comments that end a block.

use std::collections::BTreeMap;

use crate::ast::{Expr, ExprKind, Param, Stmt, StmtKind, Target, Type, TypeKind, TypeParam};
use crate::lex::{self, Span, Token};
use crate::parse::{TOP, parse};
use crate::{ast, source};

/// The text of `unit`, parsed from `tokens` of `text`, in the formatter's layout, with the
/// comments of `text` kept.
pub fn format(text: &str, tokens: &[Token], unit: &[Stmt]) -> String {
    let comments = lex::comments(text, tokens);
    let mut f = Formatter {
        text,
        comments: comments.into_iter().map(|c| (c.start, c)).collect(),
    };
    let whole = Span {
        start: 0,
        end: text.len(),
    };
    f.stmts(unit, whole, 0, true).into_string()
}

/// The source file `bytes` in the formatter's layout, or why it could not be read, at its
/// line and column.
pub fn format_source(bytes: &[u8]) -> Result<String, String> {
    let text = source::load(bytes).map_err(|e| e.to_string())?;
    let at = |offset: usize, why: String| {
        let (line, col) = source::line_col(text.as_bytes(), offset);
        format!("{line}:{col}: {why}")
    };
    let tokens = lex::lex(&text).map_err(|e| at(e.span.start, e.to_string()))?;
    let tree = parse(&text, &tokens, "Unit", TOP).map_err(|e| at(e.span.start, e.to_string()))?;
    let unit = ast::unit(&text, &tokens, &tree).map_err(|e| at(e.span.start, e.message))?;
    Ok(format(&text, &tokens, &unit))
}

/// Precedence levels, from the loosest form of `Expr` to `Primary`, as sec:grammar orders
/// them; an operand written at a lower level than its position needs is parenthesized.
const LAMBDA: u8 = 0;
const ELSE: u8 = 1;
const OR: u8 = 2;
const EQUALITY: u8 = 4;
const RELATION: u8 = 5;
const ADDITIVE: u8 = 6;
const PREFIX: u8 = 8;
const POWER: u8 = 9;
const POSTFIX: u8 = 10;
const PRIMARY: u8 = 11;

fn level(e: &Expr) -> u8 {
    match &e.kind {
        ExprKind::Lambda { .. } => LAMBDA,
        ExprKind::Else { .. } => ELSE,
        ExprKind::Binary(op, ..) => binary_level(op),
        ExprKind::Is { .. } => RELATION,
        ExprKind::Unary(..) => PREFIX,
        ExprKind::Call { .. } | ExprKind::Index(..) | ExprKind::Member { .. } => POSTFIX,
        _ => PRIMARY,
    }
}

fn binary_level(op: &str) -> u8 {
    match op {
        "||" => OR,
        "&&" => OR + 1,
        "==" | "!=" => EQUALITY,
        "<" | "<=" | ">" | ">=" => RELATION,
        "+" | "-" | "++" => ADDITIVE,
        "*" | "/" | "div" | "mod" => ADDITIVE + 1,
        "**" => POWER,
        _ => unreachable!("{op} is no binary operator of layer L1"),
    }
}

/// Whether `e`'s text starts with a block, which a lambda's body or an `else` default that is
/// not itself a block may not.
fn starts_with_block(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Block(_) => true,
        ExprKind::Binary(_, of, _)
        | ExprKind::Call { callee: of, .. }
        | ExprKind::Index(of, _)
        | ExprKind::Member { of, .. }
        | ExprKind::Is { of, .. }
        | ExprKind::Else { of, .. } => starts_with_block(of),
        _ => false,
    }
}

/// Whether `e`, as an `if` condition, holds a block outside any bracket, which the grammar's
/// `HEAD` forbids there, since the condition's `{` opens the branch.
fn head_unsafe(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Block(_) => true,
        ExprKind::Else { of, default, .. } => head_unsafe(of) || head_unsafe(default),
        ExprKind::Binary(_, a, b) => head_unsafe(a) || head_unsafe(b),
        ExprKind::Unary(_, a)
        | ExprKind::Is { of: a, .. }
        | ExprKind::Call { callee: a, .. }
        | ExprKind::Index(a, _)
        | ExprKind::Member { of: a, .. } => head_unsafe(a),
        _ => false,
    }
}

/// Where a block stands: a block as an operand must open with a statement, a branch (of an
/// `if`, an `else`, a lambda) need not, and a function's body is on several lines.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Place {
    Operand,
    Branch,
    Body,
}

struct Formatter<'a> {
    text: &'a str,
    /// The comments not yet written, by their first byte.
    comments: BTreeMap<usize, Span>,
}

/// A statement with the comments it keeps, and whether a blank line precedes it.
struct Entry<'s> {
    stmt: &'s Stmt,
    blank: bool,
    leading: Vec<Span>,
    trailing: Vec<Span>,
}

fn indent(n: usize) -> String {
    "  ".repeat(n)
}

impl Formatter<'_> {
    /// The comments not yet written that start in `from..to`, now marked written.
    fn take(&mut self, from: usize, to: usize) -> Vec<Span> {
        if from >= to {
            return Vec::new();
        }
        let out: Vec<Span> = self.comments.range(from..to).map(|(_, c)| *c).collect();
        for c in &out {
            self.comments.remove(&c.start);
        }
        out
    }

    /// The comments not yet written that follow byte `from` on its line, before `to`.
    fn take_same_line(&mut self, from: usize, to: usize) -> Vec<Span> {
        let mut out = Vec::new();
        let mut pos = from;
        while let Some((_, &c)) = self.comments.range(pos..to.max(pos)).next() {
            if self.text[pos..c.start].contains('\n') {
                break;
            }
            self.comments.remove(&c.start);
            out.push(c);
            pos = c.end;
        }
        out
    }

    fn has_comment(&self, span: Span) -> bool {
        span.start < span.end && self.comments.range(span.start..span.end).next().is_some()
    }

    /// The lines of `stmts`, which stand in `region` of the text, at indentation `ind`, each
    /// line ending in a newline. With `bare`, an export of one value is a trailing expression.
    fn stmts(&mut self, stmts: &[Stmt], region: Span, ind: usize, bare: bool) -> Doc {
        // The comments and blank lines are found in source order, where the export may not be
        // last.
        let mut in_order: Vec<&Stmt> = stmts.iter().collect();
        in_order.sort_by_key(|s| s.span.start);
        let mut entries = Vec::new();
        let mut prev = region.start;
        for (i, s) in in_order.iter().enumerate() {
            let leading = self.take(prev, s.span.start);
            let first = leading.first().map_or(s.span.start, |c| c.start);
            let blank = i > 0 && self.text[prev..first].matches('\n').count() > 1;
            let next = in_order.get(i + 1).map_or(region.end, |n| n.span.start);
            let trailing = self.take_same_line(s.span.end, next);
            prev = trailing.last().map_or(s.span.end, |c| c.end);
            entries.push(Entry {
                stmt: s,
                blank,
                leading,
                trailing,
            });
        }
        let (exports, mut entries): (Vec<_>, Vec<_>) = entries
            .into_iter()
            .partition(|e| matches!(e.stmt.kind, StmtKind::Return(_)));
        entries.extend(exports);
        let pad = indent(ind);
        let mut out: Vec<Doc> = Vec::new();
        for (i, e) in entries.into_iter().enumerate() {
            if e.blank && i > 0 {
                out.push("\n".into());
            }
            for c in e.leading {
                out.push(format!("{pad}{}\n", &self.text[c.start..c.end]).into());
            }
            out.push(pad.as_str().into());
            out.push(self.stmt(e.stmt, ind, bare));
            let mut tail = self.take(e.stmt.span.start, e.stmt.span.end);
            tail.extend(e.trailing);
            let mut after_line_comment = false;
            for c in tail {
                let body = &self.text[c.start..c.end];
                out.push(if after_line_comment {
                    format!("\n{pad}{body}").into()
                } else {
                    format!(" {body}").into()
                });
                after_line_comment = body.starts_with("//");
            }
            out.push("\n".into());
        }
        let rest = self.take(prev, region.end);
        if let Some(c) = rest.first()
            && !out.is_empty()
            && self.text[prev..c.start].matches('\n').count() > 1
        {
            out.push("\n".into());
        }
        for c in rest {
            out.push(format!("{pad}{}\n", &self.text[c.start..c.end]).into());
        }
        Doc::cat(out)
    }

    /// The text of `s`, which starts at indentation `ind`.
    fn stmt(&mut self, s: &Stmt, ind: usize, bare: bool) -> Doc {
        match &s.kind {
            StmtKind::Bind { targets, value } => {
                let ts: Vec<&str> = targets
                    .iter()
                    .map(|t| match t {
                        Target::Name(n) => n.as_str(),
                        Target::Wild => "_",
                    })
                    .collect();
                cat![ts.join(", "), " = ", self.expr(value, LAMBDA, ind), ";"]
            }
            StmtKind::Return(es) if bare && es.len() == 1 => self.expr(&es[0], LAMBDA, ind),
            StmtKind::Return(es) => {
                let es: Vec<Doc> = es.iter().map(|e| self.expr(e, LAMBDA, ind)).collect();
                cat!["return ", Doc::join(es, ", "), ";"]
            }
            StmtKind::Push { port, value } => {
                cat![format!("{port} <- "), self.expr(value, LAMBDA, ind), ";"]
            }
            StmtKind::Function(f) => {
                let mut out = vec![cat![
                    format!("{}(", f.name),
                    self.params(&f.params, ind),
                    ")"
                ]];
                if let Some(ports) = &f.ports {
                    let ps: Vec<Doc> = ports
                        .iter()
                        .map(|p| cat![format!("{}: ", p.name), ty(&p.ty, 0)])
                        .collect();
                    out.push(cat![" -> (", Doc::join(ps, ", "), ")"]);
                }
                if f.equation {
                    out.push(cat![" = ", self.expr(&f.body, LAMBDA, ind)]);
                    if f.tests.is_empty() {
                        out.push(";".into());
                    }
                } else {
                    out.push(cat![" ", self.block(&f.body, ind, Place::Body)]);
                }
                if !f.tests.is_empty() {
                    let cases: Vec<Doc> = f
                        .tests
                        .iter()
                        .map(|(a, b)| {
                            cat![self.expr(a, ELSE, ind), " -> ", self.expr(b, ELSE, ind)]
                        })
                        .collect();
                    out.push(cat![
                        format!("\n{}test {{ ", indent(ind + 1)),
                        Doc::join(cases, ", "),
                        " }"
                    ]);
                }
                Doc::cat(out)
            }
        }
    }

    fn params(&mut self, params: &[Param], ind: usize) -> Doc {
        let ps: Vec<Doc> = params.iter().map(|p| self.param(p, ind)).collect();
        Doc::join(ps, ", ")
    }

    fn param(&mut self, p: &Param, ind: usize) -> Doc {
        let mut out: Vec<Doc> = Vec::new();
        if p.positional {
            out.push("positional ".into());
        }
        out.push(p.name.as_str().into());
        if let Some(t) = &p.ty {
            out.push(cat![": ", ty(t, 0)]);
        }
        if let Some(d) = &p.default {
            out.push(cat![" = ", self.expr(d, LAMBDA, ind)]);
        }
        Doc::cat(out)
    }

    /// The text of `e` in a position that takes forms of level `min` and above.
    fn expr(&mut self, e: &Expr, min: u8, ind: usize) -> Doc {
        let text = self.raw(e, ind);
        if level(e) < min {
            cat!["(", text, ")"]
        } else {
            text
        }
    }

    fn raw(&mut self, e: &Expr, ind: usize) -> Doc {
        match &e.kind {
            ExprKind::Int { .. } | ExprKind::Float(_) | ExprKind::Rat(_) | ExprKind::Str(_) => {
                // A grouped literal's span holds its parentheses; a literal never starts with `(`.
                let mut t = self.text[e.span.start..e.span.end].trim();
                while let Some(inner) = t.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
                    t = inner.trim();
                }
                t.into()
            }
            ExprKind::Bool(b) => b.to_string().into(),
            ExprKind::Atom(a) => format!("#{a}").into(),
            ExprKind::Name(n) => n.as_str().into(),
            ExprKind::Unary(op, x) => match x.kind {
                ExprKind::Unary(..) => cat![format!("{op}("), self.raw(x, ind), ")"],
                _ => cat![op.to_string(), self.expr(x, PREFIX, ind)],
            },
            ExprKind::Binary(op, a, b) => {
                let l = binary_level(op);
                let (lmin, rmin) = match l {
                    POWER => (POSTFIX, PREFIX),
                    EQUALITY | RELATION => (l + 1, l + 1),
                    _ => (l, l + 1),
                };
                let a = self.expr(a, lmin, ind);
                cat![a, format!(" {op} "), self.expr(b, rmin, ind)]
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                curry,
            } => {
                let mut args: Vec<Doc> = positional
                    .iter()
                    .map(|a| self.expr(a, LAMBDA, ind))
                    .collect();
                for (n, v) in named {
                    args.push(match &v.kind {
                        ExprKind::Name(m) if m == n => format!("{n}:").into(),
                        _ => cat![format!("{n}: "), self.expr(v, LAMBDA, ind)],
                    });
                }
                if *curry {
                    args.push("...".into());
                }
                cat![
                    self.postfix_of(callee, ind),
                    "(",
                    Doc::join(args, ", "),
                    ")"
                ]
            }
            ExprKind::Index(of, k) => {
                let of = self.postfix_of(of, ind);
                cat![of, "[", self.expr(k, LAMBDA, ind), "]"]
            }
            ExprKind::Member { of, name, safe } => {
                let dot = if *safe { "?." } else { "." };
                cat![self.postfix_of(of, ind), format!("{dot}{name}")]
            }
            ExprKind::Tuple(items) => {
                let items: Vec<Doc> = items.iter().map(|i| self.expr(i, LAMBDA, ind)).collect();
                cat!["(", Doc::join(items, ", "), ")"]
            }
            ExprKind::Lambda { params, body } => {
                let head = match &params[..] {
                    [p] if !p.positional && p.ty.is_none() && p.default.is_none() => {
                        p.name.as_str().into()
                    }
                    _ => cat!["(", self.params(params, ind), ")"],
                };
                cat![head, " -> ", self.tail(body, LAMBDA, ind)]
            }
            ExprKind::Is { of, ty: t, negated } => {
                let not = if *negated { "not " } else { "" };
                cat![self.expr(of, ADDITIVE, ind), format!(" is {not}"), ty(t, 1)]
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                let of = self.expr(of, ELSE, ind);
                let pat = pattern
                    .as_ref()
                    .map_or(String::new(), |p| format!("{p} -> "));
                cat![of, format!(" else {pat}"), self.tail(default, OR, ind)]
            }
            ExprKind::Block(_) => self.block(e, ind, Place::Operand),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let c = self.expr(cond, ELSE, ind);
                let c = if head_unsafe(cond) {
                    cat!["(", c, ")"]
                } else {
                    c
                };
                let then = self.block(then, ind, Place::Branch);
                let otherwise = match otherwise.kind {
                    ExprKind::If { .. } => self.raw(otherwise, ind),
                    _ => self.block(otherwise, ind, Place::Branch),
                };
                cat!["if ", c, " ", then, " else ", otherwise]
            }
        }
    }

    /// The operand of a call, index or member: a number literal is parenthesized, so that its
    /// `.` is not read as a decimal point.
    fn postfix_of(&mut self, of: &Expr, ind: usize) -> Doc {
        match of.kind {
            ExprKind::Int { .. } | ExprKind::Float(_) | ExprKind::Rat(_) => {
                cat!["(", self.raw(of, ind), ")"]
            }
            _ => self.expr(of, POSTFIX, ind),
        }
    }

    /// A lambda's body or an `else` default: a block, or an expression of level `min` that
    /// does not start with a block.
    fn tail(&mut self, e: &Expr, min: u8, ind: usize) -> Doc {
        match e.kind {
            ExprKind::Block(_) => self.block(e, ind, Place::Branch),
            _ if starts_with_block(e) && level(e) >= min => cat!["(", self.raw(e, ind), ")"],
            _ => self.expr(e, min, ind),
        }
    }

    /// The block `e`, standing at `place`, its first line at indentation `ind`.
    fn block(&mut self, e: &Expr, ind: usize, place: Place) -> Doc {
        let ExprKind::Block(stmts) = &e.kind else {
            unreachable!("a block")
        };
        let bare = !(place == Place::Operand && stmts.len() == 1);
        if place != Place::Body
            && let [s] = &stmts[..]
            && matches!(s.kind, StmtKind::Return(_))
            && !self.has_comment(e.span)
        {
            // With no comment inside, the block is this one statement: on the block's line when
            // its text has no line break, which no indentation then enters, and on a line of
            // its own otherwise. Rendering it once keeps nested blocks linear in their depth.
            let line = self.stmt(s, ind + 1, bare);
            return if line.has_newline() {
                cat![
                    format!("{{\n{}", indent(ind + 1)),
                    line,
                    format!("\n{}}}", indent(ind))
                ]
            } else {
                cat!["{ ", line, " }"]
            };
        }
        if stmts.is_empty() && !self.has_comment(e.span) {
            return "{ }".into();
        }
        let inside = Span {
            start: e.span.start + 1,
            end: e.span.end - 1,
        };
        let lines = self.stmts(stmts, inside, ind + 1, bare);
        cat!["{\n", lines, format!("{}}}", indent(ind))]
    }
}

/// Text built by concatenation without copying: a string, or parts in order with whether any
/// holds a line break. Each level of the tree adds only its own text, so rendering a nest of
/// depth `d` is linear in the output, where joining strings copied each level's text into its
/// parent, `O(n·d)`.
enum Doc {
    Leaf(String),
    Cat(Vec<Doc>, bool),
}

/// The concatenation of the parts, each converted with `Doc::from`.
macro_rules! cat {
    ($($p:expr),* $(,)?) => { Doc::cat(vec![$(Doc::from($p)),*]) };
}
use cat;

impl Doc {
    fn cat(parts: Vec<Doc>) -> Doc {
        let newline = parts.iter().any(Doc::has_newline);
        Doc::Cat(parts, newline)
    }

    fn join(parts: Vec<Doc>, sep: &str) -> Doc {
        let mut out = Vec::with_capacity(2 * parts.len());
        for (i, p) in parts.into_iter().enumerate() {
            if i > 0 {
                out.push(sep.into());
            }
            out.push(p);
        }
        Doc::cat(out)
    }

    fn has_newline(&self) -> bool {
        match self {
            Doc::Leaf(s) => s.contains('\n'),
            Doc::Cat(_, newline) => *newline,
        }
    }

    /// The text, written without recursion, so the depth of the tree needs no stack.
    fn into_string(self) -> String {
        let mut out = String::new();
        let mut stack = vec![vec![self].into_iter()];
        while let Some(top) = stack.last_mut() {
            match top.next() {
                Some(Doc::Leaf(s)) => out += &s,
                Some(Doc::Cat(parts, _)) => stack.push(parts.into_iter()),
                None => {
                    stack.pop();
                }
            }
        }
        out
    }
}

impl From<String> for Doc {
    fn from(s: String) -> Doc {
        Doc::Leaf(s)
    }
}

impl From<&str> for Doc {
    fn from(s: &str) -> Doc {
        Doc::Leaf(s.to_string())
    }
}

/// Type precedence levels: an arrow, a union or difference, an intersection, a primary.
fn type_level(t: &Type) -> u8 {
    match t.kind {
        TypeKind::Arrow { .. } => 0,
        TypeKind::Union(_) | TypeKind::Diff(..) => 1,
        TypeKind::And(_) => 2,
        _ => 5,
    }
}

/// The text of the type `t` in a position that takes levels `min` and above.
fn ty(t: &Type, min: u8) -> Doc {
    let join = |ts: &[Type], min: u8, sep: &str| {
        let ts: Vec<Doc> = ts.iter().map(|t| ty(t, min)).collect();
        Doc::join(ts, sep)
    };
    let text = match &t.kind {
        TypeKind::Name(n) => n.as_str().into(),
        TypeKind::Atom(a) => format!("#{a}").into(),
        TypeKind::Tuple(ts) => cat!["(", join(ts, 0, ", "), ")"],
        TypeKind::Union(ts) => join(ts, 2, " | "),
        TypeKind::And(ts) => join(ts, 3, " & "),
        TypeKind::Diff(a, b) => {
            let a = match a.kind {
                TypeKind::Diff(..) => ty(a, 1),
                _ => ty(a, 3),
            };
            cat![a, " \\ ", ty(b, 3)]
        }
        TypeKind::Arrow {
            params,
            partial,
            result,
        } => {
            let params = match &params[..] {
                [
                    TypeParam {
                        name: None, ty: p, ..
                    },
                ] => match p.kind {
                    TypeKind::Tuple(_) => cat!["(", ty(p, 0), ")"],
                    _ => ty(p, 1),
                },
                ps => {
                    let ps: Vec<Doc> = ps.iter().map(type_param).collect();
                    cat!["(", Doc::join(ps, ", "), ")"]
                }
            };
            let arrow = if *partial { " ->? " } else { " -> " };
            cat![params, arrow, ty(result, 0)]
        }
    };
    if type_level(t) < min {
        cat!["(", text, ")"]
    } else {
        text
    }
}

fn type_param(p: &TypeParam) -> Doc {
    match &p.name {
        Some(n) if p.positional => cat![format!("positional {n}: "), ty(&p.ty, 0)],
        Some(n) => cat![format!("{n}: "), ty(&p.ty, 0)],
        None => ty(&p.ty, 0),
    }
}
