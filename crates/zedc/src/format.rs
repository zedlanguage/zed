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
//! between two statements, among the comments before a statement or after the last one, or
//! between those comments and the statement.

use std::borrow::Cow;
use std::collections::BTreeMap;

use crate::ast::{
    Annot, Arm, BoundaryItem, Every, Expr, ExprKind, Field, Function, ImportKind, IndexKey, Param,
    Pattern, Port, Stmt, StmtKind, Target, Type, TypeKind, TypeParam, Update,
};
use crate::lex::{self, Span, Token};
use crate::parse::{TOP, parse};
use crate::{ast, source};

/// The text of `unit`, parsed from `tokens` of `text`, in the formatter's layout, with the
/// comments of `text` kept.
pub fn format(text: &str, tokens: &[Token], unit: &[Stmt]) -> String {
    let comments = lex::comments(text, tokens);
    let f = Formatter {
        text,
        comments: comments.into_iter().map(|c| (c.start, c)).collect(),
        pieces: Vec::new(),
        breaks: 0,
    };
    let region = Span {
        start: 0,
        end: text.len(),
    };
    f.run(Job::Stmts {
        stmts: unit,
        region,
        ind: 0,
        bare: true,
    })
}

/// The source file `bytes` in the formatter's layout, or why it could not be read, at its
/// line and column.
pub fn format_source(bytes: &[u8]) -> Result<String, String> {
    let text = source::load(bytes).map_err(|e| e.render(bytes))?;
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
const REDUCE: u8 = 6;
const RANGE: u8 = 7;
const ADDITIVE: u8 = 8;
const PREFIX: u8 = 10;
const POWER: u8 = 11;
const POSTFIX: u8 = 12;
const PRIMARY: u8 = 13;

fn level(e: &Expr) -> u8 {
    match &e.kind {
        // A sort key stands only as an argument, whose level is `LAMBDA`, and its key is any `Expr`.
        ExprKind::Lambda { .. } | ExprKind::Break(_) | ExprKind::SortKey { .. } => LAMBDA,
        ExprKind::Else { .. } => ELSE,
        ExprKind::Binary(op, ..) => binary_level(op),
        ExprKind::Is { .. } | ExprKind::In { .. } => RELATION,
        ExprKind::With { .. } | ExprKind::Reduce { .. } => REDUCE,
        ExprKind::Range(..) => RANGE,
        ExprKind::Unary(..) => PREFIX,
        ExprKind::Call { .. }
        | ExprKind::Index(..)
        | ExprKind::Member { .. }
        | ExprKind::Spread { .. }
        | ExprKind::Read { .. } => POSTFIX,
        ExprKind::Int { .. }
        | ExprKind::Float(_)
        | ExprKind::Rat(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Atom(_)
        | ExprKind::Name(_)
        | ExprKind::Tuple(_)
        | ExprKind::Block(_)
        | ExprKind::If { .. }
        | ExprKind::Record(_)
        | ExprKind::This
        | ExprKind::Match { .. }
        | ExprKind::Section(_)
        | ExprKind::Array(_)
        | ExprKind::Set(_)
        | ExprKind::Map(_)
        // A `loop` has no head, so like a block it takes a suffix as written: `loop { … }.v`.
        | ExprKind::Loop { .. } => PRIMARY,
        // A `for` is a primary of the grammar, but its body block ends it, so as the operand of
        // an operator it is written in parentheses: `(for x in xs { x }).rank`.
        ExprKind::For { .. } => ELSE,
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

/// Whether `e`'s text starts with a block or a record display, which a lambda's body or an
/// `else` default that is not itself a block may not.
fn starts_with_block(mut e: &Expr) -> bool {
    loop {
        match &e.kind {
            ExprKind::Block(_) | ExprKind::Record(_) | ExprKind::Set(_) | ExprKind::Map(_) => {
                return true;
            }
            ExprKind::Binary(_, of, _)
            | ExprKind::Range(of, _)
            | ExprKind::In { of, .. }
            | ExprKind::Reduce { of, .. }
            | ExprKind::Read { of, .. }
            | ExprKind::Call { callee: of, .. }
            | ExprKind::Index(of, _)
            | ExprKind::Member { of, .. }
            | ExprKind::Spread { of, .. }
            | ExprKind::Is { of, .. }
            | ExprKind::With { of, .. }
            | ExprKind::Else { of, .. } => e = of,
            _ => return false,
        }
    }
}

/// Whether `e`, as an `if` condition or a `for` source or guard, holds a block outside any
/// bracket, which the grammar's `HEAD` forbids there, since the head's `{` opens the branch;
/// a `for` there is also written in parentheses, which the grammar allows without them.
fn head_unsafe(e: &Expr) -> bool {
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        match &e.kind {
            ExprKind::Block(_) | ExprKind::For { .. } | ExprKind::Loop { .. } => return true,
            ExprKind::Else { of, default, .. } => stack.extend([&**of, &**default]),
            ExprKind::Binary(_, a, b)
            | ExprKind::In { of: a, set: b, .. }
            | ExprKind::Reduce { of: a, op: b } => stack.extend([&**a, &**b]),
            ExprKind::Range(a, b) => {
                stack.push(a);
                stack.extend(b.bound().map(|b| &**b));
            }
            ExprKind::Unary(_, a)
            | ExprKind::Is { of: a, .. }
            | ExprKind::With { of: a, .. }
            | ExprKind::Call { callee: a, .. }
            | ExprKind::Index(a, _)
            | ExprKind::Member { of: a, .. }
            | ExprKind::Spread { of: a, .. }
            | ExprKind::Read { of: a, .. } => stack.push(a),
            _ => {}
        }
    }
    false
}

/// Whether the text of `e` starts with a non-negated `in`, which as an index key `x[k]` would
/// be read as the key `i in s`: such a key is written in parentheses.
fn starts_with_in(mut e: &Expr) -> bool {
    loop {
        match &e.kind {
            ExprKind::In { negated: false, .. } => return true,
            ExprKind::Binary(_, of, _)
            | ExprKind::Range(of, _)
            | ExprKind::In { of, .. }
            | ExprKind::Reduce { of, .. }
            | ExprKind::Read { of, .. }
            | ExprKind::Call { callee: of, .. }
            | ExprKind::Index(of, _)
            | ExprKind::Member { of, .. }
            | ExprKind::Spread { of, .. }
            | ExprKind::Is { of, .. }
            | ExprKind::With { of, .. }
            | ExprKind::Else { of, .. } => e = of,
            _ => return false,
        }
    }
}

/// The jobs that write `e` as a `head(…)` of the grammar, at level `ELSE`: in parentheses when
/// it holds a block outside any bracket.
fn head(e: &Expr, ind: usize) -> Vec<Job<'_>> {
    let job = Job::Expr { e, min: ELSE, ind };
    if head_unsafe(e) {
        vec![put("("), job, put(")")]
    } else {
        vec![job]
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
    /// The text so far. Each level adds only its own text, so writing a nest of depth `d` is
    /// linear in the output.
    pieces: Vec<Cow<'a, str>>,
    /// How many of `pieces` hold a line break.
    breaks: usize,
}

/// A statement with the comments it keeps, and whether a blank line precedes it.
struct Entry<'a> {
    stmt: &'a Stmt,
    blank: bool,
    leading: Vec<Span>,
    trailing: Vec<Span>,
}

/// Work left to write, in order from the top of the stack: nesting costs heap, not thread stack.
enum Job<'a> {
    /// Text.
    Put(Cow<'a, str>),
    /// The lines of `stmts`, which stand in `region` of the text, at indentation `ind`, each
    /// line ending in a newline. With `bare`, an export of one value is a trailing expression.
    Stmts {
        stmts: &'a [Stmt],
        region: Span,
        ind: usize,
        bare: bool,
    },
    /// One of those lines: `first` says it is the first.
    Line {
        entry: Entry<'a>,
        first: bool,
        ind: usize,
        bare: bool,
    },
    /// The comments after a statement written at `ind`, and its newline.
    After {
        span: Span,
        trailing: Vec<Span>,
        ind: usize,
    },
    /// The comments that end a `region` after byte `prev`; `any` says a statement came before.
    Rest {
        prev: usize,
        region: Span,
        ind: usize,
        any: bool,
    },
    /// The text of a statement, which starts at indentation `ind`.
    Stmt { s: &'a Stmt, ind: usize, bare: bool },
    /// The text of `e` in a position that takes forms of level `min` and above.
    Expr { e: &'a Expr, min: u8, ind: usize },
    /// The text of `e`, with no parentheses for its level.
    Raw { e: &'a Expr, ind: usize },
    /// The operand of a call, index or member: a number literal is parenthesized, so that its
    /// `.` is not read as a decimal point.
    Postfix { of: &'a Expr, ind: usize },
    /// A lambda's body or an `else` default: a block, or an expression of level `min` that
    /// does not start with a block.
    Branch { e: &'a Expr, min: u8, ind: usize },
    /// The block `e`, standing at `place`, its first line at indentation `ind`.
    Block {
        e: &'a Expr,
        ind: usize,
        place: Place,
    },
    /// The end of a block of one statement, which began at piece `mark`, written when `breaks`
    /// line breaks had been.
    BlockEnd {
        mark: usize,
        breaks: usize,
        ind: usize,
    },
    /// `exprs`, each at level `min`, with `, ` between.
    Exprs {
        exprs: &'a [Expr],
        min: u8,
        ind: usize,
    },
    /// Named arguments or a display's fields, each value at level `min`, with `, ` between;
    /// `comma` says one goes before the first.
    Named {
        args: &'a [(String, Expr)],
        min: u8,
        comma: bool,
        ind: usize,
    },
    /// The updates of a `with`, with `, ` between.
    Updates { updates: &'a [Update], ind: usize },
    /// A struct's fields, with `, ` between.
    Fields { fields: &'a [Field], ind: usize },
    /// `test` cases, with `, ` between.
    Cases {
        cases: &'a [(Expr, Expr)],
        ind: usize,
    },
    /// Parameters, with `, ` between.
    Params { params: &'a [Param], ind: usize },
    /// Output ports, with `, ` between.
    Ports(&'a [Port]),
    /// The type `t` in a position that takes levels `min` and above.
    Ty { t: &'a Type, min: u8 },
    /// `types`, each at level `min`, with `sep` between.
    Types {
        types: &'a [Type],
        min: u8,
        sep: &'static str,
    },
    /// Parameters of a function type or arguments of an applied type, with `, ` between.
    TypeParams(&'a [TypeParam]),
    /// The fields of a record type, with `, ` between.
    RecordType(&'a [(String, Type)]),
    /// A pattern.
    Pattern(&'a Pattern),
    /// Patterns, with `, ` between.
    Patterns(&'a [Pattern]),
    /// Fields of a pattern, `f: p` or `f:`, with `, ` between.
    FieldPats(&'a [(String, Option<Pattern>)]),
    /// The arms of a `match` whose `match` is at indentation `ind`, each on a line of its own
    /// and followed by `,`, with the comments in `prev..end` that the arms do not hold.
    Arms {
        arms: &'a [Arm],
        prev: usize,
        end: usize,
        ind: usize,
    },
    /// Annotations, each followed by a space.
    Annots { annots: &'a [Annot], ind: usize },
    /// Index keys, each `[k]`.
    Keys { keys: &'a [IndexKey], ind: usize },
    /// A boundary's items, `sep` before the first and `, ` before each other.
    Boundary {
        items: &'a [BoundaryItem],
        sep: &'static str,
        ind: usize,
    },
}

/// Pushes jobs to run in the order written.
macro_rules! then {
    ($stack:expr; $($job:expr),* $(,)?) => {
        $stack.extend([$($job),*].into_iter().rev())
    };
}

fn indent(n: usize) -> String {
    "  ".repeat(n)
}

fn put<'a>(s: impl Into<Cow<'a, str>>) -> Job<'a> {
    Job::Put(s.into())
}

impl<'a> Formatter<'a> {
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

    /// Whether the source has a blank line in `from..to`.
    fn blank(&self, from: usize, to: usize) -> bool {
        self.text[from..to].matches('\n').count() > 1
    }

    fn has_comment(&self, span: Span) -> bool {
        span.start < span.end && self.comments.range(span.start..span.end).next().is_some()
    }

    fn put(&mut self, s: impl Into<Cow<'a, str>>) {
        let s = s.into();
        self.breaks += usize::from(s.contains('\n'));
        self.pieces.push(s);
    }

    /// Runs `job` and all that it leaves, and returns the text.
    fn run(mut self, job: Job<'a>) -> String {
        let mut stack = vec![job];
        while let Some(job) = stack.pop() {
            self.step(job, &mut stack);
        }
        self.pieces.concat()
    }

    fn step(&mut self, job: Job<'a>, stack: &mut Vec<Job<'a>>) {
        match job {
            Job::Put(s) => self.put(s),
            Job::Stmts {
                stmts,
                region,
                ind,
                bare,
            } => self.stmts(stmts, region, ind, bare, stack),
            Job::Line {
                entry,
                first,
                ind,
                bare,
            } => {
                let pad = indent(ind);
                if entry.blank && !first {
                    self.put("\n");
                }
                // A blank line among the leading comments, or after them, is kept: a comment the
                // formatter moved to its own line after a statement leads the next one when read
                // again, and keeping the blank line after it keeps formatting idempotent.
                let mut end = None;
                for c in entry.leading {
                    if end.is_some_and(|e| self.blank(e, c.start)) {
                        self.put("\n");
                    }
                    self.put(format!("{pad}{}\n", &self.text[c.start..c.end]));
                    end = Some(c.end);
                }
                if end.is_some_and(|e| self.blank(e, entry.stmt.span.start)) {
                    self.put("\n");
                }
                self.put(pad);
                let (s, trailing) = (entry.stmt, entry.trailing);
                then![stack;
                    Job::Stmt { s, ind, bare },
                    Job::After { span: s.span, trailing, ind },
                ];
            }
            Job::After {
                span,
                trailing,
                ind,
            } => {
                let pad = indent(ind);
                let mut tail = self.take(span.start, span.end);
                tail.extend(trailing);
                let mut after_line_comment = false;
                for c in tail {
                    let body = &self.text[c.start..c.end];
                    self.put(if after_line_comment {
                        format!("\n{pad}{body}")
                    } else {
                        format!(" {body}")
                    });
                    after_line_comment = body.starts_with("//");
                }
                self.put("\n");
            }
            Job::Rest {
                prev,
                region,
                ind,
                any,
            } => {
                let pad = indent(ind);
                let rest = self.take(prev, region.end);
                // As among a statement's leading comments, a blank line among these is kept.
                let mut end = if any { Some(prev) } else { None };
                for c in rest {
                    if end.is_some_and(|e| self.blank(e, c.start)) {
                        self.put("\n");
                    }
                    self.put(format!("{pad}{}\n", &self.text[c.start..c.end]));
                    end = Some(c.end);
                }
            }
            Job::Stmt { s, ind, bare } => self.stmt(s, ind, bare, stack),
            Job::Expr { e, min, ind } => {
                if level(e) < min {
                    self.put("(");
                    stack.push(put(")"));
                }
                self.raw(e, ind, stack);
            }
            Job::Raw { e, ind } => self.raw(e, ind, stack),
            Job::Postfix { of, ind } => match of.kind {
                ExprKind::Int { .. } | ExprKind::Float(_) | ExprKind::Rat(_) => {
                    self.put("(");
                    stack.push(put(")"));
                    self.raw(of, ind, stack);
                }
                _ => stack.push(Job::Expr {
                    e: of,
                    min: POSTFIX,
                    ind,
                }),
            },
            Job::Branch { e, min, ind } => match e.kind {
                ExprKind::Block(_) => self.block(e, ind, Place::Branch, stack),
                _ if starts_with_block(e) && level(e) >= min => {
                    self.put("(");
                    stack.push(put(")"));
                    self.raw(e, ind, stack);
                }
                _ => stack.push(Job::Expr { e, min, ind }),
            },
            Job::Block { e, ind, place } => self.block(e, ind, place, stack),
            Job::BlockEnd { mark, breaks, ind } => {
                // With no line break, the block is on its own line, which no indentation enters;
                // otherwise its statement is on a line of its own.
                if self.breaks == breaks {
                    self.pieces[mark] = "{ ".into();
                    self.put(" }");
                } else {
                    self.pieces[mark] = format!("{{\n{}", indent(ind + 1)).into();
                    self.put(format!("\n{}}}", indent(ind)));
                }
            }
            Job::Exprs { exprs, min, ind } => {
                if let Some((e, rest)) = exprs.split_first() {
                    if !rest.is_empty() {
                        then![stack;
                            put(", "),
                            Job::Exprs { exprs: rest, min, ind },
                        ];
                    }
                    stack.push(Job::Expr { e, min, ind });
                }
            }
            Job::Named {
                args,
                min,
                comma,
                ind,
            } => {
                if let Some(((n, v), rest)) = args.split_first() {
                    if comma {
                        self.put(", ");
                    }
                    stack.push(Job::Named {
                        args: rest,
                        min,
                        comma: true,
                        ind,
                    });
                    match &v.kind {
                        ExprKind::Name(m) if m == n => self.put(format!("{n}:")),
                        _ => {
                            self.put(format!("{n}: "));
                            stack.push(Job::Expr { e: v, min, ind });
                        }
                    }
                }
            }
            Job::Keys { keys, ind } => {
                if let Some((k, rest)) = keys.split_first() {
                    then![stack; put("]"), Job::Keys { keys: rest, ind }];
                    match k {
                        IndexKey::In { name, set } => {
                            self.put(format!("[{name} in "));
                            stack.push(Job::Expr {
                                e: set,
                                min: LAMBDA,
                                ind,
                            });
                        }
                        IndexKey::At(e) if starts_with_in(e) => {
                            self.put("[(");
                            then![stack; Job::Expr { e, min: LAMBDA, ind }, put(")")];
                        }
                        IndexKey::At(e) => {
                            self.put("[");
                            stack.push(Job::Expr {
                                e,
                                min: LAMBDA,
                                ind,
                            });
                        }
                    }
                }
            }
            Job::Boundary { items, sep, ind } => {
                if let Some((b, rest)) = items.split_first() {
                    stack.push(Job::Boundary {
                        items: rest,
                        sep: ", ",
                        ind,
                    });
                    self.put(format!("{sep}{}", b.name));
                    then![stack;
                        Job::Keys { keys: &b.keys, ind },
                        put(" = "),
                        Job::Expr { e: &b.value, min: LAMBDA, ind },
                    ];
                }
            }
            Job::Updates { updates, ind } => {
                if let Some((u, rest)) = updates.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::Updates { updates: rest, ind }];
                    }
                    self.put(format!("{} = ", u.path.join(".")));
                    stack.push(Job::Expr {
                        e: &u.value,
                        min: LAMBDA,
                        ind,
                    });
                }
            }
            Job::Fields { fields, ind } => {
                if let Some((f, rest)) = fields.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::Fields { fields: rest, ind }];
                    }
                    match f {
                        Field::Typed {
                            name, ty, default, ..
                        } => {
                            self.put(format!("{name}: "));
                            if let Some(e) = default {
                                then![stack;
                                    Job::Ty { t: ty, min: 0 },
                                    put(" = "),
                                    Job::Expr { e, min: LAMBDA, ind },
                                ];
                            } else {
                                stack.push(Job::Ty { t: ty, min: 0 });
                            }
                        }
                        Field::Import { path, .. } => self.put(format!("import {path}")),
                    }
                }
            }
            Job::Cases { cases, ind } => {
                if let Some(((a, b), rest)) = cases.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::Cases { cases: rest, ind }];
                    }
                    then![stack;
                        Job::Expr { e: a, min: ELSE, ind },
                        put(" -> "),
                        Job::Expr { e: b, min: ELSE, ind },
                    ];
                }
            }
            Job::Params { params, ind } => {
                if let Some((p, rest)) = params.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::Params { params: rest, ind }];
                    }
                    if p.positional && p.tuple.is_none() {
                        self.put("positional ");
                    }
                    self.put(p.name.as_str());
                    if let Some(e) = &p.default {
                        then![stack;
                            put(" = "),
                            Job::Expr { e, min: LAMBDA, ind },
                        ];
                    }
                    if let Some(t) = &p.ty {
                        then![stack; put(": "), Job::Ty { t, min: 0 }];
                    }
                }
            }
            Job::Ports(ports) => {
                if let Some((p, rest)) = ports.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::Ports(rest)];
                    }
                    self.put(format!("{}: ", p.name));
                    stack.push(Job::Ty { t: &p.ty, min: 0 });
                }
            }
            Job::Ty { t, min } => {
                if type_level(t) < min {
                    self.put("(");
                    stack.push(put(")"));
                }
                self.ty(t, stack);
            }
            Job::Types { types, min, sep } => {
                if let Some((t, rest)) = types.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(sep), Job::Types { types: rest, min, sep }];
                    }
                    stack.push(Job::Ty { t, min });
                }
            }
            Job::TypeParams(params) => {
                if let Some((p, rest)) = params.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::TypeParams(rest)];
                    }
                    match &p.name {
                        Some(n) if p.positional => self.put(format!("positional {n}: ")),
                        Some(n) => self.put(format!("{n}: ")),
                        None => {}
                    }
                    stack.push(Job::Ty { t: &p.ty, min: 0 });
                }
            }
            Job::RecordType(fields) => {
                if let Some(((n, t), rest)) = fields.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::RecordType(rest)];
                    }
                    self.put(format!("{n}: "));
                    stack.push(Job::Ty { t, min: 0 });
                }
            }
            Job::Pattern(p) => self.pattern(p, stack),
            Job::Patterns(ps) => {
                if let Some((p, rest)) = ps.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::Patterns(rest)];
                    }
                    self.pattern(p, stack);
                }
            }
            Job::FieldPats(fields) => {
                if let Some(((n, p), rest)) = fields.split_first() {
                    if !rest.is_empty() {
                        then![stack; put(", "), Job::FieldPats(rest)];
                    }
                    match p {
                        Some(p) => {
                            self.put(format!("{n}: "));
                            self.pattern(p, stack);
                        }
                        None => self.put(format!("{n}:")),
                    }
                }
            }
            Job::Arms {
                arms,
                prev,
                end,
                ind,
            } => {
                let pad = indent(ind + 1);
                let Some((a, rest)) = arms.split_first() else {
                    // The comments after the last arm, each on its own line before the `}`.
                    for c in self.take(prev, end) {
                        self.put(format!("\n{pad}{}", &self.text[c.start..c.end]));
                    }
                    return;
                };
                for c in self.take(prev, a.span.start) {
                    self.put(format!("\n{pad}{}", &self.text[c.start..c.end]));
                }
                self.put(format!("\n{pad}"));
                let next = rest.first().map_or(end, |n| n.span.start);
                let trailing = self.take_same_line(a.span.end, next);
                let after: String = trailing
                    .iter()
                    .map(|c| format!(" {}", &self.text[c.start..c.end]))
                    .collect();
                stack.push(Job::Arms {
                    arms: rest,
                    prev: trailing.last().map_or(a.span.end, |c| c.end),
                    end,
                    ind,
                });
                let guard = a.guard.iter().flat_map(|g| {
                    [
                        put(" where "),
                        Job::Expr {
                            e: g,
                            min: ELSE,
                            ind: ind + 1,
                        },
                    ]
                });
                let jobs = [Job::Pattern(&a.pattern)].into_iter().chain(guard).chain([
                    put(" -> "),
                    Job::Branch {
                        e: &a.body,
                        min: LAMBDA,
                        ind: ind + 1,
                    },
                    put(format!(",{after}")),
                ]);
                let mark = stack.len();
                stack.extend(jobs);
                stack[mark..].reverse();
            }
            Job::Annots { annots, ind } => {
                if let Some((a, rest)) = annots.split_first() {
                    stack.push(Job::Annots { annots: rest, ind });
                    self.annot(a, " ", ind, stack);
                }
            }
        }
    }

    /// The pattern `p` as written: a type pattern's type is at the level of a union.
    fn pattern(&mut self, p: &'a Pattern, stack: &mut Vec<Job<'a>>) {
        match p {
            Pattern::Name(n, _) => self.put(n.as_str()),
            Pattern::Wild(_) => self.put("_"),
            Pattern::Tuple(items, _) => {
                self.put("(");
                then![stack; Job::Patterns(items), put(")")];
            }
            Pattern::Struct { name, fields, .. } => {
                self.put(format!("{name}("));
                then![stack; Job::FieldPats(fields), put(")")];
            }
            Pattern::Atom {
                name,
                fields,
                items,
                ..
            } => {
                self.put(format!("#{name}"));
                if !fields.is_empty() {
                    self.put("(");
                    then![stack; Job::FieldPats(fields), put(")")];
                } else if !items.is_empty() {
                    self.put("(");
                    then![stack; Job::Patterns(items), put(")")];
                }
            }
            Pattern::Is { name, ty, .. } => {
                if let Some(n) = name {
                    self.put(format!("{n} "));
                }
                self.put("is ");
                stack.push(Job::Ty { t: ty, min: 2 });
            }
            Pattern::Lit(e) => self.raw(e, 0, stack),
            Pattern::Range { from, to, .. } => {
                stack.extend(to.bound().map(|b| Job::Pattern(b)));
                then![stack; Job::Pattern(from), put(to.op())];
            }
        }
    }

    /// Finds the comments and blank lines of `stmts` and leaves its lines to write.
    fn stmts(
        &mut self,
        stmts: &'a [Stmt],
        region: Span,
        ind: usize,
        bare: bool,
        stack: &mut Vec<Job<'a>>,
    ) {
        // The comments and blank lines are found in source order, where the export may not be
        // last.
        let mut in_order: Vec<&Stmt> = stmts.iter().collect();
        in_order.sort_by_key(|s| s.span.start);
        let mut entries = Vec::new();
        let mut prev = region.start;
        for (i, s) in in_order.iter().enumerate() {
            let leading = self.take(prev, s.span.start);
            let first = leading.first().map_or(s.span.start, |c| c.start);
            let blank = i > 0 && self.blank(prev, first);
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
        // The `while` guards go first and the `until` guards and the export last, in the
        // order the builder stores them.
        entries.sort_by_key(|e| e.stmt.kind.place());
        stack.push(Job::Rest {
            prev,
            region,
            ind,
            any: !entries.is_empty(),
        });
        for (i, entry) in entries.into_iter().enumerate().rev() {
            stack.push(Job::Line {
                entry,
                first: i == 0,
                ind,
                bare,
            });
        }
    }

    fn stmt(&mut self, s: &'a Stmt, ind: usize, bare: bool, stack: &mut Vec<Job<'a>>) {
        let exprs = |exprs| Job::Exprs {
            exprs,
            min: LAMBDA,
            ind,
        };
        let value = |e| Job::Expr {
            e,
            min: LAMBDA,
            ind,
        };
        let with = |items| Job::Boundary {
            items,
            sep: " with ",
            ind,
        };
        match &s.kind {
            StmtKind::Bind {
                targets,
                value: v,
                boundary,
            } => {
                let ts: Vec<&str> = targets
                    .iter()
                    .map(|t| match t {
                        Target::Name(n, _) => n.as_str(),
                        Target::Wild => "_",
                    })
                    .collect();
                self.put(ts.join(", "));
                self.put(" = ");
                then![stack; value(v), with(boundary), put(";")];
            }
            StmtKind::Mutable(decl) => {
                self.put("mutable ");
                stack.push(Job::Stmt {
                    s: decl,
                    ind,
                    bare: false,
                });
            }
            StmtKind::Local(decl) => {
                self.put("local ");
                stack.push(Job::Stmt {
                    s: decl,
                    ind,
                    bare: false,
                });
            }
            StmtKind::IndexedDef(d) => {
                self.put(d.name.as_str());
                then![stack;
                    Job::Keys { keys: &d.keys, ind },
                    put(" = "),
                    value(&d.value),
                    with(&d.boundary),
                    put(";"),
                ];
            }
            StmtKind::While(c) => {
                self.put("while ");
                then![stack; value(c), put(";")];
            }
            StmtKind::Until(c) => {
                self.put("until ");
                then![stack; value(c), put(";")];
            }
            // A statement that starts with `{` would be read as a block or a display.
            StmtKind::Expr(e) if starts_with_block(e) => {
                self.put("(");
                then![stack; value(e), put(");")];
            }
            StmtKind::Expr(e) => then![stack; value(e), put(";")],
            StmtKind::Return(es) if bare && es.len() == 1 => stack.push(value(&es[0])),
            StmtKind::Return(es) => {
                self.put("return ");
                then![stack; exprs(es), put(";")];
            }
            StmtKind::Push { port, value: v } => {
                self.put(format!("{port} <- "));
                then![stack; value(v), put(";")];
            }
            StmtKind::Function(f) => {
                self.put(format!("{}(", f.name));
                self.function(f, true, ind, stack);
            }
            StmtKind::Method(m) => {
                self.put(format!("{}.{}", m.receiver, m.function.name));
                if m.called {
                    self.put("(");
                }
                self.function(&m.function, m.called, ind, stack);
            }
            StmtKind::Struct(st) if st.fields.is_empty() => {
                self.put(format!("struct {} {{}}", st.name));
            }
            StmtKind::Struct(st) => {
                self.put(format!("struct {} {{ ", st.name));
                then![stack;
                    Job::Fields { fields: &st.fields, ind },
                    put(" }"),
                ];
            }
            StmtKind::Type(t) => {
                self.put(format!("type {}", t.name));
                if !t.params.is_empty() {
                    self.put(format!("({})", t.params.join(", ")));
                }
                self.put(" = ");
                then![stack; Job::Ty { t: &t.ty, min: 0 }, put(";")];
            }
            StmtKind::Import(i) => {
                self.put(format!("import {}", i.path));
                match &i.kind {
                    ImportKind::Qualified => {}
                    ImportKind::Alias(a) => self.put(format!(" as {a}")),
                    ImportKind::Selective(names) => self.put(format!(".{{{}}}", names.join(", "))),
                }
                if let Some(h) = &i.pin {
                    self.put(format!(" @hash(\"{h}\")"));
                }
                self.put(";");
            }
            StmtKind::Annotated { annots, decl } => {
                then![stack;
                    Job::Annots { annots, ind },
                    Job::Stmt { s: decl, ind, bare: false },
                ];
            }
            StmtKind::UnitAnnot(a) => self.annot(a, ";", ind, stack),
        }
    }

    /// The annotation `a`, `@name` or `@name(args)`, followed by `end`.
    fn annot(&mut self, a: &'a Annot, end: &'static str, ind: usize, stack: &mut Vec<Job<'a>>) {
        self.put(format!("@{}", a.name));
        if !a.called {
            return self.put(end);
        }
        self.put("(");
        then![stack;
            Job::Exprs { exprs: &a.positional, min: LAMBDA, ind },
            Job::Named {
                args: &a.named,
                min: LAMBDA,
                comma: !a.positional.is_empty(),
                ind,
            },
            put(format!("){end}")),
        ];
    }

    /// A function's text after its name and `(`: its parameters and `)` when `called`, then its
    /// ports, body and tests.
    fn function(&mut self, f: &'a Function, called: bool, ind: usize, stack: &mut Vec<Job<'a>>) {
        let value = |e| Job::Expr {
            e,
            min: LAMBDA,
            ind,
        };
        let mut jobs = Vec::new();
        if called {
            jobs.extend([
                Job::Params {
                    params: &f.params,
                    ind,
                },
                put(")"),
            ]);
        }
        if let Some(ports) = &f.ports {
            jobs.extend([put(" -> ("), Job::Ports(ports), put(")")]);
        }
        if f.equation {
            jobs.extend([put(" = "), value(&f.body)]);
            if f.tests.is_empty() {
                jobs.push(put(";"));
            }
        } else {
            jobs.extend([
                put(" "),
                Job::Block {
                    e: &f.body,
                    ind,
                    place: Place::Body,
                },
            ]);
        }
        if !f.tests.is_empty() {
            jobs.extend([
                put(format!("\n{}test {{ ", indent(ind + 1))),
                Job::Cases {
                    cases: &f.tests,
                    ind,
                },
                put(" }"),
            ]);
        }
        stack.extend(jobs.into_iter().rev());
    }

    fn raw(&mut self, e: &'a Expr, ind: usize, stack: &mut Vec<Job<'a>>) {
        let at = |e, min| Job::Expr { e, min, ind };
        match &e.kind {
            ExprKind::Int { .. } | ExprKind::Float(_) | ExprKind::Rat(_) | ExprKind::Str(_) => {
                // A grouped literal's span holds its parentheses; a literal never starts with `(`.
                let mut t = self.text[e.span.start..e.span.end].trim();
                while let Some(inner) = t.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
                    t = inner.trim();
                }
                self.put(t);
            }
            ExprKind::Bool(b) => self.put(b.to_string()),
            ExprKind::Atom(a) => self.put(format!("#{a}")),
            ExprKind::Name(n) => self.put(n.as_str()),
            ExprKind::Unary(op, x) => match x.kind {
                ExprKind::Unary(..) => {
                    self.put(format!("{op}("));
                    then![stack; Job::Raw { e: x, ind }, put(")")];
                }
                _ => {
                    self.put(*op);
                    stack.push(at(x, PREFIX));
                }
            },
            ExprKind::Binary(op, a, b) => {
                let l = binary_level(op);
                let (lmin, rmin) = match l {
                    POWER => (POSTFIX, PREFIX),
                    EQUALITY | RELATION => (l + 1, l + 1),
                    _ => (l, l + 1),
                };
                then![stack; at(a, lmin), put(format!(" {op} ")), at(b, rmin)];
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                curry,
            } => {
                let comma = !positional.is_empty();
                let dots = match (curry, comma || !named.is_empty()) {
                    (true, true) => ", ...",
                    (true, false) => "...",
                    (false, _) => "",
                };
                then![stack;
                    Job::Postfix { of: callee, ind },
                    put("("),
                    Job::Exprs { exprs: positional, min: LAMBDA, ind },
                    Job::Named { args: named, min: LAMBDA, comma, ind },
                    put(dots),
                    put(")"),
                ];
            }
            ExprKind::Index(of, k) => {
                then![stack;
                    Job::Postfix { of, ind },
                    put("["),
                    at(k, LAMBDA),
                    put("]"),
                ];
            }
            ExprKind::Member { of, name, safe } => {
                let dot = if *safe { "?." } else { "." };
                then![stack; Job::Postfix { of, ind }, put(format!("{dot}{name}"))];
            }
            ExprKind::Tuple(items) => {
                self.put("(");
                then![stack;
                    Job::Exprs { exprs: items, min: LAMBDA, ind },
                    put(")"),
                ];
            }
            ExprKind::Lambda { params, body } => {
                stack.push(Job::Branch {
                    e: body,
                    min: LAMBDA,
                    ind,
                });
                stack.push(put(" -> "));
                match &params[..] {
                    [p] if !p.positional && p.ty.is_none() && p.default.is_none() => {
                        self.put(p.name.as_str());
                    }
                    _ => {
                        self.put("(");
                        then![stack; Job::Params { params, ind }, put(")")];
                    }
                }
            }
            ExprKind::Is { of, ty: t, negated } => {
                let not = if *negated { "not " } else { "" };
                then![stack;
                    at(of, REDUCE),
                    put(format!(" is {not}")),
                    Job::Ty { t, min: 2 },
                ];
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                stack.push(Job::Branch {
                    e: default,
                    min: OR,
                    ind,
                });
                if let Some(p) = pattern {
                    then![stack; Job::Pattern(p), put(" -> ")];
                }
                then![stack; at(of, ELSE), put(" else ")];
            }
            ExprKind::Block(_) => self.block(e, ind, Place::Operand, stack),
            ExprKind::Record(fields) => {
                self.put("{ ");
                then![stack;
                    Job::Named { args: fields, min: ELSE, comma: false, ind },
                    put(" }"),
                ];
            }
            ExprKind::With { of, updates } => {
                then![stack;
                    at(of, REDUCE),
                    put(" with { "),
                    Job::Updates { updates, ind },
                    put(" }"),
                ];
            }
            ExprKind::This => self.put("this"),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let otherwise = match otherwise.kind {
                    ExprKind::If { .. } => Job::Raw { e: otherwise, ind },
                    _ => Job::Block {
                        e: otherwise,
                        ind,
                        place: Place::Branch,
                    },
                };
                let unsafe_head = head_unsafe(cond);
                then![stack;
                    at(cond, ELSE),
                    put(if unsafe_head { ") " } else { " " }),
                    Job::Block { e: then, ind, place: Place::Branch },
                    put(" else "),
                    otherwise,
                ];
                self.put(if unsafe_head { "if (" } else { "if " });
            }
            ExprKind::Match { of, arms } => {
                let unsafe_head = head_unsafe(of);
                self.put(if unsafe_head { "match (" } else { "match " });
                then![stack;
                    at(of, ELSE),
                    put(if unsafe_head { ") {" } else { " {" }),
                    Job::Arms { arms, prev: of.span.end, end: e.span.end, ind },
                    put(format!("\n{}}}", indent(ind))),
                ];
            }
            ExprKind::Range(from, to) => {
                stack.extend(to.bound().map(|b| at(b, ADDITIVE)));
                then![stack; at(from, ADDITIVE), put(to.op())];
            }
            ExprKind::In { of, set, negated } => {
                let op = if *negated { " not in " } else { " in " };
                then![stack; at(of, REDUCE), put(op), at(set, REDUCE)];
            }
            ExprKind::Reduce { of, op } => {
                then![stack; at(of, REDUCE), put(" >< "), at(op, POSTFIX)];
            }
            ExprKind::Read { of, name } => {
                then![stack; Job::Postfix { of, ind }, put(format!("::{name}"))];
            }
            ExprKind::Spread { of, name } => {
                then![stack; Job::Postfix { of, ind }, put(format!("*.{name}"))];
            }
            ExprKind::Break(of) => {
                self.put("break ");
                stack.push(at(of, ELSE));
            }
            ExprKind::SortKey { desc, key } => {
                self.put(if *desc { "desc " } else { "asc " });
                stack.push(at(key, LAMBDA));
            }
            ExprKind::Loop { label, body } => {
                match label {
                    Some(t) => self.put(format!("loop {t} ")),
                    None => self.put("loop "),
                }
                stack.push(Job::Block {
                    e: body,
                    ind,
                    place: Place::Branch,
                });
            }
            ExprKind::Section(op) => self.put(format!("({op})")),
            ExprKind::Array(items) => {
                self.put("[");
                then![stack;
                    Job::Exprs { exprs: items, min: ELSE, ind },
                    put("]"),
                ];
            }
            ExprKind::Set(items) => {
                self.put("{ ");
                then![stack;
                    Job::Exprs { exprs: items, min: ELSE, ind },
                    put(" }"),
                ];
            }
            ExprKind::Map(entries) if entries.is_empty() => self.put("{}"),
            ExprKind::Map(entries) => {
                self.put("{ ");
                then![stack; Job::Cases { cases: entries, ind }, put(" }")];
            }
            ExprKind::For {
                binders,
                source,
                guard,
                body,
            } => {
                let binders: Vec<&str> = binders
                    .iter()
                    .map(|t| match t {
                        Target::Name(n, _) => n.as_str(),
                        Target::Wild => "_",
                    })
                    .collect();
                self.put(format!("for {} in ", binders.join(" -> ")));
                let mut jobs = head(source, ind);
                if let Some(g) = guard {
                    jobs.push(put(" where "));
                    jobs.extend(head(g, ind));
                }
                jobs.extend([
                    put(" "),
                    Job::Block {
                        e: body,
                        ind,
                        place: Place::Branch,
                    },
                ]);
                stack.extend(jobs.into_iter().rev());
            }
        }
    }

    fn block(&mut self, e: &'a Expr, ind: usize, place: Place, stack: &mut Vec<Job<'a>>) {
        let ExprKind::Block(stmts) = &e.kind else {
            unreachable!("a block")
        };
        let bare = !(place == Place::Operand && stmts.len() == 1);
        if place != Place::Body
            && let [s] = &stmts[..]
            && matches!(s.kind, StmtKind::Return(_))
            && !self.has_comment(e.span)
        {
            // With no comment inside, the block is this one statement. Its opening is known
            // only when the statement is written, so a piece is kept for it.
            let mark = self.pieces.len();
            self.pieces.push(Cow::Borrowed(""));
            let breaks = self.breaks;
            stack.push(Job::BlockEnd { mark, breaks, ind });
            stack.push(Job::Stmt {
                s,
                ind: ind + 1,
                bare,
            });
            return;
        }
        if stmts.is_empty() && !self.has_comment(e.span) {
            self.put("{ }");
            return;
        }
        let region = Span {
            start: e.span.start + 1,
            end: e.span.end - 1,
        };
        self.put("{\n");
        then![stack;
            Job::Stmts { stmts, region, ind: ind + 1, bare },
            put(format!("{}}}", indent(ind))),
        ];
    }

    fn ty(&mut self, t: &'a Type, stack: &mut Vec<Job<'a>>) {
        let list = |types, min, sep| Job::Types { types, min, sep };
        match &t.kind {
            TypeKind::Name(n) => self.put(n.as_str()),
            TypeKind::Atom(a) => self.put(format!("#{a}")),
            TypeKind::Every(Every::Atom) => self.put("#_"),
            TypeKind::Every(Every::Tuple) => self.put("(..)"),
            TypeKind::Every(Every::Struct) => self.put("{..}"),
            TypeKind::AtomAny(a) => self.put(format!("#{a}(..)")),
            TypeKind::Tuple(ts) => {
                self.put("(");
                let close = if ts.len() == 1 { ",)" } else { ")" };
                then![stack; list(ts, 0, ", "), put(close)];
            }
            TypeKind::Union(ts) => stack.push(list(ts, 3, " | ")),
            TypeKind::And(ts) => stack.push(list(ts, 4, " & ")),
            TypeKind::Diff(a, b) => {
                let min = match a.kind {
                    TypeKind::Diff(..) => 2,
                    _ => 4,
                };
                then![stack;
                    Job::Ty { t: a, min },
                    put(" \\ "),
                    Job::Ty { t: b, min: 4 },
                ];
            }
            TypeKind::Arrow {
                params,
                partial,
                result,
            } => {
                let arrow = if *partial { " ->? " } else { " -> " };
                then![stack; put(arrow), Job::Ty { t: result, min: 1 }];
                match &params[..] {
                    [
                        TypeParam {
                            name: None, ty: p, ..
                        },
                    ] => match p.kind {
                        TypeKind::Tuple(_) => {
                            self.put("(");
                            then![stack; Job::Ty { t: p, min: 0 }, put(")")];
                        }
                        _ => stack.push(Job::Ty { t: p, min: 2 }),
                    },
                    ps => {
                        self.put("(");
                        then![stack; Job::TypeParams(ps), put(")")];
                    }
                }
            }
            TypeKind::Bounded {
                lower,
                upper,
                result,
            } => {
                then![stack;
                    Job::Ty { t: lower, min: 2 },
                    put(" .. "),
                    Job::Ty { t: upper, min: 2 },
                    put(" -> "),
                    Job::Ty { t: result, min: 1 },
                ];
            }
            TypeKind::Apply(name, ps) => {
                self.put(format!("{name}("));
                then![stack; Job::TypeParams(ps), put(")")];
            }
            TypeKind::AtomApply(name, ps) => {
                self.put(format!("#{name}("));
                then![stack; Job::TypeParams(ps), put(")")];
            }
            TypeKind::Array(t) => {
                self.put("[");
                then![stack; Job::Ty { t, min: 0 }, put("]")];
            }
            TypeKind::For { ty, bounds } => {
                // The bounds go on the stack last first, so they print in order.
                for (i, b) in bounds.iter().enumerate().rev() {
                    then![stack; put(format!("{} in ", b.name)), Job::Ty { t: &b.carriers, min: 2 }];
                    if i > 0 {
                        stack.push(put(", "));
                    }
                }
                then![stack; Job::Ty { t: ty, min: 1 }, put(" for ")];
            }
            TypeKind::Record(fields) => {
                self.put("{ ");
                then![stack; Job::RecordType(fields), put(" }")];
            }
        }
    }
}

/// Type precedence levels: a bounds clause, an arrow, a union or difference, an intersection, a
/// primary.
fn type_level(t: &Type) -> u8 {
    match t.kind {
        TypeKind::For { .. } => 0,
        TypeKind::Arrow { .. } | TypeKind::Bounded { .. } => 1,
        TypeKind::Union(_) | TypeKind::Diff(..) => 2,
        TypeKind::And(_) => 3,
        _ => 6,
    }
}
