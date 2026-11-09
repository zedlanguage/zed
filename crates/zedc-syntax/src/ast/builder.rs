//! The builder of a syntax tree (`super`) and the steps every form's builder reads: the span,
//! words and children of a parse-tree node, the result a child built to, and the parts written
//! the same way in expressions, statements, types and patterns (arguments, a name written
//! once, a range's end, a literal). The forms' own steps are in the files above this one
//! (`super`, `super::stmts`, `super::types`, `super::body`, `super::neglit`), each file's
//! steps below the files that call them, since Zed forbids a cycle between files
//! (ZED_PORT_GAPS.md gap 10).

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use super::{Error, Expr, ExprKind, Note, Pattern, RangeEnd, Stmt, StmtKind, StrPart, Type};
use crate::lex::{Part, Span, Tok, Token};
use crate::parse::Tree;
use zedc_base::rejection::{Row, not_yet};

/// A tree to build from: a text's, or a string hole's.
pub(super) struct Level<'t> {
    pub(super) tokens: &'t [Token],
    pub(super) tree: &'t Tree,
    /// Where its own holes start in the list of all holes.
    pub(super) first: usize,
}

/// What a node of a parse tree builds to.
pub(super) enum Built {
    Expr(Expr),
    Type(Type),
    Pattern(Pattern),
    Stmt(Box<Stmt>),
}

/// The cache [`Builder::written_bare`] reads, one per source.
pub(super) type Bare<'a> = std::cell::OnceCell<std::collections::HashSet<&'a str>>;

/// The builder of one tree, a text's or a string hole's: what each node built to, until its
/// parent takes it.
pub(super) struct Builder<'a, 's: 'a> {
    pub(super) text: &'s str,
    pub(super) tokens: &'a [Token],
    pub(super) tree: &'a Tree,
    /// For each token, the index in `tree.holes` of its first hole.
    holes: Vec<usize>,
    /// The built holes of every level, and where this level's start.
    done: &'a mut [Option<Result<Expr, Error>>],
    first: usize,
    /// What the nodes built to, until their parents take them: those after `front` in the walk
    /// of `fill`, the latest at the front. What is taken leaves from the back, so this holds
    /// about one width of the tree, and the depth of a tree costs no stack. An error is a
    /// result like any other: the parent takes its children in written order, so the first
    /// error is the first in written order.
    pub(super) live: VecDeque<Option<Result<Built, Error>>>,
    /// Where in the walk of `fill` each node is, and where the walk has reached.
    pub(super) place: Vec<usize>,
    pub(super) front: usize,
    /// The names written in the source other than after a `.`, listed on first use.
    pub(super) bare: &'a Bare<'s>,
    /// The parent of each node of the tree, listed on the first rejection that names one.
    pub(super) parents: std::cell::OnceCell<Vec<usize>>,
}

impl<'a, 's> Builder<'a, 's> {
    pub(super) fn new(
        text: &'s str,
        level: &Level<'a>,
        done: &'a mut [Option<Result<Expr, Error>>],
        bare: &'a Bare<'s>,
    ) -> Builder<'a, 's> {
        let mut holes = Vec::with_capacity(level.tokens.len());
        let mut count = 0;
        for t in level.tokens {
            holes.push(count);
            if let Tok::Str(parts) = &t.tok {
                count += parts
                    .iter()
                    .filter(|p| matches!(p, Part::Hole { .. }))
                    .count();
            }
        }
        Builder {
            text,
            tokens: level.tokens,
            tree: level.tree,
            holes,
            done,
            first: level.first,
            live: VecDeque::new(),
            place: Vec::new(),
            front: 0,
            bare,
            parents: std::cell::OnceCell::new(),
        }
    }

    pub(super) fn span(&self, n: usize) -> Span {
        let node = &self.tree.nodes[n];
        Span {
            start: self.tokens[node.start].span.start,
            end: self.tokens[node.end - 1].span.end,
        }
    }

    pub(super) fn word(&self, i: usize) -> &'a str {
        let s = self.tokens[i].span;
        &self.text[s.start..s.end]
    }

    pub(super) fn kids(&self, n: usize) -> &'a [usize] {
        &self.tree.nodes[n].kids
    }

    /// The error for node `n`, a form this zedc parses and does not compile yet. The message
    /// names the kind of form in plain words ([`kind_of`]) and quotes its first line, cut at
    /// 60 characters, since a form may be a whole block.
    pub(super) fn later(&self, n: usize) -> Error {
        let s = self.span(n);
        let line = self.text[s.start..s.end]
            .lines()
            .next()
            .unwrap_or("")
            .trim_end();
        let quoted = match line.char_indices().nth(60) {
            Some((cut, _)) => format!("{}…", &line[..cut]),
            None if line.len() < s.end - s.start => format!("{line} …"),
            None => line.into(),
        };
        Error {
            row: None,
            span: s,
            message: not_yet(&format!("{} `{quoted}`", kind_of(self.tree.name(n)))),
            notes: Vec::new(),
        }
    }

    /// The expression node `n` built to.
    pub(super) fn node(&mut self, n: usize) -> Result<Expr, Error> {
        let e = self.body(n)?;
        if let ExprKind::Block(stmts) = &e.kind
            && self.tree.name(n) == "Block"
            && !matches!(
                stmts.last(),
                Some(Stmt {
                    kind: StmtKind::Return(_),
                    ..
                })
            )
        {
            // Only a brace in body position, after `->`, `else`, or an `if` or `for` head, makes
            // an empty block; elsewhere `{}` is the empty family (sec:lexical), which is what a
            // writer of `{}` there most likely meant.
            let message = if stmts.is_empty() {
                "this `{}` is an empty block, and a block gives a value, so it must export one: a brace \
                 after `->`, `else`, or the head of an `if` or a `for` is a block. To write the empty \
                 family there, write `{ {} }`, or `({})` after `->` or a fallback's `else`."
            } else {
                "this block exports nothing, and a block gives a value, so it must export one. End it \
                 with an expression, or with `return e;` to give the value `e`."
            };
            return Err(Error {
                row: None,
                span: e.span,
                message: message.into(),
                notes: Vec::new(),
            });
        }
        Ok(e)
    }

    /// What node `n` built to.
    pub(super) fn take(&mut self, n: usize) -> Option<Result<Built, Error>> {
        let i = self.place[n].checked_sub(self.front)?;
        self.live.get_mut(i)?.take()
    }

    /// The expression node `n` built to, which may be a block that exports nothing.
    pub(super) fn body(&mut self, n: usize) -> Result<Expr, Error> {
        match self.take(n) {
            Some(Ok(Built::Expr(e))) => Ok(e),
            Some(Err(e)) => Err(e),
            None if self.tree.name(n) == "Name" => Ok(Expr {
                kind: ExprKind::Name(self.word(self.tree.nodes[n].start).into()),
                span: self.span(n),
            }),
            Some(Ok(Built::Type(_) | Built::Pattern(_) | Built::Stmt(_))) | None => {
                Err(self.later(n))
            }
        }
    }

    /// The operator token at `i`, as the lexer's static text.
    pub(super) fn op(&self, i: usize) -> &'static str {
        match self.tokens[i].tok {
            Tok::Op(o) | Tok::Keyword(o) => o,
            _ => unreachable!("an operator token"),
        }
    }

    /// The end of a range whose operator is token `op`, its bound node `bound` built by `f`.
    pub(super) fn range_end<T>(
        &mut self,
        op: usize,
        bound: Option<usize>,
        f: impl FnOnce(&mut Self, usize) -> Result<T, Error>,
    ) -> Result<RangeEnd<T>, Error> {
        Ok(match (self.word(op), bound) {
            ("..<", Some(b)) => RangeEnd::Below(f(self, b)?),
            ("..=", Some(b)) => RangeEnd::Through(f(self, b)?),
            ("..", None) => RangeEnd::Open,
            _ => unreachable!("RangeTail = '..<' Additive | '..=' Additive | '..'"),
        })
    }

    /// Records the `what` named `name`, written at node `n`, in `seen`, or the error that it
    /// is `done` twice, with a note at the first.
    pub(super) fn once(
        &self,
        seen: &mut HashMap<&'a str, Span>,
        name: &'a str,
        n: usize,
        what: &str,
        done: &str,
    ) -> Result<(), Error> {
        let span = self.span(n);
        if let Some(&first) = seen.get(name) {
            return Err(Error {
                row: None,
                span,
                message: format!(
                    "the {what} `{name}` is {done} twice, and each {what} is {done} once. Remove \
                     one of the two."
                ),
                notes: vec![Note {
                    span: first,
                    text: format!("the first {what} `{name}`"),
                }],
            });
        }
        seen.insert(name, span);
        Ok(())
    }

    /// The arguments of node `n`, an `Args`, of the call or annotation written at `call`. The
    /// grammar takes them in any order; a positional one after a named one is the row "Named
    /// argument before a positional one".
    #[allow(clippy::type_complexity)]
    pub(super) fn args(
        &mut self,
        n: usize,
        call: Span,
    ) -> Result<(Vec<Expr>, Vec<(String, Expr)>, bool), Error> {
        let node = &self.tree.nodes[n];
        let curry = self.word(node.end - 1) == "...";
        let (mut positional, mut named) = (Vec::new(), Vec::new());
        let mut seen: HashMap<&str, Span> = HashMap::new();
        let mut first_named: Option<(&str, Span)> = None;
        for &k in &node.kids {
            let kids = self.kids(k);
            let rule = self.tree.name(k);
            if let (Some((word, at)), "PlainArg" | "SortArg") = (first_named, rule) {
                return Err(Error {
                    row: Some(Row::NamedBeforePositional),
                    span: self.span(k),
                    message: format!(
                        "this positional argument comes after the named argument `{word}`, and a \
                         call passes its positional arguments first, then its named ones."
                    ),
                    notes: vec![
                        Note {
                            span: at,
                            text: format!("the first named argument, `{word}`"),
                        },
                        Note {
                            span: call,
                            text: "the call".into(),
                        },
                        Note {
                            span: self.span(k),
                            text: format!(
                                "repair: pass this argument before `{word}`, the positional \
                                 arguments first"
                            ),
                        },
                    ],
                });
            }
            match rule {
                "PlainArg" => {
                    positional.push(self.node(kids[0])?);
                    continue;
                }
                "SortArg" => {
                    positional.push(Expr {
                        kind: ExprKind::SortKey {
                            desc: self.word(self.tree.nodes[k].start) == "desc",
                            key: match kids.first() {
                                Some(&key) => Some(Box::new(self.node(key)?)),
                                None => None,
                            },
                        },
                        span: self.span(k),
                    });
                    continue;
                }
                _ => {}
            }
            let span = self.span(kids[0]);
            let word = self.word(self.tree.nodes[kids[0]].start);
            if let Some(first) = seen.get(word) {
                return Err(Error {
                    row: None,
                    span,
                    message: format!(
                        "the argument `{word}` is named twice in this call, and a call names \
                         each argument once. Remove one of the two."
                    ),
                    notes: vec![Note {
                        span: *first,
                        text: format!("the first argument named `{word}`"),
                    }],
                });
            }
            seen.insert(word, span);
            first_named.get_or_insert((word, span));
            let value = match kids {
                [_, v] => self.node(*v)?,
                _ => self.node(kids[0])?,
            };
            named.push((word.to_string(), value));
        }
        Ok((positional, named, curry))
    }

    /// The literal of token `i`, written in `span`, which holds its grouping parentheses.
    pub(super) fn literal_at(&mut self, i: usize, span: Span) -> Result<Expr, Error> {
        let kind = match &self.tokens[i].tok {
            Tok::Int { radix, digits } => ExprKind::Int {
                radix: *radix,
                digits: Arc::clone(digits),
            },
            Tok::Float { digits, forced } => ExprKind::Float {
                digits: Arc::clone(digits),
                forced: *forced,
            },
            Tok::Rat(s) => ExprKind::Rat(Arc::clone(s)),
            Tok::Keyword(k) => ExprKind::Bool(*k == "true"),
            Tok::Str(parts) => {
                let mut out = Vec::with_capacity(parts.len());
                let mut hole = self.first + self.holes[i];
                for p in parts {
                    out.push(match p {
                        Part::Text(t) => StrPart::Text(Arc::clone(t)),
                        Part::Hole { .. } => {
                            let e = self.done[hole].take();
                            hole += 1;
                            StrPart::Hole(e.expect("a hole's expression is taken once")?)
                        }
                    });
                }
                ExprKind::Str(out)
            }
            _ => unreachable!("Literal = INT | FLOAT | RAT | STRING | 'true' | 'false'"),
        };
        Ok(Expr { kind, span })
    }
}

/// The kind of form the grammar rule `rule` reads, in plain words, for the message of a form
/// this zedc does not compile yet; `the form` for a rule with no plainer name.
fn kind_of(rule: &str) -> &'static str {
    match rule {
        "ReduceTail" => "the reduction",
        "ReducePolicy" => "the reduction order",
        "TypeSuffix" => "the refinement",
        "ResultType" => "the declared result type",
        "Law" => "the law",
        "TypeFacet" => "the facet",
        "Interface" => "the interface",
        "Signature" => "the signature",
        "TypedBinding" => "the binding with a declared type",
        "InferType" => "the wildcard type",
        "FieldType" => "the named type",
        "Struct" => "the struct declaration",
        "MoreGen" => "the inner generator",
        "KeyedPush" => "the push at a key",
        "LitType" => "the literal type",
        "ArrayType" => "the array type",
        "Update" => "the field update",
        "AnnotExpr" => "the annotated expression",
        _ => "the form",
    }
}
