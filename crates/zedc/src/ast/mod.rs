//! The syntax tree of expressions, statements and units (steps L1.9 to L1.12), built from a
//! parse tree (`crate::parse`).
//!
//! A node of the parse tree records its rule and tokens, and a left-associative chain nests
//! to the left; here an expression is one node
//! per operation, with its operands. Parentheses group and leave no node; the grouped
//! expression's span includes them. A postfix chain is
//! built left to right: a call with its positional arguments, then its named ones, and
//! whether it ends in `...`; an index `e[k]`; a member `e.n` or `e?.n`. A uniform call
//! `x.f(a)` stays a call of the member `x.f`, since whether `f` is a field or a function is
//! known only after name resolution (step L1.14). A lambda keeps its parameters as written;
//! an `else` chain is built left to right. A block is its statements, one of them its export.
//! A unit is its declarations and statements. The forms of layer L2 (step L2.1) are built
//! here too: a struct and its fields, a record display `{ x: 1 }` (in a block's place the
//! separator decides between a block and a display), a `with` clause and its update paths, a
//! method `T.m`, `this`, struct, name, `_` and tuple patterns, the tuple-destructuring
//! parameter `((a, b)) -> e`, `type` declarations, and record, applied and atom-payload types.
//! A name written twice in one struct, display, `with` clause or type parameter list is an
//! error. From step L6.1 the generation forms are built: `loop`, `break`, the call `c*.m`,
//! and in `stmts` the guards `while` and `until`, `mutable`, indexed definitions, boundary
//! `with` clauses and expression statements. A primed name `x'` is one token, so it is a name
//! like any other here. A form of a later layer is an error naming that layer.

mod body;
mod drop;
mod neglit;
mod node;
mod show;
mod stmts;
mod types;

use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::sync::{Arc, OnceLock};

use num_bigint::BigUint;
use zed_kernel::num::TooLarge;

pub use node::{
    Annot, Arm, BoundaryItem, Error, Every, Expr, ExprKind, Field, Function, Import, ImportKind,
    IndexKey, IndexedDef, Method, Note, Param, Pattern, Port, RangeEnd, Stmt, StmtKind, StrPart,
    Struct, Target, Type, TypeBound, TypeDecl, TypeKind, TypeParam, Update,
};

use crate::lex::{Part, Span, Tok, Token};
use crate::parse::{Tree, grammar};
use crate::rejection::Row;

/// The expression of `tree`, parsed as `Expr` from `tokens` of `text`.
pub fn build(text: &str, tokens: &[Token], tree: &Tree) -> Result<Expr, Error> {
    expr(text, tokens, tree, tree.root)
}

/// The expression of node `n` of `tree`, a node of a rule from `Expr` down to `Primary`.
pub fn expr(text: &str, tokens: &[Token], tree: &Tree, n: usize) -> Result<Expr, Error> {
    with_holes(text, tokens, tree, |b| {
        b.fill(n);
        b.node(n)
    })
}

/// The type of `tree`, parsed as `Type` from `tokens` of `text`.
pub fn ty(text: &str, tokens: &[Token], tree: &Tree) -> Result<Type, Error> {
    with_holes(text, tokens, tree, |b| {
        b.fill(tree.root);
        b.ty(tree.root)
    })
}

/// The statements of `tree`, parsed as `Unit` from `tokens` of `text`, as [`unit_all_errors`]
/// gives them, or the first error in written order.
pub fn unit(text: &str, tokens: &[Token], tree: &Tree) -> Result<Vec<Stmt>, Error> {
    unit_all_errors(text, tokens, tree)
        .map_err(|es| es.into_iter().next().expect("an error per failed unit"))
}

/// The statements of `tree`, parsed as `Unit` from `tokens` of `text`, in written order but
/// for guards, which are ordered as in a block (`StmtKind::place`), or the error of each item
/// that cannot be built, in written order. Every item is built, so which errors are reported
/// does not depend on the order of the items (step L1.29b). A unit's top level exports its
/// declarations, so `return` there is an error.
pub fn unit_all_errors(text: &str, tokens: &[Token], tree: &Tree) -> Result<Vec<Stmt>, Vec<Error>> {
    with_holes(text, tokens, tree, |b| {
        b.fill(tree.root);
        let kids = b.kids(tree.root);
        let mut out = Vec::with_capacity(kids.len());
        let mut errors = Vec::new();
        for &k in kids {
            match b.item(k) {
                Ok(s) if matches!(s.kind, StmtKind::Return(_)) => errors.push(Error {
                    row: None,
                    span: s.span,
                    message: "`return` exports from a block; a unit's top level has none".into(),
                    notes: Vec::new(),
                }),
                Ok(s) => out.push(s),
                Err(e) => errors.push(e),
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        out.sort_by_key(|s| s.kind.place());
        Ok(out)
    })
}

/// What `top` makes with a builder of `tree`, the expressions of every string hole, at any
/// depth of nesting, built first. The holes are listed outermost first, the holes of each
/// tree together, and built from the end of the list, so each finds its own holes done.
fn with_holes<'t, R>(
    text: &str,
    tokens: &'t [Token],
    tree: &'t Tree,
    top: impl FnOnce(&mut Builder<'_, '_>) -> R,
) -> R {
    let mut list = vec![Level {
        tokens,
        tree,
        first: 0,
    }];
    let mut i = 0;
    while let Some(&Level { tokens, tree, .. }) = list.get(i) {
        let first = list.len();
        list[i].first = first;
        let holes = tokens.iter().flat_map(|t| match &t.tok {
            Tok::Str(parts) => &parts[..],
            _ => &[],
        });
        let holes = holes.filter_map(|p| match p {
            Part::Hole { tokens, .. } => Some(&tokens[..]),
            Part::Text(_) => None,
        });
        for (tokens, tree) in holes.zip(&tree.holes) {
            list.push(Level {
                tokens,
                tree,
                first: 0,
            });
        }
        i += 1;
    }
    let bare = Bare::new();
    let mut done: Vec<Option<Result<Expr, Error>>> = Vec::new();
    done.resize_with(list.len(), || None);
    for (i, l) in list.iter().enumerate().skip(1).rev() {
        let mut b = Builder::new(text, l, &mut done, &bare);
        b.fill(l.tree.root);
        let e = b.node(l.tree.root);
        done[i] = Some(e);
    }
    top(&mut Builder::new(text, &list[0], &mut done, &bare))
}

/// A tree to build from: a text's, or a string hole's.
struct Level<'t> {
    tokens: &'t [Token],
    tree: &'t Tree,
    /// Where its own holes start in the list of all holes.
    first: usize,
}

/// What a node of a parse tree builds to.
enum Built {
    Expr(Expr),
    Type(Type),
    Pattern(Pattern),
    Stmt(Box<Stmt>),
}

/// What the nodes of a rule build to.
#[derive(Clone, Copy)]
enum Form {
    Expr,
    Type,
    Pattern,
    Item,
    /// Nothing of its own: its parent reads it.
    Part,
}

/// The form of each rule of the grammar, by its index.
fn forms() -> &'static [Form] {
    static FORMS: OnceLock<Vec<Form>> = OnceLock::new();
    FORMS.get_or_init(|| {
        let form = |name: &str| match name {
            "Expr" | "Lambda" | "Expr12" | "Or" | "And" | "Additive" | "Multiplicative"
            | "Equality" | "Compare" | "IsTest" | "Reduce" | "Range" | "Prefix" | "Power"
            | "Postfix" | "AtomExpr" | "Group" | "TupleExpr" | "Block" | "If" | "Literal"
            | "Display" | "This" | "Match" | "InTest" | "OpFunction" | "ArrayExpr" | "For"
            | "Loop" | "Break" => Form::Expr,
            "Type" | "TypePostfix" | "Arrow" | "TypeDiff" | "TypeOr" | "TypeAnd" | "TypeName"
            | "AtomType" | "TupleType" | "GroupType" | "TypeApply" | "AtomApply" | "RecordType"
            | "RankArrayType" => Form::Type,
            "AtomPattern" | "CtorPat" | "NamePat" | "WildPat" | "TuplePat" | "IsPat"
            | "SignedLit" | "RangePat" => Form::Pattern,
            "Item" => Form::Item,
            _ => Form::Part,
        };
        grammar().rules.iter().map(|r| form(&r.name)).collect()
    })
}

/// The cache [`Builder::written_bare`] reads, one per source.
type Bare<'a> = std::cell::OnceCell<std::collections::HashSet<&'a str>>;

struct Builder<'a, 's: 'a> {
    text: &'s str,
    tokens: &'a [Token],
    tree: &'a Tree,
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
    live: VecDeque<Option<Result<Built, Error>>>,
    /// Where in the walk of `fill` each node is, and where the walk has reached.
    place: Vec<usize>,
    front: usize,
    /// The names written in the source other than after a `.`, listed on first use.
    bare: &'a Bare<'s>,
    /// The parent of each node of the tree, listed on the first rejection that names one.
    parents: std::cell::OnceCell<Vec<usize>>,
}

impl<'a, 's> Builder<'a, 's> {
    fn new(
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

    /// Builds `n` and every node below it. A breadth-first walk from `n` lists each node after
    /// its parent, and no node has two parents, so the list read backward has each node after
    /// its children. Only nodes of the tree are visited, not the alternatives the parser left.
    fn fill(&mut self, n: usize) {
        let tree = self.tree;
        let mut order = vec![n];
        let mut i = 0;
        while let Some(&k) = order.get(i) {
            order.extend_from_slice(&tree.nodes[k].kids);
            i += 1;
        }
        self.place.resize(tree.nodes.len(), 0);
        for (i, &k) in order.iter().enumerate() {
            self.place[k] = i;
        }
        self.front = order.len();
        let forms = forms();
        for (i, &k) in order.iter().enumerate().rev() {
            let built = self.make(forms[tree.nodes[k].rule], k);
            self.live.push_front(built);
            self.front = i;
            while let Some(None) = self.live.back() {
                self.live.pop_back();
            }
        }
    }

    /// What node `n`, whose rule makes a `form`, builds to.
    fn make(&mut self, form: Form, n: usize) -> Option<Result<Built, Error>> {
        Some(match form {
            Form::Expr => self.make_expr(n).map(Built::Expr),
            Form::Type => self.make_type(n).map(Built::Type),
            Form::Pattern => self.make_pattern(n).map(Built::Pattern),
            Form::Item => self.make_item(n).map(|s| Built::Stmt(Box::new(s))),
            Form::Part => return None,
        })
    }

    fn span(&self, n: usize) -> Span {
        let node = &self.tree.nodes[n];
        Span {
            start: self.tokens[node.start].span.start,
            end: self.tokens[node.end - 1].span.end,
        }
    }

    fn word(&self, i: usize) -> &'a str {
        let s = self.tokens[i].span;
        &self.text[s.start..s.end]
    }

    fn kids(&self, n: usize) -> &'a [usize] {
        &self.tree.nodes[n].kids
    }

    /// The error for node `n`, of a form of a layer after L1.
    fn later(&self, n: usize) -> Error {
        Error {
            row: None,
            span: self.span(n),
            message: format!(
                "this form ({}) is built from layer L{}",
                self.tree.name(n),
                self.tree.layer(n)
            ),
            notes: Vec::new(),
        }
    }

    /// The expression node `n` built to.
    fn node(&mut self, n: usize) -> Result<Expr, Error> {
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
                "this `{}` is an empty block, which exports nothing: a brace after `->`, `else`, or the \
                 head of an `if` or a `for` is a block; the empty family there is `{ {} }`, or \
                 `({})` after `->` or a fallback's `else`"
            } else {
                "this block exports nothing: end it with an expression or `return e;`"
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
    fn body(&mut self, n: usize) -> Result<Expr, Error> {
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

    fn make_expr(&mut self, n: usize) -> Result<Expr, Error> {
        let kids = self.kids(n);
        match self.tree.name(n) {
            "Expr" => self.node(kids[0]),
            "Lambda" => self.lambda(n),
            // Left-recursive: `a else b else c` arrives as ((a else b) else c).
            "Expr12" => {
                let [l, t] = kids[..] else {
                    unreachable!("Expr12 = Expr12 ElseTail | ~Or")
                };
                let e = self.node(l)?;
                self.else_tail(e, t)
            }
            "Or" | "And" | "Additive" | "Multiplicative" | "Equality" | "Compare" => {
                // The operator is the token before the right operand.
                let op = self.op(self.tree.nodes[kids[1]].start - 1);
                self.binary(op, kids[0], kids[1])
            }
            "IsTest" => {
                let of = self.node(kids[0])?;
                let is = self.tree.nodes[kids[0]].end;
                let ty = self.ty(kids[1])?;
                let span = Span {
                    start: of.span.start,
                    end: ty.span.end,
                };
                Ok(Expr {
                    kind: ExprKind::Is {
                        of: Box::new(of),
                        ty,
                        negated: self.word(is + 1) == "not",
                    },
                    span,
                })
            }
            "InTest" => {
                let of = self.node(kids[0])?;
                let set = self.node(kids[1])?;
                let not = self.tree.nodes[kids[0]].end;
                let span = Span {
                    start: of.span.start,
                    end: set.span.end,
                };
                Ok(Expr {
                    kind: ExprKind::In {
                        of: Box::new(of),
                        set: Box::new(set),
                        negated: self.word(not) == "not",
                    },
                    span,
                })
            }
            "Reduce" => {
                let of = self.node(kids[0])?;
                self.reduce_tail(of, kids[1])
            }
            "Range" => {
                let from = self.node(kids[0])?;
                let t = kids[1];
                let (op, bound) = (self.tree.nodes[t].start, self.kids(t).first().copied());
                let end = self.range_end(op, bound, |b, k| b.node(k).map(Box::new))?;
                Ok(Expr {
                    kind: ExprKind::Range(Box::new(from), end),
                    span: self.span(n),
                })
            }
            "OpFunction" => Ok(Expr {
                kind: ExprKind::Section(self.op(self.tree.nodes[n].start + 1)),
                span: self.span(n),
            }),
            "ArrayExpr" => Ok(Expr {
                kind: ExprKind::Array(
                    kids.iter()
                        .map(|&k| self.node(k))
                        .collect::<Result<_, _>>()?,
                ),
                span: self.span(n),
            }),
            "For" => self.for_expr(n),
            "Prefix" => {
                let op = self.op(self.tree.nodes[n].start);
                let e = self.node(kids[0])?;
                if let Some(err) = self.negated_literal_chain(n, &e) {
                    return Err(err);
                }
                Ok(Expr {
                    kind: ExprKind::Unary(op, Box::new(e)),
                    span: self.span(n),
                })
            }
            "Power" => self.binary("**", kids[0], kids[1]),
            "Postfix" => {
                let e = self.node(kids[0])?;
                self.suffix(e, kids[1])
            }
            "AtomExpr" => {
                let i = self.tree.nodes[n].start;
                let Tok::Atom(a) = &self.tokens[i].tok else {
                    unreachable!("an ATOM token")
                };
                Ok(Expr {
                    kind: ExprKind::Atom(a.clone()),
                    span: self.span(n),
                })
            }
            "Group" => {
                let mut e = self.node(kids[0])?;
                e.span = self.span(n);
                Ok(e)
            }
            "TupleExpr" => Ok(Expr {
                kind: ExprKind::Tuple(
                    kids.iter()
                        .map(|&k| self.node(k))
                        .collect::<Result<_, _>>()?,
                ),
                span: self.span(n),
            }),
            "Block" => self.body_block(n),
            "If" => Ok(Expr {
                kind: ExprKind::If {
                    cond: Box::new(self.node(kids[0])?),
                    then: Box::new(self.node(kids[1])?),
                    otherwise: Box::new(self.node(kids[2])?),
                },
                span: self.span(n),
            }),
            "Literal" => self.literal(n),
            "Display" => self.display(n),
            "This" => Ok(Expr {
                kind: ExprKind::This,
                span: self.span(n),
            }),
            "Match" => self.matching(n),
            // The body is a block that may export nothing: a loop's value is its last frame.
            "Loop" => {
                let (&body, label) = kids.split_last().expect("Loop ends in its block");
                Ok(Expr {
                    kind: ExprKind::Loop {
                        label: label
                            .first()
                            .map(|&l| self.word(self.tree.nodes[l].start).into()),
                        body: Box::new(self.body(body)?),
                    },
                    span: self.span(n),
                })
            }
            "Break" => Ok(Expr {
                kind: ExprKind::Break(Box::new(self.node(kids[0])?)),
                span: self.span(n),
            }),
            _ => unreachable!("make builds only these rules as expressions"),
        }
    }

    /// The operator token at `i`, as the lexer's static text.
    fn op(&self, i: usize) -> &'static str {
        match self.tokens[i].tok {
            Tok::Op(o) | Tok::Keyword(o) => o,
            _ => unreachable!("an operator token"),
        }
    }

    fn binary(&mut self, op: &'static str, l: usize, r: usize) -> Result<Expr, Error> {
        let (a, b) = (self.node(l)?, self.node(r)?);
        let span = Span {
            start: a.span.start,
            end: b.span.end,
        };
        Ok(Expr {
            kind: ExprKind::Binary(op, Box::new(a), Box::new(b)),
            span,
        })
    }

    /// A lambda: `Name '->' body` or `'(' Params? ')' '->' body`.
    fn lambda(&mut self, n: usize) -> Result<Expr, Error> {
        let kids = self.kids(n);
        let body = *kids.last().expect("Lambda ends in its body");
        let params = match kids {
            [_] => Vec::new(),
            [p, _] if self.tree.name(*p) == "Name" => vec![Param {
                name: self.word(self.tree.nodes[*p].start).into(),
                tuple: None,
                positional: false,
                ty: None,
                default: None,
                span: self.span(*p),
                name_at: self.span(*p),
            }],
            [p, _] => self.params(*p, self.span(n))?,
            _ => unreachable!("Lambda = (Name | '(' Params? ')') '->' body"),
        };
        Ok(Expr {
            kind: ExprKind::Lambda {
                params,
                body: Box::new(self.node(body)?),
            },
            span: self.span(n),
        })
    }

    /// `of` followed by the `ElseTail` node `t`.
    fn else_tail(&mut self, of: Expr, t: usize) -> Result<Expr, Error> {
        let kids = self.kids(t);
        let (pattern, default) = match kids {
            [p, d] => (Some(self.pattern(*p)?), self.node(*d)?),
            [d] => (None, self.node(*d)?),
            _ => unreachable!("ElseTail = 'else' AtomPattern? '->' default"),
        };
        let span = Span {
            start: of.span.start,
            end: default.span.end,
        };
        Ok(Expr {
            kind: ExprKind::Else {
                of: Box::new(of),
                pattern,
                default: Box::new(default),
            },
            span,
        })
    }

    fn suffix(&mut self, of: Expr, s: usize) -> Result<Expr, Error> {
        let node = &self.tree.nodes[s];
        let span = Span {
            start: of.span.start,
            end: self.tokens[node.end - 1].span.end,
        };
        let of = Box::new(of);
        let name = self.tree.name(s);
        let kind = match name {
            "CallSuffix" => {
                let (positional, named, curry) = match node.kids[..] {
                    [] => (Vec::new(), Vec::new(), false),
                    [args] => self.args(args, span)?,
                    _ => unreachable!("CallSuffix = '(' Args? ')'"),
                };
                ExprKind::Call {
                    callee: of,
                    positional,
                    named,
                    curry,
                }
            }
            "IndexSuffix" => ExprKind::Index(of, Box::new(self.node(node.kids[0])?)),
            "MemberSuffix" | "SafeSuffix" => ExprKind::Member {
                of,
                name: self.word(node.end - 1).into(),
                safe: name == "SafeSuffix",
            },
            "ReadSuffix" => ExprKind::Read {
                of,
                name: self.word(node.end - 1).into(),
            },
            "SpreadSuffix" => ExprKind::Spread {
                of,
                name: self.word(node.end - 1).into(),
            },
            _ => return Err(self.later(s)),
        };
        Ok(Expr { kind, span })
    }

    /// `of` followed by the `ReduceTail` node `t`: a reduction `>< op`, or a struct update
    /// `with { … }` and the suffixes after it, which apply to the updated value.
    fn reduce_tail(&mut self, of: Expr, t: usize) -> Result<Expr, Error> {
        match (self.tree.layer(t), self.kids(t)) {
            (2, _) => {}
            (3, &[op]) => {
                let op = self.node(op)?;
                let span = Span {
                    start: of.span.start,
                    end: op.span.end,
                };
                return Ok(Expr {
                    kind: ExprKind::Reduce {
                        of: Box::new(of),
                        op: Box::new(op),
                    },
                    span,
                });
            }
            // `unordered`, of layer L9.
            (3, &[_, unordered]) => return Err(self.later(unordered)),
            _ => return Err(self.later(t)),
        }
        let mut updates = Vec::new();
        let mut paths: HashMap<Vec<&str>, Span> = HashMap::new();
        let mut kids = self.kids(t).iter().peekable();
        while let Some(&u) = kids.next_if(|&&k| self.tree.name(k) == "Update") {
            if self.tree.layer(u) != 2 {
                return Err(self.later(u));
            }
            let (&value, names) = self.kids(u).split_last().expect("Update ends in its value");
            let path: Vec<&str> = (names.iter())
                .map(|&k| self.word(self.tree.nodes[k].start))
                .collect();
            let span = self.span(u);
            if let Some(&first) = paths.get(&path) {
                let path = path.join(".");
                return Err(Error {
                    row: None,
                    span,
                    message: format!("the field `{path}` is updated twice"),
                    notes: vec![Note {
                        span: first,
                        text: format!("the first update of `{path}`"),
                    }],
                });
            }
            updates.push(Update {
                path: path.iter().map(|&p| p.to_string()).collect(),
                value: self.node(value)?,
                span,
            });
            paths.insert(path, span);
        }
        let suffixes: Vec<usize> = kids.copied().collect();
        // The `with` ends at its `}`, the token before the first suffix.
        let end = match suffixes.first() {
            Some(&s) => self.tokens[self.tree.nodes[s].start - 1].span.end,
            None => self.span(t).end,
        };
        let mut e = Expr {
            span: Span {
                start: of.span.start,
                end,
            },
            kind: ExprKind::With {
                of: Box::new(of),
                updates,
            },
        };
        for s in suffixes {
            e = self.suffix(e, s)?;
        }
        Ok(e)
    }

    /// The display of node `n`, a `Display`: a record `{x: 1, y:}`, `y:` being `y: y`, or from
    /// layer L3 a set `{a, b}`, a map `{k -> v}`, or `{}`.
    fn display(&mut self, n: usize) -> Result<Expr, Error> {
        if self.tree.layer(n) != 2 {
            return self.family(n);
        }
        let mut fields: Vec<(String, Expr)> = Vec::new();
        let mut seen = HashMap::new();
        for &k in self.kids(n) {
            // A field's name is the kid a `:` follows. Its rule name does not tell: a value that
            // is a bare name arrives as a `Name` node too, since `Expr12 = ~Or` passes it up.
            if self.word(self.tree.nodes[k].end) == ":" {
                let name = self.word(self.tree.nodes[k].start);
                self.once(&mut seen, name, k, "field", "given")?;
                // Until a value follows, the field is the variable of its name.
                fields.push((name.into(), self.body(k)?));
            } else {
                let value = self.node(k)?;
                fields
                    .last_mut()
                    .expect("a value follows its field's name")
                    .1 = value;
            }
        }
        Ok(Expr {
            kind: ExprKind::Record(fields),
            span: self.span(n),
        })
    }

    /// The set or map display of node `n`, a `Display` of layer L3, whose children are its
    /// `Entry` nodes: `k -> v` of a map, or an element of a set. One display holds one kind.
    fn family(&mut self, n: usize) -> Result<Expr, Error> {
        let entries = self.kids(n);
        let Some(&first) = entries.first() else {
            return Ok(Expr {
                kind: ExprKind::Map(Vec::new()),
                span: self.span(n),
            });
        };
        let map = self.kids(first).len() == 2;
        if let Some(&odd) = entries.iter().find(|&&e| (self.kids(e).len() == 2) != map) {
            let (this, that) = if map {
                ("a set element", "map entry `k -> v`")
            } else {
                ("a map entry `k -> v`", "set element")
            };
            return Err(Error {
                row: None,
                span: self.span(odd),
                message: format!(
                    "{this} in a display whose first entry is a {that}: a display is a set \
                     or a map, not both"
                ),
                notes: vec![Note {
                    span: self.span(first),
                    text: format!("the first entry, a {that}"),
                }],
            });
        }
        let kind = if map {
            let mut out = Vec::with_capacity(entries.len());
            for &e in entries {
                let &[k, v] = self.kids(e) else {
                    unreachable!("Entry = Expr12 '->' Expr12")
                };
                out.push((self.node(k)?, self.node(v)?));
            }
            ExprKind::Map(out)
        } else {
            let elems = entries.iter().map(|&e| self.node(self.kids(e)[0]));
            ExprKind::Set(elems.collect::<Result<_, _>>()?)
        };
        Ok(Expr {
            kind,
            span: self.span(n),
        })
    }

    /// The `for` of node `n`: its generator, a `MoreGen` (of layer L5) for each further
    /// generator, its `where` guard if written, and its block. The generator holds the
    /// `InPattern`, whose `Binder`s are names or `_`, and the source.
    fn for_expr(&mut self, n: usize) -> Result<Expr, Error> {
        let kids = self.kids(n);
        let (&generator, rest) = kids.split_first().expect("For = 'for' Generator …");
        let (&body, rest) = rest.split_last().expect("For ends in its block");
        if let Some(&more) = rest.iter().find(|&&k| self.tree.name(k) == "MoreGen") {
            return Err(self.later(more));
        }
        let &[pattern, source] = self.kids(generator) else {
            unreachable!("Generator = InPattern 'in' head(Expr12)")
        };
        let binders = self.kids(pattern).iter().map(|&b| self.target(b)).collect();
        let source = Box::new(self.node(source)?);
        let guard = match rest {
            [] => None,
            [g] => Some(Box::new(self.node(*g)?)),
            _ => unreachable!("one `where` guard"),
        };
        Ok(Expr {
            kind: ExprKind::For {
                binders,
                source,
                guard,
                body: Box::new(self.node(body)?),
            },
            span: self.span(n),
        })
    }

    /// The end of a range whose operator is token `op`, its bound node `bound` built by `f`.
    fn range_end<T>(
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

    /// The `match` of node `n`: the value matched, then each `Arm`, which holds its pattern,
    /// its guard if written, and its value.
    fn matching(&mut self, n: usize) -> Result<Expr, Error> {
        let (&of, arms) = self
            .kids(n)
            .split_first()
            .expect("Match = 'match' Expr12 …");
        let of = Box::new(self.node(of)?);
        let mut out = Vec::with_capacity(arms.len());
        for &a in arms {
            let (pattern, guard, body) = match *self.kids(a) {
                [p, b] => (p, None, b),
                [p, g, b] => (p, Some(g), b),
                _ => unreachable!("Arm = Pattern ('where' Expr12)? '->' body"),
            };
            out.push(Arm {
                pattern: self.pattern(pattern)?,
                guard: guard.map(|g| self.node(g)).transpose()?,
                body: self.node(body)?,
                span: self.span(a),
            });
        }
        Ok(Expr {
            kind: ExprKind::Match { of, arms: out },
            span: self.span(n),
        })
    }

    /// Records the `what` named `name`, written at node `n`, in `seen`, or the error that it
    /// is `done` twice, with a note at the first.
    fn once(
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
                message: format!("the {what} `{name}` is {done} twice"),
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
    fn args(
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
                        "a positional argument after the named argument `{word}`: a call \
                         passes its positional arguments first, then its named ones"
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
                            key: Box::new(self.node(kids[0])?),
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
                    message: format!("the argument `{word}` is named twice"),
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

    fn literal(&mut self, n: usize) -> Result<Expr, Error> {
        self.literal_at(self.tree.nodes[n].start, self.span(n))
    }

    /// The literal of token `i`, written in `span`, which holds its grouping parentheses.
    fn literal_at(&mut self, i: usize, span: Span) -> Result<Expr, Error> {
        let kind = match &self.tokens[i].tok {
            Tok::Int { radix, digits } => ExprKind::Int {
                radix: *radix,
                digits: Arc::clone(digits),
                generic: false,
            },
            Tok::Generic { radix, digits } => ExprKind::Int {
                radix: *radix,
                digits: Arc::clone(digits),
                generic: true,
            },
            Tok::Float(s) => ExprKind::Float(Arc::clone(s)),
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

/// The text `x` writes, in memory the system gives first for all of it; [`TooLarge`] when it
/// refuses, naming that memory. The text is written twice, once to count its bytes, so a
/// literal too long to copy is an error and not an abort.
pub fn shown(x: &impl fmt::Display) -> Result<String, TooLarge> {
    let mut len = Count(0);
    fmt::write(&mut len, format_args!("{x}")).expect("counting cannot fail");
    let mut out = String::new();
    out.try_reserve_exact(len.0).map_err(|_| TooLarge {
        bits: BigUint::from(len.0) << 3u32,
    })?;
    fmt::write(&mut out, format_args!("{x}")).expect("writing to a String");
    Ok(out)
}

/// Counts the bytes written to it.
struct Count(usize);

impl fmt::Write for Count {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0 += s.len();
        Ok(())
    }
}
