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
//! error. A form of a later layer is an error naming that layer.

mod drop;
mod show;
mod stmts;
mod types;

use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::sync::OnceLock;

pub use stmts::{Field, Function, Method, Port, Stmt, StmtKind, Struct, Target, TypeDecl};
pub use types::{Param, Pattern, Type, TypeKind, TypeParam};

use crate::lex::{Part, Span, Tok, Token};
use crate::parse::{Tree, grammar};

/// An expression and its span.
pub struct Expr {
    /// What it is.
    pub kind: ExprKind,
    /// Its text.
    pub span: Span,
}

/// The kinds of expression.
#[derive(Debug)]
pub enum ExprKind {
    /// An integer: its base and digits.
    Int {
        /// The base.
        radix: u32,
        /// The digits.
        digits: String,
    },
    /// A float, as its decimal text.
    Float(String),
    /// An exact rational, as its decimal text.
    Rat(String),
    /// A string: its text and its holes.
    Str(Vec<StrPart>),
    /// `true` or `false`.
    Bool(bool),
    /// An atom, without its `#`.
    Atom(String),
    /// A name.
    Name(String),
    /// A prefix operator, `-` or `!`, and its operand.
    Unary(&'static str, Box<Expr>),
    /// A binary operator and its operands.
    Binary(&'static str, Box<Expr>, Box<Expr>),
    /// A call `f(…)`.
    Call {
        /// The function.
        callee: Box<Expr>,
        /// The positional arguments, in order.
        positional: Vec<Expr>,
        /// The named arguments, in written order; `x:` is `x: x`.
        named: Vec<(String, Expr)>,
        /// Whether the arguments end in `...`, currying the named parameters left out.
        curry: bool,
    },
    /// An index `e[k]`.
    Index(Box<Expr>, Box<Expr>),
    /// A tuple `(a, b, …)`.
    Tuple(Vec<Expr>),
    /// A lambda `x -> e` or `(params) -> e`.
    Lambda {
        /// The parameters.
        params: Vec<Param>,
        /// The body.
        body: Box<Expr>,
    },
    /// A type test `e is T`, or `e is not T` when `negated`: whether the value of `e` is in the
    /// set of `T`, decided when the program runs. It is not the subtype relation `S <: T`
    /// between two types, which the checker decides and Zed has no syntax for
    /// (DESIGN.md sec:type_language).
    Is {
        /// The value tested.
        of: Box<Expr>,
        /// The type.
        ty: Type,
        /// Whether it is `is not`.
        negated: bool,
    },
    /// `e else d`, or `e else #a -> d` with its atom pattern.
    Else {
        /// The value whose atom members are replaced.
        of: Box<Expr>,
        /// The members replaced: every loose atom member when `None`.
        pattern: Option<Pattern>,
        /// The default.
        default: Box<Expr>,
    },
    /// A block `{ … }`: its statements in written order, except that its `return` is last
    /// (none in a function's body block that only pushes).
    Block(Vec<Stmt>),
    /// `if c { a } else { b }`; `else if` is an `If` in the `else` branch.
    If {
        /// The condition.
        cond: Box<Expr>,
        /// The branch taken when it holds.
        then: Box<Expr>,
        /// The other branch.
        otherwise: Box<Expr>,
    },
    /// A member `e.n`, or `e?.n` when `safe`.
    Member {
        /// The value.
        of: Box<Expr>,
        /// The member's name.
        name: String,
        /// Whether it is `?.`, which passes an atom member of the value's type through.
        safe: bool,
    },
    /// A record display `{x: 1, y:}`: its fields in written order; `y:` is `y: y`.
    Record(Vec<(String, Expr)>),
    /// A struct update `e with { x = 1, c.y = 2 }`.
    With {
        /// The value updated.
        of: Box<Expr>,
        /// The updates, in written order.
        updates: Vec<Update>,
    },
    /// `this`, a method's receiver.
    This,
}

/// One update of a `with`: a field path, `c.y`, and its new value.
#[derive(Debug)]
pub struct Update {
    /// The fields of the path, outermost first.
    pub path: Vec<String>,
    /// The new value.
    pub value: Expr,
    /// Its text.
    pub span: Span,
}

/// A part of a string expression.
#[derive(Debug)]
pub enum StrPart {
    /// Text.
    Text(String),
    /// A `${…}` hole.
    Hole(Expr),
}

/// Why an expression could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// Where.
    pub span: Span,
    /// Why.
    pub message: String,
    /// How the checker reached it: each constraint and step, in the order it met them.
    pub notes: Vec<Note>,
}

/// One step of a derivation: a place in the source and what holds there.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Note {
    /// Where.
    pub span: Span,
    /// What holds there.
    pub text: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

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

/// The statements of `tree`, parsed as `Unit` from `tokens` of `text`, in written order. A
/// unit's top level exports its declarations, so `return` there is an error.
pub fn unit(text: &str, tokens: &[Token], tree: &Tree) -> Result<Vec<Stmt>, Error> {
    with_holes(text, tokens, tree, |b| {
        b.fill(tree.root);
        let kids = b.kids(tree.root);
        let mut out = Vec::with_capacity(kids.len());
        for &k in kids {
            let s = b.item(k)?;
            if let StmtKind::Return(_) = s.kind {
                return Err(Error {
                    span: s.span,
                    message: "`return` exports from a block; a unit's top level has none".into(),
                    notes: Vec::new(),
                });
            }
            out.push(s);
        }
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
    top: impl FnOnce(&mut Builder<'_>) -> R,
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
    let mut done: Vec<Option<Result<Expr, Error>>> = Vec::new();
    done.resize_with(list.len(), || None);
    for (i, l) in list.iter().enumerate().skip(1).rev() {
        let mut b = Builder::new(text, l, &mut done);
        b.fill(l.tree.root);
        let e = b.node(l.tree.root);
        done[i] = Some(e);
    }
    top(&mut Builder::new(text, &list[0], &mut done))
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
            | "Display" | "This" => Form::Expr,
            "Type" | "TypePostfix" | "Arrow" | "TypeDiff" | "TypeOr" | "TypeAnd" | "TypeName"
            | "AtomType" | "TupleType" | "GroupType" | "TypeApply" | "AtomApply" | "RecordType" => {
                Form::Type
            }
            "AtomPattern" | "CtorPat" | "NamePat" | "WildPat" | "TuplePat" => Form::Pattern,
            "Item" => Form::Item,
            _ => Form::Part,
        };
        grammar().rules.iter().map(|r| form(&r.name)).collect()
    })
}

struct Builder<'a> {
    text: &'a str,
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
}

impl<'a> Builder<'a> {
    fn new(
        text: &'a str,
        level: &Level<'a>,
        done: &'a mut [Option<Result<Expr, Error>>],
    ) -> Builder<'a> {
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
            return Err(Error {
                span: e.span,
                message: "this block exports nothing: end it with an expression or `return e;`"
                    .into(),
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
            "Reduce" => {
                let of = self.node(kids[0])?;
                self.reduce_tail(of, kids[1])
            }
            "Range" => Err(self.later(kids[1])),
            "Prefix" => {
                let op = self.op(self.tree.nodes[n].start);
                let e = self.node(kids[0])?;
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
            "Block" => self.block(n),
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
            }],
            [p, _] => self.params(*p)?,
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
                    [args] => self.args(args)?,
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
            _ => return Err(self.later(s)),
        };
        Ok(Expr { kind, span })
    }

    /// `of` followed by the `ReduceTail` node `t`: a struct update `with { … }` and the suffixes
    /// after it, which apply to the updated value.
    fn reduce_tail(&mut self, of: Expr, t: usize) -> Result<Expr, Error> {
        if self.tree.layer(t) != 2 {
            return Err(self.later(t));
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

    /// The record display of node `n`, a `Display`: `{x: 1, y:}`, `y:` being `y: y`. The other
    /// displays, of sets and maps, are of layer L3.
    fn display(&mut self, n: usize) -> Result<Expr, Error> {
        if self.tree.layer(n) != 2 {
            return Err(self.later(n));
        }
        let mut fields: Vec<(String, Expr)> = Vec::new();
        let mut seen = HashMap::new();
        for &k in self.kids(n) {
            if self.tree.name(k) == "Name" {
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

    #[allow(clippy::type_complexity)]
    fn args(&mut self, n: usize) -> Result<(Vec<Expr>, Vec<(String, Expr)>, bool), Error> {
        let node = &self.tree.nodes[n];
        let curry = self.word(node.end - 1) == "...";
        let (mut positional, mut named) = (Vec::new(), Vec::new());
        let mut seen: HashMap<&str, Span> = HashMap::new();
        for &k in &node.kids {
            let kids = self.kids(k);
            match self.tree.name(k) {
                "PlainArg" => {
                    positional.push(self.node(kids[0])?);
                    continue;
                }
                "SortArg" => return Err(self.later(k)),
                _ => {}
            }
            let span = self.span(kids[0]);
            let word = self.word(self.tree.nodes[kids[0]].start);
            if let Some(first) = seen.get(word) {
                return Err(Error {
                    span,
                    message: format!("the argument `{word}` is named twice"),
                    notes: vec![Note {
                        span: *first,
                        text: format!("the first argument named `{word}`"),
                    }],
                });
            }
            seen.insert(word, span);
            let value = match kids {
                [_, v] => self.node(*v)?,
                _ => self.node(kids[0])?,
            };
            named.push((word.to_string(), value));
        }
        Ok((positional, named, curry))
    }

    fn literal(&mut self, n: usize) -> Result<Expr, Error> {
        let i = self.tree.nodes[n].start;
        let kind = match &self.tokens[i].tok {
            Tok::Int { radix, digits } => ExprKind::Int {
                radix: *radix,
                digits: digits.clone(),
            },
            Tok::Float(s) => ExprKind::Float(s.clone()),
            Tok::Rat(s) => ExprKind::Rat(s.clone()),
            Tok::Keyword(k) => ExprKind::Bool(*k == "true"),
            Tok::Str(parts) => {
                let mut out = Vec::with_capacity(parts.len());
                let mut hole = self.first + self.holes[i];
                for p in parts {
                    out.push(match p {
                        Part::Text(t) => StrPart::Text(t.clone()),
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
        Ok(Expr {
            kind,
            span: self.span(n),
        })
    }
}
