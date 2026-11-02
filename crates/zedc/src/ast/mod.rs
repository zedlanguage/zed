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
//! A unit is its declarations and statements. A form of a later layer is an error naming that
//! layer.

mod stmts;
mod types;

use std::collections::HashMap;
use std::fmt;

pub use stmts::{Function, Port, Stmt, StmtKind, Target};
pub use types::{Param, Pattern, Type, TypeKind, TypeParam};

use crate::lex::{Part, Span, Tok, Token};
use crate::parse::Tree;

/// An expression and its span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    /// What it is.
    pub kind: ExprKind,
    /// Its text.
    pub span: Span,
}

/// The kinds of expression.
#[derive(Clone, Debug, PartialEq, Eq)]
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
}

/// A part of a string expression.
#[derive(Clone, Debug, PartialEq, Eq)]
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
    builder(text, tokens, tree).node(n)
}

/// The statements of `tree`, parsed as `Unit` from `tokens` of `text`, in written order. A
/// unit's top level exports its declarations, so `return` there is an error.
pub fn unit(text: &str, tokens: &[Token], tree: &Tree) -> Result<Vec<Stmt>, Error> {
    let b = builder(text, tokens, tree);
    let items = b.kids(tree.root).iter().map(|&k| b.item(k));
    items
        .map(|s| match s? {
            Stmt {
                kind: StmtKind::Return(_),
                span,
            } => Err(Error {
                span,
                message: "`return` exports from a block; a unit's top level has none".into(),
                notes: Vec::new(),
            }),
            s => Ok(s),
        })
        .collect()
}

fn builder<'a>(text: &'a str, tokens: &'a [Token], tree: &'a Tree) -> Builder<'a> {
    let mut holes = Vec::new();
    let mut count = 0;
    for t in tokens {
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
        tokens,
        tree,
        holes,
    }
}

struct Builder<'a> {
    text: &'a str,
    tokens: &'a [Token],
    tree: &'a Tree,
    /// For each token, the index in `tree.holes` of its first hole.
    holes: Vec<usize>,
}

impl Builder<'_> {
    fn span(&self, n: usize) -> Span {
        let node = &self.tree.nodes[n];
        Span {
            start: self.tokens[node.start].span.start,
            end: self.tokens[node.end - 1].span.end,
        }
    }

    fn word(&self, i: usize) -> &str {
        let s = self.tokens[i].span;
        &self.text[s.start..s.end]
    }

    fn kids(&self, n: usize) -> &[usize] {
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

    fn node(&self, n: usize) -> Result<Expr, Error> {
        let kids = self.kids(n);
        match self.tree.name(n) {
            "Expr" => self.node(kids[0]),
            "Lambda" => self.lambda(n),
            "Expr12" => {
                let mut e = self.node(kids[0])?;
                for &t in &kids[1..] {
                    e = self.else_tail(e, t)?;
                }
                Ok(e)
            }
            "Or" | "And" | "Additive" | "Multiplicative" | "Equality" | "Compare" => self.fold(n),
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
            "Reduce" => Err(self.later(self.kids(self.spine(n).1[0])[1])),
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
                let (base, links) = self.spine(n);
                let mut e = self.node(base)?;
                for l in links {
                    e = self.suffix(e, self.kids(l)[1])?;
                }
                Ok(e)
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
            "Group" => Ok(Expr {
                span: self.span(n),
                ..self.node(kids[0])?
            }),
            "TupleExpr" => Ok(Expr {
                kind: ExprKind::Tuple(
                    kids.iter()
                        .map(|&k| self.node(k))
                        .collect::<Result<_, _>>()?,
                ),
                span: self.span(n),
            }),
            "Block" => self.block(n, true),
            "If" => Ok(Expr {
                kind: ExprKind::If {
                    cond: Box::new(self.node(kids[0])?),
                    then: Box::new(self.node(kids[1])?),
                    otherwise: Box::new(self.node(kids[2])?),
                },
                span: self.span(n),
            }),
            "Name" => Ok(Expr {
                kind: ExprKind::Name(self.word(self.tree.nodes[n].start).into()),
                span: self.span(n),
            }),
            "Literal" => self.literal(n),
            _ => Err(self.later(n)),
        }
    }

    /// The left spine of node `n`, of a left-recursive rule `R = R … | …`: the first child
    /// below the last node of rule `R`, and those nodes from the innermost out.
    fn spine(&self, n: usize) -> (usize, Vec<usize>) {
        let rule = self.tree.nodes[n].rule;
        let mut links = vec![n];
        let mut base = self.kids(n)[0];
        while self.tree.nodes[base].rule == rule {
            links.push(base);
            base = self.kids(base)[0];
        }
        links.reverse();
        (base, links)
    }

    /// The operator token at `i`, as the lexer's static text.
    fn op(&self, i: usize) -> &'static str {
        match self.tokens[i].tok {
            Tok::Op(o) | Tok::Keyword(o) => o,
            _ => unreachable!("an operator token"),
        }
    }

    fn binary(&self, op: &'static str, l: usize, r: usize) -> Result<Expr, Error> {
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

    /// A left-associative chain; each operator is the token before its right operand.
    fn fold(&self, n: usize) -> Result<Expr, Error> {
        let (base, links) = self.spine(n);
        let mut e = self.node(base)?;
        for l in links {
            let k = self.kids(l)[1];
            let op = self.op(self.tree.nodes[k].start - 1);
            let r = self.node(k)?;
            let span = Span {
                start: e.span.start,
                end: r.span.end,
            };
            e = Expr {
                kind: ExprKind::Binary(op, Box::new(e), Box::new(r)),
                span,
            };
        }
        Ok(e)
    }

    /// A lambda: `Name '->' body` or `'(' Params? ')' '->' body`.
    fn lambda(&self, n: usize) -> Result<Expr, Error> {
        let kids = self.kids(n);
        let body = *kids.last().expect("Lambda ends in its body");
        let params = match kids {
            [_] => Vec::new(),
            [p, _] if self.tree.name(*p) == "Name" => vec![Param {
                name: self.word(self.tree.nodes[*p].start).into(),
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
    fn else_tail(&self, of: Expr, t: usize) -> Result<Expr, Error> {
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

    fn suffix(&self, of: Expr, s: usize) -> Result<Expr, Error> {
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

    #[allow(clippy::type_complexity)]
    fn args(&self, n: usize) -> Result<(Vec<Expr>, Vec<(String, Expr)>, bool), Error> {
        let node = &self.tree.nodes[n];
        let curry = self.word(node.end - 1) == "...";
        let (mut positional, mut named) = (Vec::new(), Vec::new());
        let mut seen: HashMap<String, Span> = HashMap::new();
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
            let name = self.node(kids[0])?;
            let ExprKind::Name(word) = &name.kind else {
                unreachable!("NamedArg = Name ':' Expr?")
            };
            if let Some(first) = seen.get(word) {
                return Err(Error {
                    span: name.span,
                    message: format!("the argument `{word}` is named twice"),
                    notes: vec![Note {
                        span: *first,
                        text: format!("the first argument named `{word}`"),
                    }],
                });
            }
            seen.insert(word.clone(), name.span);
            let value = match kids {
                [_, v] => self.node(*v)?,
                _ => name.clone(),
            };
            named.push((word.clone(), value));
        }
        Ok((positional, named, curry))
    }

    fn literal(&self, n: usize) -> Result<Expr, Error> {
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
                let mut out = Vec::new();
                let mut hole = self.holes[i];
                for p in parts {
                    out.push(match p {
                        Part::Text(t) => StrPart::Text(t.clone()),
                        Part::Hole { tokens, .. } => {
                            let tree = &self.tree.holes[hole];
                            hole += 1;
                            StrPart::Hole(build(self.text, tokens, tree)?)
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

/// Writes `xs` with a space between each two, each straight into `f`.
fn spaced<T: fmt::Display>(f: &mut fmt::Formatter<'_>, xs: &[T]) -> fmt::Result {
    let mut sep = "";
    for x in xs {
        write!(f, "{sep}{x}")?;
        sep = " ";
    }
    Ok(())
}

/// An s-expression: `(call f 1 (x: 2) ...)`, `(index m k)`, `(. p x)`, `(?. p x)`, `(+ a b)`,
/// `(tuple a b)`, `(fn (x (y: int)) e)`, `(is e T)`, `(else e #a d)`.
impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ExprKind::Int { radix, digits } => {
                let prefix = match radix {
                    2 => "0b",
                    8 => "0o",
                    16 => "0x",
                    _ => "",
                };
                write!(f, "{prefix}{digits}")
            }
            ExprKind::Float(s) => f.write_str(s),
            ExprKind::Rat(s) => write!(f, "{s}r"),
            ExprKind::Str(parts) => {
                f.write_str("(str")?;
                for p in parts {
                    match p {
                        StrPart::Text(t) => write!(f, " {t:?}")?,
                        StrPart::Hole(e) => write!(f, " {e}")?,
                    }
                }
                f.write_str(")")
            }
            ExprKind::Bool(b) => write!(f, "{b}"),
            ExprKind::Atom(a) => write!(f, "#{a}"),
            ExprKind::Name(n) => f.write_str(n),
            ExprKind::Unary(op, e) => write!(f, "({op} {e})"),
            ExprKind::Binary(op, a, b) => write!(f, "({op} {a} {b})"),
            ExprKind::Call {
                callee,
                positional,
                named,
                curry,
            } => {
                write!(f, "(call {callee}")?;
                for a in positional {
                    write!(f, " {a}")?;
                }
                for (n, a) in named {
                    write!(f, " ({n}: {a})")?;
                }
                if *curry {
                    f.write_str(" ...")?;
                }
                f.write_str(")")
            }
            ExprKind::Index(e, k) => write!(f, "(index {e} {k})"),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => write!(f, "(if {cond} {then} {otherwise})"),
            ExprKind::Block(stmts) => {
                f.write_str("(block")?;
                for s in stmts {
                    write!(f, " {s}")?;
                }
                f.write_str(")")
            }
            ExprKind::Tuple(es) => {
                f.write_str("(tuple")?;
                for e in es {
                    write!(f, " {e}")?;
                }
                f.write_str(")")
            }
            ExprKind::Lambda { params, body } => {
                f.write_str("(fn (")?;
                spaced(f, params)?;
                write!(f, ") {body})")
            }
            ExprKind::Is { of, ty, negated } => {
                write!(f, "(is {}{of} {ty})", if *negated { "not " } else { "" })
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => match pattern {
                Some(p) => write!(f, "(else {of} {p} {default})"),
                None => write!(f, "(else {of} {default})"),
            },
            ExprKind::Member { of, name, safe } => {
                write!(f, "({} {of} {name})", if *safe { "?." } else { "." })
            }
        }
    }
}
