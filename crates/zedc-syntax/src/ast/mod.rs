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
//! and in `stmts` the guards `while` and `until`, `initial` statements with `with carryForward`,
//! indexed definitions, boundary `with` clauses and expression statements. A primed name `x'` is one token, so it is a name
//! like any other here. A form of a later layer is an error naming that layer.

mod body;
mod builder;
mod drop;
mod initial;
mod neglit;
mod node;
mod sentinel;
mod show;
mod stmts;
mod types;
mod walk;

use std::collections::HashMap;
use std::fmt;
use std::sync::OnceLock;

use num_bigint::BigUint;
use zed_kernel::num::TooLarge;
use zedc_base::rejection::Row;

pub use node::{
    Annot, Arm, BinaryOp, BoundaryItem, CARRY_FORWARD, Error, Every, Expr, ExprKind, Field,
    Function, Import, ImportKind, IndexKey, IndexedDef, Initial, MainHeader, Method, Note, Param,
    Pattern, Port, PortName, PortValue, RangeEnd, Stmt, StmtKind, StrPart, Struct, Target,
    TestPorts, Type, TypeBound, TypeDecl, TypeKind, TypeParam, UnaryOp, Update,
};

use crate::lex::{Part, Span, Tok, Token};
use crate::parse::{Tree, grammar};
use builder::{Bare, Builder, Built, Level, Mains, Methods};
pub use walk::{expr_kids_mut, stmts_exprs_mut};

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
                    menu: String::new(),
                    span: s.span,
                    message:
                        "`return` gives the value a block exports, and this one stands at the top \
                              level of the unit, outside every block. Write it inside the block \
                              whose value it gives, or remove it."
                            .into(),
                    notes: Vec::new(),
                }),
                Ok(s) => out.push(s),
                Err(e) => errors.push(e),
            }
        }
        if let Err(e) = b.initials_placed(None, &out) {
            errors.push(e);
            errors.sort_by_key(|e| e.span);
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
        // A skipped declaration's holes have no tree (`Tree::skipped`).
        let kept = tokens.iter().enumerate().filter(|&(j, _)| !tree.skips(j));
        let holes = kept.flat_map(|(_, t)| match &t.tok {
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
    let mains = Mains::new(text, tokens, tree);
    let qualifiers = initial::qualifiers(text, &list);
    let methods = Methods::new(text, tokens, tree);
    let mut done: Vec<Option<Result<Expr, Error>>> = Vec::new();
    done.resize_with(list.len(), || None);
    for (i, l) in list.iter().enumerate().skip(1).rev() {
        let mut b = Builder::new(text, l, &mut done, &bare, &mains, &qualifiers, &methods);
        b.fill(l.tree.root);
        let e = b.node(l.tree.root);
        done[i] = Some(e);
    }
    top(&mut Builder::new(
        text,
        &list[0],
        &mut done,
        &bare,
        &mains,
        &qualifiers,
        &methods,
    ))
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

impl<'a, 's> Builder<'a, 's> {
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
                let op =
                    BinaryOp::of_token(op).expect("Or to Multiplicative join by a binary operator");
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
            "OpFunction" => {
                let op = self.op(self.tree.nodes[n].start + 1);
                let op = BinaryOp::of_token(op)
                    .expect("OpFunction = '(' BinOp ')', each BinOp a binary operator");
                Ok(Expr {
                    kind: ExprKind::Section(op),
                    span: self.span(n),
                })
            }
            "ArrayExpr" => Ok(Expr {
                kind: ExprKind::Array(
                    kids.iter()
                        .map(|&k| self.node(k))
                        .collect::<Result<_, _>>()?,
                ),
                span: self.span(n),
            }),
            "For" => self.for_expr(n),
            // `Prefix = AnnotExpr`, an annotation on an operand, `@fpsafe (x - y)`: not built
            // yet, so its node gives the error naming its layer.
            "Prefix" if self.tree.name(kids[0]) == "AnnotExpr" => self.node(kids[0]),
            "Prefix" => {
                let op = self.op(self.tree.nodes[n].start);
                let op = UnaryOp::of_token(op).expect("Prefix = ('-' | '!') Prefix");
                let e = self.node(kids[0])?;
                if let Some(err) = self.negated_literal_chain(n, &e) {
                    return Err(err);
                }
                Ok(Expr {
                    kind: ExprKind::Unary(op, Box::new(e)),
                    span: self.span(n),
                })
            }
            "Power" => self.binary(BinaryOp::Pow, kids[0], kids[1]),
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
                let label: Option<String> = label
                    .first()
                    .map(|&l| self.word(self.tree.nodes[l].start).into());
                let body = self.body(body)?;
                let span = self.span(n);
                self.loop_initials(label.as_deref(), span, &body, n)?;
                Ok(Expr {
                    kind: ExprKind::Loop {
                        label,
                        body: Box::new(body),
                    },
                    span,
                })
            }
            "Break" => Ok(Expr {
                kind: ExprKind::Break(Box::new(self.node(kids[0])?)),
                span: self.span(n),
            }),
            _ => unreachable!("make builds only these rules as expressions"),
        }
    }

    fn binary(&mut self, op: BinaryOp, l: usize, r: usize) -> Result<Expr, Error> {
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
            // `main` written as the one word, as [`Mains::new`] finds the read before the build.
            "ReadSuffix"
                if matches!(&of.kind, ExprKind::Name(n) if n == "main")
                    && of.span.end - of.span.start == "main".len()
                    && self.word(node.end - 1) == "files" =>
            {
                return self.main_files(span);
            }
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
            "MemberSuffix" if self.main_param(&of).is_some() => {
                return self.main_field(*of, self.word(node.end - 1), span);
            }
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
                    menu: String::new(),
                    span,
                    message: format!(
                        "the field `{path}` is updated twice in one `with`, and a `with` updates \
                         each field once. Remove one of the two updates."
                    ),
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
                menu: String::new(),
                span: self.span(odd),
                message: format!(
                    "{this} stands in a display whose first entry is a {that}, and a display \
                     is a set or a map, not both. Write every entry as a {that}, or write the \
                     entries in two displays."
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

    fn literal(&mut self, n: usize) -> Result<Expr, Error> {
        self.literal_at(self.tree.nodes[n].start, self.span(n))
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

/// A lexical error as an error of the source, with no derivation.
impl From<crate::lex::Error> for Error {
    fn from(e: crate::lex::Error) -> Error {
        Error {
            menu: String::new(),
            span: e.span,
            message: e.to_string(),
            notes: Vec::new(),
            row: None,
        }
    }
}

impl Error {
    /// The parse error `e` of the source `text` as an error of the source: at a `with` clause
    /// that gives a sentinel value, or at a reserved word written as a name, its row, message
    /// and repairs; elsewhere the headline "Syntax error at `area`.", with the token where
    /// the parse stopped as written, and a note there with the tokens the grammar takes there
    /// (DESIGN.md sec:diagnostics, "A short headline" and the row "Syntax error"). A token
    /// that spans lines or holds a backtick is not quoted: the excerpt under the headline
    /// shows it. O(t) for a token of t bytes.
    pub fn of_parse(text: &str, e: crate::parse::Error) -> Error {
        let message = e.to_string();
        let Some(c) = e.clause else {
            let quotable = |t: &str| !t.is_empty() && !t.contains(['\n', '`']);
            let mut headline = match text.get(e.span.start..e.span.end).unwrap_or("") {
                "" if e.span.start >= text.len() => "Syntax error at the end of the text.".into(),
                t if !quotable(t) => "Syntax error here.".into(),
                t => format!("Syntax error at `{t}`."),
            };
            // A repair is a source line as it reads repaired; one that cannot be quoted is
            // left out, as the token in the headline is.
            let repairs: Vec<(Span, String)> = e
                .recovery
                .repairs
                .into_iter()
                .filter(|(_, r)| quotable(r))
                .collect();
            if let Some((_, r)) = repairs.first() {
                headline.push_str(&format!(" Try `{r}` instead."));
            }
            let mut notes = vec![Note {
                span: e.span,
                text: message,
            }];
            notes.extend(
                e.recovery
                    .notes
                    .into_iter()
                    .map(|(span, text)| Note { span, text }),
            );
            notes.extend(repairs.into_iter().map(|(span, r)| Note {
                span,
                text: format!("repair: `{r}`"),
            }));
            return Error {
                menu: String::new(),
                span: e.span,
                message: headline,
                notes,
                row: Some(Row::SyntaxError),
            };
        };
        Error {
            menu: String::new(),
            span: c.span,
            message,
            notes: c
                .notes
                .into_iter()
                .map(|(span, text)| Note { span, text })
                .collect(),
            row: c.row,
        }
    }
}
