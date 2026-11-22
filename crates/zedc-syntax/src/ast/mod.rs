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
//! indexed definitions, boundary `with` clauses and expression statements. A primed name `x'` is
//! one token, so it is a name like any other here. A form of a later layer is an error naming that
//! layer.

mod body;
mod breaks;
mod builder;
mod drop;
mod infix;
mod initial;
mod neglit;
mod node;
mod sentinel;
mod show;
mod stmts;
mod top;
mod types;
mod walk;

use std::collections::HashMap;
use std::fmt;
use std::sync::OnceLock;

use zed_kernel::num::{TooLarge, bits_of_digits};
use zedc_base::rejection::Row;

pub use node::{
    Annot, Arm, BinaryOp, BoundaryItem, CARRY_FORWARD, Error, Every, Expr, ExprKind, Field,
    Function, Import, ImportKind, IndexKey, IndexedDef, Initial, MainHeader, Method, Note, Param,
    Pattern, Port, PortName, PortValue, RangeEnd, RemapLevel, Stmt, StmtKind, StrPart, Struct,
    Target, TestPorts, Type, TypeBound, TypeDecl, TypeKind, TypeParam, UnaryOp, Update,
    type_var_form,
};

use crate::lex::{Part, Span, Tok, Token};
use crate::parse::{Tree, grammar};
use builder::{Bare, Builder, Built, Level, Mains, Methods};
pub use walk::{Blocks, expr_kids, expr_kids_mut, stmts_exprs, stmts_exprs_mut};

// Why the shape of a node is known. The builder here and in `builder`, `stmts`, `types` and
// `infix` reads a parse node by its rule's name, its alternative and its children, and where
// the grammar allows only some shapes it says so with an `unreachable!` or an `expect` whose
// text is the grammar rule (`"Lambda = (Name | '(' Params? ')') '->' body"`) or what follows
// from it (`"Loop ends in its block"`). Each such site points here. The argument:
//
// 1. The grammar is the text of `zed/grammar/syntax.peg` and `notation.peg`, fixed at build
//    time (`parse::grammar`), so the facts below are about one fixed grammar.
// 2. The parser (`parse::engine`, `Parser::run`) builds a node only when an alternative of a
//    rule matches, and never for a `~R` alternative: that match is the node of `R` (`if
//    alt.pass { self.kids[*base] }`). The node's `kids` are the nodes pushed while that
//    alternative's expression matched, in order of position: a rule reference pushes the one
//    node of its match (`self.kids.push(node)` after `Frame::Rule` ends); a literal, a token
//    kind or `head` pushes none; a failed branch of a choice, sequence, loop or separated
//    list truncates `kids` to the mark it began at; `&e` and `!e` truncate to their mark
//    whether they match or not (`Frame::And`, `Frame::Not`); the branch markers pushed by a
//    choice are split out into `branches` (`split_kids`). Left-recursive growth (`grown`)
//    keeps the longest match of the rule, a node built by the same steps.
// 3. So the rules of a node's children, in order, are a word of the alternative's expression
//    read with every rule reference as one letter and every other part as nothing, each
//    letter a node of the rule named there or of a rule reached from it through `~`
//    alternatives. The root a recovered unit builds (`recover::recovering`) is the `Unit`
//    alternative `Item* END` over the declarations kept, which is such a word too.
// 4. A site that reads child `i`, or splits off the first or last child, or matches on the
//    rule name of a child, relies only on this: its message names the alternative whose
//    words it relies on, and the words of that alternative have the child it reads.
//
// The test `l01_08_parser::grammar_shape::every_node_s_children_match_its_alternative` checks
// steps 2 and 3 on every node of every unit under `zed/` and the steps' `zed/` folders, of
// every case of `zed/grammar/cases.txt` that parses, and of written texts for the rules those
// leave out: it computes the words of each alternative and fails on a node whose children are
// not one, or a node of a `~` alternative (a negative control, the children reversed, fails
// it at once). Step 4 is read at each site against its rule in `syntax.peg`; a change to the
// grammar that changes a rule a site names must change the site, and the test does not see
// that the message names the rule correctly, only that the tree is shaped as the grammar is.

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
    // Cannot fail: `unit_all_errors` returns `Err(errors)` only under `!errors.is_empty()`.
    unit_all_errors(text, tokens, tree)
        .map_err(|es| es.into_iter().next().expect("an error per failed unit"))
}

/// The statements of `tree`, parsed as `Unit` from `tokens` of `text`, in written order but
/// for guards, which are ordered as in a block (`StmtKind::place`), or the error of each item
/// that cannot be built, in written order. Every item is built, so which errors are reported
/// does not depend on the order of the items (step L1.29b). A unit's top level holds
/// declarations only, so a statement there is an error (`Builder::top_statement`), in place
/// of any error building it gave, as `break;` outside a loop.
pub fn unit_all_errors(text: &str, tokens: &[Token], tree: &Tree) -> Result<Vec<Stmt>, Vec<Error>> {
    with_holes(text, tokens, tree, |b| {
        b.fill(tree.root);
        let kids = b.kids(tree.root);
        let mut out = Vec::with_capacity(kids.len());
        let mut errors = Vec::new();
        let mut main = None;
        for &k in kids {
            if let Some(e) = b.top_statement(k, &mut main) {
                errors.push(e);
                continue;
            }
            match b.item(k) {
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
    let mains = Mains::new(text, &list);
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
            | "Equality" | "Compare" | "IsTest" | "Reduce" | "Range" | "Infix" | "Prefix"
            | "Power" | "Postfix" | "AtomExpr" | "Group" | "TupleExpr" | "Block" | "If"
            | "Literal" | "Display" | "This" | "Match" | "InTest" | "OpFunction" | "ArrayExpr"
            | "For" | "Loop" => Form::Expr,
            "Type" | "TypePostfix" | "Arrow" | "TypeDiff" | "TypeOr" | "TypeAnd" | "TypeName"
            | "AtomType" | "TupleType" | "GroupType" | "TypeApply" | "AtomApply" | "RecordType"
            | "RankArrayType" => Form::Type,
            "AtomPattern" | "CtorPat" | "NamePat" | "WildPat" | "TuplePat" | "IsPat"
            | "SignedLit" | "RangePat" | "OrPat" | "AtomUnion" => Form::Pattern,
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
                // Shape: see "Why the shape of a node is known" above; `~Or` builds no node.
                let [l, t] = kids[..] else {
                    unreachable!("Expr12 = Expr12 ElseTail | ~Or")
                };
                let e = self.node(l)?;
                self.else_tail(e, t)
            }
            "Or" | "And" | "Additive" | "Multiplicative" | "Equality" | "Compare" => {
                // The operator is the token before the right operand. Shape: see "Why the
                // shape of a node is known" above; each of these alternatives that builds a
                // node is `L op R`, its operator a literal between its two children, and every
                // operator these alternatives name is one `BinaryOp::of_token` reads.
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
            "Infix" => self.infix_call(n),
            "OpFunction" => {
                // Shape: see "Why the shape of a node is known" above; `BinaryOp::of_token`
                // reads all sixteen `BinOp` literals.
                let op = self.op(self.tree.nodes[n].start + 1);
                let op = BinaryOp::of_token(op)
                    .expect("OpFunction = '(' BinOp ')', each BinOp a binary operator");
                let span = self.span(n);
                Ok(Expr {
                    kind: ExprKind::Section(op, Box::new(section_lambda(op, span))),
                    span,
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
                // Shape: see "Why the shape of a node is known" above; the `AnnotExpr`
                // alternative is read on the line before.
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
                // Shape: see "Why the shape of a node is known" above (`AtomExpr = ATOM`).
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
                // Shape: see "Why the shape of a node is known" above.
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
            // Cannot be reached: `make` calls this only for a rule `forms` maps to
            // `Form::Expr`, and the thirty names listed there are the thirty arms above.
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
        // Shape: see "Why the shape of a node is known" above; the children are `[Name,
        // body]`, `[Params, body]` or `[body]`.
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
        // Shape: see "Why the shape of a node is known" above.
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
            // `main` as the one word in any number of parentheses, which a `Group` builds to
            // the name with the parentheses' span: the reads [`Mains::new`] finds before the
            // build.
            "ReadSuffix"
                if matches!(&of.kind, ExprKind::Name(n) if n == "main")
                    && self.word(node.end - 1) == "files" =>
            {
                return Ok(self.main_files(span));
            }
            "CallSuffix" => {
                // Shape: see "Why the shape of a node is known" above.
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
                    infix: false,
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
            // `as` and `into`, a remap (sec:remap_law).
            (8, _) => return self.remap(of, t),
            // `with f(…)` and `without f(…)` attach and drop a facet (sec:facets). Shape: see
            // "Why the shape of a node is known" above; the arms above take the alternatives
            // of layers 2, 3 and 8, and those left, of layers 7 and 12, begin with `with` and
            // `without` (the `into` arm is never taken).
            _ => {
                let kind = match self.word(self.tree.nodes[t].start) {
                    "into" => "the remap",
                    "with" => "the facet attachment",
                    "without" => "the facet removal",
                    w => unreachable!(
                        "a ReduceTail of layer 7 or 12 begins with `with` or `without`, not `{w}`"
                    ),
                };
                return Err(self.later_as(t, kind));
            }
        }
        let mut updates = Vec::new();
        let mut paths: HashMap<Vec<&str>, Span> = HashMap::new();
        let mut kids = self.kids(t).iter().peekable();
        while let Some(&u) = kids.next_if(|&&k| self.tree.name(k) == "Update") {
            if self.tree.layer(u) != 2 {
                return Err(self.later(u));
            }
            // Shape: see "Why the shape of a node is known" above; layer 2 is `Name ('.'
            // Name)* '=' Expr`.
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

    /// `of` followed by the remap tail `t`, `as (InPattern) Suffix*` or `into (OutPattern)
    /// Suffix*` (DESIGN.md sec:remap_law). An `into` written right after an `as` makes one
    /// remap with both halves. So does `(m as (…)) into (…)`, which means the same: `as` alone
    /// only names the source's levels, and the `into` pattern then binds them by those names.
    fn remap(&mut self, of: Expr, t: usize) -> Result<Expr, Error> {
        // Shape: see "Why the shape of a node is known" above; both layer-8 alternatives of
        // `ReduceTail` read their pattern first, then `Suffix*`.
        let (&pattern, suffixes) = (self.kids(t).split_first())
            .expect("a remap tail holds its pattern after the parenthesis");
        // The pattern's `)` is the token after its last.
        let span = Span {
            start: of.span.start,
            end: self.tokens[self.tree.nodes[pattern].end].span.end,
        };
        let mut e = if self.word(self.tree.nodes[t].start) == "as" {
            let binders = self.kids(pattern).iter().map(|&b| self.target(b)).collect();
            Expr {
                kind: ExprKind::Remap {
                    of: Box::new(of),
                    binders: Some(binders),
                    levels: None,
                },
                span,
            }
        } else {
            let levels = (self.kids(pattern).iter())
                .map(|&l| self.remap_level(l))
                .collect::<Result<Vec<_>, _>>()?;
            let mut of = of;
            match &mut of.kind {
                ExprKind::Remap {
                    levels: written @ None,
                    ..
                } => {
                    *written = Some(levels);
                    of.span = span;
                    of
                }
                _ => Expr {
                    kind: ExprKind::Remap {
                        of: Box::new(of),
                        binders: None,
                        levels: Some(levels),
                    },
                    span,
                },
            }
        };
        for &s in suffixes {
            e = self.suffix(e, s)?;
        }
        Ok(e)
    }

    /// The `Level` node `l` of an output pattern: a key, or a key and the reducer `>< op` that
    /// collapses its level. A sort key, a join of keys, a named key `name: e` and a reduction
    /// policy belong to later steps (L8.1, L8.2, L8.2b, L9) and are refused as such.
    fn remap_level(&mut self, l: usize) -> Result<RemapLevel, Error> {
        let sort = "the sort key";
        if matches!(self.word(self.tree.nodes[l].start), "asc" | "desc") {
            return Err(self.later_as(l, sort));
        }
        let (mut k, reduce) = match *self.kids(l) {
            [k] => (k, None),
            [k, op] if self.tree.name(op) != "ReducePolicy" => (k, Some(op)),
            [_, _, policy] | [_, policy] => return Err(self.later(policy)),
            _ => return Err(self.later_as(l, sort)),
        };
        // Down through the one-key forms of `JoinTerm` and `KeyTerm`, parentheses included.
        let key = loop {
            match (self.tree.name(k), self.kids(k)) {
                ("SortKey", _) => return Err(self.later_as(k, sort)),
                ("JoinTerm" | "KeyTerm", &[one]) => k = one,
                ("JoinTerm" | "AndJoin", _) => {
                    return Err(self.later_as(k, "the join"));
                }
                ("Key", &[]) => break None,
                ("Key", &[_, _]) => {
                    return Err(self.later_as(k, "the named key"));
                }
                ("Key", &[e]) => break Some(self.node(e)?),
                _ => break Some(self.node(k)?),
            }
        };
        Ok(RemapLevel {
            key,
            reduce: reduce.map(|op| self.node(op)).transpose()?,
            span: self.span(l),
        })
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
                // Shape: see "Why the shape of a node is known" above. In `Name ':' (Lambda
                // | Expr12)?` a value comes after its name, and a value is followed by `,` or
                // `}`, never `:`, so the first child is a name.
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
                // Shape: see "Why the shape of a node is known" above; an entry of one child
                // in a map was refused above (`odd`).
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
        // Shape: see "Why the shape of a node is known" above; the children are the
        // generator, each `MoreGen`, the guard if written, and the block, and a `MoreGen` is
        // refused below, so what is left between is the guard or nothing.
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
        // Shape: see "Why the shape of a node is known" above, here and for each `Arm`.
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
    // Why the two `expect`s cannot fail: `Count::write_str` and `String`'s `write_str` always
    // return `Ok`, and `fmt::write` errs only when the writer or `x`'s `Display` does. That
    // `Display` errs only when its writer errs is the contract of `std::fmt` ("formatting
    // should only fail if the writer fails"), assumed of every caller's type, not checked
    // here; a `Display` that returned `Err` on its own would panic here.
    fmt::write(&mut len, format_args!("{x}")).expect("counting cannot fail");
    let mut out = String::new();
    // The literal's characters are counted as its digits: the size named is a number of that
    // many digits, and the memory asked a byte for each.
    out.try_reserve_exact(len.0).map_err(|_| TooLarge {
        size: bits_of_digits(&len.0.into()),
        ask: num_bigint::BigUint::from(len.0) << 3u32,
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

/// A lexical error as an error of the source, with no derivation; a `Bidi_Control` character
/// in a comment or in a string's text with its row, why it is refused and its repair
/// (DESIGN.md sec:diagnostics).
impl From<crate::lex::Error> for Error {
    fn from(e: crate::lex::Error) -> Error {
        let (notes, row) = match &e.kind {
            crate::lex::ErrorKind::TextDirection { c, repair, .. } => {
                let mut notes = vec![Note {
                    span: e.span,
                    text: crate::lex::text_direction_note(*c),
                }];
                notes.extend(repair.iter().map(|r| Note {
                    span: e.span,
                    text: format!("repair: `{r}`"),
                }));
                (notes, Some(Row::BidiControlInText))
            }
            crate::lex::ErrorKind::LeadingZero { decimal, octal, .. } => {
                let mut notes = vec![Note {
                    span: e.span,
                    text: crate::lex::LEADING_ZERO_NOTE.to_string(),
                }];
                notes.extend(std::iter::once(decimal).chain(octal).map(|r| Note {
                    span: e.span,
                    text: format!("repair: `{r}`"),
                }));
                (notes, Some(Row::LeadingZero))
            }
            _ => (Vec::new(), None),
        };
        Error {
            menu: String::new(),
            span: e.span,
            message: e.to_string(),
            notes,
            row,
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

/// The lambda `(l, r) -> l op r` that the section `(op)` at `span` stands for
/// ([`ExprKind::Section`]): the parameters `<left>` and `<right>`, names no identifier spells,
/// read at the opening and closing parentheses, and the body at the text between them.
fn section_lambda(op: BinaryOp, span: Span) -> Expr {
    let open = Span {
        start: span.start,
        end: span.start + 1,
    };
    let close = Span {
        start: span.end - 1,
        end: span.end,
    };
    let inner = Span {
        start: open.end,
        end: close.start,
    };
    let name = |text: &str, at: Span| Expr {
        kind: ExprKind::Name(text.to_string()),
        span: at,
    };
    let param = |text: &str, at: Span| Param {
        name: text.to_string(),
        tuple: None,
        positional: false,
        ty: None,
        default: None,
        span: at,
        name_at: at,
    };
    Expr {
        kind: ExprKind::Lambda {
            params: vec![param("<left>", open), param("<right>", close)],
            body: Box::new(Expr {
                kind: ExprKind::Binary(
                    op,
                    Box::new(name("<left>", open)),
                    Box::new(name("<right>", close)),
                ),
                span: inner,
            }),
        },
        span,
    }
}
