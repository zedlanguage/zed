//! Type expressions, parameter lists and atom patterns (step L1.10): what an `is` test, a
//! lambda's parameters and an `else` pattern are written with. Step L2.1 adds the applied
//! types `Tree(T)` and `#node(l: T)`, the record type `{x: int}`, the tuple-destructuring
//! parameter `(a, b)`, and the patterns that destructure a struct, `Point(x:, y: b)`, with the
//! name, `_` and tuple patterns they hold. Step L2.2 adds the patterns of a `match` arm: the
//! type pattern `n is T` and the literal pattern.

use std::collections::HashMap;
use std::mem;

use super::{Builder, Built, Error, Expr, ExprKind, Note, RangeEnd, Target};
use crate::lex::{Span, Tok};
use crate::rejection::Row;

/// A type expression and its span.
pub struct Type {
    /// What it is.
    pub kind: TypeKind,
    /// Its text.
    pub span: Span,
}

/// The kinds of type expression.
#[derive(Debug)]
pub enum TypeKind {
    /// A type name, its unit path included (`geometry.Point`).
    Name(String),
    /// An atom, without its `#`.
    Atom(String),
    /// Every member of one kind: `#_` every atom, `(..)` every tuple, `{..}` every struct.
    Every(Every),
    /// An atom with any payload, `#a(..)`: the atom, without its `#`.
    AtomAny(String),
    /// A tuple type `(A, B)`.
    Tuple(Vec<Type>),
    /// A union `A | B | …`.
    Union(Vec<Type>),
    /// An intersection `A & B & …`.
    And(Vec<Type>),
    /// A difference `A \ B`.
    Diff(Box<Type>, Box<Type>),
    /// A function type: one parameter per level, right-associative.
    Arrow {
        /// The parameters.
        params: Vec<TypeParam>,
        /// Whether it is `->?`, a partial map.
        partial: bool,
        /// The result.
        result: Box<Type>,
    },
    /// A morphism type with its two domain bounds, `L .. U -> V`.
    Bounded {
        /// The guarantee `L`, the keys certainly present.
        lower: Box<Type>,
        /// The permission `U`, the keys possibly present.
        upper: Box<Type>,
        /// The value type `V`.
        result: Box<Type>,
    },
    /// A type applied to arguments, `Tree(T)` or `geometry.Grid(int)`: its name, its unit path
    /// included, and the arguments.
    Apply(String, Vec<TypeParam>),
    /// An atom with a payload type, `#node(left: Tree, right: Tree)` or `#pair(int, int)`:
    /// the atom, without its `#`, and the payload's components.
    AtomApply(String, Vec<TypeParam>),
    /// A record type `{x: int, y: f64}`, its fields in written order.
    Record(Vec<(String, Type)>),
    /// The family type `[T]`, the array type `int[0..<_] -> T`: a `T` at each rank of a
    /// domain `0..<n` the type leaves open (sec:grammar, `RankArrayType`). It is not `Seq(T)`
    /// (sec:order), whose keys are origins.
    Array(Box<Type>),
    /// A type with its type variables bounded, `(x: T) -> T for T in int | f64`: each variable
    /// ranges over the carriers of its bound, one carrier at every place it stands.
    For {
        /// The type the variables stand in.
        ty: Box<Type>,
        /// The variables, in written order.
        bounds: Vec<TypeBound>,
    },
}

impl Type {
    /// The operands of the intersection of `ts`, with each intersection in parentheses among
    /// them replaced by its own operands, in written order: `(A & B) & C` has `A`, `B` and `C`.
    /// The walk keeps its own stack, as parentheses nest as deep as the text.
    pub fn and_operands(ts: &[Type]) -> Vec<&Type> {
        let mut out = Vec::with_capacity(ts.len());
        let mut stack: Vec<&Type> = ts.iter().rev().collect();
        while let Some(t) = stack.pop() {
            match &t.kind {
                TypeKind::And(ts) => stack.extend(ts.iter().rev()),
                _ => out.push(t),
            }
        }
        out
    }

    /// Its parameter list if it is a function type, a bounds clause around one included: `x`
    /// for a parameter named and not `positional`, and `_` for the others, which a call does
    /// not name; and the clauses around it.
    fn param_list(&self) -> Option<(Vec<&str>, Vec<&TypeBound>)> {
        let mut t = self;
        let mut bounds = Vec::new();
        while let TypeKind::For { ty, bounds: bs } = &t.kind {
            bounds.extend(bs);
            t = ty;
        }
        match &t.kind {
            TypeKind::Arrow { params, .. } => Some((
                params
                    .iter()
                    .map(|p| match &p.name {
                        Some(n) if !p.positional => n.as_str(),
                        _ => "_",
                    })
                    .collect(),
                bounds,
            )),
            TypeKind::Bounded { .. } => Some((vec!["_"], bounds)),
            _ => None,
        }
    }

    /// Of `ts`, the operands of an intersection as [`Type::and_operands`] gives them: whether
    /// they are all function types, and so one function's list of arrows, an overload
    /// (DESIGN.md sec:type_language, "Relation to semantic subtyping" (2)), or why they are no
    /// type. The arrows of one function share its parameter list and its bounds, so function
    /// types that take different parameter lists are no type, as are two that bound one
    /// variable by different carriers, and a bounds clause around an intersection that is
    /// itself an operand, since its variables would be bounded on part of the function.
    pub fn overload(ts: &[&Type]) -> Result<bool, String> {
        let mut lists = Vec::with_capacity(ts.len());
        let mut clause_around_and = false;
        for t in ts {
            match t.param_list() {
                Some(l) => lists.push(l),
                None if t.is_clause_around_and() => clause_around_and = true,
                None => return Ok(false),
            }
        }
        if clause_around_and {
            return Err(
                "a bounds clause stands around an intersection of function types that is \
                        part of another; write the clause once, after the whole intersection"
                    .to_string(),
            );
        }
        let Some(((list, _), _)) = lists.split_first() else {
            return Ok(false);
        };
        if let Some((other, _)) = lists.iter().find(|(l, _)| l != list) {
            return Err(format!(
                "the arrows of an intersection of function types share one parameter list, but \
                 one takes ({}) and another ({})",
                list.join(", "),
                other.join(", ")
            ));
        }
        let mut carriers: HashMap<&str, Vec<&str>> = HashMap::new();
        for b in lists.iter().flat_map(|(_, bs)| bs) {
            let these = b.carriers.carrier_names();
            match carriers.get(b.name.as_str()) {
                Some(first) if *first != these => {
                    return Err(format!(
                        "the type variable `{}` is bounded by {} on one arrow of an intersection \
                         of function types and by {} on another, but the arrows of one function \
                         share its bounds",
                        b.name,
                        first.join(" | "),
                        these.join(" | ")
                    ));
                }
                Some(_) => {}
                None => {
                    carriers.insert(b.name.as_str(), these);
                }
            }
        }
        Ok(true)
    }

    /// Whether it is a bounds clause around an intersection.
    fn is_clause_around_and(&self) -> bool {
        let mut t = self;
        while let TypeKind::For { ty, .. } = &t.kind {
            t = ty;
        }
        matches!(t.kind, TypeKind::And(_))
    }

    /// The carrier names of a bound, a union of them, sorted and each once, so two bounds
    /// written in different orders compare equal.
    fn carrier_names(&self) -> Vec<&str> {
        let mut out = Vec::new();
        let mut stack = vec![self];
        while let Some(t) = stack.pop() {
            match &t.kind {
                TypeKind::Union(ts) => stack.extend(ts),
                TypeKind::Name(n) => out.push(n.as_str()),
                // Resolve and the reader of printed types reject any other bound.
                _ => {}
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

/// The kind a kind-wide type `#_`, `(..)` or `{..}` names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Every {
    /// Every atom, `#_`.
    Atom,
    /// Every tuple, `(..)`.
    Tuple,
    /// Every struct, `{..}`.
    Struct,
}

/// One variable of a bounds clause, `T in int | f64`.
#[derive(Debug)]
pub struct TypeBound {
    /// The variable.
    pub name: String,
    /// The variable's text.
    pub span: Span,
    /// The bound, a union of carriers.
    pub carriers: Type,
}

/// A parameter of a function type: `int`, `x: int` or `positional x: int`.
#[derive(Debug)]
pub struct TypeParam {
    /// Its name, which documents it, if written.
    pub name: Option<String>,
    /// Whether it is written `positional`.
    pub positional: bool,
    /// Its type.
    pub ty: Type,
}

/// A parameter of a lambda or a declaration.
#[derive(Debug)]
pub struct Param {
    /// Its name. A tuple-destructuring parameter `(a, b)` has none in the source; its name is
    /// its text, `(a, b)`, which no identifier spells, so it names the fresh parameter of the
    /// desugaring (`let a = p[0]`, `let b = p[1]` in the body) and meets no other name.
    pub name: String,
    /// The targets of a tuple-destructuring parameter `(a, b)`, in order; such a parameter is
    /// positional.
    pub tuple: Option<Vec<Target>>,
    /// Whether it is written `positional`.
    pub positional: bool,
    /// Its type, if written.
    pub ty: Option<Type>,
    /// Its default, if written.
    pub default: Option<Expr>,
    /// Its text.
    pub span: Span,
    /// The text of its name; for a tuple-destructuring parameter, its text.
    pub name_at: Span,
}

/// A pattern: an atom pattern, which `else` takes at L1, and from step L2.1 the patterns a
/// struct is destructured with, which a payload or a `match` arm holds.
pub enum Pattern {
    /// `Point(x:, y: b)`: a struct's fields matched by name; `x:` (no pattern) binds the field
    /// to the name `x`.
    Struct {
        /// The struct's name.
        name: String,
        /// The fields matched, in written order.
        fields: Vec<(String, Option<Pattern>)>,
        /// Its text.
        span: Span,
    },
    /// A name, bound to the value matched.
    Name(String, Span),
    /// `_`, matching any value and binding nothing.
    Wild(Span),
    /// `(p, q, …)`, a tuple's components matched by position.
    Tuple(Vec<Pattern>, Span),
    /// `#name`, `#name(f: p, g:)` or `#name(p, q)`.
    Atom {
        /// The atom, without its `#`.
        name: String,
        /// Fields matched by name; `g:` (no pattern) binds the field to the name `g`.
        fields: Vec<(String, Option<Pattern>)>,
        /// Payload components matched by position.
        items: Vec<Pattern>,
        /// Its text.
        span: Span,
    },
    /// `n is T`, the value matched when it is in the set of `T`, bound to `n` if written.
    Is {
        /// The name bound.
        name: Option<String>,
        /// The type.
        ty: Box<Type>,
        /// Its text.
        span: Span,
    },
    /// A literal, `-1`, `"a"` or `true`, matching the value equal to it.
    Lit(Box<Expr>),
    /// A range pattern `0..<10`, `1..=9` or `0..`, matching the values in the range; its ends
    /// are literal patterns.
    Range {
        /// The first value.
        from: Box<Pattern>,
        /// The end.
        to: RangeEnd<Box<Pattern>>,
        /// Its text.
        span: Span,
    },
}

impl Pattern {
    /// Its text.
    pub fn span(&self) -> Span {
        match self {
            Pattern::Struct { span, .. }
            | Pattern::Atom { span, .. }
            | Pattern::Is { span, .. }
            | Pattern::Range { span, .. } => *span,
            Pattern::Lit(e) => e.span,
            Pattern::Name(_, span) | Pattern::Wild(span) | Pattern::Tuple(_, span) => *span,
        }
    }
}

impl Builder<'_, '_> {
    /// The type node `n` built to.
    pub(super) fn ty(&mut self, n: usize) -> Result<Type, Error> {
        match self.take(n) {
            Some(Ok(Built::Type(t))) => Ok(t),
            Some(Err(e)) => Err(e),
            Some(Ok(Built::Expr(_) | Built::Pattern(_) | Built::Stmt(_))) | None => {
                Err(self.later(n))
            }
        }
    }

    /// The type of node `n`, of a rule from `Type` down to `TypePrimary`.
    pub(super) fn make_type(&mut self, n: usize) -> Result<Type, Error> {
        let kids = self.kids(n);
        let node = &self.tree.nodes[n];
        let span = self.span(n);
        let kind = match self.tree.name(n) {
            "Type" if kids.len() == 1 => return self.ty(kids[0]),
            "Type" if kids.len() == 2 && self.tree.name(kids[1]) == "TypeBounds" => {
                let ty = Box::new(self.ty(kids[0])?);
                let pairs = self.kids(kids[1]);
                let mut bounds = Vec::with_capacity(pairs.len() / 2);
                let mut seen = HashMap::new();
                for &[v, c] in pairs.as_chunks::<2>().0 {
                    let name = self.word(self.tree.nodes[v].start);
                    self.once(&mut seen, name, v, "type variable", "bounded")?;
                    bounds.push(TypeBound {
                        name: name.to_string(),
                        span: self.span(v),
                        carriers: self.ty(c)?,
                    });
                }
                TypeKind::For { ty, bounds }
            }
            "Type" => return Err(self.later(kids[1])),
            "TypePostfix" if self.tree.nodes[kids[0]].rule == node.rule => {
                return self.ty(kids[0]);
            }
            "TypePostfix" => return Err(self.later(kids[1])),
            "Arrow" if self.tree.name(kids[0]) == "ArrowParams" => {
                let params = self.arrow_params(kids[0])?;
                self.arrow(params, kids[0], kids[1])?
            }
            "Arrow" if kids.len() == 3 => TypeKind::Bounded {
                lower: Box::new(self.ty(kids[0])?),
                upper: Box::new(self.ty(kids[1])?),
                result: Box::new(self.ty(kids[2])?),
            },
            "Arrow" => {
                let ty = self.ty(kids[0])?;
                let param = TypeParam {
                    name: None,
                    positional: false,
                    ty,
                };
                self.arrow(vec![param], kids[0], kids[1])?
            }
            "TypeDiff" => {
                let t = self.ty(kids[0])?;
                let r = self.ty(kids[1])?;
                let span = Span {
                    start: t.span.start,
                    end: r.span.end,
                };
                return Ok(Type {
                    kind: TypeKind::Diff(Box::new(t), Box::new(r)),
                    span,
                });
            }
            "TypeOr" => TypeKind::Union(self.operands(n)?),
            "TypeAnd" => TypeKind::And(self.operands(n)?),
            "TypeName" => TypeKind::Name(
                (node.start..node.end)
                    .step_by(2)
                    .map(|i| self.word(i))
                    .collect::<Vec<_>>()
                    .join("."),
            ),
            "AtomType" if self.word(node.start) == "#_" => TypeKind::Every(Every::Atom),
            "AtomType" => {
                let Tok::Atom(a) = &self.tokens[node.start].tok else {
                    unreachable!("an ATOM token")
                };
                TypeKind::Atom(a.clone())
            }
            "TupleType" if self.dots(node.start + 1) => TypeKind::Every(Every::Tuple),
            "TupleType" => TypeKind::Tuple(self.types(kids)?),
            "TypeApply" => {
                let path = &self.tree.nodes[kids[0]];
                let name = (path.start..path.end)
                    .step_by(2)
                    .map(|i| self.word(i))
                    .collect::<Vec<_>>()
                    .join(".");
                let args = kids[1..]
                    .iter()
                    .map(|&k| self.type_param(k))
                    .collect::<Result<_, _>>()?;
                TypeKind::Apply(name, args)
            }
            "AtomApply" if self.dots(node.start + 2) => {
                let Tok::Atom(a) = &self.tokens[node.start].tok else {
                    unreachable!("an ATOM token")
                };
                TypeKind::AtomAny(a.clone())
            }
            "AtomApply" => {
                let Tok::Atom(a) = &self.tokens[node.start].tok else {
                    unreachable!("an ATOM token")
                };
                let args = kids
                    .iter()
                    .map(|&k| self.type_param(k))
                    .collect::<Result<_, _>>()?;
                TypeKind::AtomApply(a.clone(), args)
            }
            "RecordType" if self.dots(node.start + 1) => TypeKind::Every(Every::Struct),
            "RecordType" => {
                let mut fields = Vec::with_capacity(kids.len() / 2);
                let mut seen = HashMap::new();
                for &[n, t] in kids.as_chunks::<2>().0 {
                    let name = self.word(self.tree.nodes[n].start);
                    self.once(&mut seen, name, n, "field", "declared")?;
                    fields.push((name.to_string(), self.ty(t)?));
                }
                TypeKind::Record(fields)
            }
            "RankArrayType" => TypeKind::Array(Box::new(self.ty(kids[0])?)),
            "GroupType" => {
                let mut t = self.ty(kids[0])?;
                t.span = span;
                return Ok(t);
            }
            _ => unreachable!("make builds only these rules as types"),
        };
        Ok(Type { kind, span })
    }

    /// The operands of the left-recursive chain of node `n`, in written order: the list of the
    /// shorter chain below it, which it takes over, and one more.
    fn operands(&mut self, n: usize) -> Result<Vec<Type>, Error> {
        let kids = self.kids(n);
        let first = self.ty(kids[0])?;
        let mut ts = if self.tree.nodes[kids[0]].rule == self.tree.nodes[n].rule {
            let mut first = first;
            match &mut first.kind {
                TypeKind::Union(ts) | TypeKind::And(ts) => mem::take(ts),
                _ => unreachable!("a chain builds to its list"),
            }
        } else {
            vec![first]
        };
        ts.push(self.ty(kids[1])?);
        Ok(ts)
    }

    /// Whether token `i` is the `..` of a kind-wide type, `(..)`, `{..}` or `#a(..)`.
    fn dots(&self, i: usize) -> bool {
        self.tokens.get(i).is_some_and(|t| t.tok == Tok::Op(".."))
    }

    fn types(&mut self, kids: &[usize]) -> Result<Vec<Type>, Error> {
        kids.iter().map(|&k| self.ty(k)).collect()
    }

    /// The arrow from `params`, written at node `p`, to the type of node `r`.
    fn arrow(&mut self, params: Vec<TypeParam>, p: usize, r: usize) -> Result<TypeKind, Error> {
        let partial = self.word(self.tree.nodes[p].end) == "->?";
        Ok(TypeKind::Arrow {
            params,
            partial,
            result: Box::new(self.ty(r)?),
        })
    }

    fn arrow_params(&mut self, n: usize) -> Result<Vec<TypeParam>, Error> {
        let node = &self.tree.nodes[n];
        match node.kids[..] {
            [] => Ok(Vec::new()),
            [first, ..] if self.tree.name(first) == "TypeParam" => {
                node.kids.iter().map(|&k| self.type_param(k)).collect()
            }
            [name, ty] => Ok(vec![TypeParam {
                name: Some(self.word(self.tree.nodes[name].start).into()),
                positional: self.word(node.start + 1) == "positional",
                ty: self.ty(ty)?,
            }]),
            _ => unreachable!("ArrowParams has no other form"),
        }
    }

    fn type_param(&mut self, n: usize) -> Result<TypeParam, Error> {
        let node = &self.tree.nodes[n];
        Ok(match node.kids[..] {
            [name, ty] => TypeParam {
                name: Some(self.word(self.tree.nodes[name].start).into()),
                positional: self.word(node.start) == "positional",
                ty: self.ty(ty)?,
            },
            [ty] => TypeParam {
                name: None,
                positional: false,
                ty: self.ty(ty)?,
            },
            _ => unreachable!("TypeParam = 'positional'? Name ':' Type | Type"),
        })
    }

    /// The parameters of node `n`, a `Params`, of the declaration or lambda written at `decl`.
    /// The grammar takes them in any order; a positional one after a named one is the row
    /// "`positional` parameter after a named one".
    pub(super) fn params(&mut self, n: usize, decl: Span) -> Result<Vec<Param>, Error> {
        let mut out: Vec<Param> = Vec::with_capacity(self.kids(n).len());
        let mut first_named: Option<usize> = None;
        for &k in self.kids(n) {
            let p = self.param(k)?;
            match first_named {
                Some(i) if p.positional => {
                    let named = &out[i];
                    return Err(Error {
                        row: Some(Row::PositionalAfterNamed),
                        span: p.span,
                        message: format!(
                            "the positional parameter `{}` comes after the named parameter \
                             `{}`: a declaration lists its positional parameters first",
                            p.name, named.name
                        ),
                        notes: vec![
                            Note {
                                span: named.span,
                                text: format!("the first named parameter, `{}`", named.name),
                            },
                            Note {
                                span: decl,
                                text: "the declaration".into(),
                            },
                            Note {
                                span: p.span,
                                text: format!(
                                    "repair: declare `{}` before `{}`, the positional parameters \
                                     first",
                                    p.name, named.name
                                ),
                            },
                        ],
                    });
                }
                None if !p.positional => first_named = Some(out.len()),
                _ => {}
            }
            out.push(p);
        }
        Ok(out)
    }

    fn param(&mut self, n: usize) -> Result<Param, Error> {
        let node = &self.tree.nodes[n];
        if self.tree.name(n) == "TupleParam" {
            let (targets, ty) = match node.kids.split_last() {
                Some((&t, targets)) if self.tree.name(t) == "Type" => (targets, Some(t)),
                _ => (&node.kids[..], None),
            };
            let targets: Vec<Target> = targets.iter().map(|&t| self.target(t)).collect();
            let text: Vec<&str> = targets
                .iter()
                .map(|t| match t {
                    Target::Name(n, _) => n.as_str(),
                    Target::Wild => "_",
                })
                .collect();
            return Ok(Param {
                name: format!("({})", text.join(", ")),
                tuple: Some(targets),
                positional: true,
                ty: ty.map(|t| self.ty(t)).transpose()?,
                default: None,
                span: self.span(n),
                name_at: self.span(n),
            });
        }
        let mut p = Param {
            name: self.word(self.tree.nodes[node.kids[0]].start).into(),
            tuple: None,
            positional: self.tree.name(n) == "PositionalParam",
            ty: None,
            default: None,
            span: self.span(n),
            name_at: self.span(node.kids[0]),
        };
        for &k in &node.kids[1..] {
            if self.tree.name(k) == "Type" {
                p.ty = Some(self.ty(k)?);
            } else {
                p.default = Some(self.node(k)?);
            }
        }
        Ok(p)
    }

    /// The pattern node `n` built to.
    pub(super) fn pattern(&mut self, n: usize) -> Result<Pattern, Error> {
        match self.take(n) {
            Some(Ok(Built::Pattern(p))) => Ok(p),
            Some(Err(e)) => Err(e),
            Some(Ok(Built::Expr(_) | Built::Type(_) | Built::Stmt(_))) | None => Err(self.later(n)),
        }
    }

    /// The pattern of node `n`, of a rule `AtomPattern`, `CtorPat`, `NamePat`, `WildPat`,
    /// `TuplePat`, `IsPat` or `SignedLit`.
    pub(super) fn make_pattern(&mut self, n: usize) -> Result<Pattern, Error> {
        let node = &self.tree.nodes[n];
        let span = self.span(n);
        match self.tree.name(n) {
            "NamePat" => return Ok(Pattern::Name(self.word(node.start).into(), span)),
            "WildPat" => return Ok(Pattern::Wild(span)),
            "TuplePat" => {
                let items = node.kids.iter().map(|&k| self.pattern(k));
                return Ok(Pattern::Tuple(items.collect::<Result<_, _>>()?, span));
            }
            "IsPat" => {
                let (&ty, name) = node
                    .kids
                    .split_last()
                    .expect("IsPat = Name? 'is' TypeUnion");
                return Ok(Pattern::Is {
                    name: name
                        .first()
                        .map(|&k| self.word(self.tree.nodes[k].start).into()),
                    ty: Box::new(self.ty(ty)?),
                    span,
                });
            }
            "SignedLit" if self.word(node.start) == "-" => {
                let i = node.start + 1;
                let value = self.literal_at(i, self.tokens[i].span)?;
                return Ok(Pattern::Lit(Box::new(Expr {
                    kind: ExprKind::Unary("-", Box::new(value)),
                    span,
                })));
            }
            "SignedLit" => return Ok(Pattern::Lit(Box::new(self.literal_at(node.start, span)?))),
            "RangePat" => {
                let op = self.tree.nodes[node.kids[0]].end;
                let from = Box::new(self.pattern(node.kids[0])?);
                let bound = node.kids.get(1).copied();
                let to = self.range_end(op, bound, |b, k| b.pattern(k).map(Box::new))?;
                return Ok(Pattern::Range { from, to, span });
            }
            "CtorPat" => {
                let (&name, fields) = node.kids.split_first().expect("CtorPat = Name '(' …");
                let out = fields.iter().map(|&k| self.field_pattern(k));
                let out = out.collect::<Result<_, _>>()?;
                return Ok(Pattern::Struct {
                    name: self.word(self.tree.nodes[name].start).into(),
                    fields: out,
                    span,
                });
            }
            _ => {}
        }
        let Tok::Atom(name) = &self.tokens[node.start].tok else {
            unreachable!("AtomPattern = ATOM …")
        };
        let (mut fields, mut items) = (Vec::new(), Vec::new());
        for &k in &node.kids {
            if self.tree.name(k) == "FieldPat" {
                fields.push(self.field_pattern(k)?);
            } else {
                items.push(self.pattern(k)?);
            }
        }
        Ok(Pattern::Atom {
            name: name.clone(),
            fields,
            items,
            span: self.span(n),
        })
    }

    /// The field and its pattern of node `n`, a `FieldPat`: `f: p`, or `f:` with none.
    fn field_pattern(&mut self, n: usize) -> Result<(String, Option<Pattern>), Error> {
        let kids = self.kids(n);
        let field = self.word(self.tree.nodes[kids[0]].start).to_string();
        let p = kids.get(1).map(|&p| self.pattern(p)).transpose()?;
        Ok((field, p))
    }
}
