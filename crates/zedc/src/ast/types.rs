//! Type expressions, parameter lists and atom patterns (step L1.10): what an `is` test, a
//! lambda's parameters and an `else` pattern are written with.

use std::mem;

use super::{Builder, Built, Error, Expr};
use crate::lex::{Span, Tok};

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
    /// Its name.
    pub name: String,
    /// Whether it is written `positional`.
    pub positional: bool,
    /// Its type, if written.
    pub ty: Option<Type>,
    /// Its default, if written.
    pub default: Option<Expr>,
    /// Its text.
    pub span: Span,
}

/// A pattern. At L1 the only patterns are atom patterns, which `else` takes.
pub enum Pattern {
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
}

impl Builder<'_> {
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
            "Type" => return Err(self.later(kids[1])),
            "TypePostfix" if self.tree.nodes[kids[0]].rule == node.rule => {
                return self.ty(kids[0]);
            }
            "TypePostfix" => return Err(self.later(kids[1])),
            "Arrow" if self.tree.name(kids[0]) == "ArrowParams" => {
                let params = self.arrow_params(kids[0])?;
                self.arrow(params, kids[0], kids[1])?
            }
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
            "AtomType" => {
                let Tok::Atom(a) = &self.tokens[node.start].tok else {
                    unreachable!("an ATOM token")
                };
                TypeKind::Atom(a.clone())
            }
            "TupleType" => TypeKind::Tuple(self.types(kids)?),
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

    /// The parameters of node `n`, a `Params`.
    pub(super) fn params(&mut self, n: usize) -> Result<Vec<Param>, Error> {
        self.kids(n).iter().map(|&k| self.param(k)).collect()
    }

    fn param(&mut self, n: usize) -> Result<Param, Error> {
        let node = &self.tree.nodes[n];
        if self.tree.name(n) == "TupleParam" {
            return Err(self.later(n));
        }
        let mut p = Param {
            name: self.word(self.tree.nodes[node.kids[0]].start).into(),
            positional: self.tree.name(n) == "PositionalParam",
            ty: None,
            default: None,
            span: self.span(n),
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

    /// The pattern of node `n`, an `AtomPattern`.
    pub(super) fn make_pattern(&mut self, n: usize) -> Result<Pattern, Error> {
        let node = &self.tree.nodes[n];
        let Tok::Atom(name) = &self.tokens[node.start].tok else {
            unreachable!("AtomPattern = ATOM …")
        };
        let (mut fields, mut items) = (Vec::new(), Vec::new());
        for &k in &node.kids {
            if self.tree.name(k) == "FieldPat" {
                let kids = self.kids(k);
                let field = self.word(self.tree.nodes[kids[0]].start).to_string();
                let p = kids.get(1).map(|&p| self.pattern(p)).transpose()?;
                fields.push((field, p));
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
}
