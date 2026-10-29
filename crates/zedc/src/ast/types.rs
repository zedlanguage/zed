//! Type expressions, parameter lists and atom patterns (step L1.10): what an `is` test, a
//! lambda's parameters and an `else` pattern are written with.

use std::fmt;

use super::{Builder, Error, Expr};
use crate::lex::{Span, Tok};

/// A type expression and its span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Type {
    /// What it is.
    pub kind: TypeKind,
    /// Its text.
    pub span: Span,
}

/// The kinds of type expression.
#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeParam {
    /// Its name, which documents it, if written.
    pub name: Option<String>,
    /// Whether it is written `positional`.
    pub positional: bool,
    /// Its type.
    pub ty: Type,
}

/// A parameter of a lambda or a declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    /// The type of node `n`, of a rule from `Type` down to `TypePrimary`.
    pub(super) fn ty(&self, n: usize) -> Result<Type, Error> {
        let kids = self.kids(n);
        let node = &self.tree.nodes[n];
        let span = self.span(n);
        let kind = match (self.tree.name(n), node.alt) {
            ("Type", _)
            | ("TypeNot", 1)
            | ("TypePostfix", _)
            | ("TypeUnion", 1)
            | ("TypeAnd", _)
                if kids.len() == 1 =>
            {
                return self.ty(kids[0]);
            }
            ("Type" | "TypePostfix", _) => return Err(self.later(kids[1])),
            ("Arrow", 0) => {
                let params = self.arrow_params(kids[0])?;
                self.arrow(params, kids[0], kids[1])?
            }
            ("Arrow", 1) => match kids[..] {
                [t] => return self.ty(t),
                [t, r] => {
                    let ty = self.ty(t)?;
                    let param = TypeParam {
                        name: None,
                        positional: false,
                        ty,
                    };
                    self.arrow(vec![param], t, r)?
                }
                _ => unreachable!("Arrow = TypeUnion (('->' | '->?') Arrow)?"),
            },
            ("TypeUnion", 0) => {
                let mut t = self.ty(kids[0])?;
                for &k in &kids[1..] {
                    let r = self.ty(k)?;
                    let span = Span {
                        start: t.span.start,
                        end: r.span.end,
                    };
                    t = Type {
                        kind: TypeKind::Diff(Box::new(t), Box::new(r)),
                        span,
                    };
                }
                return Ok(t);
            }
            ("TypeUnion", 1) => TypeKind::Union(self.types(kids)?),
            ("TypeAnd", _) => TypeKind::And(self.types(kids)?),
            ("TypePrimary", 1) => TypeKind::Name(
                (node.start..node.end)
                    .step_by(2)
                    .map(|i| self.word(i))
                    .collect::<Vec<_>>()
                    .join("."),
            ),
            ("TypePrimary", 3) => {
                let Tok::Atom(a) = &self.tokens[node.start].tok else {
                    unreachable!("an ATOM token")
                };
                TypeKind::Atom(a.clone())
            }
            ("TypePrimary", 6) => TypeKind::Tuple(self.types(kids)?),
            ("TypePrimary", 8) => {
                return Ok(Type {
                    span,
                    ..self.ty(kids[0])?
                });
            }
            _ => return Err(self.later(n)),
        };
        Ok(Type { kind, span })
    }

    fn types(&self, kids: &[usize]) -> Result<Vec<Type>, Error> {
        kids.iter().map(|&k| self.ty(k)).collect()
    }

    /// The arrow from `params`, written at node `p`, to the type of node `r`.
    fn arrow(&self, params: Vec<TypeParam>, p: usize, r: usize) -> Result<TypeKind, Error> {
        let partial = self.word(self.tree.nodes[p].end) == "->?";
        Ok(TypeKind::Arrow {
            params,
            partial,
            result: Box::new(self.ty(r)?),
        })
    }

    fn arrow_params(&self, n: usize) -> Result<Vec<TypeParam>, Error> {
        let node = &self.tree.nodes[n];
        match node.alt {
            0 => Ok(Vec::new()),
            1 => node.kids.iter().map(|&k| self.type_param(k)).collect(),
            _ => Ok(vec![TypeParam {
                name: Some(self.word(self.tree.nodes[node.kids[0]].start).into()),
                positional: self.word(node.start + 1) == "positional",
                ty: self.ty(node.kids[1])?,
            }]),
        }
    }

    fn type_param(&self, n: usize) -> Result<TypeParam, Error> {
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
    pub(super) fn params(&self, n: usize) -> Result<Vec<Param>, Error> {
        self.kids(n).iter().map(|&k| self.param(k)).collect()
    }

    fn param(&self, n: usize) -> Result<Param, Error> {
        let node = &self.tree.nodes[n];
        if self.tree.name(n) == "PosParam" && node.alt == 0 {
            return Err(self.later(n));
        }
        let mut p = Param {
            name: self.word(self.tree.nodes[node.kids[0]].start).into(),
            positional: self.tree.name(n) == "PosParam",
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

    /// The pattern of node `n`, a `Pattern` or an `AtomPattern`.
    pub(super) fn pattern(&self, n: usize) -> Result<Pattern, Error> {
        let node = &self.tree.nodes[n];
        match self.tree.name(n) {
            "Pattern" if node.alt == 1 => self.pattern(node.kids[0]),
            "AtomPattern" => {
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
            _ => Err(self.later(n)),
        }
    }
}

/// `int`, `#none`, `(tuple A B)`, `(| A B)`, `(& A B)`, `(\ A B)`, `(-> (A (x: B)) R)`.
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |f: &mut fmt::Formatter<'_>, head: &str, ts: &[Type]| {
            write!(f, "({head}")?;
            for t in ts {
                write!(f, " {t}")?;
            }
            f.write_str(")")
        };
        match &self.kind {
            TypeKind::Name(n) => f.write_str(n),
            TypeKind::Atom(a) => write!(f, "#{a}"),
            TypeKind::Tuple(ts) => list(f, "tuple", ts),
            TypeKind::Union(ts) => list(f, "|", ts),
            TypeKind::And(ts) => list(f, "&", ts),
            TypeKind::Diff(a, b) => write!(f, "(\\ {a} {b})"),
            TypeKind::Arrow {
                params,
                partial,
                result,
            } => {
                write!(f, "({} (", if *partial { "->?" } else { "->" })?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    match (&p.name, p.positional) {
                        (Some(n), true) => write!(f, "(positional {n}: {})", p.ty)?,
                        (Some(n), false) => write!(f, "({n}: {})", p.ty)?,
                        (None, _) => write!(f, "{}", p.ty)?,
                    }
                }
                write!(f, ") {result})")
            }
        }
    }
}

/// `x`, or `(positional x: int = 0)` with what is written.
impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.positional && self.ty.is_none() && self.default.is_none() {
            return f.write_str(&self.name);
        }
        f.write_str("(")?;
        if self.positional {
            f.write_str("positional ")?;
        }
        f.write_str(&self.name)?;
        if let Some(t) = &self.ty {
            write!(f, ": {t}")?;
        }
        if let Some(d) = &self.default {
            write!(f, " = {d}")?;
        }
        f.write_str(")")
    }
}

/// `#name`, `#name(f: p, g:)`, `#name(p, q)`.
impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Pattern::Atom {
            name,
            fields,
            items,
            ..
        } = self;
        write!(f, "#{name}")?;
        if fields.is_empty() && items.is_empty() {
            return Ok(());
        }
        let mut parts: Vec<String> = fields
            .iter()
            .map(|(n, p)| match p {
                Some(p) => format!("{n}: {p}"),
                None => format!("{n}:"),
            })
            .collect();
        parts.extend(items.iter().map(|p| p.to_string()));
        write!(f, "({})", parts.join(", "))
    }
}
