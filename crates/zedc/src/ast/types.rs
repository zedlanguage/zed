//! Type expressions, parameter lists and atom patterns (step L1.10): what an `is` test, a
//! lambda's parameters and an `else` pattern are written with. Step L2.1 adds the applied
//! types `Tree(T)` and `#node(l: T)`, the record type `{x: int}`, the tuple-destructuring
//! parameter `(a, b)`, and the patterns that destructure a struct, `Point(x:, y: b)`, with the
//! name, `_` and tuple patterns they hold. Step L2.2 adds the patterns of a `match` arm: the
//! type pattern `n is T` and the literal pattern.

use std::collections::HashMap;
use std::mem;

use super::{
    Builder, Built, Error, Every, Expr, ExprKind, Note, Param, Pattern, Target, Type, TypeBound,
    TypeKind, TypeParam,
};
use crate::lex::{Span, Tok};
use crate::rejection::Row;

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
