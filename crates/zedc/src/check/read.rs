//! Reading a printed type back (OSP-diag): the text the checker prints for a type, parsed as
//! `Type` and denoted, so a test can hold each printed type to type syntax (DESIGN.md
//! "Diagnostics"). Besides the forms of layer L1, the checker prints three leaves of layer L10,
//! `_`, `!_` and a literal type, and after a signature whose type variables are bounded the
//! clause `for T in int | f64 | rat` (DESIGN.md sec:checking); this reads those too.

use std::collections::BTreeMap;
use std::sync::Arc;

use num_bigint::BigInt;
use zed_kernel::{Rat, Value};

use super::denoted_with;
use super::ty::{Binds, Carrier, Sig, Ty, Vars};
use crate::ast::{self, TypeKind};
use crate::lex::{self, Part, Tok};
use crate::parse::{self, TOP};

/// The type `text` states. Text that is no type is an error, as is a form `denoted` has no
/// meaning for at layer L1, and a leaf of layer L10 other than the three above.
pub fn parse_type(text: &str) -> Result<Ty, String> {
    let (head, bounds) = clauses(text)?;
    let tokens = lex::lex(&head).map_err(|e| format!("`{text}`: {e}"))?;
    let (body, binds) = leaves(text, &head, &tokens)?;
    let tokens = lex::lex(&body).map_err(|e| format!("`{text}`: {e}"))?;
    let tree = parse::parse(&body, &tokens, "Type", TOP)
        .map_err(|e| format!("`{text}` is not a type: {e}"))?;
    let t = ast::ty(&body, &tokens, &tree).map_err(|e| format!("`{text}`: {e}"))?;
    // A later layer's form, found with an explicit stack.
    let mut stack = vec![&t];
    while let Some(t) = stack.pop() {
        match &t.kind {
            TypeKind::Apply(..) | TypeKind::AtomApply(..) | TypeKind::Record(_) => {
                return Err(format!("`{text}` holds a form of layer L2"));
            }
            TypeKind::Seq(_) => return Err(format!("`{text}` holds a form of layer L3")),
            TypeKind::Name(_) | TypeKind::Atom(_) => {}
            TypeKind::Tuple(ts) | TypeKind::Union(ts) | TypeKind::And(ts) => stack.extend(ts),
            TypeKind::Diff(a, b) => stack.extend([&**a, &**b]),
            TypeKind::Arrow { params, result, .. } => {
                stack.extend(params.iter().map(|p| &p.ty));
                stack.push(result);
            }
        }
    }
    let mut ty = denoted_with(&t, &binds);
    for (v, m) in bounds {
        if !bound(&mut ty, &v, m) {
            return Err(format!(
                "`{text}`: the bound of `{v}` is on no signature that names it"
            ));
        }
    }
    Ok(ty)
}

/// Type variables, each with the mask of the carriers it is bounded by.
type Bounds = Vec<(Arc<str>, u8)>;

/// `text` without its `for` clauses, and the bounds they give, in written order. A clause
/// runs from ` for ` to the parenthesis that closes the group it is in, or to the end.
fn clauses(text: &str) -> Result<(String, Bounds), String> {
    let (mut out, mut bounds) = (String::with_capacity(text.len()), Vec::new());
    // The open groups, each with the start in `text` of its clause if it has one.
    let mut groups: Vec<Option<usize>> = vec![None];
    let mut quoted = false;
    let mut chars = text.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        let in_clause = groups.last().copied().flatten().is_some();
        match c {
            '"' => quoted = !quoted,
            '\\' if quoted => {
                if !in_clause {
                    out.push(c);
                }
                if let Some((_, d)) = chars.next()
                    && !in_clause
                {
                    out.push(d);
                }
                continue;
            }
            ' ' if !quoted && !in_clause && text[i..].starts_with(" for ") => {
                *groups.last_mut().expect("the outermost group") = Some(i + " for ".len());
                continue;
            }
            '(' if !quoted => groups.push(None),
            ')' if !quoted => {
                if let Some(Some(from)) = groups.pop() {
                    bounds.extend(clause(text, &text[from..i])?);
                }
            }
            _ => {}
        }
        if groups.last().copied().flatten().is_none() || c == ')' {
            out.push(c);
        }
    }
    if let Some(Some(from)) = groups.pop() {
        bounds.extend(clause(text, &text[from..])?);
    }
    Ok((out, bounds))
}

/// The bounds of the clause `body`, `T in int | rat, U in f64`.
fn clause(text: &str, body: &str) -> Result<Bounds, String> {
    body.split(", ")
        .map(|b| {
            let (v, cs) = b
                .split_once(" in ")
                .ok_or_else(|| format!("`{text}`: the bound `{b}` has no ` in `"))?;
            let mut mask = 0;
            for c in cs.split(" | ") {
                let carrier = Carrier::ALL.iter().find(|k| k.name() == c).ok_or_else(|| {
                    format!("`{text}`: `{c}` in the bound of `{v}` is no carrier")
                })?;
                mask |= carrier.bit();
            }
            Ok((v.into(), mask))
        })
        .collect()
}

/// `head` with each leaf of layer L10 replaced by a type variable, and what each variable
/// stands for: `_` the unknown, `!_` the empty type, a literal its value.
fn leaves(text: &str, head: &str, tokens: &[lex::Token]) -> Result<(String, Binds), String> {
    let (mut out, mut binds) = (String::with_capacity(head.len()), BTreeMap::new());
    let mut from = 0;
    let mut i = 0;
    while i < tokens.len() {
        let (start, tok) = (tokens[i].span.start, &tokens[i].tok);
        let next = tokens.get(i + 1).map(|t| &t.tok);
        let (ty, used) = match (tok, next) {
            (Tok::Wildcard, _) => (Ty::dynamic(), 1),
            (Tok::Op("!"), Some(Tok::Wildcard)) => (Ty::empty(), 2),
            (Tok::Op("!"), _) => return Err(format!("`{text}`: `!` stands before no `_`")),
            (Tok::Op("-"), Some(Tok::Int { radix, digits })) => {
                (Ty::lit(&int(*radix, digits, true)?), 2)
            }
            (Tok::Int { radix, digits }, _) => (Ty::lit(&int(*radix, digits, false)?), 1),
            (Tok::Float(s), _) => (
                Ty::lit(&Value::float(
                    s.parse()
                        .map_err(|_| format!("`{text}`: the float `{s}`"))?,
                )),
                1,
            ),
            (Tok::Rat(s), _) => (
                Ty::lit(&Value::rat(
                    Rat::decimal(s).ok_or_else(|| format!("`{text}`: the rational `{s}`"))?,
                )),
                1,
            ),
            (Tok::Str(parts), _) => match &parts[..] {
                [] => (Ty::lit(&Value::str("")), 1),
                [Part::Text(s)] => (Ty::lit(&Value::str(s)), 1),
                _ => return Err(format!("`{text}`: a literal type with a hole")),
            },
            (Tok::Keyword(k @ ("true" | "false")), _) => (Ty::lit(&Value::Bool(*k == "true")), 1),
            _ => {
                i += 1;
                continue;
            }
        };
        let name: Arc<str> = format!("Leaf{}", binds.len()).into();
        out.push_str(&head[from..start]);
        out.push_str(&name);
        from = tokens[i + used - 1].span.end;
        binds.insert(name, ty);
        i += used;
    }
    out.push_str(&head[from..]);
    Ok((out, binds))
}

/// The integer of `digits` in `radix`, negated when `negative`.
fn int(radix: u32, digits: &str, negative: bool) -> Result<Value, String> {
    let n = BigInt::parse_bytes(digits.as_bytes(), radix)
        .ok_or_else(|| format!("the digits `{digits}` in base {radix}"))?;
    Ok(Value::int(if negative { -n } else { n }))
}

/// Bounds `v` by the carriers of `mask` on the first signature of `t`, outermost first, whose
/// arrows name `v`; whether one does.
fn bound(t: &mut Ty, v: &Arc<str>, mask: u8) -> bool {
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        for s in t.fns.iter_mut() {
            if names(s, v) {
                Arc::make_mut(s).bounds.insert(v.clone(), mask);
                return true;
            }
        }
        // The children, the first last, so the first is taken next.
        let mut kids: Vec<&mut Ty> = Vec::new();
        for cs in t.tuples.iter_mut() {
            kids.extend(cs.iter_mut());
        }
        for s in t.fns.iter_mut() {
            for a in Arc::make_mut(s).arrows.iter_mut() {
                kids.extend(a.params.iter_mut());
                kids.push(&mut a.result);
            }
        }
        stack.extend(kids.into_iter().rev());
    }
    false
}

/// Whether an arrow of `s` names the type variable `v`.
fn names(s: &Sig, v: &Arc<str>) -> bool {
    let mut vars = Vars::default();
    for a in &s.arrows {
        a.params.iter().for_each(|p| p.vars_in(&mut vars));
        a.result.vars_in(&mut vars);
    }
    vars.order.contains(v)
}
