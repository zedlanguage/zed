//! Reading a printed type back (OSP-diag): the text the checker prints for a type, parsed as
//! `Type` and denoted, so a test can hold each printed type to type syntax (DESIGN.md
//! "Diagnostics"). Besides the forms of layer L1, the checker prints an atom with its payload
//! type, `#ioError(op: String, path: String, why: String)`, a form of layer L2 the checker builds
//! from L1 on (L29-print), three leaves of layer L10, `_`, `!_` and a literal type, and after a
//! signature whose type variables are bounded the clause `for T in int | f64 | rat` (DESIGN.md
//! sec:type_resolution); this reads those too.

use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

use zed_kernel::num::{TooLarge, bytes_of};
use zed_kernel::{Rat, Value};

use super::ty::{Binds, Ty};
use super::{carrier_mask, denoted_with};
use zedc_syntax::ast::{self, Type, TypeKind};
use zedc_syntax::lex::{self, Part, Tok};
use zedc_syntax::parse::{self, TOP};

/// The type `text` states. Text that is no type is an error, as is a form `denoted` has no
/// meaning for at layer L1 other than an atom with its payload type, and a leaf of layer L10
/// other than the three above.
pub fn parse_type(text: &str) -> Result<Ty, String> {
    let tokens = lex::lex(text).map_err(|e| format!("`{text}`: {e}"))?;
    let (body, binds) = leaves(text, text, &tokens)?;
    let tokens = lex::lex(&body).map_err(|e| format!("`{text}`: {e}"))?;
    let tree = parse::parse(&body, &tokens, "Type", TOP)
        .map_err(|e| format!("`{text}` is not a type: {e}"))?;
    let t = ast::ty(&body, &tokens, &tree).map_err(|e| format!("`{text}`: {e}"))?;
    // A later layer's form, found with an explicit stack, and the variables bounded.
    let mut bounded = Vec::new();
    let mut stack = vec![&t];
    while let Some(t) = stack.pop() {
        match &t.kind {
            TypeKind::Apply(..) | TypeKind::Record(_) => {
                return Err(format!("`{text}` holds a form of layer L2"));
            }
            TypeKind::Array(_) => return Err(format!("`{text}` holds a form of layer L3")),
            TypeKind::Name(_) | TypeKind::Atom(_) | TypeKind::Every(_) | TypeKind::AtomAny(_) => {}
            TypeKind::Tuple(ts) | TypeKind::Union(ts) => stack.extend(ts),
            TypeKind::And(ts) => {
                let ts = Type::and_operands(ts);
                Type::overload(&ts).map_err(|why| format!("`{text}`: {why}"))?;
                stack.extend(ts);
            }
            TypeKind::AtomApply(_, ps) => stack.extend(ps.iter().map(|p| &p.ty)),
            TypeKind::Diff(a, b) => stack.extend([&**a, &**b]),
            TypeKind::Arrow { params, result, .. } => {
                stack.extend(params.iter().map(|p| &p.ty));
                stack.push(result);
            }
            TypeKind::Bounded {
                lower,
                upper,
                result,
            } => stack.extend([&**lower, &**upper, &**result]),
            TypeKind::For { ty, bounds } => {
                for b in bounds {
                    if let Err(c) = carrier_mask(&b.carriers) {
                        let c = &body[c.span.start..c.span.end];
                        return Err(format!(
                            "`{text}`: `{c}` in the bound of `{}` is no carrier",
                            b.name
                        ));
                    }
                    bounded.push(b.name.as_str());
                }
                stack.push(ty);
            }
        }
    }
    let ty = denoted_with(&t, &binds);
    let on = bounds_in(&ty);
    if let Some(v) = bounded.into_iter().find(|v| !on.contains(*v)) {
        return Err(format!(
            "`{text}`: the bound of `{v}` is on no signature that names it"
        ));
    }
    // The names the resolver finds, as in a written type: a variable no clause bounds is not
    // defined.
    let leaves = binds.keys().cloned().collect();
    if let Err(es) = zedc_resolve::resolve::printed_type(&t, leaves) {
        let why: Vec<String> = es.into_iter().map(|e| e.message).collect();
        return Err(format!("`{text}`: {}", why.join("; ")));
    }
    Ok(ty)
}

/// The variables the signatures of `t` bound, at any depth. A type read from text is a tree,
/// each signature built once, so the walk meets each node once.
fn bounds_in(t: &Ty) -> HashSet<Arc<str>> {
    let mut out = HashSet::new();
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        stack.extend(t.tuples.iter().flatten());
        for s in &t.fns {
            out.extend(s.bounds.keys().cloned());
            for a in &s.arrows {
                stack.extend(&a.params);
                stack.push(&a.result);
            }
        }
    }
    out
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
                (Ty::lit(&int(*radix, digits, true, text)?), 2)
            }
            (Tok::Int { radix, digits }, _) => (Ty::lit(&int(*radix, digits, false, text)?), 1),
            (Tok::Float(s), _) => (
                Ty::lit(&Value::float(
                    s.parse()
                        .map_err(|_| format!("`{text}`: the float `{s}`"))?,
                )),
                1,
            ),
            (Tok::Rat(s), _) => (
                Ty::lit(&Value::rat(
                    Rat::decimal(s)
                        .map_err(|e| refused(text, &e))?
                        .ok_or_else(|| format!("`{text}`: the rational `{s}`"))?,
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

/// The integer of `digits` in `radix`, negated when `negative`, read in memory the system
/// gives first; the type text `text` names it in an error.
fn int(radix: u32, digits: &str, negative: bool, text: &str) -> Result<Value, String> {
    let n = Value::int_text(digits, radix)
        .map_err(|e| refused(text, &e))?
        .ok_or_else(|| format!("the digits `{digits}` in base {radix}"))?;
    Ok(match negative {
        true => Value::integer(n.as_integer().expect("an integer literal is an int").neg()),
        false => n,
    })
}

/// The message for a number in the type text `text` whose digits the system refused the memory
/// to read.
fn refused(text: &str, e: &TooLarge) -> String {
    format!(
        "`{text}`: the system refused the {} bytes of memory asked to read a number in it",
        bytes_of(&e.bits)
    )
}
