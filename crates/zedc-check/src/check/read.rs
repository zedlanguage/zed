//! Reading a printed type back (OSP-diag): the text the checker prints for a type, parsed as
//! `Type` and denoted, so a test can hold each printed type to type syntax (DESIGN.md
//! "Diagnostics"). Besides the forms of layer L1, the checker prints an atom with its payload
//! type, `#ioError(op: String, path: String, why: String)`, a form of layer L2 the checker builds
//! from L1 on (L29-print), the leaves of layer L10 `_` and a literal type, and after a signature
//! whose type variables are bounded the clause `for T in int | f64 | rat` (DESIGN.md
//! sec:type_resolution); this reads those too. The empty type prints as `Never`, a prelude type
//! name of L1; its L10 form `!_` is read as well.

use std::collections::HashSet;
use std::sync::Arc;

use zed_kernel::num::{TooLarge, bytes_of};
use zed_kernel::{Rat, Value};

use super::ty::{Binds, NodeId, Sig, Ty};
use super::{carrier_mask, denoted_with};
use zedc_syntax::ast::{self, Type, TypeKind};
use zedc_syntax::lex::{self, Part, Tok};
use zedc_syntax::parse::{self, TOP};

/// The type `text` states. Text that is no type is an error, as is a form `denoted` has no
/// meaning for at layer L1 other than an atom with its payload type, and a leaf of layer L10
/// other than the three above. A printed type opens with a definition `type Tk = …;` for each
/// part it uses more than once (`Type::surfaces_by_name`): each definition is read in turn, its
/// body may name the ones before it, and its name stands for its type where the rest names it.
/// Time linear in the text: each part is read once, and a name's type is shared where it is
/// named (`Ty` copies its outer level only).
pub fn parse_type(text: &str) -> Result<Ty, String> {
    let tokens = lex::lex(text).map_err(|e| format!("`{text}`: {e}"))?;
    let tok = |i: usize| tokens.get(i).map(|t| &t.tok);
    let mut named = Binds::new();
    let mut i = 0;
    while let (Some(Tok::Keyword("type")), Some(Tok::Name(name)), Some(Tok::Op("="))) =
        (tok(i), tok(i + 1), tok(i + 2))
    {
        let end = (i + 3..tokens.len())
            .find(|&j| tokens[j].tok == Tok::Op(";"))
            .ok_or_else(|| format!("`{text}`: the definition of `{name}` has no `;`"))?;
        let body = &text[tokens[i + 3].span.start..tokens[end].span.start];
        let t = read_part(text, body, &mut named)?;
        named.insert(name.as_str().into(), t);
        i = end + 1;
    }
    let rest = &text[tokens.get(i).map_or(text.len(), |t| t.span.start)..];
    read_part(text, rest, &mut named)
}

/// The type `head`, a part of the printed type `text`, which may name the types of `named`:
/// the definitions before it, and the leaves of layer L10 read so far, to which it adds its own.
fn read_part(text: &str, head: &str, named: &mut Binds) -> Result<Ty, String> {
    let tokens = lex::lex(head).map_err(|e| format!("`{text}`: {e}"))?;
    // The names the resolver finds: the definitions `head` names, and its own leaves.
    let mut found: HashSet<Arc<str>> = (tokens.iter())
        .filter_map(|t| match &t.tok {
            Tok::Name(n) => named.get_key_value(n.as_str()).map(|(k, _)| k.clone()),
            _ => None,
        })
        .collect();
    let body = leaves(text, head, &tokens, named, &mut found)?;
    let binds = &*named;
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
                return Err(format!(
                    "`{text}` holds a record type or a type applied to arguments, which the \
                     checker never prints"
                ));
            }
            TypeKind::Array(_) => {
                return Err(format!(
                    "`{text}` holds an array type, which the checker never prints"
                ));
            }
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
    let ty = denoted_with(&t, binds);
    // Complexity tradeoff: naive version, `bounds_in` on every part, which walks the parts
    // of the definitions a part names again: O(n²) for a printed type of n definitions each
    // naming the one before. Used: the walk only for a part with a `for` clause, which no
    // answer changes (with no bound there is nothing to find), O(n) when few parts bound a
    // variable. Tradeoff: n definitions each with its own `for` clause and naming the one
    // before still cost O(n²); a walk that skips the definitions' own parts would make that
    // O(n), but it would reject a part whose bound is found now only on a signature of a
    // definition it names, an answer change (COMPLEXITY.md F153). Test
    // `l01_26_type_resolution::bounds::reading_a_chain_of_shared_bounded_parts_scales`.
    if !bounded.is_empty() {
        let on = bounds_in(&ty);
        if let Some(v) = bounded.into_iter().find(|v| !on.contains(*v)) {
            return Err(format!(
                "`{text}`: the bound of `{v}` is on no signature that names it"
            ));
        }
    }
    // The names the resolver finds, as in a written type: a variable no clause bounds is not
    // defined.
    if let Err(es) = zedc_resolve::resolve::printed_type(&t, found) {
        let why: Vec<String> = es.into_iter().map(|e| e.message).collect();
        return Err(format!("`{text}`: {}", why.join("; ")));
    }
    Ok(ty)
}

/// The variables the signatures of `t` bound, at any depth. A type read from text shares the
/// rows, payloads and signatures of a definition at each name for it, so the walk keeps the
/// rows, payloads and signatures it met and meets each once: time linear in the text.
fn bounds_in(t: &Ty) -> HashSet<Arc<str>> {
    let mut out = HashSet::new();
    // Complexity tradeoff: naive version, a walk of `t` as a tree, O(2^d) for parts shared d
    // levels deep. Used: the rows and payload shapes met, by their numbers (`Row::node`,
    // `Shape::node`), and the signatures met, by address, each read once, O(n) for the n
    // distinct parts, a hash lookup each. The rows were keyed by `row.as_ptr()`, the address
    // of the components' buffer, which every row with no components shares (an empty `Vec`
    // has no buffer); a row's number is its own (PTR-keys-rest). A signature has no number:
    // its address is a key only while `t`, which every key is borrowed from, is borrowed,
    // and none of the three sets is iterated. Tests in `l01_26_type_resolution::bounds`:
    // `bounds_on_two_rows_are_both_found`, `bounds_on_two_payloads_are_both_found` and
    // `reading_a_chain_of_shared_bounded_parts_scales`;
    // COMPLEXITY.md F153.
    let mut rows: HashSet<NodeId> = HashSet::new();
    let mut sigs: HashSet<*const Sig> = HashSet::new();
    let mut shapes: HashSet<NodeId> = HashSet::new();
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        for row in &t.tuples {
            if rows.insert(row.node()) {
                stack.extend(row);
            }
        }
        for s in t.payloads.values().flatten().flatten() {
            if shapes.insert(s.node()) {
                stack.extend(&s.items);
                stack.extend(s.fields.values());
            }
        }
        for s in t.fns.iter().filter(|s| sigs.insert(Arc::as_ptr(s))) {
            out.extend(s.bounds.keys().cloned());
            for a in &s.arrows {
                stack.extend(&a.params);
                stack.push(&a.result);
            }
        }
    }
    out
}

/// `head` with each leaf of layer L10 replaced by a type variable, put in `binds` with what it
/// stands for (`_` the unknown, `!_` the empty type, a literal its value) and in `found`.
fn leaves(
    text: &str,
    head: &str,
    tokens: &[lex::Token],
    binds: &mut Binds,
    found: &mut HashSet<Arc<str>>,
) -> Result<String, String> {
    let mut out = String::with_capacity(head.len());
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
            (Tok::Float { digits: s, .. }, _) => (
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
                _ => {
                    return Err(format!(
                        "`{text}` holds a text literal with an expression inside it, which is \
                         no type"
                    ));
                }
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
        found.insert(name.clone());
        binds.insert(name, ty);
        i += used;
    }
    out.push_str(&head[from..]);
    Ok(out)
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
