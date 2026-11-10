//! Reading a printed type back (OSP-diag): the text the checker prints for a type, parsed as
//! `Type` and denoted, so a test can hold each printed type to type syntax (DESIGN.md
//! "Diagnostics"). Besides the forms of layer L1, the checker prints an atom with its payload
//! type, `#ioError(op: String, path: String, why: String)`, a form of layer L2 the checker builds
//! from L1 on (L29-print), the leaves of layer L10 `_` and a literal type, and after a signature
//! whose type variables are bounded the clause `for T in int | f64 | rat` (DESIGN.md
//! sec:type_resolution); this reads those too. The empty type prints as `Never`, a prelude type
//! name of L1; its L10 form `!_` is read as well.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::num::{TooLarge, bytes_of};
use zed_kernel::{Rat, Value};

use super::ty::{Binds, NodeId, Row, Shape, Sig, Ty};
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
    let mut seen = Seen::default();
    let mut i = 0;
    while let (Some(Tok::Keyword("type")), Some(Tok::Name(name)), Some(Tok::Op("="))) =
        (tok(i), tok(i + 1), tok(i + 2))
    {
        let end = (i + 3..tokens.len())
            .find(|&j| tokens[j].tok == Tok::Op(";"))
            .ok_or_else(|| format!("`{text}`: the definition of `{name}` has no `;`"))?;
        let body = &text[tokens[i + 3].span.start..tokens[end].span.start];
        let t = read_part(text, body, &mut named, &mut seen)?;
        named.insert(name.as_str().into(), t);
        i = end + 1;
    }
    let rest = &text[tokens.get(i).map_or(text.len(), |t| t.span.start)..];
    read_part(text, rest, &mut named, &mut seen)
}

/// The type `head`, a part of the printed type `text`, which may name the types of `named`:
/// the definitions before it, and the leaves of layer L10 read so far, to which it adds its own.
/// `seen` holds what the parts before it walked of their types, and gets what this one walks.
fn read_part(text: &str, head: &str, named: &mut Binds, seen: &mut Seen) -> Result<Ty, String> {
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
    // Each variable the part bounds must be on a signature its type reaches, at any depth,
    // the definitions it names included. Only a part with a `for` clause is walked: with no
    // bound there is nothing to find.
    // Complexity tradeoff: naive version (F153), a walk of all that the part's type reaches
    // for each part with a `for` clause, which walks the definitions it names again: O(n²)
    // for n definitions each with its own clause and naming the one before (25x at 8n,
    // 3.6x per 2x at n = 3,200). Used (F155): one walk for the whole printed type, which
    // meets each row, payload and signature once, in the first part that reaches it, and
    // finds there the variables bounded on the signatures it meets first (`Seen::fresh`);
    // a variable not among them, which a part has when its own signature for it was emptied
    // away (`((x: T) -> T, Never)`), or is equal to one met before, or was never written, is
    // looked for in all the part reaches by a search that keeps, for that variable, whether
    // each node reaches a signature that bounds it (`Seen::reaches`). O(n) in all when each
    // bound is on a signature its part makes, as in every type the checker prints, and when
    // the variables searched for share a few names. Tradeoff: each variable name searched
    // for adds at most one visit of each node, so k parts whose signatures are emptied away,
    // each for a variable of its own name and each naming the one before, cost O(n·k), with
    // memory to match (measured 28.7 and 593 ms at n = 200 and 1,600, k = n, 20.7x at 8n).
    // No input reaches that case (READ-bounds-reach-sets, F155): (1) zedc never calls
    // `parse_type`; only tests do, on text they write and on types the checker prints, and
    // a program's types are read by the front end, never here. (2) In a printed type no
    // part but the last holds a clause: `write_parts` writes each clause (`Print::Bounds`)
    // right after the arrows of the signature it bounds, and the definitions before the
    // text are kernel sets (`KType::surfaces_by_name`), whose printer writes no clause. (3)
    // Read back, the last part denotes each signature it writes as a new `Sig`, at an
    // address no part before met (`Seen` holds each signature it met), bounding each
    // variable of its clause the signature uses (one it does not use the resolver rejects:
    // the type before `for` does not hold it, so no printed type that reads back has one);
    // and the denotation keeps every signature of a type the checker made with the
    // same constructors (`Ty::of_row` and `Ty::atom_of` empty a part only where a
    // component is empty, which such a type has already done). So `fresh` gives every
    // bounded variable of a printed type, and `reaches` runs on none; the definitions'
    // signatures (kernel arrows) bound nothing. Only hand-written text with a clause on a
    // signature emptied away, or on one of a definition, reaches `reaches`. A printed type
    // whose part dropped a signature would not read back as itself, which the read-back
    // tests catch; such a part costs one search before its rejection. A linear method for
    // the hand-written case would need reachability from many nodes to many sets in a
    // shared graph. Every answer is the one of the naive walk. Tests in
    // `l01_26_type_resolution::bounds`: `reading_a_chain_of_bounded_definitions_scales`,
    // `a_bound_deep_in_a_chain_is_found_and_a_bound_on_no_signature_is_rejected`,
    // `a_printed_type_has_each_bounds_clause_on_a_signature_of_its_last_part` and
    // `reading_back_a_printed_type_of_many_distinct_bounded_variables_scales` (which fails if
    // the reading searches for a variable `fresh` gave).
    if !bounded.is_empty() {
        let own = seen.fresh(&ty);
        if let Some(v) = (bounded.into_iter()).find(|v| !own.contains(*v) && !seen.reaches(&ty, v))
        {
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

/// What the reading of one printed type has walked of its parts' types, for the check that
/// each variable a `for` clause bounds is on a signature the part's type reaches. A type read
/// from text shares the rows, payloads and signatures of a definition at each name for it, so
/// a part reaches the nodes of every definition it names, and of those they name.
#[derive(Default)]
struct Seen {
    /// The rows met, by number (`Row::node`).
    rows: HashSet<NodeId>,
    /// The payload shapes met, by number (`Shape::node`).
    shapes: HashSet<NodeId>,
    /// The signatures met, by address, each held here: a signature has no number, and held,
    /// no other signature takes its address while the reading lasts. Never iterated.
    sigs: HashMap<*const Sig, Arc<Sig>>,
    /// For each variable `reaches` was asked about, the nodes it found to reach a signature
    /// that bounds the variable, and those it found not to. Each is in `rows`, `shapes` or
    /// `sigs`, since `fresh` walked the type before `reaches` was asked about it.
    reach: HashMap<Arc<str>, HashMap<Node, bool>>,
}

/// A row, a payload shape or a signature: a node a type shares, which a part's type reaches.
#[derive(Clone, Copy)]
enum Piece<'a> {
    Row(&'a Row),
    Shape(&'a Shape),
    Sig(&'a Arc<Sig>),
}

/// The key of a [`Piece`] in [`Seen`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Row(NodeId),
    Shape(NodeId),
    Sig(*const Sig),
}

impl<'a> Piece<'a> {
    /// The pieces of the outer level of `t`.
    fn of(t: &'a Ty) -> impl Iterator<Item = Piece<'a>> {
        (t.tuples.iter().map(Piece::Row))
            .chain(t.payloads.values().flatten().flatten().map(Piece::Shape))
            .chain(t.fns.iter().map(Piece::Sig))
    }

    /// The pieces of the types it holds: a row's components, a payload's items and fields, a
    /// signature's parameters and results.
    fn inner(self) -> Vec<Piece<'a>> {
        match self {
            Piece::Row(r) => r.iter().flat_map(Piece::of).collect(),
            Piece::Shape(s) => (s.items.iter().chain(s.fields.values()))
                .flat_map(Piece::of)
                .collect(),
            Piece::Sig(s) => (s.arrows.iter())
                .flat_map(|a| a.params.iter().chain([&a.result]))
                .flat_map(Piece::of)
                .collect(),
        }
    }

    fn node(self) -> Node {
        match self {
            Piece::Row(r) => Node::Row(r.node()),
            Piece::Shape(s) => Node::Shape(s.node()),
            Piece::Sig(s) => Node::Sig(Arc::as_ptr(s)),
        }
    }
}

impl Seen {
    /// The variables bounded on the signatures `t` reaches that no part before met, each node
    /// `t` reaches now met: time linear in the nodes no part before met.
    fn fresh(&mut self, t: &Ty) -> HashSet<Arc<str>> {
        let mut own = HashSet::new();
        let mut stack: Vec<Piece> = Piece::of(t).collect();
        while let Some(p) = stack.pop() {
            let new = match p {
                Piece::Row(r) => self.rows.insert(r.node()),
                Piece::Shape(s) => self.shapes.insert(s.node()),
                Piece::Sig(s) => match self.sigs.entry(Arc::as_ptr(s)) {
                    Entry::Occupied(_) => false,
                    Entry::Vacant(e) => {
                        own.extend(s.bounds.keys().cloned());
                        e.insert(s.clone());
                        true
                    }
                },
            };
            if new {
                stack.extend(p.inner());
            }
        }
        own
    }

    /// Whether a signature `t` reaches, which [`Seen::fresh`] walked, bounds `v`. A search
    /// with an explicit stack that stops at the first such signature: a node it leaves with
    /// none found reaches none, and the nodes on the stack when it finds one reach it; both
    /// are kept for `v`, so each node is searched at most once for each variable.
    fn reaches(&mut self, t: &Ty, v: &str) -> bool {
        let known = self.reach.entry(v.into()).or_default();
        let mut stack: Vec<(Option<Node>, std::vec::IntoIter<Piece>)> =
            vec![(None, Piece::of(t).collect::<Vec<_>>().into_iter())];
        while let Some((at, next)) = stack.last_mut() {
            let at = *at;
            let Some(p) = next.next() else {
                if let Some(at) = at {
                    known.insert(at, false);
                }
                stack.pop();
                continue;
            };
            let n = p.node();
            let found = match known.get(&n) {
                Some(&k) => k,
                None if matches!(p, Piece::Sig(s) if s.bounds.contains_key(v)) => true,
                None => {
                    stack.push((Some(n), p.inner().into_iter()));
                    continue;
                }
            };
            if found {
                known.insert(n, true);
                known.extend(stack.iter().filter_map(|(at, _)| *at).map(|at| (at, true)));
                return true;
            }
        }
        false
    }
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
