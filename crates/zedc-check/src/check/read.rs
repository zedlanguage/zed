//! Reading a printed type back (OSP-diag): the text the checker prints for a type, parsed as
//! `Type` and denoted, so a test can hold each printed type to type syntax (DESIGN.md
//! "Diagnostics"). Besides the forms of layer L1, the checker prints an atom with its payload
//! type, `#ioError(op: String, path: String, why: String)`, a form of layer L2 the checker builds
//! from L1 on (L29-print), the leaves of layer L10 `_` and a literal type, and after a signature
//! whose type variables are bounded the clause `for T in int | f64 | rat` (DESIGN.md
//! sec:type_resolution); this reads those too, and a list `[V]`, a form of step L3.1 the
//! checker prints for a family of the ranks `0 ..< n` (MSG-list-type-printed-by-arrows). The empty
//! type prints as `Never`, a prelude type name of L1; its L10 form `!_` is read as well.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use zed_collections::by_address::ByAddress;

use zed_kernel::num::{TooLarge, literal_f64};
use zed_kernel::{Rat, Value};

use super::ty::{Binds, NodeId, Row, Shape, Sig, Ty, WrittenRange};
use super::{Inexact, Loss, Ranged, carrier_mask, denoted_inexact};
use zedc_lattice::interval::Num;
use zedc_syntax::ast::{self, Expr, ExprKind, RangeEnd, Type, TypeKind};
use zedc_syntax::lex::{self, Part, Tok};
use zedc_syntax::parse::{self, TOP};

/// The type `text` states. Text that is no type is an error, as is a form `denoted` has no
/// meaning for at layer L1 other than an atom with its payload type, and a leaf of layer L10
/// other than the three above. A printed type opens with a definition `type Tk = …;` for each
/// part it uses more than once (`Type::surfaces_by_name`): each definition is read in turn, its
/// body may name the ones before it, and its name stands for its type where the rest names it.
/// Time linear in the text: each part is read once, and a name's type is shared where it is
/// named (`Ty` copies its outer level only). The text is lexed once; a part's tokens are taken
/// from it (`part_tokens`), and lexed again only once its leaves are replaced.
///
/// A capitalized name is a variable by the rule a written type has, applied to the text with
/// each definition written out at each name for it ([`Times`]): so a part the printer writes
/// once as a definition, whose variables stand once in its body and twice in the type, reads
/// back as the type written in full (row PRINT-shared-part-exponential).
pub fn parse_type(text: &str) -> Result<Ty, String> {
    let tokens = lex::lex(text).map_err(|e| format!("`{text}`: {e}"))?;
    // Each definition by its name and the tokens of its body, and last the text's, each with
    // the bytes of the text it spans.
    let mut parts: Vec<(Option<Arc<str>>, std::ops::Range<usize>, usize, usize)> = Vec::new();
    let mut i = 0;
    loop {
        let tok = |j: usize| tokens.get(i + j).map(|t| &t.tok);
        let (Some(Tok::Keyword("type")), Some(Tok::Name(name)), Some(Tok::Op("="))) =
            (tok(0), tok(1), tok(2))
        else {
            break;
        };
        let end = (i + 3..tokens.len())
            .find(|&j| tokens[j].tok == Tok::Op(";"))
            .ok_or_else(|| format!("`{text}`: the definition of `{name}` has no `;`"))?;
        let (from, to) = (tokens[i + 3].span.start, tokens[end].span.start);
        parts.push((Some(name.as_str().into()), i + 3..end, from, to));
        i = end + 1;
    }
    let from = tokens.get(i).map_or(text.len(), |t| t.span.start);
    parts.push((None, i..tokens.len(), from, text.len()));
    let times = Times::of(&tokens, &parts);
    let mut named = Binds::new();
    let mut seen = Seen::default();
    // The variables each definition holds, its own and those of the definitions it names.
    let mut held: HashMap<Arc<str>, Arc<[Arc<str>]>> = HashMap::new();
    let mut tokens = tokens.into_iter();
    let mut at = 0;
    for (name, range, from, to) in parts {
        tokens.by_ref().take(range.start - at).for_each(drop);
        at = range.end;
        let part: Vec<lex::Token> = tokens.by_ref().take(range.len()).collect();
        let inner: Vec<Arc<str>> = (part.iter())
            .filter_map(|t| match &t.tok {
                Tok::Name(n) => held.get(n.as_str()).cloned(),
                _ => None,
            })
            .flat_map(|vs| vs.to_vec())
            .collect();
        let read = Reader {
            times: &times,
            held: &held,
        };
        let (t, free) = read_part(
            text,
            &text[from..to],
            from,
            part,
            &mut named,
            &mut seen,
            read,
        )?;
        let Some(name) = name else {
            return Ok(t);
        };
        let mut vs: Vec<Arc<str>> = free.into_iter().chain(inner).collect();
        vs.sort_unstable();
        vs.dedup();
        held.insert(name.clone(), vs.into());
        named.insert(name, t);
    }
    unreachable!("the text's own part is the last of `parts`")
}

/// How many times the text of a printed type writes each capitalized name, with each
/// definition written out at each name for it: the count the rule for a variable reads
/// (sec:type_resolution, rule 4, a name written twice or more), so that a definition used
/// twice counts each name in its body twice (row PRINT-shared-part-exponential). A name a
/// `for` clause binds, one followed by `in` (`TypeBounds = 'for' (Name 'in' TypeUnion) % ','`,
/// syntax.peg), and a name of a definition, are not counted, as the reading of each part
/// skips them.
// Complexity tradeoff: naive, the text written out with each definition at each name for it and
// the names counted there, O(2^d) for a part used twice at each of d levels, the fault the
// definitions remove. Used: each definition's uses counted in each part's tokens, its weight
// (the times the written-out text holds it) found from the weights of the parts that name it,
// in the order last to first, since a definition names only those before it; then each name's
// count is the sum over the parts of its count there times the part's weight. O(n) in the
// tokens with a hash lookup each, and saturating sums, so a count past 2^64 stays above 2.
// Test: `l01_29_diagnostics::shared_parts`, the three cases of the rule.
struct Times {
    times: HashMap<Arc<str>, u64>,
}

impl Times {
    fn of<'t>(
        tokens: &'t [lex::Token],
        parts: &[(Option<Arc<str>>, std::ops::Range<usize>, usize, usize)],
    ) -> Times {
        let capital = |n: &str| n.starts_with(|c: char| c.is_ascii_uppercase());
        let clause: HashSet<&str> = (tokens.windows(2))
            .filter_map(|w| match (&w[0].tok, &w[1].tok) {
                (Tok::Name(n), Tok::Keyword("in")) if capital(n) => Some(n.as_str()),
                _ => None,
            })
            .collect();
        // The definitions named before each part, by name, the last of a name kept, as the
        // reading of each part sees them.
        let mut defined: HashMap<&str, usize> = HashMap::new();
        let mut uses: Vec<Vec<usize>> = Vec::with_capacity(parts.len());
        let mut names: Vec<HashMap<&'t str, u64>> = Vec::with_capacity(parts.len());
        for (p, (name, range, ..)) in parts.iter().enumerate() {
            let (mut u, mut m) = (Vec::new(), HashMap::new());
            for t in &tokens[range.clone()] {
                let Tok::Name(n) = &t.tok else { continue };
                match defined.get(n.as_str()) {
                    Some(&q) => u.push(q),
                    None if capital(n) && !clause.contains(n.as_str()) => {
                        *m.entry(n.as_str()).or_insert(0u64) += 1;
                    }
                    None => {}
                }
            }
            uses.push(u);
            names.push(m);
            if let Some(name) = name {
                defined.insert(&**name, p);
            }
        }
        let mut weight = vec![0u64; parts.len()];
        if let Some(last) = weight.last_mut() {
            *last = 1;
        }
        for p in (0..parts.len()).rev() {
            for &q in &uses[p] {
                weight[q] = weight[q].saturating_add(weight[p]);
            }
        }
        let mut times: HashMap<&'t str, u64> = HashMap::new();
        for (m, w) in names.into_iter().zip(weight) {
            for (n, c) in m {
                let t = times.entry(n).or_insert(0);
                *t = t.saturating_add(c.saturating_mul(w));
            }
        }
        let times = times.into_iter().map(|(n, t)| (n.into(), t)).collect();
        Times { times }
    }

    /// Whether `name` is written twice or more in the text written out.
    fn twice(&self, name: &str) -> bool {
        self.times.get(name).is_some_and(|&t| t >= 2)
    }
}

/// What the reading of each part of a printed type knows of the whole text.
#[derive(Clone, Copy)]
struct Reader<'a> {
    /// How many times the text written out writes each name.
    times: &'a Times,
    /// The variables each definition read so far holds, which the outermost signature around a
    /// name for it binds, as it binds them written out there.
    held: &'a HashMap<Arc<str>, Arc<[Arc<str>]>>,
}

/// The tokens of `head`, the text of a printed type from byte `from` to a token's start or the
/// end, given `tokens`, the tokens the whole text has there: the same tokens with their spans
/// moved to start at `head`, as lexing `head` gives them. A part with a string is lexed again:
/// a string holds tokens of its own, and a `"""` string reads its indentation from the text.
// Claim (row PROOF-part-tokens-slice-lex): where `lex(text)` succeeds, lexing `text[s..c]`,
// with `s` the start of a token and `c` the start of a later token or the end, gives the tokens
// of `lex(text)` that lie in `s..c`, with spans moved by `s`, provided none is a string.
// Proof, from `lex_from` and its readers in crates/zedc-syntax/src/lex (zedc-syntax at this
// commit; a change there must keep each step):
// 1. The start. Outside a string, `lex_from` keeps no state from one token to the next but
//    `pos`: `levels` and `reading` are empty there, `docs` only collects, and `elisions` is
//    false for `lex`. Each reader (`comment::comment`, `number::number`, `name::word`,
//    `name::wildcard`, `infix::infix`, `punct::operator`) is called with `(text, pos)` and reads
//    bytes from `pos` on; the one look back, `text[..end].ends_with('\'')` in `name::word`,
//    looks at the word's own last byte. So the lexer at byte 0 of the slice is in the state the
//    whole lex is in at byte `s`, and step 2 applies to each token in turn.
// 2. The end. Take a reader run at `p < c` in both texts; they hold the same bytes below `c`,
//    and where the whole text has the byte that starts a token at `c`, the slice has its end.
//    The whole lex's token ends at `e <= c`, since a token starts at `c`. Each test a reader
//    makes at or past `c` is one of:
//    a. "the next character is in a set of characters that continue the token": digits, `_`
//       before a digit, `.` before a digit, `e`/`E` and its sign before a digit, `r`, `f32` or
//       `f64` after a fraction, a name character (`number`, `name::word`, `wildcard`), `'` after
//       a word, or the rest of an operator (`punct::operator`). Each holds for a byte and fails
//       at the end of the text. In the whole text it fails at `c` too, or the token would run
//       past `c`; and a test past `c` is made only after one at `c` holds. So the slice sees the
//       same answers.
//    b. a search for a closing mark: the `\n` that ends a `//` comment, the `*/` that closes a
//       block comment, the `~` that closes `~f~`. In the whole text the mark is found before
//       `c`, or the comment or call would hold the byte at `c`; so it is found at the same
//       place in the slice.
//    c. `punct::operator` takes the first entry of `OPERATORS` that `text[p..]` starts with. An
//       entry that ends past `c` is false in the slice; it is false in the whole text too, or
//       the operator would run past `c` (an entry wholly before `c` reads the same bytes in
//       both). So the first true entry is the same.
//    The error paths of the readers (`run_on`, `leading_zero`, the infix messages) are not
//    reached in the whole text, which lexes; by a. to c. they are not reached in the slice.
// 3. A string is read by `Reading`, which reads holes and a `"""` string's indentation from
//    the text around it; such a part is lexed again, which needs no proof.
// Test: `tests::a_cut_at_any_token_start_lexes_as_the_whole_text` cuts at every pair of token
// starts in texts that end each token kind at a cut. Evidence before the proof: an assertion
// that the moved tokens equal those of a new lex held on all 914 test pieces of the groups
// that read printed types and on the 5.6 MB of printed types of the many-bounded-variables
// bench.
fn part_tokens(
    text: &str,
    head: &str,
    from: usize,
    mut tokens: Vec<lex::Token>,
) -> Result<Vec<lex::Token>, String> {
    if tokens.iter().any(|t| matches!(t.tok, Tok::Str(_))) {
        return lex::lex(head).map_err(|e| format!("`{text}`: {e}"));
    }
    for t in &mut tokens {
        t.span.start -= from;
        t.span.end -= from;
    }
    Ok(tokens)
}

/// The type `head`, a part of the printed type `text` from its byte `from`, whose tokens there
/// are `tokens`, which may name the types of `named`: the definitions before it, and the leaves
/// of layer L10 read so far, to which it adds its own. `seen` holds what the parts before it
/// walked of their types, and gets what this one walks. Gives the type and the variables
/// written in the part.
fn read_part(
    text: &str,
    head: &str,
    from: usize,
    tokens: Vec<lex::Token>,
    named: &mut Binds,
    seen: &mut Seen,
    read: Reader,
) -> Result<(Ty, HashSet<Arc<str>>), String> {
    let tokens = part_tokens(text, head, from, tokens)?;
    // The names the resolver finds: the definitions `head` names, and its own leaves.
    let mut found: HashSet<Arc<str>> = (tokens.iter())
        .filter_map(|t| match &t.tok {
            Tok::Name(n) => named.get_key_value(n.as_str()).map(|(k, _)| k.clone()),
            _ => None,
        })
        .collect();
    // A part with no leaf is parsed from the tokens it has; one with a leaf is lexed again,
    // since each leaf there is now a name.
    let mut written = Written::default();
    let (body, tokens) = match leaves(text, head, &tokens, named, &mut found, &mut written)? {
        Some(body) => {
            let tokens = lex::lex(&body)
                .map_err(|e| format!("`{text}`: {}", written.back(&e.to_string())))?;
            (Cow::Owned(body), tokens)
        }
        None => (Cow::Borrowed(head), tokens),
    };
    let binds = &*named;
    let tree = parse::parse(&body, &tokens, "Type", TOP)
        .map_err(|e| format!("`{text}` is not a type: {}", written.back(&e.to_string())))?;
    let t = ast::ty(&body, &tokens, &tree)
        .map_err(|e| format!("`{text}`: {}", written.back(&e.to_string())))?;
    // A later layer's form, found with an explicit stack, and the variables bounded.
    let mut bounded = Vec::new();
    let mut keyed = HashMap::new();
    let mut hulls = HashMap::new();
    let mut stack = vec![&t];
    while let Some(t) = stack.pop() {
        match &t.kind {
            TypeKind::Apply(..) | TypeKind::Record(_) => {
                return Err(format!(
                    "`{text}` holds a record type or a type applied to arguments, which the \
                     checker never prints"
                ));
            }
            // A list, which the checker prints `[V]` (MSG-list-type-printed-by-arrows).
            TypeKind::Array(of) => stack.push(of),
            // A signature prints a parameter's range, `(x: int[1..]) -> int`, but a printed
            // type read back holds none: the kernel has no ranged type to read it as.
            // So does a fixed-width alias, the name of a range (`u8`, step L1.12). The key of
            // a family or of a function of one positional parameter, `int[2..=4] -> V`, and
            // the hull of an exact arrow's int result, `int -> int[1..=10]`, are read where
            // their arrow is, below, and not walked.
            TypeKind::Range { .. } => {
                return Err(format!(
                    "`{text}` holds a range type, which the checker never prints as a type"
                ));
            }
            TypeKind::Name(n)
                if zedc_syntax::fixed_width::is_alias(n) && !binds.contains_key(n.as_str()) =>
            {
                return Err(format!(
                    "`{text}` holds the range type `{n}`, which the checker never prints as a \
                     type"
                ));
            }
            TypeKind::Name(_) | TypeKind::Atom(_) | TypeKind::Every(_) | TypeKind::AtomAny(_) => {}
            TypeKind::Tuple(ts) | TypeKind::Union(ts) => stack.extend(ts),
            TypeKind::And(ts) => {
                let ts = Type::and_operands(ts);
                Type::overload(&ts).map_err(|why| format!("`{text}`: {}", written.back(&why)))?;
                stack.extend(ts);
            }
            TypeKind::AtomApply(_, ps) => stack.extend(ps.iter().map(|p| &p.ty)),
            TypeKind::Diff(a, b) => stack.extend([&**a, &**b]),
            // A family with its keys exactly, `int[2..=4] -> V` or `u8 -> V`, as the printer
            // writes one (`Sig::keys`, row RANGE-keys-in-printed-type), and a function of one
            // positional parameter declared that range, which prints alike (row
            // PRINT-positional-range-ambiguous, option A): its key, a range, is read here and
            // not walked; the arrow is denoted as the union of the two (`Denote::keyed`).
            TypeKind::Arrow {
                params,
                partial: false,
                result,
            } if let [p] = &params[..]
                && p.name.is_none()
                && let Some(k) = range_read(&p.ty, &written, binds, false) =>
            {
                keyed.insert(t.span, k);
                hull_or_walk(t.span, result, (&written, binds), &mut hulls, &mut stack);
            }
            TypeKind::Arrow {
                params,
                partial,
                result,
            } => {
                stack.extend(params.iter().map(|p| &p.ty));
                match partial {
                    true => stack.push(result),
                    false => {
                        hull_or_walk(t.span, result, (&written, binds), &mut hulls, &mut stack)
                    }
                }
            }
            TypeKind::Bounded {
                lower,
                upper,
                result,
            } => stack.extend([&**lower, &**upper, &**result]),
            TypeKind::For { ty, bounds } => {
                for b in bounds {
                    if let Err(c) = carrier_mask(&b.carriers) {
                        let c = written.back(&body[c.span.start..c.span.end]);
                        return Err(format!(
                            "`{text}`: `{c}` in the bound of `{}` is not a carrier",
                            b.name
                        ));
                    }
                    bounded.push(b.name.as_str());
                }
                stack.push(ty);
            }
        }
    }
    // A capitalized name written twice or more that neither a definition nor a clause binds is a
    // variable of the outermost signature around it (sec:type_resolution, rule 4), as the
    // printer writes a variable that stands in two places or more (UNDERSCORE-print); a name
    // written once stays undefined, as in a written signature. Written means in the text with
    // each definition written out at each name for it ([`Times`]), so that a definition used
    // twice writes the names of its body twice. One pass over the tokens with a hash lookup,
    // O(n).
    let clauses: HashSet<&str> = bounded.iter().copied().collect();
    let free: HashSet<Arc<str>> = (tokens.iter())
        .filter_map(|t| match &t.tok {
            Tok::Name(n)
                if n.starts_with(|c: char| c.is_ascii_uppercase())
                    && !binds.contains_key(n.as_str())
                    && !clauses.contains(n.as_str())
                    && read.times.twice(n) =>
            {
                Some(n.as_str().into())
            }
            _ => None,
        })
        .collect();
    found.extend(free.iter().cloned());
    // A difference from the unknown `_` is refused rather than read as more than it says:
    // before, `_ \ #a` read as `_` (TEST-read-type-flaws), so a printed type that lost its
    // difference read back as another type with no word of it. `Ty` has no form for part of
    // the unknown. Only this cause is refused: the exactness flag of `Ty::diff_exact` is
    // conservative for payloads and tuples (`#a(x: int) \ #a(y: int)` is flagged though it
    // reads back as `#a(x: int)`, l01_22
    // `kinds::the_difference_of_payloads_of_one_atom_takes_the_payloads`),
    // and a difference that takes part of a variable is held by `left_of`.
    let (ty, inexact) = denoted_inexact(&t, binds, &free, read.held, Ranged { keyed, hulls });
    if let Some(Inexact { span, printed, .. }) = inexact
        .into_iter()
        .find(|i| matches!(i.cause, Loss::Unknown))
    {
        let d = match body.get(span.start..span.end) {
            Some(s) => written.back(s),
            None => printed,
        };
        return Err(format!(
            "`{text}`: `{d}` takes away part of the unknown `_`, which no type the checker \
             holds can state; it would read back as all of `_`"
        ));
    }
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
    // text are kernel sets (`KType::surfaces_by_name`), whose printer writes no clause, or
    // tuples written once (zedc-types `Shared::local`), which hold no function and no
    // variable any clause bounds, so no clause either. (3)
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
        let why: Vec<String> = es.into_iter().map(|e| written.back(&e.message)).collect();
        return Err(format!("`{text}`: {}", why.join("; ")));
    }
    Ok((ty, free))
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
    sigs: HashSet<ByAddress<Sig>>,
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
                Piece::Sig(s) => {
                    let new = self.sigs.insert(ByAddress::new(s));
                    if new {
                        own.extend(s.bounds.keys().cloned());
                    }
                    new
                }
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

/// The text each leaf of a part was written as, by the name [`leaves`] gave it, so that an
/// error about the part names the leaf as the printed type writes it, `int \ 0`, never as the
/// name it was given there, `int \ Leaf0` (TEST-read-type-flaws).
#[derive(Default)]
struct Written<'a> {
    by_name: HashMap<Arc<str>, &'a str>,
    /// The int each leaf written as an int literal stands for, by its name: the ends of a
    /// range `int[a..=b]`, which `key_range` reads.
    ints: HashMap<Arc<str>, Value>,
}

impl Written<'_> {
    /// `s` with each leaf name in it, a whole name, put back as the leaf was written. One
    /// pass over `s` with a hash lookup per name found: O(|s|) besides the text put back.
    fn back(&self, s: &str) -> String {
        if self.by_name.is_empty() {
            return s.to_string();
        }
        let name_byte = |b: u8| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'';
        let bytes = s.as_bytes();
        let mut out = String::with_capacity(s.len());
        let (mut from, mut i) = (0, 0);
        while let Some(at) = s[i..].find(LEAF).map(|k| i + k) {
            let digits = bytes[at + LEAF.len()..]
                .iter()
                .take_while(|b| b.is_ascii_digit())
                .count();
            let end = at + LEAF.len() + digits;
            let whole = digits > 0
                && (at == 0 || !name_byte(bytes[at - 1]))
                && bytes.get(end).is_none_or(|&b| !name_byte(b));
            match self.by_name.get(&s[at..end]) {
                Some(w) if whole => {
                    out.push_str(&s[from..at]);
                    out.push_str(w);
                    from = end;
                }
                _ => {}
            }
            i = end.max(at + 1);
        }
        out.push_str(&s[from..]);
        out
    }
}

/// The range the printer wrote as `t` ([`WrittenRange::new`]): `int[a..=b]`, its ends int
/// literals, which [`leaves`] made names of and `written` keeps the ints of, or a fixed-width
/// alias, `u8`, that no definition names, which `WrittenRange::new` prints for exactly its
/// range; and, where `open`, also `int[a..]`, `int[_..=b]` and `int[_..]`, an end `_` or left
/// out being open. A key (`Sig::keys`, row RANGE-keys-in-printed-type) is read with `open`
/// false, as the printer writes a key's two ends; the hull of a result (`Sig::hull`, row
/// READ-result-hull) with `open` true. `None` for any other type, which the walk then reads
/// as before (a range elsewhere is refused). The printer writes no `..<`, as
/// `WrittenRange::new` writes `..=`. O(1) and O(digits) for the alias's ends.
fn range_read(t: &Type, written: &Written, binds: &Binds, open: bool) -> Option<WrittenRange> {
    // An end: `Some(None)` where it is open, `None` where it is not one the printer writes.
    let end = |e: Option<&Expr>| -> Option<Option<Value>> {
        let Some(e) = e else {
            return open.then_some(None);
        };
        let ExprKind::Name(n) = &e.kind else {
            return None;
        };
        match written.ints.get(n.as_str()) {
            Some(v) => Some(Some(v.clone())),
            None if open && written.by_name.get(n.as_str()) == Some(&"_") => Some(None),
            None => None,
        }
    };
    match &t.kind {
        TypeKind::Name(n) if !binds.contains_key(n.as_str()) => {
            let (lo, hi) = zedc_syntax::fixed_width::range(n)?;
            let (lo, hi) = (Value::from(&Num::from(lo)), Value::from(&Num::from(hi)));
            Some(WrittenRange::new(Some(lo), Some(hi)))
        }
        TypeKind::Range { of, low, high } if matches!(&of.kind, TypeKind::Name(n) if n == "int") => {
            let high = match high {
                RangeEnd::Through(h) => end(h.as_deref())?,
                RangeEnd::Open if open => None,
                _ => return None,
            };
            let low = end(low.as_deref())?;
            Some(WrittenRange::new(low, high))
        }
        _ => None,
    }
}

/// Records the hull of the exact arrow at `span` whose result `result` is a range the printer
/// writes ([`range_read`], open ends allowed, row READ-result-hull), or pushes `result` to be
/// walked where it is not one.
fn hull_or_walk<'t>(
    span: zedc_syntax::lex::Span,
    result: &'t Type,
    (written, binds): (&Written, &Binds),
    hulls: &mut HashMap<zedc_syntax::lex::Span, WrittenRange>,
    stack: &mut Vec<&'t Type>,
) {
    match range_read(result, written, binds, true) {
        Some(h) => {
            hulls.insert(span, h);
        }
        None => stack.push(result),
    }
}

/// The start of the name [`leaves`] gives each leaf, followed by its number in `binds`.
const LEAF: &str = "Leaf";

/// `head` with each leaf of layer L10 replaced by a type variable, put in `binds` with what it
/// stands for (`_` the unknown, `!_` the empty type, a literal its value) and in `found`, and
/// in `written` with its text in `head`; `None` when `head` has no leaf.
fn leaves<'h>(
    text: &str,
    head: &'h str,
    tokens: &[lex::Token],
    binds: &mut Binds,
    found: &mut HashSet<Arc<str>>,
    written: &mut Written<'h>,
) -> Result<Option<String>, String> {
    let mut out = String::new();
    let mut any = false;
    let mut from = 0;
    let mut i = 0;
    while i < tokens.len() {
        let (start, tok) = (tokens[i].span.start, &tokens[i].tok);
        let next = tokens.get(i + 1).map(|t| &t.tok);
        let mut int_leaf = None;
        let mut an_int = |v: Value, used: usize| {
            let ty = Ty::lit(&v);
            int_leaf = Some(v);
            (ty, used)
        };
        let (ty, used) = match (tok, next) {
            (Tok::Op("-") | Tok::Int { .. }, _)
                if let Some((v, used)) = power_product(text, &tokens[i..])? =>
            {
                an_int(v, used)
            }
            (Tok::Wildcard, _) => (Ty::dynamic(), 1),
            (Tok::Op("!"), Some(Tok::Wildcard)) => (Ty::empty(), 2),
            (Tok::Op("!"), _) => return Err(format!("`{text}`: `!` stands before no `_`")),
            (Tok::Op("-"), Some(Tok::Int { radix, digits })) => {
                an_int(int(*radix, digits, true, text)?, 2)
            }
            (Tok::Int { radix, digits }, _) => an_int(int(*radix, digits, false, text)?, 1),
            (Tok::Float { digits: s, .. }, _) => (
                Ty::lit(&Value::float(
                    literal_f64(s)
                        .and_then(Result::ok)
                        .ok_or_else(|| format!("`{text}`: the float `{s}`"))?,
                )),
                1,
            ),
            (Tok::Rat(s), _) => (
                Ty::lit(&Value::rat(
                    Rat::decimal(s)
                        .map_err(|e| refused(text, &e, "rat"))?
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
                         not a type"
                    ));
                }
            },
            (Tok::Keyword(k @ ("true" | "false")), _) => (Ty::lit(&Value::Bool(*k == "true")), 1),
            _ => {
                i += 1;
                continue;
            }
        };
        let name: Arc<str> = format!("{LEAF}{}", binds.len()).into();
        if !any {
            any = true;
            out.reserve(head.len());
        }
        out.push_str(&head[from..start]);
        out.push_str(&name);
        from = tokens[i + used - 1].span.end;
        written.by_name.insert(name.clone(), &head[start..from]);
        if let Some(v) = int_leaf {
            written.ints.insert(name.clone(), v);
        }
        found.insert(name.clone());
        binds.insert(name, ty);
        i += used;
    }
    if !any {
        return Ok(None);
    }
    out.push_str(&head[from..]);
    Ok(Some(out))
}

/// The integer of a literal type's product of powers at the start of `tokens`, `3^200000` or
/// `-5*3^200000` (`LitType` in DESIGN.md sec:grammar), with the number of tokens it takes;
/// `None` when they start no `^` or `*` between integers, which the other leaves read. The
/// power is kept as exponents (`Value::power_product`), so reading costs the text.
fn power_product(text: &str, tokens: &[lex::Token]) -> Result<Option<(Value, usize)>, String> {
    let tok = |j: usize| tokens.get(j).map(|t| &t.tok);
    let uint = |j: usize| match tok(j) {
        Some(Tok::Int { radix, digits }) => int(*radix, digits, false, text).map(Some),
        _ => Ok(None),
    };
    let negative = tok(0) == Some(&Tok::Op("-"));
    let mut j = usize::from(negative);
    let mut factors = Vec::new();
    loop {
        let Some(b) = uint(j)? else {
            return Ok(None);
        };
        let k = match tok(j + 1) {
            Some(Tok::Op("^")) => match uint(j + 2)? {
                Some(k) => {
                    j += 2;
                    k
                }
                None => return Ok(None),
            },
            _ => Value::int(1.into()),
        };
        factors.push((b, k));
        j += 1;
        if tok(j) != Some(&Tok::Op("*")) {
            break;
        }
        j += 1;
    }
    if j == usize::from(negative) + 1 {
        return Ok(None);
    }
    Value::power_product(negative, &factors)
        .map(|v| Some((v, j)))
        .map_err(|e| refused(text, &e, "int"))
}

/// The integer of `digits` in `radix`, negated when `negative`, read in memory the system
/// gives first; the type text `text` names it in an error.
fn int(radix: u32, digits: &str, negative: bool, text: &str) -> Result<Value, String> {
    let n = Value::int_text(digits, radix)
        .map_err(|e| refused(text, &e, "int"))?
        .ok_or_else(|| format!("the digits `{digits}` in base {radix}"))?;
    Ok(match negative {
        true => Value::integer(n.as_integer().expect("an integer literal is an int").neg()),
        false => n,
    })
}

/// The message for a number in the type text `text` whose value does not fit in the memory the
/// system gives, with its repair written as code (DESIGN.md sec:diagnostics): the literal type
/// replaced by its carrier `carrier`, `int` or `rat`, a type that holds the number and needs no
/// memory for its digits.
fn refused(text: &str, e: &TooLarge, carrier: &str) -> String {
    format!(
        "Number too large for memory: `{text}` needs {}. Write `{carrier}` in place of the \
         literal type.",
        e.number()
    )
}

#[cfg(test)]
mod tests {
    use super::{Written, lex, part_tokens};

    /// Row PROOF-part-tokens-slice-lex: the tokens `part_tokens` moves from the whole text are
    /// those a new lex of the slice gives, for a cut at every pair of token starts. The texts
    /// end each token kind right before a token: numbers with a fraction, an exponent, a sign,
    /// separators, a base, `r` and `f32`; names with `'`; keywords; atoms and annotations; the
    /// wildcard; infix calls; each operator that has a shorter operator as its start; a `//`
    /// comment and a nested block comment; a string.
    #[test]
    fn a_cut_at_any_token_start_lexes_as_the_whole_text() {
        let texts = [
            "1.5e+3;1.5;1e3;1E-2 ;0x1F;0o7;0b1;1_000;3r;1.5f32;2.0f64;0..1;1..<2;0..=9;1.x",
            "a' b'c type T = int;_ _x x_ #a #_ @ann x ~f~ y ~a.b~ z",
            "x->?y->z...w..<v..=u..t?.s*.r^q++p<-o<=n>=m><l==k!=j&&i||h::g:f",
            "x // a comment\n;y /* a /* nested */ block */ z;(int, #a) | !_ \\ 0",
            "f(\"text\", 1) -> [int] for T in int",
        ];
        for text in texts {
            let whole = lex::lex(text).unwrap_or_else(|e| panic!("{text:?}: {e}"));
            let ends: Vec<usize> = whole
                .iter()
                .map(|t| t.span.start)
                .chain([text.len()])
                .collect();
            for (i, first) in whole.iter().enumerate() {
                for (j, &to) in ends.iter().enumerate().skip(i + 1) {
                    let from = first.span.start;
                    let head = &text[from..to];
                    let part = lex::lex(text).expect("lexed above").into_iter();
                    let moved = part_tokens(text, head, from, part.take(j).skip(i).collect());
                    let fresh = lex::lex(head).map_err(|e| e.to_string());
                    assert_eq!(moved, fresh, "{text:?} cut to {head:?}");
                }
            }
        }
    }

    /// Row TEST-read-type-flaws: a leaf name in an error is put back as the leaf was written,
    /// only as a whole name, so `Leaf1` is never read inside `Leaf10` or `Leaf1x`.
    #[test]
    fn a_leaf_name_is_put_back_only_whole() {
        let mut w = Written::default();
        w.by_name.insert("Leaf1".into(), "0");
        w.by_name.insert("Leaf10".into(), "!_");
        assert_eq!(
            w.back("`Leaf1` and `Leaf10`, not Leaf1x, xLeaf1 or Leaf"),
            "`0` and `!_`, not Leaf1x, xLeaf1 or Leaf"
        );
        assert_eq!(Written::default().back("Leaf0"), "Leaf0");
    }
}
