//! The pretty-printer of kernel terms (step L1.15), in the notation of DESIGN.md sec:kernel:
//! `fam(D, i -> e)`, `reindex(F, kf, vf)`, `fold(F, op, ev)` and the rest, with Tier 0 written
//! as Zed writes it (`(x, y) -> e`, `f(a)`, `x = e; body`, `if c { a } else { b }`).
//!
//! [`Term`]'s `Display` writes a term on one line. [`pretty`] writes the same text, broken
//! into lines of at most a given width where it can: a term that does not fit puts each of
//! its parts on its own line, indented two spaces, so the only difference from the one-line
//! form is whitespace. Binary primitives are written infix and always parenthesized. Negation,
//! `!`, an index and an atom are written as a program writes them (`-x`, `!x`, `t[0]`, `f[k]`,
//! `#err(code: 3)`), their operands parenthesized wherever sec:grammar would read the text
//! otherwise, so the text reads back as the same term. A part of the types in its `is` tests
//! written more than once is declared once, on a line of its own before the term, as a type
//! printed alone is (module `types::defs`).
//!
//! A term is laid out as a sequence of tokens, not a tree, and each pass over it (laying out,
//! writing, measuring, breaking) is a loop with a stack of its own, so that a term of any depth
//! prints on a small call stack (step T2-types-rest).
//!
//! [`written`] writes a term as the program it came from wrote it, as far as the term shows:
//! each name through a function the caller gives, which maps a name elaboration made back to
//! the one the program wrote, and the `if` forms that elaboration gives `&&` and `||` as those
//! operators, for a message about the term (sec:diagnostics). It writes parentheses only
//! where the grammar's precedence needs them (P191), by the level table of module [`level`],
//! which the source formatter reads too.

mod dag;
pub mod level;

use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::term::walk::{Binds, Kid, kids};
use crate::term::{Evidence, FixKind, Grade, GuardPos, Pattern, Prim, Term, Witness};
use crate::text::ident::numbered;
use crate::types::defs;
use crate::value::Value;

/// How names are written: each as it is (`written` is `None`), or through the function a
/// message gives ([`written`]), with each binder in `fresh` written with its new spelling
/// ([`respelled`]).
#[derive(Clone, Copy)]
struct Names<'a> {
    written: Option<fn(&str) -> &str>,
    fresh: Option<&'a HashMap<&'a str, String>>,
}

/// Each name as it is.
const PLAIN: Names<'static> = Names {
    written: None,
    fresh: None,
};

impl<'a> Names<'a> {
    /// How the name `x` is written.
    fn spell(self, x: &'a str) -> &'a str {
        match self.fresh.and_then(|fresh| fresh.get(x)) {
            Some(s) => s,
            None => self.written.map_or(x, |f| f(x)),
        }
    }
}

/// The names that resolve where a term is written: the program's own names and the prelude's.
pub type Resolves<'r> = &'r dyn Fn(&str) -> bool;

/// `t` with each of its shared parts written once (module `dag`), and the parts written with a
/// label. Without `resolves` a part that reads a name bound in more than one place is labeled;
/// with it no part is.
fn form<'t>(
    t: &'t Term,
    resolves: Option<Resolves<'_>>,
    names: Option<fn(&str) -> &str>,
) -> (Cow<'t, Term>, HashSet<*const Term>) {
    match dag::shared_form(t, resolves, names) {
        Some(f) => (Cow::Owned(f.term), f.labels),
        None => (Cow::Borrowed(t), HashSet::new()),
    }
}

/// `t` broken into lines of at most `width` columns where its parts allow, for debugging: a
/// part that reads a name bound in more than one place is written `#1=<text>` at its first
/// place and `#1#` at the others, which is not a program. A message prints with [`pretty_in`].
pub fn pretty(t: &Term, width: usize) -> String {
    let local = defs::local();
    let (t, labels) = form(t, None, None);
    let mut out = String::new();
    Doc::of(Piece::Term(&t), PLAIN, &labels).render(width, &mut out);
    alone(local, out)
}

/// `t` broken into lines of at most `width` columns where its parts allow, written where the
/// names `resolves` accepts are in scope: the printer for a user. The text is a program that
/// reads back to a term with the same value (not always an equal term: a part that reads a name
/// bound in more than one place is a function of one value holding those names, module
/// `dag`), in O(n log n) text and time for a term of n distinct parts.
pub fn pretty_in(t: &Term, width: usize, resolves: Resolves<'_>) -> String {
    let local = defs::local();
    let (t, labels) = form(t, Some(resolves), None);
    debug_assert!(labels.is_empty(), "a scoped term has no label");
    let mut out = String::new();
    Doc::of(Piece::Term(&t), PLAIN, &labels).render(width, &mut out);
    alone(local, out)
}

/// `t` on one line as the program wrote it, for a message, written where the names `resolves`
/// accepts are in scope, as by [`pretty_in`]: each name a variable, a binder or a call's head
/// writes is `name` of it; `if c { b } else { false }` and `if c { true } else { b }`, the
/// terms elaboration gives `c && b` and `c || b`, are written `c && b` and `c || b`, and
/// `if c { false } else { b }` and `if c { a } else { true }` are written `!c && b` and
/// `!c || a`, which mean the same; and an operator's operands are parenthesized only where
/// the grammar's precedence needs it (P191, module [`level`]): `x - y >= 1 || x >= 0`,
/// `a - (b - c)`, `- -x`, `(-x)^2`. A binder whose name, so written, would capture a read of
/// another binder is written with a new spelling (`respelled`): `x -> { x2 = 5; x }`.
/// Otherwise the text is that of [`pretty_in`] on one line, and costs the same.
pub fn written(t: &Term, name: fn(&str) -> &str, resolves: Resolves<'_>) -> String {
    let local = defs::local();
    let (t, labels) = form(t, Some(resolves), Some(name));
    let fresh = respelled(&t, name);
    let names = Names {
        written: Some(name),
        fresh: Some(&fresh),
    };
    let mut out = String::new();
    Doc::of(Piece::Term(&t), names, &labels)
        .write_flat(&mut out)
        .expect("writing to a string does not fail");
    alone(local, out)
}

/// The new spelling of each binder whose written name, `name` of it, would make a read in the
/// text of `t` name another binder: the parameter `x@1` read under a `let` of `x@2` is written
/// `x -> { x2 = 5; x }`, not `x -> { x = 5; x }`, which reads 5 (round 2 of
/// XR-lazy-and-kernel-batch-1: Codex D5 and C7, Gemini C.2). `t` is the term [`form`] gives,
/// whose reads are proved right on kernel names (module `dag`), so it is enough that each read
/// in the text names the binder its kernel name names.
///
/// The walk goes over `t` with each binder over the parts it binds over ([`kids`]: the
/// text writes a binder exactly where the evaluator binds it), keeping for each spelling the
/// binders of it in scope, the innermost on top. At a read of `k`, every binder above the
/// innermost binder of `k` on its spelling's stack, or every binder there when `k` is bound
/// nowhere around it (a name the text does not bind), is a binder the read would name in place
/// of `k`: its kernel name is respelled, and its entries leave the stack. Why the text then
/// reads right: at each read of a kernel name `k` not respelled, the innermost binder of its
/// spelling in scope is a binder of `k` when the read is reached, and a later respelling only
/// takes binders off the stacks, so it stays so; a kernel name respelled has a spelling no
/// other kernel name and no name of the text has, so each read of it names its innermost
/// binder, as in `t`. The binder respelled is the one that would capture, the inner, so the
/// names the program wrote stay where they can.
///
/// What this cannot tell apart: two names `t` does not bind with one spelling, `x@1` and
/// `x@2` both free, are one name in the text; elaboration binds every name it renames, so a
/// whole program's term has none.
// Complexity tradeoff: checking each read against every binder around it is O(n d) for n
// reads under d binders; with a stack for each spelling, each binder is pushed once and taken
// off once, so the walk is O(text) with O(1) expected hash work a node, as the text itself.
fn respelled<'t>(t: &'t Term, name: fn(&str) -> &str) -> HashMap<&'t str, String> {
    enum Step<'t> {
        Term(&'t Term),
        Bind(&'t str, usize),
        Unbind(&'t str, usize),
    }
    // For each spelling, its binders in scope, innermost last, each with a number.
    let mut stacks: HashMap<&'t str, Vec<(&'t str, usize)>> = HashMap::new();
    // For each kernel name, how many of its binders are on the stacks.
    let mut live: HashMap<&'t str, usize> = HashMap::new();
    let mut taken: HashSet<&'t str> = HashSet::new();
    let mut marked: HashSet<&'t str> = HashSet::new();
    let mut order: Vec<&'t str> = Vec::new();
    let mut binders = 0;
    let mut todo = vec![Step::Term(t)];
    while let Some(step) = todo.pop() {
        match step {
            Step::Term(u) => {
                if let Term::Var(k) = u {
                    let k: &str = k;
                    taken.insert(name(k));
                    if !marked.contains(k) {
                        let bound = live.get(k).is_some_and(|&n| n > 0);
                        let stack = stacks.entry(name(k)).or_default();
                        while let Some(&(top, _)) = stack.last()
                            && (!bound || top != k)
                        {
                            stack.pop();
                            *live.get_mut(top).expect("counted at its binder") -= 1;
                            if marked.insert(top) {
                                order.push(top);
                            }
                        }
                    }
                }
                let mut parts = Vec::new();
                kids(u, |kid, binds| parts.push((kid.term(), binds)));
                for (part, binds) in parts.into_iter().rev() {
                    let mut xs = Vec::new();
                    binds.each(|x| xs.push((&**x, binders + xs.len())));
                    binders += xs.len();
                    todo.extend(xs.iter().map(|&(x, i)| Step::Unbind(x, i)));
                    todo.push(Step::Term(part));
                    todo.extend(xs.iter().rev().map(|&(x, i)| Step::Bind(x, i)));
                }
            }
            Step::Bind(x, i) => {
                taken.insert(name(x));
                if !marked.contains(x) {
                    stacks.entry(name(x)).or_default().push((x, i));
                    *live.entry(x).or_default() += 1;
                }
            }
            Step::Unbind(x, i) => {
                // Off the stack already if respelled since (then it is not on top), or never
                // put on (respelled before its binder was reached).
                if let Some(stack) = stacks.get_mut(name(x))
                    && stack.last().is_some_and(|&(_, j)| j == i)
                {
                    stack.pop();
                    *live.get_mut(x).expect("counted at its binder") -= 1;
                }
            }
        }
    }
    // Numbered from 2 past every spelling the text writes and every one given (`numbered`).
    let mut next: HashMap<&str, usize> = HashMap::new();
    let mut given: HashSet<String> = HashSet::new();
    let mut out = HashMap::with_capacity(order.len());
    for k in order {
        let base = name(k);
        let from = next.get(base).copied().unwrap_or(2);
        let (n, s) = numbered(base, from, |s| !taken.contains(s) && !given.contains(s));
        next.insert(base, n + 1);
        given.insert(s.clone());
        out.insert(k, s);
    }
    out
}

/// `text`, a term or pattern written while `local` collected the definitions of the types in
/// its `is` tests, finished as a type printed alone is: each part written more than once
/// declared on a line of its own before the text (module `defs`). With `local` off, a message
/// around the text lays its definitions out, and the text is as written.
fn alone(local: Option<defs::Collecting>, text: String) -> String {
    match local {
        Some(_) => defs::plain(&text),
        None => text,
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let local = defs::local();
        let mut out = String::new();
        let (t, labels) = form(self, None, None);
        Doc::of(Piece::Term(&t), PLAIN, &labels).write_flat(&mut out)?;
        f.write_str(&alone(local, out))
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let local = defs::local();
        let mut out = String::new();
        Doc::of(Piece::Pattern(self), PLAIN, &HashSet::new()).write_flat(&mut out)?;
        f.write_str(&alone(local, out))
    }
}

/// How a binary primitive is written between its operands, with its spaces.
fn infix(p: Prim) -> Option<&'static str> {
    use Prim::*;
    Some(match p {
        Add => " + ",
        Sub => " - ",
        Mul => " * ",
        Div => " / ",
        IntDiv => " div ",
        Mod => " mod ",
        Eq => " == ",
        Ne => " != ",
        Lt => " < ",
        Le => " <= ",
        Gt => " > ",
        Ge => " >= ",
        And => " && ",
        Or => " || ",
        Concat => " ++ ",
        Pow => "^",
        _ => return None,
    })
}

/// The name of a primitive written as a function, `get(f, k)`.
fn name(p: Prim) -> &'static str {
    use Prim::*;
    match p {
        Neg => "neg",
        Not => "not",
        Min => "min",
        Max => "max",
        Get => "get",
        Count => "count",
        Union => "union",
        Path => "path",
        PathKey => "pathKey",
        PathLen => "pathLen",
        Tuple => "tuple",
        TupleGet => "tupleGet",
        Atom => "atom",
        Show => "String",
        CastInt => "int",
        CastRat => "rat",
        CastF64 => "f64",
        CastF32 => "f32",
        Sqrt => "sqrt",
        Fma => "fma",
        FloatMod => "floatMod",
        CastIntBase => "intBase",
        Abs => "abs",
        Len => "len",
        Lower => "lower",
        Upper => "upper",
        Trim => "trim",
        Sum => "sum",
        BitAnd => "bitAnd",
        BitOr => "bitOr",
        BitXor => "bitXor",
        BitNot => "bitNot",
        Shl => "shl",
        Shr => "shr",
        PopCount => "popCount",
        LeadingZeros => "leadingZeros",
        TrailingZeros => "trailingZeros",
        Rotl => "rotl",
        Rotr => "rotr",
        F64Bits => "f64Bits",
        CodePoint => "codePoint",
        Scalar => "scalar",
        Utf8 => "utf8",
        FromUtf8 => "fromUtf8",
        MulHi => "mulHi",
        BitReverse => "bitReverse",
        ByteSwap => "byteSwap",
        Pdep => "pdep",
        Pext => "pext",
        FunnelShl => "funnelShl",
        FunnelShr => "funnelShr",
        At => "at",
        GetAtomKey => "getAtomKey",
        Entries => "entries",
        Has => "has",
        Range => "range",
        FirstEntry => "firstEntry",
        LastEntry => "lastEntry",
        EntryAfter => "entryAfter",
        EntryBefore => "entryBefore",
        First => "first",
        Last => "last",
        Split => "split",
        Lines => "lines",
        Join => "concat",
        RangeFrom => "rangeFrom",
        ListConcat => "listConcat",
        Place => "place",
        CallNamed => "callNamed",
        Round => "round",
        RoundTiesAway => "roundTiesAway",
        Floor => "floor",
        Ceil => "ceil",
        Trunc => "trunc",
        AwayFromZero => "awayFromZero",
        Allocate => "allocate",
        _ => infix(p)
            .expect("every primitive has a name or an infix spelling")
            .trim(),
    }
}

impl Prim {
    /// How a message names the primitive: as a program writes it, the operator (`>`, `++`,
    /// `-` for both `Sub` and `Neg`, `!` for `Not`), the prelude word (`popCount`,
    /// `String`), or the form DESIGN.md gives one with no word of its own: a tuple `(..)`, a
    /// component `[i]` (`p[0]`), an entry `[k]` (`f[k]`), and the methods `.count` and
    /// `.union`, `.first` and `.last`. An atom is `#_(..)`, an atom of any name with any payload,
    /// since a fixed text cannot carry its name; a message that has the name writes `#err(..)`
    /// instead ([`Prim::written_with`]). The three steps on key paths and the four entry steps,
    /// which only the compiler generates and for which DESIGN.md gives no written form, are words
    /// ([`Prim::in_words`]), not code; a sentence names a primitive through [`Prim::named`], which
    /// quotes only code.
    pub fn written(self) -> &'static str {
        if let Some(words) = self.in_words() {
            return words;
        }
        match self {
            Prim::Neg => "-",
            Prim::Not => "!",
            Prim::Tuple => "(..)",
            Prim::TupleGet => "[i]",
            Prim::Get => "[k]",
            Prim::At | Prim::GetAtomKey => "[k]",
            Prim::Count => ".count",
            Prim::Union => ".union",
            Prim::Entries => "{..}",
            Prim::Has => "in",
            Prim::Range => "..<",
            Prim::RangeFrom => "..",
            Prim::ListConcat => "++",
            Prim::First => ".first",
            Prim::Last => ".last",
            Prim::Atom => "#_(..)",
            Prim::RoundTiesAway => "round(x, ties: #away)",
            // The call DESIGN.md sec:corner_cases writes; `intBase` is no word of a program.
            Prim::CastIntBase => "int(s, base: b)",
            p => name(p),
        }
    }

    /// As [`Prim::written`], with the primitive's first argument where a message has it: an
    /// atom whose first argument is its name, the string `"err"`, is `#err(..)`.
    pub fn written_with(self, first: Option<&Value>) -> Cow<'static, str> {
        match (self, first) {
            (Prim::Atom, Some(Value::Str(name))) => Cow::Owned(format!("#{name}(..)")),
            _ => Cow::Borrowed(self.written()),
        }
    }

    /// The step in words, for the three primitives on key paths and the four entry steps of
    /// the folds, quantifiers and scans: the compiler generates them, the first three in the
    /// key map and value map of a `reindex` and the test of a `discard` (the swap of two key
    /// levels that `group` makes, for one), the entry steps in the `gen` that walks a level in
    /// key order, and no program writes them, so a message says what the step does rather
    /// than print a name the program never had.
    pub fn in_words(self) -> Option<&'static str> {
        match self {
            Prim::Path => Some("the step that builds a key path from its keys"),
            Prim::PathKey => Some("the step that reads the key at a given position of a key path"),
            Prim::PathLen => Some("the step that counts the keys of a key path"),
            Prim::FirstEntry => Some("the step that reads the first entry of a level in key order"),
            Prim::LastEntry => Some("the step that reads the last entry of a level in key order"),
            Prim::EntryAfter => Some("the step that reads the next entry of a level in key order"),
            Prim::EntryBefore => {
                Some("the step that reads the entry before another of a level in key order")
            }
            Prim::Place => Some("the step that gives a function value its parameter list"),
            Prim::CallNamed => Some("the call through a function value that it places"),
            _ => None,
        }
    }

    /// How a sentence names the primitive: its written form in backquotes (`` `>` ``,
    /// `` `#err(..)` ``, [`Prim::written_with`]), or for a step on key paths the words of
    /// [`Prim::in_words`], unquoted.
    pub fn named(self, first: Option<&Value>) -> Cow<'static, str> {
        match self.in_words() {
            Some(words) => Cow::Borrowed(words),
            None => Cow::Owned(format!("`{}`", self.written_with(first))),
        }
    }

    /// The name the printer writes the primitive by in function form (`neg`, `get`, `+`),
    /// a different one for each primitive, so the ZIR text form reads it back.
    pub fn printed(self) -> &'static str {
        name(self)
    }
}

/// A field name stored as a string value, written bare.
fn field(v: &Value) -> String {
    match v {
        Value::Str(s) => s.to_string(),
        other => other.to_string(),
    }
}

fn grade(g: Grade) -> &'static str {
    match g {
        Grade::Axiom => "axiom",
        Grade::CheckedExhaustive => "checkedExhaustive",
        Grade::Proved => "proved",
        Grade::Bounded => "bounded",
        Grade::Obligated => "obligated",
        Grade::Assumed => "assumed",
    }
}

/// A term laid out: a sequence of tokens, in which a group is written on one line when it fits
/// and its parts on lines of their own when it does not.
struct Doc<'a> {
    toks: Vec<Tok<'a>>,
    /// For a `Start`, the index of its `End`; for a `Sep` or an `End`, that of its `Start`.
    link: Vec<usize>,
}

enum Tok<'a> {
    Text(Cow<'a, str>),
    /// The start of a group, whose parts are the tokens and groups up to its `End`.
    Start(Group<'a>),
    /// Between two items of a `List`.
    Sep,
    End,
}

enum Group<'a> {
    /// Always written on one line, as the head of a call.
    Flat,
    /// Its parts one after another, on the line where they start.
    Cat,
    /// As `Cat`, but when it does not fit every list among its parts breaks, so the two
    /// branches of an `if` break alike.
    Together,
    /// `open`, the items separated by `sep`, `close`, each item one part. Broken, each item
    /// goes on its own line indented two spaces, `sep` with its trailing spaces removed ending
    /// all but the last.
    List {
        open: Cow<'a, str>,
        sep: &'static str,
        close: &'static str,
    },
}

/// What is left to lay out: a token, or a term, an operand or a pattern to lay out.
enum Piece<'a> {
    Tok(Tok<'a>),
    Term(&'a Term),
    /// A term as the operand of a prefix `-` or `!` or the receiver of `[k]`: parenthesized
    /// unless it is written as a primary or a postfix expression (sec:grammar, Prefix and
    /// Postfix).
    Operand(&'a Term),
    /// A term in a place that needs at least the given precedence level, in [`written`]'s
    /// text: parenthesized when its own level ([`written_level`]) is lower.
    At(&'a Term, u8),
    Pattern(&'a Pattern),
}

/// The pieces one term or pattern is laid out as, in order, how names are written, and what
/// the `let`s laid out read.
struct Pieces<'a>(Vec<Piece<'a>>, Names<'a>, LetReads<'a>);

/// Which `let`s of the term in hand read a name written as one a block binds, found by one walk
/// of the term per `let` the printer meets first (PRINT-let-reading-its-own-name; see the
/// `Term::Let` case of [`Pieces::lay_out`] for how the printer uses them).
///
/// A block `{ x1 = e1; …; body }` binds each `x_i` in the whole block, while the kernel's
/// `e_i` reads the binders above it. So the printer asks, for a `let` `x = e`, whether `e`
/// reads a name written as `x` that is bound outside `e` ([`LetReads::own`]), and for the
/// `let`s of a block from `S`, whether a binding above `x = e` in the block reads one
/// ([`LetReads::above`]). The walk is in the order of the text (each `let`'s bound term
/// before its body, as [`kids`] gives them). Each binder of a name pushes the time it is
/// reached on a stack for that kernel name; each variable records a read, its time `t` and
/// the time `p` of the binder it reads (0 when free), under the name as written. A bound term
/// begun at time `T` reads a name written `x` from outside it exactly when a read of a name
/// written `x` has `t >= T` and `p < T`: the reads after `T` are those of the bound term, and
/// a binder reached before `T` is outside it. The bindings of a block from `S` begun at `T`
/// are read between `T` and the binding in hand, the same test; the block's own binders are
/// reached after `T`, and none is written `x` (else the block ends at that binder).
///
/// The test is one binary search: for each name as written the reads are kept in order of
/// `t`, and a read with a `p` no less than a later read's is dropped, as every range of `t`
/// that holds the earlier read holds the later one, so the reads kept have `p` rising with
/// `t`, and the least `p` of the reads with `t >= T` is that of the first. Exact on the text
/// written: names are compared as written, so `x@1` and `x@2`, both written `x` in a message
/// ([`written`]), are one name, as the text reads them.
// Complexity tradeoff: O(m log m) for a walk over m nodes, a node held in two places walked at
// each, as the printer writes it at each, so O(the text's nodes · log) in all: a labeled part
// (`Display`, which writes `#1#` at its other places) is walked at its first place only, so
// its reads at the other places are not seen (that text is not a program). The method before
// this one took `eval::made::reads` of each bound term, which walks a part shared by m bound
// terms m times: Θ(m k) for a part reading k names (bench
// `writing_a_part_reading_many_names_bound_twice_scales`, 51.9 times the bytes at 8n).
#[derive(Default)]
struct LetReads<'a> {
    /// The labeled parts, by address ([`Form::labels`](dag::Form)), and those a walk has read.
    labels: HashSet<*const Term>,
    walked: HashSet<*const Term>,
    /// The `let`s a walk has read, and those it has read as the first `let` of a block: a node
    /// held in two places may be first at one and in a block at the other, and [`Self::above`]
    /// holds the pairs of the blocks walked.
    seen: HashSet<*const Term>,
    starts: HashSet<*const Term>,
    /// The `let`s `x = e` whose `e` reads a name written `x` from outside it.
    own: HashSet<*const Term>,
    /// `(S, L)`: in the block of `let`s from `S`, a binding above `L` reads a name written as
    /// `L`'s from outside the block.
    above: HashSet<(*const Term, *const Term)>,
    /// The time, one more at each step of a walk, kept across walks so that a read of an
    /// earlier walk is before every time of a later one.
    now: u64,
    /// For each kernel name, the times its binders in scope were reached.
    binders: HashMap<&'a str, Vec<u64>>,
    /// For each name as written, the reads `(t, p)` kept, `t` and `p` rising.
    reads: HashMap<&'a str, Vec<(u64, u64)>>,
}

impl<'a> LetReads<'a> {
    /// Walks the term from the `let` `root`, as the first `let` of a block. A `let` met in the walk is in the block of the one whose body it is, unless that
    /// one's bound term reads its own name (then its body is a lambda's) or the block ends at
    /// it, as the printer writes them.
    fn walk(&mut self, root: &'a Term, names: Names<'a>) {
        // A part to read, in the block with that index if it is a `let` in one; a binder's
        // names bound or unbound; or a `let` whose bound term, begun at that time, is read.
        enum Step<'a> {
            Read(&'a Term, Option<usize>),
            Bind(Binds<'a>),
            Unbind(Binds<'a>),
            Bound(&'a Term, usize, u64),
        }
        // A block: its first `let`, the time before its first bound term, its names written.
        struct Block<'a> {
            first: *const Term,
            from: u64,
            bound: HashSet<&'a str>,
        }
        if !matches!(root, Term::Let(..)) {
            return;
        }
        // As the printer writes each name ([`Names::spell`]), a binder given a new spelling
        // ([`respelled`]) included.
        let spelled = |x: &'a str| names.spell(x);
        let mut blocks: Vec<Block<'a>> = Vec::new();
        let mut steps = vec![Step::Read(root, None)];
        while let Some(step) = steps.pop() {
            self.now += 1;
            let now = self.now;
            match step {
                Step::Bind(b) => b.each(|x| self.binders.entry(x).or_default().push(now)),
                Step::Unbind(b) => b.each(|x| {
                    self.binders.get_mut(&**x).and_then(Vec::pop);
                }),
                Step::Read(Term::Var(x), _) => {
                    let p = self
                        .binders
                        .get(&**x)
                        .and_then(|v| v.last())
                        .map_or(0, |&p| p);
                    let reads = self.reads.entry(spelled(x)).or_default();
                    while reads.last().is_some_and(|&(_, q)| q >= p) {
                        reads.pop();
                    }
                    reads.push((now, p));
                }
                Step::Read(t @ Term::Let(x, e, _), block) => {
                    let x = spelled(x);
                    self.seen.insert(std::ptr::from_ref(t));
                    let block = match block {
                        Some(b) if blocks[b].bound.contains(x) => None,
                        Some(b) if self.read_since(x, blocks[b].from) => {
                            self.above.insert((blocks[b].first, t));
                            None
                        }
                        b => b,
                    };
                    let block = block.unwrap_or_else(|| {
                        self.starts.insert(std::ptr::from_ref(t));
                        blocks.push(Block {
                            first: t,
                            from: now,
                            bound: HashSet::new(),
                        });
                        blocks.len() - 1
                    });
                    steps.push(Step::Bound(t, block, now));
                    if !self.labeled_again(e) {
                        steps.push(Step::Read(e, None));
                    }
                }
                Step::Bound(t, block, from) => {
                    let Term::Let(x, _, body) = t else {
                        unreachable!("a `Bound` step is a `let`'s")
                    };
                    let own = self.read_since(spelled(x), from);
                    let next = match own {
                        true => {
                            self.own.insert(std::ptr::from_ref(t));
                            None
                        }
                        false => {
                            blocks[block].bound.insert(spelled(x));
                            Some(block)
                        }
                    };
                    let b = Binds::Names(std::slice::from_ref(x));
                    steps.push(Step::Unbind(b));
                    if !self.labeled_again(body) {
                        steps.push(Step::Read(body, next));
                    }
                    steps.push(Step::Bind(b));
                }
                Step::Read(t, _) => {
                    // Popped in reverse: each part's names bound, the part read, then unbound.
                    let mut parts = Vec::new();
                    kids(t, |k, b| parts.push((k, b)));
                    for (k, b) in parts.into_iter().rev() {
                        steps.push(Step::Unbind(b));
                        match k {
                            Kid::Inline(u) => steps.push(Step::Read(u, None)),
                            Kid::Shared(s) if self.labeled_again(s) => {}
                            Kid::Shared(s) => steps.push(Step::Read(s, None)),
                        }
                        steps.push(Step::Bind(b));
                    }
                }
            }
        }
    }

    /// Whether `u` is a labeled part a walk has read, so is not read again; the first call on a
    /// labeled part marks it read.
    fn labeled_again(&mut self, u: &Term) -> bool {
        let u = std::ptr::from_ref(u);
        self.labels.contains(&u) && !self.walked.insert(u)
    }

    /// Whether a read of a name written `x` has a time `t >= from` and its binder's `p < from`.
    fn read_since(&self, x: &str, from: u64) -> bool {
        self.reads.get(x).is_some_and(|r| {
            let i = r.partition_point(|&(t, _)| t < from);
            r.get(i).is_some_and(|&(_, p)| p < from)
        })
    }
}

impl<'a> Pieces<'a> {
    /// How the name `x` is written.
    fn name(&self, x: &'a str) -> &'a str {
        self.1.spell(x)
    }

    fn text(&mut self, s: impl Into<Cow<'a, str>>) -> &mut Self {
        self.0.push(Piece::Tok(Tok::Text(s.into())));
        self
    }

    fn term(&mut self, t: &'a Term) -> &mut Self {
        self.0.push(Piece::Term(t));
        self
    }

    fn operand(&mut self, t: &'a Term) -> &mut Self {
        self.0.push(Piece::Operand(t));
        self
    }

    /// `t` in a place that needs the precedence level `min`: in [`written`]'s text,
    /// parenthesized only when its level is lower; in the other printers' text, which
    /// parenthesizes each binary operator, as [`Pieces::operand`] writes it.
    fn at(&mut self, t: &'a Term, min: u8) -> &mut Self {
        self.0.push(match self.1.written {
            Some(_) => Piece::At(t, min),
            None => Piece::Operand(t),
        });
        self
    }

    /// The prefix operator `p` (`Neg` or `Not`) and its operand `x`. `Prefix = ('-' | '!')
    /// Prefix` (sec:grammar), so in [`written`]'s text a prefix on a prefix needs no
    /// parentheses (P191), and the same operator twice is written with a space, `- -x`,
    /// `! !b`, as the source formatter writes it (`zedc-syntax` `format`): `--x` and `!!b`
    /// would read as C's decrement and JavaScript's cast to a boolean (P292). A negative
    /// literal under `-` is the same case, `- -3`.
    fn prefix(&mut self, p: Prim, x: &'a Term) -> &mut Self {
        self.text(p.written());
        if self.minimal() {
            let twice = match x {
                Term::Prim(q, args) => *q == p && args.len() == 1,
                Term::Lit(_) => p == Prim::Neg && written_level(x) == level::PREFIX,
                _ => false,
            };
            if twice {
                self.text(" ");
            }
        }
        self.at(x, level::PREFIX)
    }

    /// Whether the text is [`written`]'s, which writes minimal parentheses.
    fn minimal(&self) -> bool {
        self.1.written.is_some()
    }

    fn pattern(&mut self, p: &'a Pattern) -> &mut Self {
        self.0.push(Piece::Pattern(p));
        self
    }

    fn start(&mut self, g: Group<'a>) -> &mut Self {
        self.0.push(Piece::Tok(Tok::Start(g)));
        self
    }

    fn cat(&mut self) -> &mut Self {
        self.start(Group::Cat)
    }

    fn list(
        &mut self,
        open: impl Into<Cow<'a, str>>,
        sep: &'static str,
        close: &'static str,
    ) -> &mut Self {
        self.start(Group::List {
            open: open.into(),
            sep,
            close,
        })
    }

    /// `head(`, the start of a call's list of arguments.
    fn call(&mut self, head: &str) -> &mut Self {
        self.list(format!("{head}("), ", ", ")")
    }

    fn sep(&mut self) -> &mut Self {
        self.0.push(Piece::Tok(Tok::Sep));
        self
    }

    fn end(&mut self) -> &mut Self {
        self.0.push(Piece::Tok(Tok::End));
        self
    }

    /// The terms as the items of a list.
    fn items(&mut self, ts: &'a [Term]) -> &mut Self {
        for (i, t) in ts.iter().enumerate() {
            if i > 0 {
                self.sep();
            }
            self.term(t);
        }
        self
    }

    /// `key: `, before the value of a named part of a generator such as `depth: 2`.
    fn named(&mut self, key: &str) -> &mut Self {
        self.cat().text(format!("{key}: "))
    }

    /// Whether the `let` `t`, `x = e`, has an `e` that reads a name written `x` from outside it
    /// ([`LetReads::own`]): O(1) once a walk has read `t`.
    fn own(&mut self, t: &'a Term) -> bool {
        let at = std::ptr::from_ref(t);
        if !self.2.seen.contains(&at) {
            self.2.walk(t, self.1);
        }
        self.2.own.contains(&at)
    }

    /// Whether, in the block of `let`s from `first`, a binding above the `let` `t` reads a name
    /// written as `t`'s from outside the block ([`LetReads::above`]).
    fn above(&mut self, first: &'a Term, t: &'a Term) -> bool {
        if !self.2.starts.contains(&std::ptr::from_ref(first)) {
            self.2.walk(first, self.1);
        }
        (self.2.above).contains(&(std::ptr::from_ref(first), std::ptr::from_ref(t)))
    }

    /// `(x -> body)(e)`: a `let` of `x` to an `e` that reads `x`, as a call, so that `e`
    /// reads the `x` outside. Unlike a call's head in the `Term::App` case, the lambda is not
    /// kept on one line, as it holds the rest of the chain.
    fn called(&mut self, x: &'a str, e: &'a Term, body: &'a Term) -> &mut Self {
        self.cat().text("(").lambda(&[x], body).text(")");
        self.call("").items(std::slice::from_ref(e)).end().end()
    }

    /// `(x, y) -> body`, or `x -> body` for one parameter. A body that is a chain of `let`s
    /// binding a parameter is written in one more block: the parameters share one scope with
    /// the statements of a body block (zedc-resolve, resolve.rs: "so `f(x) { x = 1; }`
    /// rebinds `x`"), so `x -> { x = 1; x }` is refused with "`x` is already bound in this
    /// scope", and `x -> { { x = 1; x } }` binds it in a nested block, where it shadows the
    /// parameter (PRINT-let-reading-its-own-name). The walk stops at a binding that reads its
    /// own name, written as a call whose lambda holds the rest of the chain
    /// ([`Pieces::own`]). O(the chain's length + the parameters), each chain read by the one
    /// lambda right above it.
    fn lambda(&mut self, params: &[&str], body: &'a Term) -> &mut Self {
        let head = match params {
            [p] => format!("{p} -> "),
            _ => format!("({}) -> ", params.join(", ")),
        };
        self.cat().text(head);
        let mut rebinds = false;
        if let Term::Let(..) = body {
            let params: HashSet<&str> = params.iter().copied().collect();
            let mut t = body;
            while let Term::Let(x, _, rest) = t {
                if self.own(t) {
                    break;
                }
                let x = self.name(x);
                if params.contains(x) {
                    rebinds = true;
                    break;
                }
                t = rest;
            }
        }
        match rebinds {
            true => self.block(body),
            false => self.term(body),
        };
        self.end()
    }

    fn evidence(&mut self, ev: &Evidence) -> &mut Self {
        self.named("ev").list("{", ", ", "}");
        for (i, (p, g)) in ev.iter().enumerate() {
            if i > 0 {
                self.sep();
            }
            self.text(format!("{p}: {}", grade(*g)));
        }
        self.end().end()
    }

    /// `{ e }`, an `if` branch in its braces.
    fn block(&mut self, t: &'a Term) -> &mut Self {
        self.list("{", " ", "}").term(t).end()
    }

    fn lay_out(&mut self, t: &'a Term) {
        match t {
            Term::Lit(v) => {
                self.text(v.to_string());
            }
            Term::Var(x) => {
                let x = self.name(x);
                self.text(x);
            }
            Term::Lam(params, body) => {
                let ps: Vec<&str> = params.iter().map(|p| self.name(p)).collect();
                self.lambda(&ps, body);
            }
            Term::App(f, args) => match &**f {
                Term::Var(x) => {
                    let x = self.name(x);
                    self.call(x).items(args).end();
                }
                Term::PrimFn(p) => {
                    self.call(&prim_fn(*p)).items(args).end();
                }
                // The head is written on one line, as the list after it starts where it ends.
                _ => {
                    self.cat()
                        .start(Group::Flat)
                        .cat()
                        .text("(")
                        .term(f)
                        .text(")")
                        .end()
                        .end();
                    self.call("").items(args).end().end();
                }
            },
            Term::Prim(Prim::Tuple, items) if items.len() == 1 => {
                self.cat().text("(").term(&items[0]).text(",)").end();
            }
            Term::Prim(Prim::Tuple, items) => {
                self.list("(", ", ", ")").items(items).end();
            }
            // An atom is written as Zed writes it: `#err(1)`, `#err(code: 3)`. Elaboration gives
            // the name and the field names as literals; a term that gives them any other way has
            // no written form, so its name is written `#_` and its payload positionally. No such
            // term reaches a message: elaboration builds an atom at one place (zedc-elab
            // walk.rs, `Frame::AtomArgs`), always with literal name and field names.
            Term::Prim(Prim::Atom, args) if !args.is_empty() => {
                let open = match &args[0] {
                    Term::Lit(Value::Str(name)) => format!("#{name}("),
                    _ => "#_(".into(),
                };
                let rest = args.get(2..).unwrap_or_default();
                let fs: &[Value] = match args.get(1) {
                    Some(Term::Lit(Value::Tuple(fs))) if fs.len() == rest.len() => fs,
                    _ => &[],
                };
                self.list(open, ", ", ")");
                for (i, a) in rest.iter().enumerate() {
                    if i > 0 {
                        self.sep();
                    }
                    match fs.get(i) {
                        Some(f) => self.cat().text(format!("{}: ", field(f))).term(a).end(),
                        None => self.term(a),
                    };
                }
                self.end();
            }
            // `-x` and `!x`: the operator before its operand (sec:grammar, Prefix).
            Term::Prim(p @ (Prim::Neg | Prim::Not), args) if args.len() == 1 => {
                self.cat().prefix(*p, &args[0]).end();
            }
            // `t[0]` and `f[k]`: the key in brackets after its receiver (sec:grammar, IndexSuffix).
            // A chain `t[0][1]` is one `Cat` of its receiver and its indices, gathered by a loop,
            // so that `fits` meets the receiver's text first rather than after walking down the
            // chain, which made a broken layout quadratic in the chain's length.
            Term::Prim(Prim::TupleGet | Prim::Get | Prim::At | Prim::GetAtomKey, args)
                if args.len() == 2 =>
            {
                let mut keys = vec![&args[1]];
                let mut receiver = &args[0];
                while let Term::Prim(
                    Prim::TupleGet | Prim::Get | Prim::At | Prim::GetAtomKey,
                    inner,
                ) = receiver
                    && inner.len() == 2
                {
                    keys.push(&inner[1]);
                    receiver = &inner[0];
                }
                self.cat().at(receiver, receiver_level(receiver));
                for k in keys.into_iter().rev() {
                    self.list("[", ", ", "]").term(k).end();
                }
                self.end();
            }
            // `f.count`, `l.first` and `l.last`: methods, written after their receiver as the
            // program writes them (DESIGN.md sec:reduction: `count` "is a method (`.count`)"),
            // not as calls `count(f)`, which no program writes (KERNEL-print-distinct).
            Term::Prim(p @ (Prim::Count | Prim::First | Prim::Last), args) if args.len() == 1 => {
                self.cat()
                    .at(&args[0], receiver_level(&args[0]))
                    .text(p.written())
                    .end();
            }
            Term::Prim(p, args) => match (infix(*p), &args[..]) {
                // In [`written`]'s text each operand is parenthesized only below the level
                // its side of the operator needs.
                (Some(sep), [a, b]) if self.minimal() => {
                    let (l, r) = level::operands(level::binary(*p).expect("an infix operator"));
                    self.cat().at(a, l).text(sep).at(b, r).end();
                }
                // The left operand of `^` is a postfix expression (sec:grammar, Power), so
                // `-x^2` would read as `-(x^2)`.
                (Some(sep), [a, b]) => {
                    self.list("(", sep, ")");
                    if *p == Prim::Pow {
                        self.operand(a)
                    } else {
                        self.term(a)
                    };
                    self.sep().term(b).end();
                }
                _ => {
                    self.call(name(*p)).items(args).end();
                }
            },
            Term::PrimFn(p) => {
                self.text(prim_fn(*p));
            }
            // A chain of `let`s is one block, `{ x1 = e1; …; body }`, where every binding is
            // in scope in the whole block and a binding reads itself (zedc-resolve,
            // resolve.rs: "a name bound anywhere in a scope is in scope throughout it"), while
            // the kernel's `e_i` reads the binders above it. So the block ends where that
            // would change what a name reads (PRINT-let-reading-its-own-name):
            // - at a binder of a name the block binds already ("`x` is already bound in this
            //   scope"), or one an earlier `e_i` of the block reads ("used above its
            //   definition"): that binder starts a nested block, where it shadows the outer
            //   name, and the earlier `e_i` still reads the outer one;
            // - at a binder `x = e` whose `e` reads `x` ("defined in terms of its own value"),
            //   which no block can write: it is written `(x -> rest)(e)`, the call binding the
            //   parameter `x` over `rest` and `e` read outside it ([`Pieces::called`]). Such a
            //   binding first in the chain is the call alone, with no braces: `{ e }` with no
            //   statement in it reads back as a set (`{ (x -> x)(x + 1) }` gave
            //   `Family({1: 1})`, not 1).
            // Which `e_i` reads which name is found by one walk of the term ([`LetReads`]),
            // O(1) a binding after it, so the block costs O(its bindings) more.
            Term::Let(x, e, body) if self.own(t) => {
                self.called(self.name(x), e, body);
            }
            Term::Let(..) => {
                self.list("{", " ", "}");
                let mut bound = HashSet::new();
                let first = t;
                let mut t = t;
                let mut called = false;
                while let Term::Let(x, e, body) = t {
                    let x = self.name(x);
                    if bound.contains(x) || self.above(first, t) {
                        break;
                    }
                    if self.own(t) {
                        self.called(x, e, body);
                        called = true;
                        break;
                    }
                    bound.insert(x);
                    self.cat()
                        .text(format!("{x} = "))
                        .term(e)
                        .text(";")
                        .end()
                        .sep();
                    t = body;
                }
                if !called {
                    self.term(t);
                }
                self.end();
            }
            // `c && b` and `c || b` as elaboration gives them, and `!c && b` and `!c || a`,
            // written as the operators when the text is for a message ([`written`]).
            Term::If(c, a, b) if self.minimal() && connective(a, b).is_some() => {
                let (and, not, rhs) = connective(a, b).expect("matched");
                let (op, sep) = match and {
                    true => (Prim::And, " && "),
                    false => (Prim::Or, " || "),
                };
                let (l, r) = level::operands(level::binary(op).expect("an infix operator"));
                self.cat();
                match not {
                    true => self.cat().prefix(Prim::Not, c).end(),
                    false => self.at(c, l),
                };
                self.text(sep).at(rhs, r).end();
            }
            Term::If(c, a, b) => {
                self.cat()
                    .text("if ")
                    .term(c)
                    .text(" ")
                    .start(Group::Together);
                self.block(a).text(" else ").block(b).end().end();
            }
            Term::Match(e, arms) => {
                self.cat()
                    .text("match ")
                    .term(e)
                    .text(" ")
                    .list("{", ", ", "}");
                for (i, (p, t)) in arms.iter().enumerate() {
                    if i > 0 {
                        self.sep();
                    }
                    self.cat().pattern(p).text(" -> ").term(t).end();
                }
                self.end().end();
            }
            Term::Fam { domain, var, body } => {
                let var = self.name(var);
                self.call("fam")
                    .term(domain)
                    .sep()
                    .lambda(&[var], body)
                    .end();
            }
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => {
                let w = match witness {
                    Witness::Residue => "residue".to_string(),
                    Witness::Catalog(name) => format!("catalog({name:?})"),
                };
                self.call("reindex")
                    .term(family)
                    .sep()
                    .term(kf)
                    .sep()
                    .term(vf)
                    .sep();
                self.named("witness").text(w).end().end();
            }
            Term::Discard { family, sel } => {
                self.call("discard").term(family).sep().term(sel).end();
            }
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => {
                self.call("fold").term(family).sep().term(op).sep();
                if let Some(i) = identity {
                    self.named("identity").term(i).end().sep();
                }
                self.named("depth").text(depth.to_string()).end().sep();
                self.evidence(ev).end();
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind,
                ev,
            } => {
                self.call("fix").term(init).sep();
                match kind {
                    FixKind::Lattice { join } => {
                        self.term(step).sep().named("join").term(join).end();
                    }
                    FixKind::Definedness => {
                        let names = [self.name(this), self.name(key)];
                        self.lambda(&names, step).sep().text("definedness");
                    }
                }
                self.sep().evidence(ev).end();
            }
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => {
                let pos = match pos {
                    GuardPos::Before => "before",
                    GuardPos::After => "after",
                };
                self.call("gen")
                    .term(init)
                    .sep()
                    .term(step)
                    .sep()
                    .term(guard)
                    .sep();
                self.named("guard").text(pos).end().end();
            }
            Term::Read(port) => {
                self.call("port.read").text(&**port).end();
            }
            Term::Push(port, v) => {
                self.call("port.push").text(&**port).sep().term(v).end();
            }
        }
    }

    /// The pattern as text, which never breaks.
    fn pattern_out(&mut self, pat: &'a Pattern) {
        match pat {
            Pattern::Wild => self.text("_"),
            Pattern::Bind(x) => self.text(self.name(x)),
            Pattern::Lit(v) => self.text(v.to_string()),
            Pattern::Atom(name, ps) if ps.is_empty() => self.text(format!("#{name}")),
            Pattern::Atom(name, ps) => self
                .text(format!("#{name}("))
                .patterns(ps.iter().map(|p| (None, p)))
                .text(")"),
            Pattern::Fields(name, fs) => self
                .text(format!("#{name}("))
                .patterns(fs.iter().map(|(k, p)| (Some(&**k), p)))
                .text(")"),
            Pattern::Tuple(ps) if ps.len() == 1 => self.text("(").pattern(&ps[0]).text(",)"),
            // sec:grammar's `TuplePat` has a comma, so the empty tuple is the type test of the
            // type `()`, whose one value it is.
            Pattern::Tuple(ps) if ps.is_empty() => self.text("(is ())"),
            Pattern::Tuple(ps) => self
                .text("(")
                .patterns(ps.iter().map(|p| (None, p)))
                .text(")"),
            // No pattern of sec:grammar is `#_`, the type of every atom, so any atom is the type
            // test of that type.
            Pattern::AnyAtom => self.text("(is #_)"),
            // `(is T)`, sec:grammar's `IsPat` with no name, in the parentheses that hold it alone
            // (DESIGN.md step L2.7b), the type as a program writes it after `is`: only an arrow
            // is parenthesized. The type ends at the `)`, which a `TypeUnion` does not take. As
            // an atom's payload it is written in the payload's parentheses too, `#ok((is T))`,
            // which sec:grammar's `AtomPattern` reads as the payload list of one pattern.
            Pattern::Is(t) => self.text(format!("(is {})", t.surface_after_is())),
        };
    }

    /// The patterns, each after its field name if it has one, separated by commas.
    fn patterns(&mut self, ps: impl Iterator<Item = (Option<&'a str>, &'a Pattern)>) -> &mut Self {
        for (i, (key, p)) in ps.enumerate() {
            if i > 0 {
                self.text(", ");
            }
            if let Some(k) = key {
                self.text(format!("{k}: "));
            }
            self.pattern(p);
        }
        self
    }
}

/// The text of a primitive written as a function, a call's head or an argument. A primitive with
/// no operator function of its own is written as the lambda a program writes for it (DESIGN.md
/// writes `neg: (a -> -a)`), parenthesized as `(+)` is, so that a call or an operator after it
/// is not read as part of its body.
fn prim_fn(p: Prim) -> Cow<'static, str> {
    match p {
        Prim::Neg | Prim::Not => format!("(x -> {}x)", p.written()).into(),
        Prim::TupleGet => "((t, i) -> t[i])".into(),
        Prim::Get | Prim::At | Prim::GetAtomKey => "((f, k) -> f[k])".into(),
        _ => match infix(p) {
            Some(op) => format!("({})", op.trim()).into(),
            None => name(p).into(),
        },
    }
}

/// Whether the printer writes `t` as a primary or a postfix expression: a name, a call, a
/// parenthesized or bracketed form, or a literal with no sign or slash in its text. A prefix
/// operation, a lambda, a block, an `if`, a `match` and the other literals are not; nor is
/// `-x` a primary, as `-x[0]` reads as `-(x[0])`.
fn primary(t: &Term) -> bool {
    match t {
        Term::Lit(v) => match v {
            Value::Int(n) => *n >= 0,
            Value::Bool(_) | Value::Str(_) | Value::Atom(_) | Value::Tuple(_) => true,
            Value::Big(_)
            | Value::Rat(_)
            | Value::Float(_)
            | Value::Float32(_)
            | Value::Path(_)
            | Value::Family(_) => false,
        },
        Term::Prim(Prim::Neg | Prim::Not, args) => args.len() != 1,
        Term::Lam(..) | Term::Let(..) | Term::If(..) | Term::Match(..) => false,
        Term::Var(_)
        | Term::App(..)
        | Term::Prim(..)
        | Term::PrimFn(_)
        | Term::Fam { .. }
        | Term::Reindex { .. }
        | Term::Discard { .. }
        | Term::Fold { .. }
        | Term::Fix { .. }
        | Term::Gen { .. }
        | Term::Read(_)
        | Term::Push(..) => true,
    }
}

/// The connective `if c { a } else { b }` is, as [`written`] writes it: whether it is `&&`,
/// whether its left side is `!c` rather than `c`, and its right side. `if c { a } else { false }`
/// is `c && a`, `if c { true } else { b }` is `c || b`, `if c { false } else { b }` is
/// `!c && b`, and `if c { a } else { true }` is `!c || a`; tried in that order, so
/// `if c { true } else { false }` is `c && true`. O(1).
fn connective<'t>(a: &'t Term, b: &'t Term) -> Option<(bool, bool, &'t Term)> {
    let lit = |t: &Term| match t {
        Term::Lit(Value::Bool(v)) => Some(*v),
        _ => None,
    };
    match (lit(a), lit(b)) {
        (_, Some(false)) => Some((true, false, a)),
        (Some(true), _) => Some((false, false, b)),
        (Some(false), _) => Some((true, true, b)),
        (_, Some(true)) => Some((false, true, a)),
        _ => None,
    }
}

/// The level the receiver `t` of a postfix (`t[k]`, `t.count`) needs. A number receiver is
/// parenthesized, `(5)[1]`, as the formatter writes every postfix of a number (zedc-syntax
/// format.rs, `Job::Postfix`: a `.` after it would read as a decimal point), so that the
/// formatter leaves this text as it is. `PRIMARY + 1` is above every level, so `at` always
/// parenthesizes it.
fn receiver_level(t: &Term) -> u8 {
    match t {
        Term::Lit(
            Value::Int(_) | Value::Big(_) | Value::Rat(_) | Value::Float(_) | Value::Float32(_),
        ) => level::PRIMARY + 1,
        _ => level::POSTFIX,
    }
}

/// The precedence level (module [`level`]) of `t` as [`written`] writes it. A literal's is
/// that of its text: a sign makes it a prefix expression (`-3`), a slash a quotient (`1/3`),
/// and a key path or a family, which has no written form of its own, is parenthesized
/// wherever it is an operand. O(1), but for a big number, a rational or a float, whose text
/// is written to read it.
fn written_level(t: &Term) -> u8 {
    match t {
        Term::Lit(v) => match v {
            Value::Int(n) if *n < 0 => level::PREFIX,
            Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Atom(_) | Value::Tuple(_) => {
                level::PRIMARY
            }
            Value::Big(_) | Value::Rat(_) | Value::Float(_) | Value::Float32(_) => {
                let s = v.to_string();
                if s.starts_with('-') {
                    level::PREFIX
                } else if s.contains('/') {
                    level::MULTIPLICATIVE
                } else {
                    level::PRIMARY
                }
            }
            Value::Path(_) | Value::Family(_) => level::LAMBDA,
        },
        Term::Prim(Prim::Neg | Prim::Not, args) if args.len() == 1 => level::PREFIX,
        Term::Prim(p, args) if args.len() == 2 && infix(*p).is_some() => {
            level::binary(*p).expect("an infix operator")
        }
        Term::Prim(Prim::Tuple | Prim::Atom, _) => level::PRIMARY,
        Term::If(_, a, b) => match connective(a, b) {
            Some((true, ..)) => level::AND,
            Some((false, ..)) => level::OR,
            None => level::PRIMARY,
        },
        Term::Lam(..) => level::LAMBDA,
        Term::Var(_) | Term::PrimFn(_) | Term::Let(..) | Term::Match(..) => level::PRIMARY,
        Term::App(..)
        | Term::Prim(..)
        | Term::Fam { .. }
        | Term::Reindex { .. }
        | Term::Discard { .. }
        | Term::Fold { .. }
        | Term::Fix { .. }
        | Term::Gen { .. }
        | Term::Read(_)
        | Term::Push(..) => level::POSTFIX,
    }
}

/// What is left of a group being broken: a `Cat` or `Together` whose parts from `at` are still to
/// write, or a `List` whose items are.
enum Frame {
    Parts {
        at: usize,
        ind: usize,
        together: bool,
    },
    Items {
        at: usize,
        ind: usize,
    },
}

impl<'a> Doc<'a> {
    /// The doc of what `root` lays out, one group. Each term and pattern is laid out once, its
    /// pieces taken from a stack. A term in `labels`, a part of a term shared by address
    /// (identity only), is written `#n=` before its text at its first place and `#n#` alone
    /// at each other, `n` counted from 1 in the order written.
    fn of(root: Piece<'a>, names: Names<'a>, labels: &HashSet<*const Term>) -> Doc<'a> {
        let mut toks = Vec::new();
        let mut todo = vec![
            Piece::Tok(Tok::End),
            root,
            Piece::Tok(Tok::Start(Group::Cat)),
        ];
        let lets = LetReads {
            labels: labels.clone(),
            ..LetReads::default()
        };
        let mut out = Pieces(Vec::new(), names, lets);
        let mut seen: HashMap<*const Term, usize> = HashMap::new();
        while let Some(piece) = todo.pop() {
            let whole = match piece {
                Piece::Term(t) => Some(t),
                Piece::Operand(t) if primary(t) => Some(t),
                Piece::At(t, min) if written_level(t) >= min => Some(t),
                _ => None,
            };
            if let Some(t) = whole
                && labels.contains(&std::ptr::from_ref(t))
            {
                let n = seen.len() + 1;
                match seen.entry(std::ptr::from_ref(t)) {
                    Entry::Occupied(e) => {
                        toks.push(Tok::Text(format!("#{}#", e.get()).into()));
                        continue;
                    }
                    Entry::Vacant(e) => {
                        e.insert(n);
                        toks.push(Tok::Text(format!("#{n}=").into()));
                    }
                }
            }
            match piece {
                Piece::Tok(t) => {
                    toks.push(t);
                    continue;
                }
                Piece::Term(t) => out.lay_out(t),
                Piece::Operand(t) if primary(t) => out.lay_out(t),
                Piece::Operand(t) => {
                    out.cat().text("(").term(t).text(")").end();
                }
                Piece::At(t, min) if written_level(t) >= min => out.lay_out(t),
                Piece::At(t, _) => {
                    out.cat().text("(").term(t).text(")").end();
                }
                Piece::Pattern(p) => out.pattern_out(p),
            }
            todo.extend(out.0.drain(..).rev());
        }
        let mut link: Vec<usize> = (0..toks.len()).collect();
        let mut open = Vec::new();
        for (i, t) in toks.iter().enumerate() {
            match t {
                Tok::Start(_) => open.push(i),
                Tok::Sep => link[i] = *open.last().expect("a separator inside a list"),
                Tok::End => {
                    let s = open.pop().expect("each end after its start");
                    link[i] = s;
                    link[s] = i;
                }
                Tok::Text(_) => {}
            }
        }
        Doc { toks, link }
    }

    /// The index after the token or group starting at `i`.
    fn next(&self, i: usize) -> usize {
        match self.toks[i] {
            Tok::Start(_) => self.link[i] + 1,
            _ => i + 1,
        }
    }

    /// The list a `Sep` or `End` at `i` is in, if it is in one.
    fn list_of(&self, i: usize) -> Option<(&'static str, &'static str)> {
        match &self.toks[self.link[i]] {
            Tok::Start(Group::List { sep, close, .. }) => Some((sep, close)),
            _ => None,
        }
    }

    /// The space inside the braces of a nonempty `{ … }` written on one line, the list starting
    /// at `s`.
    fn pad(&self, s: usize, close: &str) -> &'static str {
        if close == "}" && self.link[s] > s + 1 {
            " "
        } else {
            ""
        }
    }

    /// Gives `f` the pieces of the one-line text of the token or group at `i`, in order, until
    /// it returns `false`; returns whether every piece was given.
    fn flat(&self, i: usize, mut f: impl FnMut(&str) -> bool) -> bool {
        (i..self.next(i)).all(|k| match &self.toks[k] {
            Tok::Text(s) => f(s),
            Tok::Start(Group::List { open, close, .. }) => f(open) && f(self.pad(k, close)),
            Tok::Start(_) => true,
            Tok::Sep => f(self.list_of(k).expect("a separator inside a list").0),
            Tok::End => match self.list_of(k) {
                Some((_, close)) => f(self.pad(self.link[k], close)) && f(close),
                None => true,
            },
        })
    }

    /// Writes the one-line text.
    fn write_flat(&self, w: &mut impl fmt::Write) -> fmt::Result {
        let mut r = Ok(());
        self.flat(0, |s| {
            r = w.write_str(s);
            r.is_ok()
        });
        r
    }

    /// Whether the one-line text of the token or group at `i` fits in `room` columns, one column
    /// a character, not a byte: the literal `"é"`, quotes included, takes three columns, as `"e"`
    /// does. It stops once the room runs out, so it reads at most `room + 1` characters of text.
    fn fits(&self, i: usize, mut room: usize) -> bool {
        self.flat(i, |s| {
            match room.checked_sub(s.chars().take(room.saturating_add(1)).count()) {
                Some(r) => {
                    room = r;
                    true
                }
                None => false,
            }
        })
    }

    /// Writes the doc in at most `width` columns where it can.
    fn render(&self, width: usize, out: &mut String) {
        let mut frames = Vec::new();
        let mut col = 0;
        self.enter(0, 0, width, &mut col, out, &mut frames);
        while let Some(frame) = frames.last_mut() {
            match frame {
                Frame::Parts { at, ind, together } => {
                    let (c, ind, together) = (*at, *ind, *together);
                    if let Tok::End = self.toks[c] {
                        frames.pop();
                        continue;
                    }
                    *at = self.next(c);
                    match &self.toks[c] {
                        Tok::Start(Group::List { open, .. }) if together => {
                            *out += open;
                            frames.push(Frame::Items { at: c + 1, ind });
                        }
                        _ => self.enter(c, ind, width, &mut col, out, &mut frames),
                    }
                }
                Frame::Items { at, ind } => {
                    let (c, ind) = (*at, *ind);
                    match &self.toks[c] {
                        Tok::End => {
                            let close = self.list_of(c).expect("items inside a list").1;
                            *out += "\n";
                            *out += &" ".repeat(ind);
                            *out += close;
                            col = ind + close.len();
                            frames.pop();
                        }
                        Tok::Sep => {
                            *at = c + 1;
                            *out += self
                                .list_of(c)
                                .expect("a separator inside a list")
                                .0
                                .trim_end();
                        }
                        _ => {
                            *at = self.next(c);
                            let inner = ind + 2;
                            *out += "\n";
                            *out += &" ".repeat(inner);
                            col = inner;
                            self.enter(c, inner, width, &mut col, out, &mut frames);
                        }
                    }
                }
            }
        }
    }

    /// Starts the token or group at `i`, at column `col` of a line indented `ind`: writes it
    /// on one line when it fits, and otherwise pushes what is left of it to write.
    fn enter(
        &self,
        i: usize,
        ind: usize,
        width: usize,
        col: &mut usize,
        out: &mut String,
        frames: &mut Vec<Frame>,
    ) {
        let flat = matches!(self.toks[i], Tok::Text(_) | Tok::Start(Group::Flat))
            || self.fits(i, width.saturating_sub(*col));
        if flat {
            self.flat(i, |s| {
                *out += s;
                *col += s.chars().count();
                true
            });
            return;
        }
        match &self.toks[i] {
            Tok::Start(Group::Cat) => frames.push(Frame::Parts {
                at: i + 1,
                ind,
                together: false,
            }),
            Tok::Start(Group::Together) => frames.push(Frame::Parts {
                at: i + 1,
                ind,
                together: true,
            }),
            Tok::Start(Group::List { open, .. }) => {
                *out += open;
                frames.push(Frame::Items { at: i + 1, ind });
            }
            _ => unreachable!("a text, a flat group, a separator or an end is not entered broken"),
        }
    }
}
