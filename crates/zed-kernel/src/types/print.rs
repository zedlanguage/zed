//! Types in the surface syntax (cross-review xe, SYNTHESIS Q5): the text a message shows, which a
//! user can write back.
//!
//! One walk over the whole type graph: the types, and the nodes of the decision diagrams of
//! their tuple and morphism parts. Each node is visited once, keyed by its contents (a type, or
//! a diagram node's interned id), never by its address. A node used twice or more, unless its
//! text is one token, gets a definition `type Tk = …;`, numbered in the order the walk leaves
//! the nodes; a recursive type always gets one, or the name of the definition its text is, so
//! a cycle prints as definitions that refer to each other. So the text is linear in the graph,
//! however many paths its diagrams have.
//!
//! Written by name ([`Type::surface_by_name`]), a recursive type is its group's name for it, as
//! `L(int | #x)`, and a node used twice still gets a definition, placed before the whole text.
//!
//! A diagram node over the tuple type `a`, with `hi` and `lo`, is `a & hi | (lo \ a)`, and
//! the cases where `hi` or `lo` is a leaf drop the parts that are empty. A part kept as its
//! operands prints its connective. A type with every other atom, every tuple length not listed
//! and every struct prints as `_ \ c`, `c` its complement. Every atom, every tuple and every
//! struct alone print as the kind-wide types `#_`, `(..)` and `{..}` (step L1.40d), and an atom
//! `#a` with any payload as `#a(..)`, so `#a(_)` is only the one-tuple payload. An atom's
//! payload of every tuple but not every struct, or the reverse, has no surface type: it prints
//! as `#a(tuple)` or `#a(struct)` and is marked not exact.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use super::TextClass as Class;
use super::TextPlace as At;
use super::bdd::{Bdd, Form, Part};
use super::hash::names_first;
use super::{Lits, Morphism, Node, Rope, Row, Spell, Surface, Surfaces, Tuples, Type, Verdict};
use crate::value::Value;
use order::{Member, NumberType};
use zed_graph::on_cycle;

pub mod defs;
pub mod names;
pub mod order;
mod uses;

#[cfg(test)]
mod bench;

impl Type {
    /// The type in the surface syntax (module `print`).
    pub fn surface(&self) -> Surface {
        self.surface_at(At::Any)
    }

    /// The type in the surface syntax as an operand of any connective, parenthesized unless it
    /// is a tuple or one token.
    #[cfg(test)]
    pub(crate) fn surface_operand(&self) -> Surface {
        self.surface_at(At::Prim)
    }

    /// The type in the surface syntax after `is`, where sec:grammar reads a `TypeUnion` (in
    /// `IsTest` and `IsPat`), parenthesized where it would not be one: an arrow. A union, a
    /// difference and an intersection are written bare, `is int | bool`.
    pub(crate) fn surface_after_is(&self) -> Surface {
        self.surface_at(At::Is)
    }

    /// The type in the surface syntax at `at`, parenthesized where the text would not be read
    /// there as one operand.
    pub(crate) fn surface_at(&self, at: At) -> Surface {
        Printer::default().print(&[(self.clone(), at)]).single()
    }

    /// The type in the surface syntax at `at`, each recursive member written by the name its
    /// group gives it, as `L(int | #x)`; a part of a definition kept unevaluated is unfolded
    /// once (an atom's payload is never a recursive type as a whole: sub-case (c) at
    /// `Printer::force_cycles`). A part used more than once
    /// gets a definition placed before the type, as with [`Type::surface`], and a part used once
    /// is written where it stands, so the text is linear in the type's graph. Several types
    /// written together share their definitions ([`Type::surfaces_by_name`]).
    pub fn surface_by_name(&self, at: At) -> Surface {
        Type::surfaces_by_name(&[(self.clone(), at)]).single()
    }

    /// Several types written by name as [`Type::surface_by_name`] writes one, each at its place,
    /// with one set of definitions for the parts used more than once among them all, which the
    /// caller places before the whole text the types stand in: a refused group's message writes
    /// the types its definitions hold so (`rec::Show`), and a compiler type its kernel parts.
    /// Time `O(t log t)` in the tokens of the texts and the definitions, which are linear in the
    /// types' graph (`Printer::canon`).
    pub fn surfaces_by_name(types: &[(Type, At)]) -> Surfaces {
        Printer {
            by_name: true,
            ..Printer::default()
        }
        .print(types)
    }

    /// Several types written as [`Type::surfaces_by_name`] writes them. With `spell`, each
    /// literal value that `spell` spells is written so, as the program wrote it (DESIGN.md
    /// sec:diagnostics: a message prints a literal as written), and any other in canonical
    /// form, with one lookup in `spell` per literal written; a spelling must read back to the
    /// value it spells. Each type `k` for which `apart[k]` holds is written out where it
    /// stands, never by a name of its own, and not counted as a use of it: a part of a set that a
    /// compiler type prints apart from the rest of the set, in the order of a union (`order`), such
    /// as the atoms of `int | #a | #b` after a tuple. The parts inside it are named as usual. Time
    /// as [`Type::surfaces_by_name`].
    pub fn surfaces_apart(
        types: &[(Type, At)],
        apart: &[bool],
        spell: Option<Spell<'_>>,
    ) -> Surfaces {
        Printer {
            by_name: true,
            spell,
            apart: apart.to_vec(),
            ..Printer::default()
        }
        .print(types)
    }
}

impl Surfaces {
    /// The one text of a single type, with its definitions.
    fn single(mut self) -> Surface {
        let root = self.roots.pop().expect("one type, one text");
        debug_assert!(self.roots.is_empty(), "one type, one text");
        Surface {
            defs: self.defs,
            root,
            exact: self.exact,
        }
    }
}

impl Printer<'_> {
    /// The texts of `types`, each at its place, with one set of definitions.
    fn print(mut self, types: &[(Type, At)]) -> Surfaces {
        let p = &mut self;
        let roots: Vec<(usize, At)> = types
            .iter()
            .map(
                |(t, at)| match p.refer(Item::Ty(None, t.clone())).segs[..] {
                    [Seg::Node(i, _)] => (i, *at),
                    _ => unreachable!("a reference is one node"),
                },
            )
            .collect();
        // A set printed apart is written out where it stands, so it is no use of its node.
        // No count goes below 0: each root's `refer` above added 1 to `uses[i]`, and each root
        // takes off at most that 1, so `uses[i]` stays at least the uses counted otherwise.
        for (&(i, _), _) in roots.iter().zip(&p.apart).filter(|(_, apart)| **apart) {
            p.uses[i] -= 1;
        }
        p.exact = true;
        // A root is written as itself, never as a reference from an earlier print: one printed
        // apart is written out where it stands, and a message's sentence writes a tuple whole.
        p.reuse = defs::active() && !p.anew;
        for &(i, _) in &roots {
            p.walk(i);
        }
        // The elements of a group are ordered by their contents ([`Printer::canon`]), which a
        // reference from an earlier print hides: such a print is made again with every part
        // printed anew, in the time of the print before this step.
        let grouped = |t: &Option<Text>| {
            (t.as_ref().expect("visited").segs.iter()).any(|s| matches!(s, Seg::Group(_)))
        };
        if p.reused.contains(&true) && p.texts.iter().any(grouped) {
            return Printer {
                by_name: p.by_name,
                spell: p.spell,
                apart: std::mem::take(&mut p.apart),
                anew: true,
                ..Printer::default()
            }
            .print(types);
        }
        p.force_cycles();
        p.canon(&roots);
        p.render(&roots)
    }
}

#[derive(Debug)]
enum Seg {
    Str(String),
    Node(usize, At),
    /// Texts that may stand in any order, joined by a separator: the operands of a union or
    /// an intersection, which [`Printer::canon`] orders by their contents.
    Group(Group),
}

#[derive(Debug)]
struct Group {
    sep: &'static str,
    elems: Vec<Vec<Seg>>,
}

/// A string or a node of a text, groups spelled out with their separators.
#[derive(Clone, Copy)]
enum Piece<'a> {
    Str(&'a str),
    Node(usize, At),
}

/// The pieces of segments in order, with a stack of their own; [`Printer::write`] pushes the
/// text of a node it spells out.
struct Pieces<'a> {
    stack: Vec<Frame<'a>>,
}

enum Frame<'a> {
    Segs(std::slice::Iter<'a, Seg>),
    /// A group's elements, and whether the next is the first.
    Elems(&'static str, std::slice::Iter<'a, Vec<Seg>>, bool),
    Close,
}

impl<'a> Pieces<'a> {
    fn new(segs: &'a [Seg]) -> Pieces<'a> {
        Pieces {
            stack: vec![Frame::Segs(segs.iter())],
        }
    }
}

impl<'a> Iterator for Pieces<'a> {
    type Item = Piece<'a>;

    fn next(&mut self) -> Option<Piece<'a>> {
        loop {
            match self.stack.last_mut()? {
                Frame::Segs(it) => match it.next() {
                    None => drop(self.stack.pop()),
                    Some(Seg::Str(s)) => return Some(Piece::Str(s)),
                    Some(Seg::Node(i, at)) => return Some(Piece::Node(*i, *at)),
                    Some(Seg::Group(g)) => {
                        self.stack.push(Frame::Elems(g.sep, g.elems.iter(), true))
                    }
                },
                Frame::Elems(sep, it, first) => match it.next() {
                    None => drop(self.stack.pop()),
                    Some(e) => {
                        let (sep, first) = (*sep, std::mem::replace(first, false));
                        self.stack.push(Frame::Segs(e.iter()));
                        if !first {
                            return Some(Piece::Str(sep));
                        }
                    }
                },
                Frame::Close => {
                    self.stack.pop();
                    return Some(Piece::Str(")"));
                }
            }
        }
    }
}

/// A text with its class.
struct Text {
    segs: Vec<Seg>,
    class: Class,
}

impl Text {
    fn word(s: impl Into<String>, class: Class) -> Text {
        Text {
            segs: vec![Seg::Str(s.into())],
            class,
        }
    }

    /// The text of one or more `items` in any order, joined by `sep`, each operand at `at`;
    /// `class` when there are two or more.
    fn group(items: Vec<Text>, sep: &'static str, at: At, class: Class) -> Text {
        match items.len() {
            1 => items.into_iter().next().expect("one item"),
            _ => Text {
                segs: vec![group(items, sep, at)],
                class,
            },
        }
    }

    /// The text of `items` joined by `sep`, each operand at `at`; `class` when there are two
    /// or more, and `none` when there are none.
    fn joined(items: Vec<Text>, sep: &str, at: At, class: Class, none: &str) -> Text {
        match items.len() {
            0 => Text::word(none, Class::Prim),
            1 => items.into_iter().next().expect("one item"),
            _ => {
                let mut segs = Vec::new();
                for (i, t) in items.into_iter().enumerate() {
                    if i > 0 {
                        segs.push(Seg::Str(sep.into()));
                    }
                    put(&mut segs, t, at);
                }
                Text { segs, class }
            }
        }
    }
}

/// Appends `t` at `at`, parenthesized when its class is not admitted there. A text that is one
/// node is left for rendering to decide, since only then is it known whether the node is named.
fn put(segs: &mut Vec<Seg>, t: Text, at: At) {
    match t.class {
        Class::Of(_) => match t.segs.into_iter().next() {
            Some(Seg::Node(i, _)) => segs.push(Seg::Node(i, at)),
            // A text of class `Of` is made only by `Printer::node`, one `Seg::Node`; `group`
            // and `joined` pass a single item on unchanged; and a list's text takes
            // `first[0].class` only in the cases of its `class` table where the text written
            // is that one item put at `At::Any` with nothing before or after it
            // (every block of a list has a literal, `Bdd::list`, so none is without text).
            _ => unreachable!("a text of class Of is one node"),
        },
        c if at.admits(c) => segs.extend(t.segs),
        _ => {
            segs.push(Seg::Str("(".into()));
            segs.extend(t.segs);
            segs.push(Seg::Str(")".into()));
        }
    }
}

/// The group of `items`, each at `at`.
fn group(items: Vec<Text>, sep: &'static str, at: At) -> Seg {
    debug_assert!(!items.is_empty(), "a group has an element");
    Seg::Group(Group {
        sep,
        elems: items
            .into_iter()
            .map(|t| {
                let mut segs = Vec::new();
                put(&mut segs, t, at);
                segs
            })
            .collect(),
    })
}

/// A token of a text's contents, a node by its rank ([`Printer::canon`]).
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Tok<'a> {
    /// A recursive type: its context, its name, and the type, whose order breaks a tie of names.
    Rec(&'a str, &'a Rope, &'a Type),
    /// Whether the node is named, and the class it has.
    Head(bool, Class),
    Str(&'a str),
    Node(u32, At),
}

/// The tokens of `segs`.
fn toks<'a>(segs: &'a [Seg], rank: &[u32], out: &mut Vec<Tok<'a>>) {
    out.extend(Pieces::new(segs).map(|p| match p {
        Piece::Str(s) => Tok::Str(s),
        Piece::Node(i, at) => Tok::Node(rank[i], at),
    }));
}

/// Orders the elements of each group in `segs` by their tokens, groups inside elements first.
/// The recursion is as deep as groups are nested in one text, which is at most once, since an
/// element is an operand or a literal.
fn sort_groups(segs: &mut [Seg], rank: &[u32]) {
    for s in segs {
        let Seg::Group(g) = s else { continue };
        for e in &mut g.elems {
            sort_groups(e, rank);
        }
        let mut keyed: Vec<(Vec<Tok>, usize)> = g
            .elems
            .iter()
            .enumerate()
            .map(|(k, e)| {
                let mut key = Vec::new();
                toks(e, rank, &mut key);
                (key, k)
            })
            .collect();
        keyed.sort_unstable();
        let order: Vec<usize> = keyed.into_iter().map(|(_, k)| k).collect();
        let mut old: Vec<Option<Vec<Seg>>> =
            std::mem::take(&mut g.elems).into_iter().map(Some).collect();
        g.elems = order
            .into_iter()
            .map(|k| old[k].take().expect("each element is placed once"))
            .collect();
    }
}

/// The atom name whose payloads a type stands for, or `None` for the values themselves.
type Ctx = Option<Arc<str>>;

/// A node of the walk. A part is written as it is, or turned over when its flag is set (the
/// values it does not hold), which only an expression takes: a list turned over is the list
/// of the other value ([`signed`]).
enum Item {
    Ty(Ctx, Type),
    Tuples(Ctx, usize, Part<Row>, bool),
    Morphisms(Part<Morphism>, bool),
}

/// An item's key: its contents, a diagram too. A diagram's interned id is its contents only
/// among the diagrams of one thread (`bdd::Tables`): a type whose unfoldings were made on two
/// threads, or made again on another after the end of a unit (`rec::unfold::Env::forget`),
/// holds equal diagrams of two ids, which keyed by id were two items, and printed with one
/// definition fewer than when made on one thread (item PERF-print-by-name-after-plain). Two
/// keys of one node still compare in O(1): the order of two diagrams reads their digests and
/// stops at a cell of one id (`order` in module `types`).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Ty(Ctx, Type),
    Tuples(Ctx, usize, Part<Row>, bool),
    Morphisms(Part<Morphism>, bool),
}

/// Hashes the contents' name-free digests, never the names-aware ones or an expression's id:
/// two keys equal have equal name-free digests in every mode of the order, since
/// [`Type::cmp`] and the order of two expressions answer equal only on the same node or on
/// tied digests, and `digests_cmp` ties only on equal name-free digests whether names are left
/// out ([`super::hash::blind`]) or compared first ([`names_first`]). The names-aware digest
/// differs between two types `blind` finds equal.
impl std::hash::Hash for Key {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        fn expr<A: super::bdd::Literal>(p: &Part<A>, h: &mut impl std::hash::Hasher) {
            match p {
                Part::Bdd(b) => b.digest().hash(h),
                Part::Expr(e) => e.digest.hash(h),
            }
        }
        std::mem::discriminant(self).hash(h);
        match self {
            Key::Ty(c, t) => {
                c.hash(h);
                t.digest().hash(h);
            }
            Key::Tuples(c, n, p, not) => {
                (c, n, not).hash(h);
                expr(p, h);
            }
            Key::Morphisms(p, not) => {
                not.hash(h);
                expr(p, h);
            }
        }
    }
}

impl Item {
    fn key(&self) -> Key {
        match self {
            Item::Ty(c, t) => Key::Ty(c.clone(), t.clone()),
            Item::Tuples(c, n, p, not) => Key::Tuples(c.clone(), *n, p.clone(), *not),
            Item::Morphisms(p, not) => Key::Morphisms(p.clone(), *not),
        }
    }
}

/// The part `p`, or the values it does not hold when `not` is set, in the one form an item
/// takes: a list turned over is the list of the other value, and a complement `!q` turned over
/// is `q`.
fn signed<A: super::bdd::Literal>(p: &Part<A>, not: bool) -> (Part<A>, bool) {
    let mut p = p;
    let mut not = not;
    loop {
        match p {
            Part::Bdd(b) => return (Part::Bdd(if not { b.not() } else { b.clone() }), false),
            Part::Expr(e) => match (e.form(), not) {
                (Form::Not(q), true) => {
                    p = q;
                    not = false;
                }
                _ => return (p.clone(), not),
            },
        }
    }
}

#[derive(Default)]
struct Printer<'s> {
    /// Each item's node, by its key.
    // Complexity tradeoff (PERF-print-by-name-after-plain): an ordered map took O(log n)
    // comparisons of keys per reference, each reading a node's digests, out of cache once the
    // map is large: `Type::cmp` and the map's search were a sixth of a print of a ring of
    // 16,000 parts, and grew 13 times from 2,000. Used: a hash of the name-free digests
    // ([`Key`]'s `Hash`), O(1) expected per reference. Nothing reads the map in order: its
    // one iteration ([`Printer::remember`]) puts each key into an ordered table of its own.
    // Keys whose hashes tie (renamed recursive definitions have equal name-free digests, and in
    // the build with short addresses a digest keeps 8 bits) are kept in their order
    // ([`crate::digest::TiedMap`], PERF-row-hash-tied-digest), O(log b) comparisons for a key
    // whose hash `b` others share, where a hashed map compared it with all `b`.
    index: crate::digest::TiedMap<Key, usize>,
    texts: Vec<Option<Text>>,
    uses: Vec<u32>,
    /// A recursive type, named however often it is used: its context, its name and the
    /// type, by whose order (its key) names alike are ranked ([`Printer::canon`]).
    // Complexity tradeoff: the name was kept as a string, made from the type's rope in time
    // linear in its length; the names of parts nested `k` deep, each spelling out the parts
    // inside it, then took O(k^2) to write out (printing 2,000 such parts took 41.1 times the
    // instructions of 250, measured for FAIL-print-height-cycle-seed). Used: the rope the type
    // already keeps, compared byte by byte only up to where two names differ, so a name costs
    // nothing to keep and a comparison no more than on the strings, in the same order
    // (9.27 times at the same sizes).
    forced: Vec<Option<(String, Rope, Type)>>,
    /// A recursive type written by name and unfolded where it stands, as a part kept
    /// unevaluated is ([`Printer::ty`]): its node, its context and the type. One on a cycle of
    /// the texts is given a definition after the walk ([`Printer::force_cycles`]).
    unfolded: Vec<(usize, Ctx, Type)>,
    /// The nodes in the order the walk leaves them.
    post: Vec<usize>,
    /// Each node's item, until visited.
    items: Vec<Option<Item>>,
    /// The items visited, kept for the printer's life. A diagram node is keyed by its id
    /// ([`Item::key`]), and a node is shared among parts only while one holds it (`bdd::cell`
    /// keeps a weak table): a diagram made again by an operand, as `!x` of a literal `x` turned
    /// over twice is, has the id of the one met first only while that one is alive. Dropped
    /// once visited, the node met first would be freed or kept by the order of the walk, and
    /// with it whether the two uses are one node with a definition or two written out, which
    /// depends on the order of the atoms (FAIL-print-alias-atom-order). Kept, a node is one node
    /// however often it is made, at no cost but the items' memory, which the walk held already.
    held: Vec<Item>,
    exact: bool,
    /// Whether a recursive member is written by its group's name for it
    /// ([`Type::surface_by_name`]).
    by_name: bool,
    /// The value of each part met outside every atom, by its node's id ([`Printer::outside`]).
    outsides: HashMap<u64, bool>,
    /// Whether each part of the morphisms met is a meet of morphism types and nothing else, by
    /// its node's id ([`Printer::meet_of_literals`]).
    meets: HashMap<u64, bool>,
    /// The program's own spelling of a literal value, where a message has one
    /// ([`Type::surfaces_apart`]).
    spell: Option<Spell<'s>>,
    /// Whether each root is printed apart, written out where it stands
    /// ([`Type::surfaces_apart`]); a root past its end is not.
    apart: Vec<bool>,
    /// Whether a part met now is taken from an earlier print of the message where it was
    /// printed ([`printed`]): on while the walk runs, and never in a print made again
    /// with every part printed anew ([`Printer::print`]).
    reuse: bool,
    /// Whether this print is made again with every part printed anew.
    anew: bool,
    /// Whether each node is a part taken from an earlier print, its text that print's reference.
    reused: Vec<bool>,
    /// Whether each node's own literals are spelled so wherever a message is written
    /// ([`super::Spelled::everywhere`]); and that of the node being given its text.
    fixed: Vec<bool>,
    fixed_now: bool,
    /// The nodes each node's text refers to, once for each use [`Printer::refer`] counts.
    kids: Vec<Vec<usize>>,
    /// The node whose text is being made, to which [`Printer::refer`] adds a child.
    building: Option<usize>,
}

/// A part's key in the table of parts printed so far ([`printed`]): whether written by name,
/// whether with the program's spellings, and the item's key.
type Printed = (bool, bool, Key);

/// The parts printed so far for the message's table of definitions, each with its reference
/// and class, kept in that table ([`defs::with_kept`]) so that they end with it.
#[derive(Default)]
struct Kept {
    parts: BTreeMap<Printed, (String, Class)>,
    /// The reference of each part placed before its body, as a cycle's parts are
    /// ([`Printer::collect`]), by its key: a later print of the message that meets the same
    /// part takes it, so the message defines the cycle once (FAIL-print-cycle-defined-twice).
    cycles: BTreeMap<Printed, String>,
}

/// Runs `f` on the parts kept so far, made empty if there are none.
fn with_kept<R>(f: impl FnOnce(&mut Kept) -> R) -> Option<R> {
    defs::with_kept(|kept| {
        let kept = kept.get_or_insert_with(|| Box::new(Kept::default()));
        f(kept
            .downcast_mut::<Kept>()
            .expect("only the printer keeps parts"))
    })
}

/// The reference and class of a part an earlier print of the message wrote, and which prints
/// the same in any type ([`Printer::remember`]): a type that holds it writes the reference
/// rather than print it again, so the steps of a derivation that each print the next of a
/// chain print each part once (steps MSG-derive-print-per-message, MSG-derive-print-unions).
fn printed(key: &Printed) -> Option<(String, Class)> {
    with_kept(|kept| kept.parts.get(key).cloned()).flatten()
}

/// Keeps `parts` for [`printed`], each with its reference and class.
fn keep(parts: impl Iterator<Item = (Printed, String, Class)>) {
    with_kept(|kept| {
        for (key, name, class) in parts {
            kept.parts.entry(key).or_insert((name, class));
        }
    });
}

enum Step {
    Enter(usize),
    Leave(usize),
}

/// Pushes the nodes `segs` names, so that the first is visited first.
fn push_children(stack: &mut Vec<Step>, segs: &[Seg]) {
    let children: Vec<usize> = Pieces::new(segs)
        .filter_map(|p| match p {
            Piece::Node(j, _) => Some(j),
            Piece::Str(_) => None,
        })
        .collect();
    stack.extend(children.into_iter().rev().map(Step::Enter));
}

impl Printer<'_> {
    /// The text that refers to `item`, counting the use; `put` says where it stands.
    /// A part an earlier print of the message wrote, and which prints the same in any type
    /// ([`Printer::remember`]), is the reference that print gave it, a node with no item to
    /// visit.
    fn refer(&mut self, item: Item) -> Text {
        let key = item.key();
        let i = match self.index.get(&key) {
            Some(&i) => i,
            None => {
                let i = self.texts.len();
                let probe = (self.by_name, self.spell.is_some(), key);
                let found = match self.reuse {
                    true => printed(&probe),
                    false => None,
                };
                self.index.insert(probe.2, i);
                self.uses.push(0);
                self.forced.push(None);
                self.fixed.push(true);
                self.reused.push(found.is_some());
                self.kids.push(Vec::new());
                match found {
                    Some((name, class)) => {
                        self.texts.push(Some(Text::word(name, class)));
                        self.items.push(None);
                    }
                    None => {
                        self.texts.push(None);
                        self.items.push(Some(item));
                    }
                }
                i
            }
        };
        self.uses[i] += 1;
        if let Some(parent) = self.building {
            self.kids[parent].push(i);
        }
        Text {
            segs: vec![Seg::Node(i, At::Any)],
            class: Class::Of(i),
        }
    }

    /// Visits every node from the root, depth first with a stack of its own, children in the
    /// order their texts name them, so a node leaves after every node its text names, except
    /// one it is inside of (a recursive type's cycle).
    fn walk(&mut self, root: usize) {
        let mut stack = vec![Step::Enter(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Leave(i) => self.post.push(i),
                Step::Enter(i) => {
                    let Some(item) = self.items[i].take() else {
                        continue;
                    };
                    self.fixed_now = true;
                    self.building = Some(i);
                    let text = self.text(&item);
                    self.building = None;
                    self.fixed[i] = self.fixed_now;
                    self.held.push(item);
                    stack.push(Step::Leave(i));
                    push_children(&mut stack, &text.segs);
                    self.texts[i] = Some(text);
                }
            }
        }
    }

    /// The walk's order again, over the texts as [`Printer::canon`] ordered them, from each root
    /// in turn.
    fn order(&mut self, roots: &[(usize, At)]) {
        let mut seen = vec![false; self.texts.len()];
        self.post.clear();
        let mut stack: Vec<Step> = roots.iter().rev().map(|&(i, _)| Step::Enter(i)).collect();
        while let Some(step) = stack.pop() {
            match step {
                Step::Leave(i) => self.post.push(i),
                Step::Enter(i) => {
                    if std::mem::replace(&mut seen[i], true) {
                        continue;
                    }
                    stack.push(Step::Leave(i));
                    push_children(&mut stack, &self.texts[i].as_ref().expect("visited").segs);
                }
            }
        }
    }

    /// Whether node `i` gets a definition: a recursive type, or a node used twice or more
    /// whose text is more than one token.
    fn named(&self, i: usize) -> bool {
        let text = self.texts[i].as_ref().expect("visited");
        let token = matches!(&text.segs[..], [Seg::Str(s)] if !s.contains([' ', '(', ',']));
        self.forced[i].is_some() || (self.uses[i] >= 2 && !token)
    }

    /// Gives a definition to each recursive type unfolded where it stands ([`Printer::ty`]) that
    /// lies on a cycle of the texts once the edges out of the recursive types with a definition
    /// are cut, as the printer without names gives every recursive type one: written out where
    /// it stands, such a cycle would have no end. Every cycle of the texts passes through a
    /// recursive type, the one way a type holds itself, so afterward every cycle passes through
    /// one with a definition, as [`Printer::heights`] needs. Which types are named depends only
    /// on the texts, not on the order of the walk.
    // Complexity tradeoff: naive, a search from each unfolded type for a path back to itself,
    // O(k (n + e)) for k such types in a graph of n nodes and e references. Used: the strongly
    // connected components of the whole graph at once, by Tarjan's algorithm (R. E. Tarjan,
    // "Depth-first search and linear graph algorithms", SIAM Journal on Computing 1(2):146-160,
    // 1972, doi:10.1137/0201010, read 2026-11-20, PDF, the journal's scan, verification only.
    // Section 4, pp. 156-157: a depth-first search numbers the vertices; "LOWLINK (v) is the
    // smallest vertex which is in the same component as v and is reachable by traversing zero
    // or more tree arcs followed by at most one frond or cross-link"; Lemma 12, v is the root
    // of a strongly connected component "if and only if LOWLINK (v) = v"; Theorem 13, p. 157,
    // the algorithm "requires O(V, E) space and time"; the code is `zed_graph::on_cycle`),
    // O(n + e) time and O(n + e) memory for the edge lists, none when no type was unfolded.
    // Every unfolded type on a cycle is named, not a least set of them that cuts every cycle
    // (a least feedback vertex set, NP-hard), so a cycle through two of them names both, as
    // the printer without names would.
    // Claim: every cycle of the texts passes through a recursive type that is either named in
    // `forced` or pushed on `unfolded` by [`Printer::ty`], so naming the unfolded ones on a
    // cycle leaves no cycle for [`Printer::heights`] (which else panics on user input, "every
    // cycle passes through a recursive type with a definition"). Proof (PROOF-sweep-zed-kernel;
    // (c) by PROOF-kernel-open-subcases), in sub-cases (a), (b) and (c), all proved:
    // - Depth. A node of parts holds the column types of the rows its tuple parts name, its
    //   atoms' payloads, and the three types of each morphism its morphism part names; a
    //   recursive node holds the arguments of its key, not its unfolding, which
    //   `Rec::unfolding` makes later and keeps in a cache. Each is an `Arc` whose fields are set
    //   when it is made, so a type holds only older types, and its depth `d` (0 for one that
    //   holds none, else one more than the greatest depth of a type it holds) is finite. A node
    //   of the texts has the depth `D`: `d(t)` for `Item::Ty(_, t)`, and for `Item::Tuples` or
    //   `Item::Morphisms` of a part `p`, one more than the greatest `d` of a type its literals
    //   hold.
    // - Edges. Every `Seg::Node` of a text is made by `refer`; its calls fall in five kinds.
    //   E1, to a type the node holds: a row's columns (`row`), an atom's payload (`atom`), the
    //   arguments of a member written `name(args)`, the three types of a morphism (`morphism`),
    //   and the types of an arrow folded by `meet_text`, each `==` a literal's own field or
    //   `Never` (its `named`), so the same node as that field's. `D` drops. E2, from
    //   `Item::Ty(_, t)` to its own tuple or morphism part (`tuples`, `items`): `D` does not
    //   grow. E3, from a part to an operand of its expression, turned over or not (`part`):
    //   `D` does not grow, and the operand is a strict subexpression, so a chain of E3 ends.
    //   E4, from `Item::Ty(_, t)` to a type made there: `!t` (the arm with every atom, the rest
    //   of the tuples and the structs), `payloads() - t` (the same arm in a payload) and
    //   `except` (`tuples`, the rest of the tuples), and, as E1 above, an atom's payload turned
    //   over, `payloads() - P` (`items` with every atom, and the payloads of `!t`). E5, from a
    //   recursive node to its unfolding: outside a payload and by name it is `name(args)`, E1;
    //   else `ty` pushes it on `unfolded` or sets `forced` and refers to the body. Only E5 can
    //   make `D` grow.
    // - E4 keeps depth, for a payload `P` that is a node of parts. The code of `bdd` is
    //   generic over `Literal`, which has no constructor, so every literal of a `not`, `zip` or
    //   `minus` is one of its operands', and `payloads()` holds no type; so `!t`, `payloads() -
    //   t` and `except` hold the columns of `t`'s rows and morphisms, and, as payloads, the
    //   types `payloads() - P` for payloads `P` of `t`; and `payloads() - P` holds only the
    //   columns of `P`'s rows, since `P.p()` of a node of parts is its own parts. So the target
    //   has `D` at most `d(t)`. Nor does the target take an E4 arm of its own: `!t` has a finite
    //   set of atoms and no rest of the tuples, `payloads() - t` no structs and no rest, and
    //   `except` no atoms, no structs and no rest (`Tuples::not` turns `rest` over).
    // - (a) Proved, given E4 keeps depth: every cycle has an E5 edge. Around a cycle `D`
    //   returns to its start, so a cycle with an E1 edge also has an edge where `D` grows, an
    //   E5. A cycle with neither has `D` constant and only E2, E3 and E4 edges: a part node has
    //   no edge out but E1 and E3, so once at a part the cycle stays among parts on E3 edges,
    //   which end; with no part node, only E4 edges, and the target of one takes no E4. So the
    //   cycle runs through a recursive node in `forced` or `unfolded`. The edges out of
    //   `forced` are cut below, so a cycle left passes through `unfolded`, which is named.
    // - (b) Proved: E4 keeps depth for every payload that is a node of parts, as above.
    // - (c) Proved: no payload is a recursive node as a whole, so (b) covers every payload.
    //   An `AtomPart` is visible only in the module `types` and its submodules, where only
    //   `types.rs` and `empty.rs` build one (read 2026-11-20 by a search for `AtomPart {`);
    //   its payload is set only by the following, each
    //   giving a node of parts, by induction over the order the types were made:
    //   `AtomPart::all` and `AtomPart::none` (`PAYLOADS`, a union of two universes, and
    //   `EMPTY`); `AtomPart::zip` (`Type::zip`) and `AtomPart::not` (`Type::payloads() - p`,
    //   `Type::minus`); `Type::atom_part` (`Type::empty()`, or `payload & Type::payloads()`, a
    //   `Type::zip`); `flat_part` and `nonflat_part` in empty.rs (`Type::empty()`,
    //   `Type::payloads()`, or a payload already made, copied); `Atoms::zip`, `join`, `not`,
    //   `minus` and `set` (an `AtomPart::zip` or `not`, or a part already made, copied); and
    //   `Type::rewrite_levels` (what `level` gives, which it asserts in every build is a node of
    //   parts). `Type::zip` answers an operand only from `zip_at_once`, which requires both
    //   operands to be nodes of parts (`let (Node::Parts(..), Node::Parts(..))`), and else
    //   `Type::new`; `Type::minus` answers `self` only when it is `EMPTY`, and else
    //   `Type::new`; and `Type::new` makes `Node::Parts` on both of its paths. So `ty` never
    //   meets a recursive node with `ctx` set: `ctx` is set only at an atom's payload
    //   (`Item::Ty(Some(name), part.payload)` in `atom`), at the E4 targets `&all - t` and
    //   `except` (built by `Type::minus` and `Type::zip`, nodes of parts), and at a recursive
    //   node's body, which carries on a `ctx` it was given. The unfolding taken in `ty` for a
    //   recursive node with `ctx` set is kept as written, though no input reaches it.
    // Tests: `a_cycle_of_parts_written_by_name_is_defined`,
    // `groups_whose_printing_met_a_cycle_without_a_recursive_type_build_and_print`,
    // `a_cycle_of_parts_inside_every_value_but_one_atom_payload_is_defined` (both E4 edges over
    // a payload whose column is recursive), and a sweep of 240,000 `gen_cells` seeds (480,000
    // systems) with no panic.
    fn force_cycles(&mut self) {
        if self.unfolded.is_empty() {
            return;
        }
        let edges: Vec<Vec<usize>> = (self.texts.iter().zip(&self.forced))
            .map(|(text, forced)| match forced {
                Some(_) => Vec::new(),
                None => Pieces::new(&text.as_ref().expect("visited").segs)
                    .filter_map(|p| match p {
                        Piece::Node(j, _) => Some(j),
                        Piece::Str(_) => None,
                    })
                    .collect(),
            })
            .collect();
        let cyclic = on_cycle(&edges);
        for (i, ctx, t) in std::mem::take(&mut self.unfolded) {
            if cyclic[i] {
                let ctx_name = ctx.as_deref().unwrap_or("").to_string();
                self.forced[i] = Some((ctx_name, t.rope(), t));
            }
        }
    }

    /// Orders the elements of every group by their contents, so that the text does not depend
    /// on the order the parts' operands and literals were found in, which follows the atoms'
    /// digests (step BDD-atom-order). Each node gets a rank by its contents, as in the tree
    /// isomorphism test of Aho, Hopcroft and Ullman (A. V. Aho, J. E. Hopcroft and J. D. Ullman,
    /// "The Design and Analysis of Computer Algorithms", Addison-Wesley, 1974, no DOI; read
    /// 2026-11-20 in a scanned copy from LibGen, kept out of the repository and used only to
    /// check this comment: section 3.2, "Radix sorting", Example 3.2, pp. 84-85, with Theorem
    /// 3.3 and its proof, pp. 85-86. Step 1: "Assign to all leaves of T1 and T2 the integer 0."
    /// Then, one level at a time towards the roots, each nonleaf gets the tuple of its sons'
    /// integers in nondecreasing order, the tuples of a level are sorted by Algorithm 3.2 (a
    /// lexicographic radix sort of strings of varying length), and the distinct tuples get the
    /// integers 1, 2, ... in sorted order; the trees are isomorphic when the roots get the same
    /// integer, in O(n) time. The corollary on p. 86 puts a vertex's label first in its tuple,
    /// which is what the tokens do here. This agrees with the secondary sources checked before
    /// the book was read, F. Ingels, "Revisiting Tree Isomorphism: An Algorithmic
    /// Bric-a-Brac", arXiv:2309.14441, and NetworkX's documentation): the nodes are taken by
    /// height, those of one height ordered by their tokens, a child by its rank, each group's
    /// elements sorted first; a recursive type is a leaf ranked by its name, since every cycle
    /// passes through one. The walk's order is then found again, and with it the names'
    /// numbers. Departures: the book's level of a vertex is "the height of the tree minus the
    /// depth of v" (section 2.4, p. 52), so leaves sit on many levels and the book puts each
    /// level's leaves at the front of its list; here the texts form a graph cut at recursive
    /// types, which has no single root to count depth from, and the nodes go by their own
    /// height, which also ranks every child of a node before the node. The sort is a
    /// comparison sort, not the book's radix sort, hence `O(t log t)` below. Tests:
    /// `random_types_print_alike_in_every_order_of_their_atoms` and
    /// `a_union_of_tuple_types_less_another_prints_alike_in_every_order` catch a text that
    /// depends on the atoms' order; neither checks the `O(t log t)` bound.
    // Complexity tradeoff: the tokens of one height are sorted together, so the time is
    // `O(t log t)` in the tokens of all texts, against `O(t)` for the walk alone.
    fn canon(&mut self, roots: &[(usize, At)]) {
        let n = self.texts.len();
        let height = self.heights();
        let mut levels: Vec<Vec<usize>> = Vec::new();
        for (i, h) in height.into_iter().enumerate() {
            let h = h.expect("every node gets a height");
            if levels.len() <= h {
                levels.resize_with(h + 1, Vec::new);
            }
            levels[h].push(i);
        }
        let mut rank = vec![u32::MAX; n];
        let mut next = 0;
        for level in &levels {
            for &i in level {
                let text = self.texts[i].as_mut().expect("visited");
                sort_groups(&mut text.segs, &rank);
            }
            let mut sigs: Vec<(Vec<Tok>, usize)> =
                level.iter().map(|&i| (self.sig(i, &rank), i)).collect();
            sigs.sort_unstable();
            let mut last = None;
            for (sig, i) in &sigs {
                if last != Some(sig) {
                    next += 1;
                    last = Some(sig);
                }
                rank[*i] = next;
            }
        }
        self.order(roots);
    }

    /// Each node's height in the graph of the texts with the edges out of the recursive types
    /// with a definition cut, a recursive type at height 0. Every cycle passes through a
    /// recursive type with a definition ([`Printer::force_cycles`]), so that graph has no cycle.
    /// The walk's order is not an order of it in which a node comes after those it names: the walk
    /// may enter a cycle at a node that is not a recursive type, such as a tuple diagram that a
    /// recursive type's unfolding shares with a part of its body kept unevaluated
    /// (`R0 = ((#a | #b), (#a | #b | R0)) \ (#b, #a)` enters at the diagram of `R0`'s unfolding,
    /// which names the part `#a | #b | R0`, whose unfolding names the diagram), and then the node
    /// that closes the cycle leaves before the one it names. So the heights come from a search of
    /// their own, depth first with a stack, each node entered once: time linear in the tokens of
    /// all texts.
    fn heights(&self) -> Vec<Option<usize>> {
        let mut height: Vec<Option<usize>> =
            self.forced.iter().map(|f| f.as_ref().map(|_| 0)).collect();
        let mut entered: Vec<bool> = height.iter().map(Option::is_some).collect();
        let mut stack = Vec::new();
        for &start in &self.post {
            stack.push(Step::Enter(start));
            while let Some(step) = stack.pop() {
                let segs = |i: usize| &self.texts[i].as_ref().expect("visited").segs;
                match step {
                    Step::Enter(i) => {
                        if std::mem::replace(&mut entered[i], true) {
                            continue;
                        }
                        stack.push(Step::Leave(i));
                        push_children(&mut stack, segs(i));
                    }
                    Step::Leave(i) => {
                        let h = Pieces::new(segs(i))
                            .filter_map(|p| match p {
                                Piece::Node(j, _) => Some(height[j].expect(
                                    "every cycle passes through a recursive type with a definition",
                                )),
                                Piece::Str(_) => None,
                            })
                            .max()
                            .unwrap_or(0);
                        height[i] = Some(h + 1);
                    }
                }
            }
        }
        height
    }

    /// The tokens of node `i`, its children by `rank`.
    fn sig<'a>(&'a self, i: usize, rank: &[u32]) -> Vec<Tok<'a>> {
        if let Some((ctx, name, t)) = &self.forced[i] {
            return vec![Tok::Rec(ctx, name, t)];
        }
        let text = self.texts[i].as_ref().expect("visited");
        let class = match text.class {
            Class::Of(j) => Class::Of(rank[j] as usize),
            c => c,
        };
        let mut sig = vec![Tok::Head(self.named(i), class)];
        toks(&text.segs, rank, &mut sig);
        sig
    }

    fn text(&mut self, item: &Item) -> Text {
        match item {
            Item::Ty(ctx, t) => self.ty(ctx, t),
            Item::Tuples(ctx, n, p, not) => self.part(
                p,
                *not,
                &|me: &mut Printer, r: &Row| me.row(ctx, *n, Some(r)),
                &|me: &mut Printer| me.row(ctx, *n, None),
                &|c: &Part<Row>, not| Item::Tuples(ctx.clone(), *n, c.clone(), not),
                // `&` of tuple types is their meet to a program as to the kernel.
                &|_: &mut Printer, _: &[Row]| None,
            ),
            Item::Morphisms(p, not) => match (!*not).then(|| self.folded(p)).flatten() {
                Some(t) => t,
                None => self.part(
                    p,
                    *not,
                    &|me: &mut Printer, m: &Morphism| me.morphism(m),
                    &|_: &mut Printer| every_morphism(),
                    &|c: &Part<Morphism>, not| Item::Morphisms(c.clone(), not),
                    &|me: &mut Printer, ms: &[Morphism]| me.meet_text(ms),
                ),
            },
        }
    }

    /// The text of a part of the morphisms that is the meet of two or more morphism types and
    /// nothing else, as the one morphism type it is. A program reads `A & B` of two function
    /// types as an overload (DESIGN.md sec:type_language, "Relation to semantic subtyping"
    /// (2)), the arrows of one function, not as the meet of the two sets, so `&` would read
    /// back as another type.
    ///
    /// Proof that the two are one set: a function `f` lies in `L1 .. U1 -> V1` and in
    /// `L2 .. U2 -> V2` exactly when `L1 ⊆ dom f ⊆ U1`, `L2 ⊆ dom f ⊆ U2` and its values lie
    /// in `V1` and in `V2`, that is when `L1 | L2 ⊆ dom f ⊆ U1 & U2` and its values lie in
    /// `V1 & V2`: the members of `(L1 | L2) .. (U1 & U2) -> (V1 & V2)`. By induction the same
    /// holds of any number of them, as the kernel decides such a meet (module `empty`, the
    /// meet of morphism literals). A program writes `L .. U` only with `L` within `U`: where
    /// the kernel builds a value of `L` outside `U`, no domain lies between them, the meet is
    /// empty and is written `Never`; where `U` is also within `L`, the two are one type and
    /// the arrow is written `U -> V`. Where the kernel decides neither way, `None`, and the
    /// meet is written with its connective as before.
    // Complexity tradeoff: whether a node is such a meet is kept by its id
    // ([`Printer::meet_of_literals`]), so the test costs each node once for the printer's life.
    // The literals of a node found to be one are then read from its nodes, each once, and
    // joined with [`Type::union_all`] and [`Type::meet_all`]: linear in the nodes of that
    // meet, and its operands are not printed through it. A meet that is an operand of another
    // meet and is also printed elsewhere is read again there: the naive `&` text would share
    // it by name, but reads back as another type, so the folded text is the one used. The two
    // bounds are then compared by the kernel ([`Type::subtype_verdict`]), once per meet
    // printed, a cost the `&` text did not have.
    fn folded(&mut self, p: &Part<Morphism>) -> Option<Text> {
        if !self.meet_of_literals(p) {
            return None;
        }
        match p.view() {
            Ok(_) => {
                let ms = p.forced().0;
                self.meet_text(&ms)
            }
            // `meet_of_literals(p)` held, so `p` is a list or an `&` of two parts it holds of;
            // an `&` of two lists that are each the meet of their atoms is never made, so `p`
            // is a list. Proof. (1) A list equal to the meet `a1 & … & ak` of its atoms is a
            // chain under `And` (one atom's literal for k = 1): a list is in its one form (module
            // `list` in `bdd.rs`), whose first block holds every literal under which the
            // function is constant, all of one value; the meet is `false` under each `!ai` and
            // under no other literal, so the first block is `{!a1, …, !ak}` of value `false`, and
            // these are all the atoms, so no block follows and the default is `true`: the chain.
            // (2) A `Form::And` is made by `Part::connect`, called with `Op::And` by
            // `Connect::zipped` (after `Bdd::zip_chain`, which answers with a list whenever one
            // operand is a list that is a chain under `And`, literals included, and the other a
            // list) and by `xor::meet` (whose two lists are literals, joined as a list there);
            // `Part::of_form` makes again only a form an expression had. So no `&` has two
            // operands each such a list; and since an `&` it holds of has two operands it holds
            // of, the lowest such `&` would have two lists, which (2) excludes. cover4 asked
            // whether (1) holds (COMPLETENESS.md); the test
            // `l01_23_subtyping`
            // `printed_meets::a_meet_joined_to_an_exclusive_or_keeps_its_connective` reaches the
            // `&` arm of `meet_of_literals` with one operand no meet.
            Err(_) => unreachable!("a meet of morphism literals is one list"),
        }
    }

    /// The text of the meet of the morphism types `ms`, two or more, as the one morphism type
    /// it is, or `Never`, as [`Printer::folded`] proves; `None` for fewer than two, where the
    /// kernel decides neither whether the lower bound is within the upper nor that it is not,
    /// or where the arrow would name a type the literals do not.
    ///
    /// The arrow is written only when each type it names, its bounds and its value, is empty,
    /// a type whose parts hold no other type, or a type some literal's own text names. Each
    /// such type is then a node the text of the literals would refer to as well
    /// ([`Printer::refer`] keys a node by its type), the node `Never`, which names nothing, or
    /// a node every node below which holds a subset of its scalars and bare atoms (the text of
    /// a type names only types its parts hold, or groups of its own parts), none of them a
    /// recursive type; so the folded text adds no edge to the graph of the texts that could
    /// close a cycle, since every cycle of the texts passes through a recursive type
    /// ([`Printer::force_cycles`]), and every cycle still passes through a recursive type with
    /// a definition, as [`Printer::heights`] needs. A type built here could hold a cycle
    /// of its own the printer has no name for: in `R0 = (R0, R1) | (int -> R1);
    /// R1 = (R0 & (int -> R0)) | (int, R1)`, the value of `(int -> R1) & (int -> R0)` is
    /// `R1 & R0`, which holds `int -> (R1 & R0)`. Such a meet keeps its connective.
    // Complexity tradeoff: each built type is compared with the types of the k literals, 3k
    // comparisons, each O(1) unless the two are equal (two types of different digests compare
    // at their digests). Naive: name every built type and add its cycles to the printer's
    // definitions, a second walk of the type for each meet printed.
    fn meet_text(&mut self, ms: &[Morphism]) -> Option<Text> {
        if ms.len() < 2 {
            return None;
        }
        let lower = Type::union_all(ms.iter().map(|m| m.guarantee.clone()));
        let upper = Type::meet_all(ms.iter().map(|m| m.permission.clone()));
        let value = Type::meet_all(ms.iter().map(|m| m.value.clone()));
        // A type whose parts hold no other type ([`Type::holds_no_type`]), as the permission
        // `int` of `partial(int | #a, bool) & partial(int | #b, bool)`, reaches no node and no
        // recursive type least of all, so it adds no edge that could close a cycle, as a type
        // a literal names adds none (row FAIL-print-meet-unnamed-bound).
        let named = |t: &Type| {
            *t == Type::empty()
                || t.holds_no_type()
                || (ms.iter()).any(|m| m.guarantee == *t || m.permission == *t || m.value == *t)
        };
        // Where the upper bound is also within the lower, the two are one set (the verdict
        // `Empty` puts the lower within the upper), so the arrow may be written with either as
        // both bounds, and is written with one a literal names. The upper bound is often a
        // meet node no literal names, as `a & (a | v)` for the literals `a -> rat` and
        // `(a | v) ->? rat`, whose lower bound `a` a literal names (seed 76 of
        // `parens::the_kernel_printer_reads_back_and_holds_no_parentheses_the_grammar_does_not_need`).
        // Complexity tradeoff: `upper <: lower` is now asked also where the upper bound is not
        // named, one more kernel comparison for such a meet, where before the meet was given up
        // and kept its connective, which reads back as an overload.
        match lower.subtype_verdict(&upper) {
            Verdict::Inhabited => Some(Text::word("Never", Class::Prim)),
            Verdict::Empty if !named(&value) => None,
            Verdict::Empty if (named(&upper) || named(&lower)) && upper.subtype(&lower) => {
                let one = if named(&upper) { upper } else { lower };
                Some(self.morphism(&Morphism::new(one.clone(), one, value)))
            }
            Verdict::Empty if named(&lower) && named(&upper) => {
                Some(self.morphism(&Morphism::new(lower, upper, value)))
            }
            Verdict::Empty | Verdict::Refused(_) => None,
        }
    }

    /// Whether a part of the morphisms is the meet of its atoms and nothing else: a list
    /// that is the meet of its atoms, or a meet of two such parts.
    ///
    /// A list is the meet of its atoms when [`Part::forced`] finds each of them taken and none
    /// refused, and the list holds where every atom is taken. By the three-valued logic of
    /// `forced`, refusing any one atom, whatever the others, makes the list `false`, so the
    /// one setting where it can hold is the one where every atom is taken; it holds there, so
    /// it is the meet of the atoms. An `or` or a complement is never taken for one: a part
    /// that is such a meet but kept in another form is written as before, with its connective.
    // Complexity tradeoff: each node is decided once and kept by its id for the printer's life,
    // with a stack of its own, as [`Printer::outside`] is; a list costs one `forced`, O(n log n)
    // in its nodes, and one evaluation. Naive version: decide each node printed afresh, which
    // walks the meets below it again, O(n²) for `n` meets inside each other.
    fn meet_of_literals(&mut self, p: &Part<Morphism>) -> bool {
        if let Some(&v) = self.meets.get(&p.id()) {
            return v;
        }
        let mut stack = vec![(p.clone(), false)];
        while let Some((q, ready)) = stack.pop() {
            let id = q.id();
            if self.meets.contains_key(&id) {
                continue;
            }
            let v = match q.view() {
                Ok(_) => {
                    q.is_leaf().is_none() && {
                        let (taken, refused) = q.forced();
                        refused.is_empty()
                            && taken.len() == q.distinct_atoms().len()
                            && q.eval(&|_| true)
                    }
                }
                Err(Form::And(x, y)) => {
                    if !ready {
                        stack.push((q.clone(), true));
                        for o in [x, y] {
                            if !self.meets.contains_key(&o.id()) {
                                stack.push((o.clone(), false));
                            }
                        }
                        continue;
                    }
                    self.meets[&x.id()] && self.meets[&y.id()]
                }
                Err(_) => false,
            };
            self.meets.insert(id, v);
        }
        self.meets[&p.id()]
    }

    fn ty(&mut self, ctx: &Ctx, t: &Type) -> Text {
        if let Node::Rec(r) = &*t.0 {
            // Written by name, a member is `name(args)`. A part kept unevaluated has no name, and
            // an atom's payload that is a recursive type as a whole (no type has one: (c) at
            // `Printer::force_cycles`) would have none of its own to follow the atom's: each is
            // unfolded once, as `#c(int, L(int))`, the recursive types inside
            // by name. An unfolding that is itself a recursive node gets a definition, as without
            // names, and so does one met again inside its own unfolding, as the part `#a | R0` of
            // `R0 = (#a, (#a | R0))` is inside `(#a, #a | R0) | #a`, since a cycle written out
            // where it stands has no end ([`Printer::force_cycles`]).
            if self.by_name {
                match r.key.member_name() {
                    Some((name, [])) if ctx.is_none() => return Text::word(name, Class::Prim),
                    Some((name, args)) if ctx.is_none() => {
                        let mut segs = vec![Seg::Str(format!("{name}("))];
                        for (k, a) in args.iter().enumerate() {
                            if k > 0 {
                                segs.push(Seg::Str(", ".into()));
                            }
                            let a = self.refer(Item::Ty(None, a.clone()));
                            put(&mut segs, a, At::Any);
                        }
                        segs.push(Seg::Str(")".into()));
                        return Text {
                            segs,
                            class: Class::Prim,
                        };
                    }
                    _ => {
                        let body = r.unfolding();
                        if !matches!(&*body.0, Node::Rec(_)) {
                            let i = self.building.expect("a type's text is made for its node");
                            self.unfolded.push((i, ctx.clone(), t.clone()));
                            return self.refer(Item::Ty(ctx.clone(), body));
                        }
                    }
                }
            }
            let i = self.index[&Key::Ty(ctx.clone(), t.clone())];
            let ctx_name = ctx.as_deref().unwrap_or("").to_string();
            self.forced[i] = Some((ctx_name, t.rope(), t.clone()));
            let body = r.unfolding();
            return self.refer(Item::Ty(ctx.clone(), body));
        }
        let p = t.p();
        match ctx {
            None => {
                if *t == Type::top() {
                    return Text::word("_", Class::Prim);
                }
                if p.atoms.cofinite() && p.tuples.rest && p.structs {
                    let c = self.refer(Item::Ty(None, !t));
                    let mut segs = vec![Seg::Str("_ \\ ".into())];
                    put(&mut segs, c, At::Prim);
                    return Text {
                        segs,
                        class: Class::Diff,
                    };
                }
                let items = self.items(ctx, t);
                Text::joined(items, " | ", At::Union, Class::Union, "Never")
            }
            Some(a) => {
                let all = Type::payloads();
                if *t == all {
                    return Text::word(format!("#{a}(..)"), Class::Prim);
                }
                if p.tuples.rest && p.structs {
                    let c = self.refer(Item::Ty(ctx.clone(), &all - t));
                    let mut segs = vec![Seg::Str(format!("#{a}(..) \\ "))];
                    put(&mut segs, c, At::Prim);
                    return Text {
                        segs,
                        class: Class::Diff,
                    };
                }
                let items = self.items(ctx, t);
                Text::joined(items, " | ", At::Union, Class::Union, "Never")
            }
        }
    }

    /// The items of a type's union, in the order a union prints its members
    /// ([`order::cmp`], DESIGN.md sec:diagnostics).
    // Complexity tradeoff: the items are made kind by kind and then sorted by their places in
    // the order, O(m log m) for m items, each comparison O(1) but for two numbers, compared
    // exactly. A merge of the three sorted literal sets would be O(m), but the kinds would then
    // need an order of their own written out here, a second statement of the order that
    // `order::cmp` is the one statement of.
    fn items(&mut self, ctx: &Ctx, t: &Type) -> Vec<Text> {
        let p = t.p();
        let mut items: Vec<(Member<'_>, Text)> = Vec::new();
        match p.bools {
            1 => items.push((Member::False, Text::word("false", Class::Prim))),
            2 => items.push((Member::True, Text::word("true", Class::Prim))),
            3 => items.push((Member::Bool, Text::word("bool", Class::Prim))),
            _ => {}
        }
        for (name, l, whole) in [
            ("int", &p.ints, Member::NumberType(NumberType::Int)),
            ("rat", &p.rats, Member::NumberType(NumberType::Rat)),
            ("f32", &p.f32s, Member::NumberType(NumberType::F32)),
            ("f64", &p.floats, Member::NumberType(NumberType::F64)),
            ("String", &p.strings, Member::Named("String")),
        ] {
            if !lits(&mut items, name, l, whole, self.spell) {
                self.fixed_now = false;
            }
        }
        if p.atoms.cofinite() {
            let mut except = Vec::new();
            for (name, part) in p.atoms.names().iter() {
                self.atom(&mut except, name, &part.not());
            }
            let except: Vec<Text> = except.into_iter().map(|(_, t)| t).collect();
            items.push((
                Member::AnyAtom,
                match except.is_empty() {
                    true => Text::word("#_", Class::Prim),
                    false => minus(
                        "#_",
                        Text::joined(except, " | ", At::Union, Class::Union, ""),
                    ),
                },
            ));
        } else {
            for (name, part) in p.atoms.names().iter() {
                self.atom(&mut items, name, part);
            }
        }
        let mut tuples = Vec::new();
        self.tuples(&mut tuples, ctx, &p.tuples);
        items.extend(tuples.into_iter().map(|t| (Member::Tuple, t)));
        if p.structs {
            items.push((
                Member::Struct,
                match ctx {
                    None => Text::word("{..}", Class::Prim),
                    Some(a) => {
                        self.exact = false;
                        Text::word(format!("#{a}(struct)"), Class::Prim)
                    }
                },
            ));
        }
        match p.morphisms.is_leaf() {
            Some(false) => {}
            Some(true) => items.push((Member::Function, every_morphism())),
            None => items.push((
                Member::Function,
                self.refer(Item::Morphisms(p.morphisms.clone(), false)),
            )),
        }
        order::sort_by_member(&mut items, |(m, _)| *m);
        items.into_iter().map(|(_, t)| t).collect()
    }

    fn atom<'a>(
        &mut self,
        items: &mut Vec<(Member<'a>, Text)>,
        name: &'a Arc<str>,
        part: &super::AtomPart,
    ) {
        if part.bare {
            let member = Member::Atom {
                name,
                payload: false,
            };
            items.push((member, Text::word(format!("#{name}"), Class::Prim)));
        }
        if part.payload != Type::empty() {
            let member = Member::Atom {
                name,
                payload: true,
            };
            let text = self.refer(Item::Ty(Some(name.clone()), part.payload.clone()));
            items.push((member, text));
        }
    }

    fn tuples(&mut self, items: &mut Vec<Text>, ctx: &Ctx, t: &Tuples) {
        if t.rest {
            let word = match ctx {
                None => "(..)".to_string(),
                Some(a) => {
                    self.exact = false;
                    format!("#{a}(tuple)")
                }
            };
            let except = Type::with(|p| p.tuples = t.not());
            items.push(match except == Type::empty() {
                true => Text::word(word, Class::Prim),
                false => {
                    let c = self.refer(Item::Ty(ctx.clone(), except));
                    minus(&word, c)
                }
            });
            return;
        }
        for (n, part) in &t.lens {
            match part.is_leaf() {
                Some(false) => {}
                Some(true) => items.push(self.row(ctx, *n, None)),
                None => items.push(self.refer(Item::Tuples(ctx.clone(), *n, part.clone(), false))),
            }
        }
    }

    /// The tuple type `r` of length `n`, or every tuple of that length; in `ctx`, the atoms of
    /// that name with it as payload.
    fn row(&mut self, ctx: &Ctx, n: usize, r: Option<&Row>) -> Text {
        let mut segs = vec![Seg::Str(match ctx {
            None => "(".into(),
            Some(a) => format!("#{a}("),
        })];
        for i in 0..n {
            if i > 0 {
                segs.push(Seg::Str(", ".into()));
            }
            match r {
                Some(r) => {
                    let c = self.refer(Item::Ty(None, r[i].clone()));
                    put(&mut segs, c, At::Any);
                }
                None => segs.push(Seg::Str("_".into())),
            }
        }
        let one = n == 1 && ctx.is_none();
        segs.push(Seg::Str(if one { ",)" } else { ")" }.into()));
        Text {
            segs,
            // `(T,)` cannot read as parameters, so it is a primary even as a key.
            class: match ctx.is_none() && !one {
                true => Class::Tuple,
                false => Class::Prim,
            },
        }
    }

    fn morphism(&mut self, m: &Morphism) -> Text {
        let mut segs = Vec::new();
        if m.guarantee == m.permission || m.guarantee == Type::empty() {
            let k = self.refer(Item::Ty(None, m.permission.clone()));
            put(&mut segs, k, At::Key);
            segs.push(Seg::Str(
                // An empty guarantee is written `->?`, also where the permission is empty too:
                // `Never -> v` and `Never ->? v` hold the same one function, of empty domain,
                // but the checker finds the exact form within the partial one only, so it
                // reads the kernel type back from the partial form alone
                // (FAIL-types-exact-never-domain).
                if m.guarantee == Type::empty() {
                    " ->? "
                } else {
                    " -> "
                }
                .into(),
            ));
        } else {
            let l = self.refer(Item::Ty(None, m.guarantee.clone()));
            put(&mut segs, l, At::Bound);
            segs.push(Seg::Str(" .. ".into()));
            let u = self.refer(Item::Ty(None, m.permission.clone()));
            put(&mut segs, u, At::Bound);
            segs.push(Seg::Str(" -> ".into()));
        }
        let v = self.refer(Item::Ty(None, m.value.clone()));
        put(&mut segs, v, At::Any);
        Text {
            segs,
            class: Class::Arrow,
        }
    }

    /// A part, or the values it does not hold when `not` is set: a diagram from its decision
    /// list ([`Printer::list`]), or an expression's connective, its operands in any order, an
    /// expression turned over written by De Morgan's laws (`!(x & y)` as `!x | !y`).
    ///
    /// A part whose value outside every atom is `false` ([`Printer::outside`]) is written with
    /// no word for every value, `all`, which needs the top type `_` of layer L10 (`(_, _)` for
    /// the pairs, `_ ->? _` for the morphisms), while a program at L1 writes every such part
    /// (READ-atom-meet, PRINT-kept-meet-all). A list is so written by [`Printer::list`]. A meet
    /// `x & y` of such an `x` and a `y` of value `true` there is written `x \ !y`, `!y` a part
    /// of value `false` there; a complement `!q` of such a `q` is written as `all \ q`, and of
    /// any other `q` as `q` turned over. So, by induction on the expression, only a part that
    /// holds values outside every atom is written with `all`. `meet` writes a meet of atoms as
    /// one text where it can ([`Printer::list`]).
    fn part<A: super::bdd::Literal>(
        &mut self,
        p: &Part<A>,
        not: bool,
        lit: &dyn Fn(&mut Printer, &A) -> Text,
        all: &dyn Fn(&mut Printer) -> Text,
        item: &dyn Fn(&Part<A>, bool) -> Item,
        meet: &dyn Fn(&mut Printer, &[A]) -> Option<Text>,
    ) -> Text {
        // An operand: a leaf as text, otherwise a node of its own.
        // Every operand is one of a form's, and no form has a leaf operand: `Part::connect` folds
        // a leaf away from an `Or` or `And`, `Part::of_form` asserts it, both callers of
        // `Part::not_expr` outside tests pass a `Part::Expr` (`Connect::negate`), and the third
        // maker of forms, bdd.rs `xor::halves` (the `Or` of an exclusive or's two meets, made
        // when first read), proves at its site that neither meet is constant, so no leaf, and
        // asserts it (`Form::assert_no_leaf_operand`).
        let operand = |me: &mut Printer, (q, not): &(Part<A>, bool)| match q.is_leaf() {
            Some(_) => unreachable!("no operand of a form is a leaf"),
            None => me.refer(item(q, *not)),
        };
        let diff = |me: &mut Printer, x: &(Part<A>, bool), q: &(Part<A>, bool)| {
            let x = operand(me, x);
            let q = operand(me, q);
            let mut segs = Vec::new();
            put(&mut segs, x, At::DiffLeft);
            segs.push(Seg::Str(" \\ ".into()));
            put(&mut segs, q, At::Prim);
            Text {
                segs,
                class: Class::Diff,
            }
        };
        let (x, y, and) = match p.view() {
            Ok(b) => {
                debug_assert!(!not, "a list turned over is the list of the other value");
                return self.list(b, lit, all, meet);
            }
            Err(Form::Not(q)) => {
                debug_assert!(!not, "a complement turned over is its operand");
                // `!q` of `q` with no value outside every atom is `all \ q`; of any other `q`, it
                // is `q` turned over, a part with no such value.
                return match self.outside(q) {
                    false => {
                        let q = operand(self, &signed(q, false));
                        let mut segs = Vec::new();
                        put(&mut segs, all(self), At::DiffLeft);
                        segs.push(Seg::Str(" \\ ".into()));
                        put(&mut segs, q, At::Prim);
                        Text {
                            segs,
                            class: Class::Diff,
                        }
                    }
                    true => operand(self, &signed(q, true)),
                };
            }
            // De Morgan's laws: a union turned over is the meet of its operands turned over, and
            // a meet turned over their union.
            Err(Form::Or(x, y)) => (signed(x, not), signed(y, not), not),
            Err(Form::And(x, y)) => (signed(x, not), signed(y, not), !not),
        };
        // The operands in the order of the names, as the literals of a list ([`Printer::list`]).
        let (x, y) = match p.view() {
            Err(Form::Or(a, b) | Form::And(a, b)) if names_first(|| !a.before(b)) => (y, x),
            _ => (x, y),
        };
        if !and {
            let x = operand(self, &x);
            let y = operand(self, &y);
            return Text::group(vec![x, y], " | ", At::Union, Class::Union);
        }
        // A complement kept as an expression, `!q`, as its operand `q`.
        let complement = |(q, not): &(Part<A>, bool)| match (q.view(), not) {
            (Err(Form::Not(q)), false) => Some(signed(q, false)),
            _ => None,
        };
        match (self.outside_of(&x), self.outside_of(&y)) {
            // `x & y` of `x` with no value outside every atom and `y` with some is `x \ !y`, as
            // a program writes it at L1, and not `x & (all \ !y)` or the like: `!y` has no such
            // value either. The difference `x & !q` kept as its operands is so `x \ q`.
            (false, true) => diff(self, &x, &signed(&y.0, !y.1)),
            (true, false) => diff(self, &y, &signed(&x.0, !x.1)),
            // Both hold values outside every atom: a complement operand `!q` is written
            // `x \ q`, which writes `all` once, in `x`.
            (true, true) => match (complement(&y), complement(&x)) {
                (Some(q), _) => diff(self, &x, &q),
                (None, Some(q)) => diff(self, &y, &q),
                (None, None) => {
                    let x = operand(self, &x);
                    let y = operand(self, &y);
                    Text::group(vec![x, y], " & ", At::And, Class::And)
                }
            },
            (false, false) => {
                let x = operand(self, &x);
                let y = operand(self, &y);
                Text::group(vec![x, y], " & ", At::And, Class::And)
            }
        }
    }

    /// The value of a part, turned over when its flag is set, outside every atom
    /// ([`Printer::outside`]).
    fn outside_of<A: super::bdd::Literal>(&mut self, (p, not): &(Part<A>, bool)) -> bool {
        self.outside(p) != *not
    }

    /// The value of a part on the values outside every atom, where no literal holds but those
    /// that refuse their atom: a list's is the value of its first block that refuses an atom,
    /// or its last value; an expression's is its connective's of its operands'. Each node is
    /// evaluated once in the printer, with a stack of its own, so the time is linear in the
    /// nodes and literals of the parts printed, each list read up to its first block that
    /// refuses an atom.
    fn outside<A: super::bdd::Literal>(&mut self, p: &Part<A>) -> bool {
        // Complexity tradeoff: the naive version asks each meet `p.eval3` afresh, which walks
        // every node below it, so `n` meets inside each other cost O(n²). Here each node's value
        // is kept by its id for the printer's life, so the whole text costs O(n) evaluations
        // and O(n) memory for the table; the cost is that table, freed with the printer.
        if let Some(&v) = self.outsides.get(&p.id()) {
            return v;
        }
        let mut stack = vec![(p.clone(), false)];
        while let Some((q, ready)) = stack.pop() {
            let id = q.id();
            if self.outsides.contains_key(&id) {
                continue;
            }
            let v = match q.view() {
                Ok(_) => q
                    .eval3(&|_| Some(false))
                    .expect("a list has one value where every atom is known"),
                Err(form) => {
                    let (x, y) = match form {
                        Form::Not(x) => (x, None),
                        Form::Or(x, y) | Form::And(x, y) => (x, Some(y)),
                    };
                    if !ready {
                        stack.push((q.clone(), true));
                        for o in [Some(x), y].into_iter().flatten() {
                            if !self.outsides.contains_key(&o.id()) {
                                stack.push((o.clone(), false));
                            }
                        }
                        continue;
                    }
                    let x = self.outsides[&x.id()];
                    match (form, y.map(|y| self.outsides[&y.id()])) {
                        (Form::Or(..), Some(y)) => x || y,
                        (Form::And(..), Some(y)) => x && y,
                        _ => !x,
                    }
                }
            };
            self.outsides.insert(id, v);
        }
        self.outsides[&p.id()]
    }

    /// A diagram from its decision list in its one form (module `bdd::list`), which does not
    /// depend on the order of the atoms. A block of value `true` is the union of its literals
    /// and the rest, `a | (all \ b) | rest`; a block of value `false` is the rest without its
    /// literals, `b & rest \ a`, `a` an atom the block's literals take and `b` one they refuse.
    /// Where `rest` holds a value outside every atom, its text would hold `all`, which needs
    /// the top type `_` of layer L10, while `b` has no such value: such a block is written
    /// `b \ (a | not rest)` instead, `not rest` the rest with every value turned over, so a type
    /// a program writes at L1, `A \ (B \ C)`, prints as written and not as
    /// `A & ((all \ B) | C)` (READ-atom-meet). The literals of a block are a group. The text is
    /// written from the first block on into one list of segments, with a stack of what closes
    /// the blocks begun, so that no block's text is copied into the text before it.
    ///
    /// The atoms `b` of a block of value `false`, and the one atom `c` of a block of value
    /// `true` after it where nothing is written after that, are met (`b1 & b2 & c`). Where
    /// `meet` writes the meet of those atoms as one text (two morphism types, which a program
    /// would read as an overload, [`Printer::folded`]), that text stands for them: the rest is
    /// then `c`, or the list after the block, as before.
    // Complexity tradeoff: each diagram prints its own list, so the text is linear in the
    // lists of the distinct parts printed, where printing nodes was linear in their union.
    // Which blocks are turned over is found in two passes over the list, linear in it. `meet`
    // is asked once per block of value `false`, with that block's atoms.
    fn list<A: super::bdd::Literal>(
        &mut self,
        b: &Bdd<A>,
        lit: &dyn Fn(&mut Printer, &A) -> Text,
        all: &dyn Fn(&mut Printer) -> Text,
        meet: &dyn Fn(&mut Printer, &[A]) -> Option<Text>,
    ) -> Text {
        let mut list = b.list();
        // The literals of each block in the order the atoms had when they were ordered by the
        // digests of names ([`names_first`]). The walk makes the nodes in the order of the
        // literals, and a part written in two ways, such as `R0 & R3` and `R3 & R0`, is one type
        // named by the text of the node made first; so in this order the names and the layout
        // of a printed type do not depend on the name-free order of the atoms.
        // Complexity tradeoff: a sort of each block, O(b log b) comparisons for b literals, on
        // printing only; the search keeps the name-free order. Naive version: the atoms' order,
        // O(b), whose names then depend on the name-free digests. Given up: nothing printed.
        for (_, lits) in &mut list.blocks {
            names_first(|| lits.sort_by(|(x, _), (y, _)| x.cmp(y)));
        }
        let m = list.blocks.len();
        // Whether the list from each block on holds the values outside every atom: the value
        // of the first block from there that refuses an atom, or the tail.
        let mut outside = vec![list.tail; m + 1];
        for k in (0..m).rev() {
            let (v, lits) = &list.blocks[k];
            outside[k] = match lits.iter().any(|(_, t)| !t) {
                true => *v,
                false => outside[k + 1],
            };
        }
        // Each block's value as written, the blocks after a turn taking the other value, and
        // whether the rest is turned over after it.
        let mut value = Vec::with_capacity(m);
        let mut turn = vec![false; m];
        let mut over = false;
        for (k, (v, lits)) in list.blocks.iter().enumerate() {
            value.push(*v != over);
            if *v == over && k + 1 < m && lits.iter().any(|(_, t)| !t) && outside[k + 1] != over {
                turn[k] = true;
                over = !over;
            }
        }
        let every = list.tail != over;
        let mut tail = every.then(|| all(self));
        // The texts of each block's literals: of value `true`, `a` and `all \ b` in the order
        // of the literals; of value `false`, the atoms refused and those taken. The atoms
        // `meet` writes as one text are written so, before any of their own texts is made, so
        // that no text made and dropped counts as a use of a part.
        //
        // A block of value `false` is never met with an atom `c` of the block after it, as
        // `b & c`, where that block is `c` alone, of value `true`, with no text of a value
        // after it: no list in its one form (module `list` in `bdd.rs`) has that shape. Proof:
        // with no turn at block k nor after it (a turn after it is a text of a value, and the
        // block of `c` alone refuses no atom, so it has none), every block from k on and the
        // default have the value `over` of block k as written, except the block of `c`. So
        // once the blocks before k are false, the function is `over` under `!c` whatever the
        // other atoms, and the one form puts `!c` in block k, the first block of that
        // function; no atom is in two blocks, so `c` is not in the block after it. The
        // twelfth and thirteenth rounds' coverage found the merge never made
        // (TEST-kernel-unreached-paths-7), and it is removed. No test checks the shape's
        // absence: had a list that shape, `b & c` would print unmerged and read back as the same
        // type (inferred), so
        // `types::print::tests::random_types_print_alike_in_every_order_of_their_atoms`,
        // `l01_22_type_representation::surface::a_few_unions_differences_and_intersections_of_rows_read_back_as_the_same_type`
        // and `l01_29_repairs_and_printing::printed::every_printed_type_parses_back_to_itself`
        // would all pass; they check that what is printed is right, not that it is shortest.
        let mut texts: Vec<(Vec<Text>, Vec<Text>)> = Vec::with_capacity(m);
        for (k, (_, lits)) in list.blocks.iter().enumerate() {
            let (mut first, mut taken) = (Vec::new(), Vec::new());
            // The atoms the block of value `false` meets, written `b1 & b2 & rest`.
            let mut met = false;
            if !value[k] {
                let atoms: Vec<A> = (lits.iter().filter(|(_, t)| !t))
                    .map(|(a, _)| a.clone())
                    .collect();
                if let Some(text) = meet(self, &atoms) {
                    first.push(text);
                    met = true;
                }
            }
            for (a, t) in lits {
                if met && !t {
                    continue;
                }
                let l = lit(self, a);
                match (value[k], t) {
                    (true, true) | (false, false) => first.push(l),
                    (false, true) => taken.push(l),
                    (true, false) => {
                        let mut segs = Vec::new();
                        put(&mut segs, all(self), At::DiffLeft);
                        segs.push(Seg::Str(" \\ ".into()));
                        put(&mut segs, l, At::Prim);
                        first.push(Text {
                            segs,
                            class: Class::Diff,
                        });
                    }
                }
            }
            texts.push((first, taken));
        }
        // The class of the text from each block on, `None` where it has no value. Only the
        // text after the last block can have none: every block has a class. Proof. In the one
        // form the values alternate and the default is the value the last block does not have
        // (module `list` in `bdd.rs`). The last block is turned by no turn (a turn needs a block
        // after it), so it is written with the value `over` has at the end: written `false`,
        // its value is `over` and the default is not, so the default is written (`every`);
        // written `true`, it has a value. A block before a text with a value has one. After a
        // turn at block k, block k + 1 exists; if it is the last, the default is the value of
        // block k, `over` before the turn, so not `over` after it, and is written; otherwise
        // block k + 2 has the value of block k, and is written `true` unless a turn at k + 1
        // turned it over, which gives block k + 1 a class of its own. So the text after a
        // turn always has a value. The twelfth and thirteenth rounds' coverage found neither
        // case made (TEST-kernel-unreached-paths-7); the asserts below keep the proof checked,
        // run by `types::print::tests::random_types_print_alike_in_every_order_of_their_atoms`
        // and `::only_a_part_holding_values_outside_every_atom_prints_the_top_type`, on their
        // random draws only.
        debug_assert!(
            (list.blocks.last()).is_none_or(|(v, _)| *v != list.tail),
            "the default of a list in its one form is the value its last block does not have"
        );
        let mut class = vec![None; m + 1];
        class[m] = tail.as_ref().map(|t| t.class);
        for k in (0..m).rev() {
            let (first, taken) = &texts[k];
            let next = class[k + 1];
            class[k] = match (value[k], turn[k]) {
                (true, _) => Some(match (first.len(), next) {
                    (1, None) => first[0].class,
                    _ => Class::Union,
                }),
                // `b \ (a | not rest)`; the text after a turn has a value (above).
                (false, true) => {
                    debug_assert!(next.is_some(), "the text after a turn has a value");
                    Some(Class::Diff)
                }
                // A block of value `false` before no value leaves no value.
                // Its block is a set of one literal or more (`Bdd::list`): each refused one is in
                // `first` (or in the meet there) and each taken one in `taken`, so the two are not
                // both empty, and the text after it is not the text of this block. (A block's set
                // is a `Cell::block: Arc<Set<A>>`, a treap node that holds a literal, so
                // `set::iter` yields one at least.) Test (PROOF-kernel-proofdoc3a-gaps (l)): the
                // assert below, run by
                // `types::print::tests::random_types_print_alike_in_every_order_of_their_atoms`
                // (random lists in every order of their atoms); a list outside its draws is not
                // checked.
                (false, false) => next.map(|_| match (taken.is_empty(), first.len()) {
                    _ if cfg!(debug_assertions) && first.is_empty() && taken.is_empty() => {
                        unreachable!("a block of value `false` writes a literal")
                    }
                    (false, _) => Class::Diff,
                    (true, 1) if every && k + 1 == m => first[0].class,
                    (true, _) => Class::And,
                }),
            };
        }
        let mut segs = Vec::new();
        // What closes each block begun, last first.
        let mut closing: Vec<Vec<Seg>> = Vec::new();
        let open = |segs: &mut Vec<Seg>, closing: &mut Vec<Vec<Seg>>, at: At, c: Class| {
            if !at.admits(c) {
                segs.push(Seg::Str("(".into()));
                closing.push(vec![Seg::Str(")".into())]);
            }
        };
        // Where the text from the next block on stands.
        let mut at = At::Any;
        for (k, (mut first, taken)) in texts.into_iter().enumerate() {
            debug_assert!(class[k].is_some(), "every block has a class");
            let last = class[k + 1].is_none();
            if turn[k] {
                let refused = Text::group(first, " & ", At::And, Class::And);
                open(&mut segs, &mut closing, at, Class::Diff);
                put(&mut segs, refused, At::DiffLeft);
                segs.push(Seg::Str(" \\ ".into()));
                at = At::Prim;
                if taken.is_empty() {
                    continue;
                }
                // The atoms taken, then the rest turned over, as a block of value `true`.
                first = taken;
            } else if !value[k] {
                if !taken.is_empty() {
                    open(&mut segs, &mut closing, at, Class::Diff);
                    closing.push(vec![
                        Seg::Str(" \\ ".into()),
                        group(taken, " \\ ", At::Prim),
                    ]);
                    at = At::DiffLeft;
                }
                if first.is_empty() {
                    continue;
                }
                let refused = Text::group(first, " & ", At::And, Class::And);
                if every && k + 1 == m {
                    put(&mut segs, refused, at);
                    tail = None;
                    break;
                }
                open(&mut segs, &mut closing, at, Class::And);
                put(&mut segs, refused, At::And);
                segs.push(Seg::Str(" & ".into()));
                at = At::And;
                continue;
            }
            match (first.len(), last) {
                (1, true) => {
                    put(&mut segs, first.into_iter().next().expect("one item"), at);
                }
                (_, true) => {
                    open(&mut segs, &mut closing, at, Class::Union);
                    segs.push(group(first, " | ", At::Union));
                }
                (_, false) => {
                    open(&mut segs, &mut closing, at, Class::Union);
                    put(
                        &mut segs,
                        Text::group(first, " | ", At::Union, Class::Union),
                        At::Union,
                    );
                    segs.push(Seg::Str(" | ".into()));
                    at = At::Union;
                    continue;
                }
            }
            tail = None;
            break;
        }
        if let Some(t) = tail {
            put(&mut segs, t, at);
        }
        while let Some(s) = closing.pop() {
            segs.extend(s);
        }
        Text {
            segs,
            class: class[0].expect("a diagram that is no leaf has values"),
        }
    }

    /// The class a node shows: a name is a primary, and a part the message may write in full
    /// ([`defs::add_soft`], [`defs::add_counted`]) that of its text.
    fn class(&self, mut i: usize, named: &[Option<String>]) -> Class {
        loop {
            if let Some(name) = &named[i] {
                return match defs::is_soft(name) || defs::is_counted(name) {
                    true => self.own_class(i),
                    false => Class::Prim,
                };
            }
            match self.texts[i].as_ref().expect("visited").class {
                Class::Of(j) => i = j,
                c => return c,
            }
        }
    }

    /// The class of node `i`'s own text, through the nodes it is one reference to.
    fn own_class(&self, mut i: usize) -> Class {
        loop {
            match self.texts[i].as_ref().expect("visited").class {
                Class::Of(j) => i = j,
                c => return c,
            }
        }
    }

    /// Whether node `i`'s text is a tuple type, `(A, B)` or `(A,)`. A one-tuple is a primary
    /// ([`Printer::row`]), and the only text that ends `,)`.
    fn is_row(&self, i: usize) -> bool {
        let text = self.texts[i].as_ref().expect("visited");
        match text.class {
            Class::Tuple => true,
            Class::Prim => matches!(text.segs.last(), Some(Seg::Str(s)) if s == ",)"),
            _ => false,
        }
    }

    /// The node whose name each node's text is, or `None`: a node whose text is one reference
    /// to another is that one's, and a `marked` node whose text is not, or whose reference
    /// leads to no name, is its own. A marked node whose text is so another node's name takes
    /// that name, rather than a definition `type Part2 = Part1;` of its own; each of its cycles
    /// passes through the node it names, which keeps a name. Each node is followed once, with a
    /// list of those whose answer waits on the next: time linear in the nodes.
    fn same_names(&self, marked: &dyn Fn(usize) -> bool) -> Vec<Option<usize>> {
        let n = self.texts.len();
        let mut found: Vec<Option<Option<usize>>> = vec![None; n];
        let mut waiting: Vec<bool> = vec![false; n];
        let mut path = Vec::new();
        for &start in &self.post {
            let mut i = start;
            let mut end = loop {
                if let Some(f) = found[i] {
                    break f;
                }
                // A cycle of references alone, which a contractive group does not have.
                if waiting[i] {
                    break None;
                }
                match &self.texts[i].as_ref().expect("visited").segs[..] {
                    [Seg::Node(j, _)] => {
                        waiting[i] = true;
                        path.push(i);
                        i = *j;
                    }
                    _ => {
                        let own = marked(i).then_some(i);
                        found[i] = Some(own);
                        break own;
                    }
                }
            };
            while let Some(i) = path.pop() {
                waiting[i] = false;
                if marked(i) {
                    end = end.or(Some(i));
                }
                found[i] = Some(end);
            }
        }
        found.into_iter().map(Option::flatten).collect()
    }

    /// The definitions, then each root's text at its place.
    fn render(&self, roots: &[(usize, At)]) -> Surfaces {
        let mut named: Vec<Option<String>> = vec![None; self.texts.len()];
        let collecting = defs::active();
        // While a message collects definitions, a part it names by count gets a reference
        // whatever this type's uses of it ([`Printer::counted`]).
        let counted = match collecting {
            true => self.counted(),
            false => vec![false; self.texts.len()],
        };
        let marked = |i: usize| counted[i] || self.named(i);
        let same = self.same_names(&marked);
        // Whether node `i` gets a definition: a named node whose name is its own.
        let defined = |i: usize| self.named(i) && same[i].is_none_or(|j| j == i);
        let mut defs = Vec::new();
        if collecting {
            self.collect(&same, &counted, &mut named);
            self.remember(&named);
        } else {
            let mut k = 0;
            for &i in &self.post {
                if defined(i) {
                    named[i] = Some(names::fresh_name(names::Names::Definitions, &mut k, |_| {
                        false
                    }));
                }
            }
            for &i in &self.post {
                if let Some(j) = same[i].filter(|&j| self.named(i) && j != i) {
                    named[i] = named[j].clone();
                }
            }
        }
        for &i in &self.post {
            if let Some(name) = named[i].as_ref().filter(|_| defined(i) && !collecting) {
                let mut body = String::new();
                self.write(
                    &self.texts[i].as_ref().expect("visited").segs,
                    &named,
                    &mut body,
                );
                defs.push((name.clone(), body));
            }
        }
        let mut roots: Vec<String> = roots
            .iter()
            .enumerate()
            .map(|(k, &(i, at))| {
                let mut out = String::new();
                match self.apart.get(k).copied().unwrap_or(false) {
                    true => self.write_out(i, at, &named, &mut out),
                    false => self.write(&[Seg::Node(i, at)], &named, &mut out),
                }
                out
            })
            .collect();
        // In a message the uses of a part named by count are counted over this print, as a
        // type printed alone counts them ([`defs::enclose`]).
        if collecting {
            defs::enclose(&mut roots);
        }
        Surfaces {
            defs,
            roots,
            exact: self.exact,
        }
    }

    /// While a message collects definitions (module `defs`): names each node that gets a
    /// definition by a reference to its place in the thread's table, merged with an equal
    /// definition there, and each node whose name is another's by that reference too. A
    /// `counted` node gets a reference that the message names from its first step that uses
    /// the part twice or more ([`defs::add_counted`]), so its text is the same in every type.
    /// A definition whose body uses one not placed yet, as in a cycle, gets a place of its own
    /// first and its body after the others, or the place an earlier print of the message gave
    /// the same part, whose body that print wrote; a counted node whose body waits so is named
    /// as this type names it, and else written where it stands.
    // A place is shared by the part's key, its type, not by its body's text: a type that
    // writes a cycle's part again, as `(KT, KT)` after `KT`, would write the body as anew,
    // with references to places of its own, and so define the cycle twice. The key names the
    // same type in every print of the message, so the earlier definition is this one's. A
    // print that enters the cycle at another part meets the part placed before inside it,
    // takes its reference there, and the part it enters at then no longer waits: its body
    // is the earlier print's text and merges with it ([`defs::add`]). Not covered: a cycle
    // that no part of an earlier print's cycle is met in by its key, which would need the
    // definitions compared up to a renaming of their references. Cost: the keys of this
    // print's nodes, O(n), and, once the message has placed such a part, one search of its
    // table per node, O(log m) comparisons of keys in the m parts placed so.
    fn collect(&self, same: &[Option<usize>], counted: &[bool], named: &mut [Option<String>]) {
        let marked = |i: usize| counted[i] || self.named(i);
        let defined = |i: usize| marked(i) && same[i].is_none_or(|j| j == i);
        let mut aliases: Vec<Vec<usize>> = vec![Vec::new(); self.texts.len()];
        for &i in &self.post {
            if let Some(j) = same[i].filter(|&j| marked(i) && j != i) {
                aliases[j].push(i);
            }
            if marked(i) {
                named[i] = Some(defs::WAIT.into());
            }
        }
        let body = |i: usize, named: &[Option<String>]| {
            let mut body = String::new();
            let segs = &self.texts[i].as_ref().expect("visited").segs;
            self.write(segs, named, &mut body);
            body
        };
        let mut waiting = Vec::new();
        let mut keys: Vec<Option<&Key>> = vec![None; self.texts.len()];
        for (key, &j) in self.index.iter() {
            keys[j] = Some(key);
        }
        let printed = |i: usize| -> Printed {
            let key = keys[i].expect("every node is reached by its key");
            (self.by_name, self.spell.is_some(), key.clone())
        };
        let earlier = with_kept(|kept| !kept.cycles.is_empty()).unwrap_or(false);
        for &i in &self.post {
            if marked(i) && !defined(i) {
                // Named by the node of equal text it is an alias of.
                continue;
            }
            // A part an earlier print of the message placed before its body, met here at any
            // place of the cycle, as `KM1`'s own type is inside `KM0`'s (a type printed with
            // `KM1` alone enters the cycle there). Its definition is this part's.
            let placed = match earlier {
                true => with_kept(|kept| kept.cycles.get(&printed(i)).cloned()).flatten(),
                false => None,
            };
            if let Some(r) = placed {
                for &a in &aliases[i] {
                    named[a] = Some(r.clone());
                }
                named[i] = Some(r);
                continue;
            }
            // A tuple goes into the table as a part that `defs::lift` names only if it is
            // written inside another part, by the rule `defs::lift` gives, as when each
            // step of a chain `a2 = (a1, 2)` writes the one before, or each level of
            // `t2 = (t1, t1)` the level below; elsewhere it is written in full, so
            // `(p: (int,)) -> (int,)` keeps its two `(int,)` (MSG-derive-type-size). A
            // one-tuple is a tuple here too, though it binds as a primary. Whether this type
            // writes it twice does not decide: another type of the message may write it again.
            // One whose body waits on a definition of a cycle is named as before if this type
            // names it, and else written in full.
            let tuple = self.forced[i].is_none() && self.is_row(i);
            if !tuple && !marked(i) {
                continue;
            }
            let b = body(i, named);
            // A node whose text is one name, as a union of one tuple or a type that is one
            // tuple, writes that name, so it is named only if that part is: else a tuple used
            // once in each of two types would be named by the type that holds it.
            let alias = self.forced[i].is_none() && defs::only_reference(&b).is_some();
            if alias || (tuple && !b.contains(defs::WAIT)) {
                let r = match alias {
                    true => b,
                    false => defs::soft_reference(defs::add_soft(b)),
                };
                for &a in &aliases[i] {
                    named[a] = Some(r.clone());
                }
                named[i] = Some(r);
                continue;
            }
            if !marked(i) {
                continue;
            }
            let wait = b.contains(defs::WAIT);
            let named_here = self.named(i) || aliases[i].iter().any(|&a| self.named(a));
            let r = match (wait, counted[i]) {
                (false, true) => defs::counted_reference(defs::add_counted(b)),
                (true, true) if !named_here => {
                    named[i] = None;
                    for &a in &aliases[i] {
                        named[a] = None;
                    }
                    continue;
                }
                (true, _) => {
                    let k = defs::reserve();
                    waiting.push((i, k));
                    let r = defs::reference(k);
                    with_kept(|kept| kept.cycles.insert(printed(i), r.clone()));
                    r
                }
                (false, false) => defs::reference(defs::add(b)),
            };
            for &a in &aliases[i] {
                named[a] = Some(r.clone());
            }
            named[i] = Some(r);
        }
        for (i, k) in waiting {
            defs::fill(k, body(i, named));
        }
    }

    /// Puts each part of an exact print that prints the same in any type of the message into
    /// the table of parts printed so far, by its reference ([`printed`]), so that a later
    /// type holding it takes the reference rather than print it again. A part prints the same
    /// in any type when each node in it is a tuple, which is always a reference
    /// ([`Printer::collect`]), a part named by count, which is a reference too, a text that is
    /// one reference to another such node, one token, or a part taken from an earlier print;
    /// and none is a recursive type, spells a literal as written near one message only
    /// ([`super::Spelled::everywhere`]), or holds a group, whose order follows whether a part
    /// in it is named. A tuple's reference is its body's place in the message's table, so the
    /// part taken again is the text a print anew would give.
    // Complexity tradeoff (MSG-derive-print-per-message): naive, each type of a message printed
    // in full, O(m) for a type of m parts, so a derivation of n steps that each print the next
    // of a chain `t2 = (t1, t1); t3 = (t2, t2); …` costs O(n²); keeping use counts for one
    // print of the whole message would name a part by how often the message, not the type,
    // uses it, and counting per type needs each type's parts, O(n²) again. Used: the parts kept
    // by their keys, one ordered map for the message, so each step prints only its new parts,
    // O(log n) each, and the message O(m log m) in the m parts it prints in all. Since a part
    // named by count is a reference whatever the type's uses (MSG-derive-print-union-names),
    // no part's text depends on the type it stands in, and none needs the uses inside it kept.
    fn remember(&self, named: &[Option<String>]) {
        if !self.exact {
            return;
        }
        let mut clean = vec![false; self.texts.len()];
        for &i in &self.post {
            if self.reused[i] {
                clean[i] = true;
                continue;
            }
            let segs = &self.texts[i].as_ref().expect("visited").segs;
            clean[i] = self.forced[i].is_none()
                && self.fixed[i]
                && !segs.iter().any(|s| matches!(s, Seg::Group(_)))
                && self.kids[i].iter().all(|&j| clean[j]);
        }
        // The reference node `i` is written as, if it is a tuple or one reference to one.
        let reference = |mut i: usize| loop {
            if let Some(name) = named[i].as_deref().filter(|n| defs::is_soft(n)) {
                return Some(name);
            }
            match &self.texts[i].as_ref().expect("visited").segs[..] {
                [Seg::Node(j, _)] => i = *j,
                [Seg::Str(s)] if self.reused[i] => return Some(s.as_str()),
                _ => return None,
            }
        };
        let spelled = self.spell.is_some();
        keep(self.index.iter().filter_map(|(key, &i)| {
            if !clean[i] || self.reused[i] {
                return None;
            }
            let name = reference(i)?;
            let printed = (self.by_name, spelled, key.clone());
            Some((printed, name.to_string(), self.own_class(i)))
        }));
    }

    /// Whether each node is one that a message names by how often its steps use it
    /// ([`defs::add_counted`]), where a type printed alone names it by how often the type uses
    /// it ([`Printer::named`]): neither a token, nor a recursive type, nor a tuple, which is a
    /// reference to the table always ([`Printer::collect`]), nor a part taken from an earlier
    /// print, nor one reference to one of these but a recursive type. A node not visited is
    /// not. Each node is followed once, as in [`Printer::same_names`].
    fn counted(&self) -> Vec<bool> {
        let n = self.texts.len();
        // Whether each node is written as a reference whatever the uses.
        let mut reference: Vec<Option<bool>> = vec![None; n];
        let mut waiting = vec![false; n];
        let mut path = Vec::new();
        for &start in &self.post {
            let mut i = start;
            let found = loop {
                if let Some(r) = reference[i] {
                    break r;
                }
                if self.reused[i] || (self.forced[i].is_none() && self.is_row(i)) {
                    break true;
                }
                match &self.texts[i].as_ref().expect("visited").segs[..] {
                    [Seg::Node(j, _)] if self.forced[i].is_none() && !waiting[i] => {
                        waiting[i] = true;
                        path.push(i);
                        i = *j;
                    }
                    _ => break false,
                }
            };
            reference[i] = Some(found);
            for i in path.drain(..) {
                waiting[i] = false;
                reference[i] = Some(found);
            }
        }
        (0..n)
            .map(|i| match &self.texts[i] {
                Some(text) => {
                    let token =
                        matches!(&text.segs[..], [Seg::Str(s)] if !s.contains([' ', '(', ',']));
                    !token && self.forced[i].is_none() && reference[i] == Some(false)
                }
                None => false,
            })
            .collect()
    }

    /// Writes node `i` at `at` by its own text, not by a name, following a text that is one
    /// reference to another node to that node's text: a root printed apart
    /// ([`Type::surfaces_apart`]). The nodes inside are written by [`Printer::write`].
    fn write_out(&self, mut i: usize, at: At, named: &[Option<String>], out: &mut String) {
        let mut text = self.texts[i].as_ref().expect("visited");
        // Not proved: that no chain of texts each one `Seg::Node` comes back to a node on it,
        // so that this loop ends. Each step goes from a type to a part of it (a member of a
        // union of one member, an atom's payload), and only a recursive type holds itself
        // (`force_cycles`); no proof here that such a cycle has a text of more than one node.
        while let [Seg::Node(j, _)] = text.segs[..] {
            i = j;
            text = self.texts[i].as_ref().expect("visited");
        }
        // A text of class `Of` is one `Seg::Node` (the proof is at `put`), and the loop above
        // leaves `text` at a text that is not one node, so its class is not `Of`
        // (TEST-kernel-unreached-paths-14: the arm that read the class of `Of` here was never
        // reached).
        let class = match text.class {
            Class::Of(_) => unreachable!("a text of class Of is one node"),
            c => c,
        };
        let wrap = !at.admits(class);
        if wrap {
            out.push('(');
        }
        self.write(&text.segs, named, out);
        if wrap {
            out.push(')');
        }
    }

    /// Writes `segs`, a node by its name or else its own text, with a stack of its own.
    fn write(&self, segs: &[Seg], named: &[Option<String>], out: &mut String) {
        let mut pieces = Pieces::new(segs);
        while let Some(piece) = pieces.next() {
            match piece {
                Piece::Str(s) => out.push_str(s),
                Piece::Node(i, at) => match &named[i] {
                    // A part the message may write in full, a tuple ([`defs::add_soft`]) or a
                    // part named by count ([`defs::add_counted`]), binds as its text does: it is
                    // parenthesized if that text does not bind at `at` and the message writes it
                    // in full, and not if the message names it, `Part1 -> V` (author rule P191).
                    Some(name)
                        if (defs::is_soft(name) || defs::is_counted(name))
                            && !at.admits(self.own_class(i)) =>
                    {
                        out.push_str(&defs::wrapped(name));
                    }
                    Some(name) => out.push_str(name),
                    None => {
                        if !at.admits(self.class(i, named)) {
                            out.push('(');
                            pieces.stack.push(Frame::Close);
                        }
                        let text = self.texts[i].as_ref().expect("visited");
                        pieces.stack.push(Frame::Segs(text.segs.iter()));
                    }
                },
            }
        }
    }
}

/// The literals of `l` as items of a union, each with its member: `whole`, the base type
/// `name`, or what is left of it, or each literal by its value. Whether each is spelled so
/// wherever a message is written ([`super::Spelled::everywhere`]).
fn lits<'a>(
    items: &mut Vec<(Member<'a>, Text)>,
    name: &str,
    l: &'a Lits,
    whole: Member<'a>,
    spell: Option<Spell<'_>>,
) -> bool {
    let fixed = std::cell::Cell::new(true);
    let everywhere = &fixed;
    // Complexity tradeoff: a value with a spelling is written as the program spells it, one
    // lookup each, O(log s) in the s spellings (`Spell`), and its text copied once, as the
    // canonical text it replaces is made once; the text stays linear in what it prints. Naively
    // reparsing the printed text to swap each literal back would cost a second pass and a copy.
    let each = || {
        l.values.iter().map(move |v| {
            let spelled = spell.map(|s| s(v));
            if spelled.as_ref().is_some_and(|s| !s.everywhere) {
                everywhere.set(false);
            }
            let text = match spelled.and_then(|s| s.text) {
                Some(s) => s.into_owned(),
                None => super::lit_text(v),
            };
            (v, Text::word(text, Class::Prim))
        })
    };
    match (l.cofinite, l.values.is_empty()) {
        (true, true) => items.push((whole, Text::word(name, Class::Prim))),
        (true, false) => {
            let taken = each().map(|(_, t)| t).collect();
            let taken = Text::joined(taken, " | ", At::Union, Class::Union, "Never");
            items.push((whole, minus(name, taken)));
        }
        (false, _) => items.extend(each().map(|(v, t)| {
            let member = match v {
                Value::Str(s) => Member::Str(s),
                v => Member::Number(v),
            };
            (member, t)
        })),
    }
    fixed.get()
}

/// `word \ t`.
fn minus(word: &str, t: Text) -> Text {
    let mut segs = vec![Seg::Str(format!("{word} \\ "))];
    put(&mut segs, t, At::Prim);
    Text {
        segs,
        class: Class::Diff,
    }
}

/// Every morphism: no key promised, any key permitted, any value, `_ ->? _`, the partial-map
/// former, as DESIGN.md sec:type_language writes a morphism type whose guarantee is empty. It
/// needs the top type `_` of layer L10; a type a program writes at L1 has no part of it that
/// [`Printer::list`] writes with it (READ-atom-meet).
fn every_morphism() -> Text {
    Text::word("_ ->? _", Class::Arrow)
}

#[cfg(test)]
mod tests;
