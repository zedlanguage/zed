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

use super::TextPlace as At;
use super::bdd::{Bdd, Form, Part};
use super::{Lits, Morphism, Node, Row, Surface, Surfaces, Tuples, Type};

pub mod defs;
pub mod names;

impl Type {
    /// The type in the surface syntax (module `print`).
    pub fn surface(&self) -> Surface {
        self.surface_at(At::Any)
    }

    /// The type in the surface syntax as one operand of a union, parenthesized where it would
    /// not be one, as a message writes a type among others.
    pub fn surface_in_union(&self) -> Surface {
        self.surface_at(At::Union)
    }

    /// The type in the surface syntax as an operand of any connective, parenthesized unless it
    /// is a tuple or one token.
    #[cfg(test)]
    pub(crate) fn surface_operand(&self) -> Surface {
        self.surface_at(At::Prim)
    }

    /// The type in the surface syntax as the key of an arrow, `K -> V` or `K ->? V`, parenthesized
    /// where it would not be one: an arrow, and a tuple, which would read as the parameters.
    pub fn surface_key(&self) -> Surface {
        self.surface_at(At::Key)
    }

    /// The type in the surface syntax as a bound of `L .. U -> V`, parenthesized where it would
    /// not be one: an arrow.
    pub fn surface_bound(&self) -> Surface {
        self.surface_at(At::Bound)
    }

    /// The type in the surface syntax after `is`, where sec:grammar reads a `TypeUnion` (in
    /// `IsTest` and `IsPat`), parenthesized where it would not be one: an arrow. A union, a
    /// difference and an intersection are written bare, `is bool | int`; a bound of
    /// `L .. U -> V` is the same place ([`Type::surface_bound`]).
    pub(crate) fn surface_after_is(&self) -> Surface {
        self.surface_at(At::Bound)
    }

    /// The type in the surface syntax at `at`, parenthesized where the text would not be read
    /// there as one operand.
    pub(crate) fn surface_at(&self, at: At) -> Surface {
        Printer::default().print(&[(self.clone(), at)]).single()
    }

    /// The type in the surface syntax at `at`, each recursive member written by the name its
    /// group gives it, as `L(int | #x)`; a part of a definition kept unevaluated, and an atom's
    /// payload that is a recursive type as a whole, are unfolded once. A part used more than once
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

impl Printer {
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
        p.exact = true;
        for &(i, _) in &roots {
            p.walk(i);
        }
        p.canon(&roots);
        p.render(&roots)
    }
}

/// How a text binds, for parenthesizing it as an operand.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) enum Class {
    Arrow,
    Union,
    Diff,
    And,
    /// `(A, B)`: a primary, except as an arrow's key, where it would read as parameters.
    Tuple,
    Prim,
    /// The class of the one node the text is.
    Of(usize),
}

impl At {
    pub(crate) fn admits(self, c: Class) -> bool {
        use Class as C;
        match self {
            At::Any => true,
            At::Union => matches!(c, C::Union | C::And | C::Tuple | C::Prim),
            At::And => matches!(c, C::And | C::Tuple | C::Prim),
            At::DiffLeft => matches!(c, C::Diff | C::Tuple | C::Prim),
            At::Prim => matches!(c, C::Tuple | C::Prim),
            At::Key => matches!(c, C::Union | C::Diff | C::And | C::Prim),
            At::Bound => c != C::Arrow,
        }
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
    Rec(&'a str, &'a str, &'a Type),
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

/// An item's key: its contents, with a diagram node by its interned id.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Ty(Ctx, Type),
    TupleNode(Ctx, usize, u64),
    TupleExpr(Ctx, usize, Part<Row>, bool),
    MorphismNode(u64),
    MorphismExpr(Part<Morphism>, bool),
}

impl Item {
    fn key(&self) -> Key {
        match self {
            Item::Ty(c, t) => Key::Ty(c.clone(), t.clone()),
            Item::Tuples(c, n, p, not) => match p.view() {
                Ok(b) => Key::TupleNode(c.clone(), *n, node_id(b)),
                Err(_) => Key::TupleExpr(c.clone(), *n, p.clone(), *not),
            },
            Item::Morphisms(p, not) => match p.view() {
                Ok(b) => Key::MorphismNode(node_id(b)),
                Err(_) => Key::MorphismExpr(p.clone(), *not),
            },
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

fn node_id<A: super::bdd::Literal>(b: &Bdd<A>) -> u64 {
    b.branch().map_or_else(u64::from, |(id, ..)| id)
}

#[derive(Default)]
struct Printer {
    index: BTreeMap<Key, usize>,
    texts: Vec<Option<Text>>,
    uses: Vec<u32>,
    /// A recursive type, named however often it is used: its context, its name and the
    /// type, by whose order (its key) names alike are ranked ([`Printer::canon`]).
    forced: Vec<Option<(String, String, Type)>>,
    /// The nodes in the order the walk leaves them.
    post: Vec<usize>,
    /// Each node's item, until visited.
    items: Vec<Option<Item>>,
    exact: bool,
    /// Whether a recursive member is written by its group's name for it ([`Type::surface_by_name`]).
    by_name: bool,
    /// The value of each part met outside every atom, by its node's id ([`Printer::outside`]).
    outsides: HashMap<u64, bool>,
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

impl Printer {
    /// The text that refers to `item`, counting the use; `put` says where it stands.
    fn refer(&mut self, item: Item) -> Text {
        let key = item.key();
        let i = match self.index.get(&key) {
            Some(&i) => i,
            None => {
                let i = self.texts.len();
                self.index.insert(key, i);
                self.texts.push(None);
                self.uses.push(0);
                self.forced.push(None);
                self.items.push(Some(item));
                i
            }
        };
        self.uses[i] += 1;
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
                    let text = self.text(&item);
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

    /// Orders the elements of every group by their contents, so that the text does not depend
    /// on the order the parts' operands and literals were found in, which follows the atoms'
    /// digests (step BDD-atom-order). Each node gets a rank by its contents, as in the tree
    /// isomorphism test of Aho, Hopcroft and Ullman: the nodes are taken by height, those of
    /// one height ordered by their tokens, a child by its rank, each group's elements sorted
    /// first; a recursive type is a leaf ranked by its name, since every cycle passes through
    /// one. The walk's order is then found again, and with it the names' numbers.
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
    /// cut, a recursive type at height 0. Every cycle passes through a recursive type, so that
    /// graph has no cycle. The walk's order is not an order of it in which a node comes after
    /// those it names: the walk may enter a cycle at a node that is not a recursive type, such
    /// as a tuple diagram that a recursive type's unfolding shares with a part of its body kept
    /// unevaluated (`R0 = ((#a | #b), (#a | #b | R0)) \ (#b, #a)` enters at the diagram of
    /// `R0`'s unfolding, which names the part `#a | #b | R0`, whose unfolding names the
    /// diagram), and then the node that closes the cycle leaves before the one it names. So
    /// the heights come from a search of their own, depth first with a stack, each node
    /// entered once: time linear in the tokens of all texts.
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
                                Piece::Node(j, _) => Some(
                                    height[j].expect("every cycle passes through a recursive type"),
                                ),
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
            ),
            Item::Morphisms(p, not) => self.part(
                p,
                *not,
                &|me: &mut Printer, m: &Morphism| me.morphism(m),
                &|_: &mut Printer| every_morphism(),
                &|c: &Part<Morphism>, not| Item::Morphisms(c.clone(), not),
            ),
        }
    }

    fn ty(&mut self, ctx: &Ctx, t: &Type) -> Text {
        if let Node::Rec(r) = &*t.0 {
            // Written by name, a member is `name(args)`. A part kept unevaluated has no name, and
            // an atom's payload that is a recursive type as a whole has none of its own to follow
            // the atom's: each is unfolded once, as `#c(int, L(int))`, the recursive types inside
            // by name. An unfolding that is itself a recursive node gets a definition, as without
            // names.
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
                            return self.refer(Item::Ty(ctx.clone(), body));
                        }
                    }
                }
            }
            let i = self.index[&Key::Ty(ctx.clone(), t.clone())];
            let ctx_name = ctx.as_deref().unwrap_or("").to_string();
            self.forced[i] = Some((ctx_name, t.to_string(), t.clone()));
            let body = r.unfolding();
            return self.refer(Item::Ty(ctx.clone(), body));
        }
        let p = t.p();
        match ctx {
            None => {
                if *t == Type::top() {
                    return Text::word("_", Class::Prim);
                }
                if p.atoms.cofinite && p.tuples.rest && p.structs {
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

    /// The items of a type's union, kind by kind.
    fn items(&mut self, ctx: &Ctx, t: &Type) -> Vec<Text> {
        let p = t.p();
        let mut items = Vec::new();
        match p.bools {
            1 => items.push(Text::word("false", Class::Prim)),
            2 => items.push(Text::word("true", Class::Prim)),
            3 => items.push(Text::word("bool", Class::Prim)),
            _ => {}
        }
        for (name, l) in [
            ("int", &p.ints),
            ("rat", &p.rats),
            ("f64", &p.floats),
            ("String", &p.strings),
        ] {
            lits(&mut items, name, l);
        }
        if p.atoms.cofinite {
            let mut except: Vec<Text> = Vec::new();
            for (name, part) in p.atoms.names.iter() {
                self.atom(&mut except, name, &part.not());
            }
            items.push(match except.is_empty() {
                true => Text::word("#_", Class::Prim),
                false => minus(
                    "#_",
                    Text::joined(except, " | ", At::Union, Class::Union, ""),
                ),
            });
        } else {
            for (name, part) in p.atoms.names.iter() {
                self.atom(&mut items, name, part);
            }
        }
        self.tuples(&mut items, ctx, &p.tuples);
        if p.structs {
            items.push(match ctx {
                None => Text::word("{..}", Class::Prim),
                Some(a) => {
                    self.exact = false;
                    Text::word(format!("#{a}(struct)"), Class::Prim)
                }
            });
        }
        match p.morphisms.is_leaf() {
            Some(false) => {}
            Some(true) => items.push(every_morphism()),
            None => items.push(self.refer(Item::Morphisms(p.morphisms.clone(), false))),
        }
        items
    }

    fn atom(&mut self, items: &mut Vec<Text>, name: &Arc<str>, part: &super::AtomPart) {
        if part.bare {
            items.push(Text::word(format!("#{name}"), Class::Prim));
        }
        if part.payload != Type::empty() {
            items.push(self.refer(Item::Ty(Some(name.clone()), part.payload.clone())));
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
                if m.guarantee == m.permission {
                    " -> "
                } else {
                    " ->? "
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
    /// holds values outside every atom is written with `all`.
    fn part<A: super::bdd::Literal>(
        &mut self,
        p: &Part<A>,
        not: bool,
        lit: &dyn Fn(&mut Printer, &A) -> Text,
        all: &dyn Fn(&mut Printer) -> Text,
        item: &dyn Fn(&Part<A>, bool) -> Item,
    ) -> Text {
        // An operand: a leaf as text, otherwise a node of its own.
        let operand = |me: &mut Printer, (q, not): &(Part<A>, bool)| match q.is_leaf() {
            Some(true) => all(me),
            Some(false) => Text::word("Never", Class::Prim),
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
                return self.list(b, lit, all);
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
    // Complexity tradeoff: each diagram prints its own list, so the text is linear in the
    // lists of the distinct parts printed, where printing nodes was linear in their union.
    // Which blocks are turned over is found in two passes over the list, linear in it.
    fn list<A: super::bdd::Literal>(
        &mut self,
        b: &Bdd<A>,
        lit: &dyn Fn(&mut Printer, &A) -> Text,
        all: &dyn Fn(&mut Printer) -> Text,
    ) -> Text {
        let list = b.list();
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
        // of the literals; of value `false`, the atoms refused and those taken.
        let mut texts: Vec<(Vec<Text>, Vec<Text>)> = Vec::with_capacity(m);
        for ((_, lits), value) in list.blocks.iter().zip(&value) {
            let (mut first, mut taken) = (Vec::new(), Vec::new());
            for (a, t) in lits {
                let l = lit(self, a);
                match (value, t) {
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
        // The class of the text from each block on, `None` where it has no value.
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
                // `b \ (a | not rest)`, or `b` where the union has no value.
                (false, true) => Some(match (taken.is_empty() && next.is_none(), first.len()) {
                    (false, _) => Class::Diff,
                    (true, 1) => first[0].class,
                    (true, _) => Class::And,
                }),
                // A block of value `false` before no value leaves no value.
                (false, false) => next.map(|n| match (taken.is_empty(), first.len()) {
                    (false, _) => Class::Diff,
                    (true, 0) => n,
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
            if class[k].is_none() {
                break;
            }
            let last = class[k + 1].is_none();
            if turn[k] {
                let refused = Text::group(first, " & ", At::And, Class::And);
                if taken.is_empty() && last {
                    put(&mut segs, refused, at);
                    tail = None;
                    break;
                }
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

    /// The class a node shows: a name is a primary.
    fn class(&self, mut i: usize, named: &[Option<String>]) -> Class {
        loop {
            if named[i].is_some() {
                return Class::Prim;
            }
            match self.texts[i].as_ref().expect("visited").class {
                Class::Of(j) => i = j,
                c => return c,
            }
        }
    }

    /// The node whose name each node's text is, or `None`: a node whose text is one reference
    /// to another is that one's, and a named node whose text is not, or whose reference leads
    /// to no name, is its own. A named node whose text is so another node's name takes that
    /// name, rather than a definition `type T2 = T1;` of its own; each of its cycles passes
    /// through the node it names, which keeps a name. Each node is followed once, with a list
    /// of those whose answer waits on the next: time linear in the nodes.
    fn same_names(&self) -> Vec<Option<usize>> {
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
                        let own = self.named(i).then_some(i);
                        found[i] = Some(own);
                        break own;
                    }
                }
            };
            while let Some(i) = path.pop() {
                waiting[i] = false;
                if self.named(i) {
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
        let same = self.same_names();
        // Whether node `i` gets a definition: a named node whose name is its own.
        let defined = |i: usize| self.named(i) && same[i].is_none_or(|j| j == i);
        let mut defs = Vec::new();
        let collecting = defs::active();
        if collecting {
            self.collect(&same, &mut named);
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
        let roots = roots
            .iter()
            .map(|&(i, at)| {
                let mut out = String::new();
                self.write(&[Seg::Node(i, at)], &named, &mut out);
                out
            })
            .collect();
        Surfaces {
            defs,
            roots,
            exact: self.exact,
        }
    }

    /// While a message collects definitions (module `defs`): names each node that gets a
    /// definition by a reference to its place in the thread's table, merged with an equal
    /// definition there, and each node whose name is another's by that reference too. A
    /// definition whose body uses one not placed yet, as in a cycle, gets a place of its own
    /// first and its body after the others.
    fn collect(&self, same: &[Option<usize>], named: &mut [Option<String>]) {
        let defined = |i: usize| self.named(i) && same[i].is_none_or(|j| j == i);
        let mut aliases: Vec<Vec<usize>> = vec![Vec::new(); self.texts.len()];
        for &i in &self.post {
            if let Some(j) = same[i].filter(|&j| self.named(i) && j != i) {
                aliases[j].push(i);
            }
            if self.named(i) {
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
        for &i in &self.post {
            if !defined(i) {
                continue;
            }
            let b = body(i, named);
            let k = match b.contains(defs::WAIT) {
                true => {
                    let k = defs::reserve();
                    waiting.push((i, k));
                    k
                }
                false => defs::add(b),
            };
            let r = defs::reference(k);
            for &a in &aliases[i] {
                named[a] = Some(r.clone());
            }
            named[i] = Some(r);
        }
        for (i, k) in waiting {
            defs::fill(k, body(i, named));
        }
    }

    /// Writes `segs`, a node by its name or else its own text, with a stack of its own.
    fn write(&self, segs: &[Seg], named: &[Option<String>], out: &mut String) {
        let mut pieces = Pieces::new(segs);
        while let Some(piece) = pieces.next() {
            match piece {
                Piece::Str(s) => out.push_str(s),
                Piece::Node(i, at) => match &named[i] {
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

fn lits(items: &mut Vec<Text>, name: &str, l: &Lits) {
    let each = || {
        l.values
            .iter()
            .map(|v| Text::word(super::lit_text(v), Class::Prim))
    };
    match (l.cofinite, l.values.is_empty()) {
        (true, true) => items.push(Text::word(name, Class::Prim)),
        (true, false) => {
            let taken = Text::joined(each().collect(), " | ", At::Union, Class::Union, "Never");
            items.push(minus(name, taken));
        }
        (false, _) => items.extend(each()),
    }
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
mod tests {
    //! The text of a type does not depend on the order of its atoms (step BDD-atom-order).
    //! The order follows the digests, which differ between the full build and the
    //! short-addresses build; the test hook `SALT` changes every digest of a thread, so a type
    //! built on a thread of its own with a salt has its atoms in another order.

    use std::collections::BTreeMap;

    use super::super::bdd::Part;
    use super::super::{Op, Row, SALT, Type};
    use super::defs::{collect, holds, lift, plain};
    use crate::scaling;
    use crate::value::Value;

    fn next(seed: &mut u64) -> u64 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *seed >> 33
    }

    fn lit(i: u64) -> Type {
        Type::lit(&Value::Int(i as i64)).expect("an integer literal type")
    }

    fn leaf(seed: &mut u64, depth: u32) -> Type {
        let k = next(seed);
        match k % 7 {
            0 => Type::top(),
            1 | 2 => lit(k / 7 % 4),
            3 => Type::atom(&format!("a{}", k / 7 % 3)),
            4 if depth > 0 => ty(seed, depth - 1),
            5 => Type::exact(lit(k / 7 % 3), Type::int()),
            _ => Type::int(),
        }
    }

    /// A random type of unions, intersections, differences and complements of tuple types,
    /// some of them an atom's payload.
    fn ty(seed: &mut u64, depth: u32) -> Type {
        let k = next(seed);
        if depth == 0 || k.is_multiple_of(7) {
            let n = 1 + (k / 7 % 2) as usize;
            let t = Type::tuple(
                (0..n)
                    .map(|_| leaf(seed, depth.saturating_sub(2)))
                    .collect(),
            );
            return match k / 14 % 5 {
                0 => Type::atom_with("p", &t),
                _ => t,
            };
        }
        let a = ty(seed, depth - 1);
        match k % 4 {
            0 => &a | &ty(seed, depth - 1),
            1 => &a & &ty(seed, depth - 1),
            2 => &a - &ty(seed, depth - 1),
            _ => !&a,
        }
    }

    /// The parts of `t` kept as expressions.
    fn exprs(t: &Type) -> usize {
        let p = t.p();
        p.tuples.lens.values().filter(|q| q.view().is_err()).count()
            + usize::from(p.morphisms.view().is_err())
    }

    /// On a thread with `salt`: the texts of `n` random types in both printers, the number of
    /// their parts kept as expressions, and how 64 pairs of tuple types are ordered.
    fn texts(salt: u64, n: u64) -> (Vec<(String, String)>, usize, Vec<bool>) {
        std::thread::spawn(move || {
            SALT.set(salt);
            let mut kept = 0;
            let texts = (0..n)
                .map(|i| {
                    let mut seed = i * 7919 + 1;
                    let t = ty(&mut seed, 5);
                    kept += exprs(&t);
                    (t.to_string(), t.surface().to_string())
                })
                .collect();
            let order = (0..64)
                .map(|i| Row::new(vec![lit(i)]) < Row::new(vec![lit(i + 1)]))
                .collect();
            (texts, kept, order)
        })
        .join()
        .expect("the thread prints without panicking")
    }

    #[test]
    fn random_types_print_alike_in_every_order_of_their_atoms() {
        let n = 3000;
        let (want, kept, order) = texts(0, n);
        assert!(kept > 100, "the types keep parts as expressions: {kept}");
        for salt in [0x5555_aaaa_1234_9876, 0x0123_4567_89ab_cdef, u64::MAX] {
            let (got, _, other) = texts(salt, n);
            assert_ne!(order, other, "salt {salt:#x} orders the atoms otherwise");
            let differ: Vec<_> = (0..n as usize).filter(|&i| want[i] != got[i]).collect();
            assert!(
                differ.is_empty(),
                "salt {salt:#x}: {} of {n} types print otherwise, first {:?} and {:?}",
                differ.len(),
                want[differ[0]],
                got[differ[0]],
            );
        }
    }

    #[test]
    fn a_union_of_tuple_types_less_another_prints_alike_in_every_order() {
        // The case of L1.37a repair#1: the two builds printed `((0, #a0) | (1, #a1)) \ (1, _)`
        // and `(0, #a0) & ((_, _) \ (1, _)) | ((1, #a1) \ (1, _) \ (0, #a0))`.
        for salt in [0, 0x5555_aaaa_1234_9876, 0x0123_4567_89ab_cdef, u64::MAX] {
            let (display, surface) = std::thread::spawn(move || {
                SALT.set(salt);
                let a = Type::tuple(vec![lit(0), Type::atom("a0")]);
                let b = Type::tuple(vec![lit(1), Type::atom("a1")]);
                let t = &(&a | &b) - &Type::tuple(vec![lit(1), Type::top()]);
                (t.to_string(), t.surface().to_string())
            })
            .join()
            .expect("the thread prints without panicking");
            assert_eq!(surface, "((0, #a0) | (1, #a1)) \\ (1, _)", "salt {salt:#x}");
            assert_eq!(
                display, "(| (& (tuple 0 #a0) (! (tuple 1 _))) (& (tuple 1 #a1) (! (tuple 1 _))))",
                "salt {salt:#x}"
            );
        }
    }

    #[test]
    fn the_text_of_a_long_decision_list_scales() {
        // `((x0 | x1) \ x2 \ x3 | x4 | x5) \ x6 …`: blocks of two literals, values alternating,
        // each new literal first in the order, so the diagram is one node per atom.
        let build = |m: usize| {
            let mut xs: Vec<Row> = (0..m as u64).map(|i| Row::new(vec![lit(i)])).collect();
            xs.sort();
            let mut f = Part::literal(xs[m - 1].clone());
            for (i, x) in xs[..m - 1].iter().rev().enumerate() {
                f = match i / 2 % 2 {
                    0 => f.zip(&Part::literal(x.clone()).not(), Op::And),
                    _ => f.zip(&Part::literal(x.clone()), Op::Or),
                };
            }
            Type::with(|p| {
                p.tuples.lens.insert(1, f);
            })
        };
        let n = 1 << 10;
        let built: BTreeMap<usize, Type> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| (m, build(m)))
            .collect();
        scaling::check(
            "the text of a decision list of blocks of two, by atoms",
            n,
            |m| {
                let s = built[&m].surface();
                assert!(s.defs.is_empty());
                assert_eq!(
                    s.root.matches(" \\ ").count() + s.root.matches(" | ").count(),
                    m - 1
                );
            },
        );
    }

    fn defs_abc() -> Type {
        Type::atom("a") | Type::atom("b") | Type::atom("c")
    }

    #[test]
    fn a_shared_part_is_a_reference_while_collecting_and_reads_alone_as_before() {
        let t = Type::tuple(vec![defs_abc(), defs_abc(), defs_abc()]);
        let alone = t.surface().to_string();
        assert_eq!(alone, "type T1 = #a | #b | #c;\n(T1, T1, T1)");
        let _on = collect();
        let s = t.surface();
        assert!(s.defs.is_empty());
        assert!(holds(&s.root));
        assert_eq!(plain(&s.root), alone);
        // A type with no part used twice holds no reference.
        assert_eq!(defs_abc().surface().root, "#a | #b | #c");
    }

    #[test]
    fn one_message_has_one_numbering_and_each_definition_once() {
        let _on = collect();
        let x = Type::tuple(vec![defs_abc(), defs_abc()]).surface().root;
        let y = Type::tuple(vec![defs_abc(), defs_abc(), defs_abc()])
            .surface()
            .root;
        let ab = Type::atom("a") | Type::atom("b");
        let z = Type::tuple(vec![ab.clone(), ab]).surface().root;
        let mut message = format!("`f` does not take ({x}, {y})");
        let mut note = format!("`f` takes {z}");
        let defs = lift(&mut [&mut message, &mut note], &|_| false);
        assert_eq!(message, "`f` does not take ((T1, T1), (T1, T1, T1))");
        assert_eq!(note, "`f` takes (T2, T2)");
        assert_eq!(
            defs,
            [
                ("T1".to_string(), "#a | #b | #c".to_string()),
                ("T2".to_string(), "#a | #b".to_string())
            ]
        );
    }

    #[test]
    fn a_name_the_message_or_the_program_holds_is_skipped() {
        let _on = collect();
        let x = Type::tuple(vec![defs_abc(), defs_abc()]).surface().root;
        let mut message = format!("`T1` does not take {x}");
        let defs = lift(&mut [&mut message], &|w| w == "T2");
        assert_eq!(message, "`T1` does not take (T3, T3)");
        assert_eq!(defs[0].0, "T3");
    }

    #[test]
    fn a_difference_of_differences_prints_as_written() {
        // `A \ (B \ C)` is `A & ((all \ B) | C)`, which needs the top type `_` of L10 to write;
        // it prints as written, in the forms of L1 (READ-atom-meet).
        let a = Type::exact(Type::atom("a"), Type::int());
        let b = Type::partial(Type::atom("b"), Type::bool());
        let c = Type::exact(Type::int(), Type::empty());
        let t = &a - &(&b - &c);
        assert_eq!(
            t.surface().to_string(),
            "(#a -> int) \\ ((#b ->? bool) \\ (int -> Never))"
        );
        let d = Type::exact(Type::string(), Type::string());
        let t = &(&a - &d) - &(&b - &c);
        assert_eq!(
            t.surface().to_string(),
            "(#a -> int) \\ ((String -> String) | ((#b ->? bool) \\ (int -> Never)))"
        );
        // Tuples of one length the same.
        let row = |x: Type, y: Type| Type::tuple(vec![x, y]);
        let t =
            &row(a.clone(), a.clone()) - &(&row(b.clone(), a.clone()) - &row(b.clone(), c.clone()));
        assert_eq!(
            t.surface().to_string(),
            "type T1 = #a -> int;\ntype T2 = #b ->? bool;\n(T1, T1) \\ ((T2, T1) \\ (T2, int -> Never))"
        );
        // Every morphism but some is no type of L1, and keeps `_`.
        let t = &Type::universe(super::super::Universe::Morphism) - &a;
        assert_eq!(t.surface().to_string(), "(_ ->? _) \\ (#a -> int)");
    }

    /// A random part of 1-tuples over six rows, from literals, their complements, meets,
    /// unions and complements.
    fn random_part(seed: &mut u64, depth: u32) -> Part<Row> {
        let k = next(seed);
        if depth == 0 || k.is_multiple_of(5) {
            let l = Part::literal(Row::new(vec![lit(k / 5 % 6)]));
            return if (k / 30).is_multiple_of(2) {
                l
            } else {
                l.not()
            };
        }
        let a = random_part(seed, depth - 1);
        match k % 3 {
            0 => a.zip(&random_part(seed, depth - 1), Op::And),
            1 => a.zip(&random_part(seed, depth - 1), Op::Or),
            _ => a.not(),
        }
    }

    #[test]
    fn only_a_part_holding_values_outside_every_atom_prints_the_top_type() {
        // Item PRINT-kept-meet-all: a part prints `_` exactly when it holds the values outside
        // every atom it names, which no other text can write; a kept meet or complement whose
        // operand holds them, and that does not hold them itself, is written without `_`.
        let mut kept = 0;
        for i in 0..20000u64 {
            let mut seed = i * 7919 + 3;
            let p = random_part(&mut seed, 6);
            let outside = p.eval3(&|_| Some(false)).expect("every atom is known");
            kept += usize::from(p.view().is_err());
            let t = Type::with(|q| {
                q.tuples.lens.insert(1, p.clone());
            });
            let s = t.surface().to_string();
            assert_eq!(s.contains('_'), outside, "{s}");
        }
        // Most of the parts are kept expressions, not lists.
        assert!(kept > 5000, "{kept}");
    }
}
