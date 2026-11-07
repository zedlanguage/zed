//! Types in the surface syntax (cross-review xe, SYNTHESIS Q5): the text a message shows, which a
//! user can write back.
//!
//! One walk over the whole type graph: the types, and the nodes of the decision diagrams of
//! their tuple and morphism parts. Each node is visited once, keyed by its contents (a type, or
//! a diagram node's interned id), never by its address. A node used twice or more, unless its
//! text is one token, gets a definition `type Tk = …;`, numbered in the order the walk leaves
//! the nodes; a recursive type always gets one, so a cycle prints as definitions that refer to
//! each other. So the text is linear in the graph, however many paths its diagrams have.
//!
//! A diagram node over the tuple type `a`, with `hi` and `lo`, is `a & hi | (lo \ a)`, and
//! the cases where `hi` or `lo` is a leaf drop the parts that are empty. A part kept as its
//! operands prints its connective. A type with every other atom, every tuple length not listed
//! and every struct prints as `_ \ c`, `c` its complement. Every atom, every tuple and every
//! struct alone print as the kind-wide types `#_`, `(..)` and `{..}` (step L1.40d), and an atom
//! `#a` with any payload as `#a(..)`, so `#a(_)` is only the one-tuple payload. An atom's
//! payload of every tuple but not every struct, or the reverse, has no surface type: it prints
//! as `#a(tuple)` or `#a(struct)` and is marked not exact.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use super::bdd::{Bdd, Form, Part};
use super::{Lits, Morphism, Node, Row, Tuples, Type};

/// A type in the surface syntax: the definitions it needs, in order, then the type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Surface {
    /// Each definition's name and body.
    pub defs: Vec<(String, String)>,
    /// The type, which may name the definitions.
    pub root: String,
    /// Whether every word is in the surface syntax (the module comment names the exceptions).
    pub exact: bool,
}

impl fmt::Display for Surface {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, body) in &self.defs {
            write!(f, "type {name} = {body}; ")?;
        }
        f.write_str(&self.root)
    }
}

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

    fn surface_at(&self, at: At) -> Surface {
        let mut p = Printer::default();
        let root = p.refer(Item::Ty(None, self.clone()));
        let Seg::Node(i, _) = root.segs[0] else {
            unreachable!("a reference is one node")
        };
        p.walk(i);
        p.canon(i);
        p.render(Text {
            segs: vec![Seg::Node(i, at)],
            class: root.class,
        })
    }
}

/// How a text binds, for parenthesizing it as an operand.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Class {
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

/// Where a text stands, and so which classes it may have there unparenthesized.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum At {
    Any,
    Union,
    And,
    DiffLeft,
    Prim,
    Key,
    Bound,
}

impl At {
    fn admits(self, c: Class) -> bool {
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

/// A node of the walk.
enum Item {
    Ty(Ctx, Type),
    Tuples(Ctx, usize, Part<Row>),
    Morphisms(Part<Morphism>),
}

/// An item's key: its contents, with a diagram node by its interned id.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Ty(Ctx, Type),
    TupleNode(Ctx, usize, u64),
    TupleExpr(Ctx, usize, Part<Row>),
    MorphismNode(u64),
    MorphismExpr(Part<Morphism>),
}

impl Item {
    fn key(&self) -> Key {
        match self {
            Item::Ty(c, t) => Key::Ty(c.clone(), t.clone()),
            Item::Tuples(c, n, p) => match p.view() {
                Ok(b) => Key::TupleNode(c.clone(), *n, node_id(b)),
                Err(_) => Key::TupleExpr(c.clone(), *n, p.clone()),
            },
            Item::Morphisms(p) => match p.view() {
                Ok(b) => Key::MorphismNode(node_id(b)),
                Err(_) => Key::MorphismExpr(p.clone()),
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
        self.exact = true;
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

    /// The walk's order again, over the texts as [`Printer::canon`] ordered them.
    fn order(&mut self, root: usize) {
        let mut seen = vec![false; self.texts.len()];
        self.post.clear();
        let mut stack = vec![Step::Enter(root)];
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
    fn canon(&mut self, root: usize) {
        let n = self.texts.len();
        let mut height: Vec<Option<usize>> =
            self.forced.iter().map(|f| f.as_ref().map(|_| 0)).collect();
        for &i in &self.post {
            if height[i].is_some() {
                continue;
            }
            let segs = &self.texts[i].as_ref().expect("visited").segs;
            let h = Pieces::new(segs)
                .filter_map(|p| match p {
                    Piece::Node(j, _) => Some(
                        height[j]
                            .expect("a node leaves after those it names, but a recursive type"),
                    ),
                    Piece::Str(_) => None,
                })
                .max()
                .unwrap_or(0);
            height[i] = Some(h + 1);
        }
        let mut levels: Vec<Vec<usize>> = Vec::new();
        for (i, h) in height.into_iter().enumerate() {
            let h = h.expect("the walk leaves every node");
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
        self.order(root);
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
            Item::Tuples(ctx, n, p) => self.part(
                p,
                &|me: &mut Printer, r: &Row| me.row(ctx, *n, Some(r)),
                &|me: &mut Printer| me.row(ctx, *n, None),
                &|c: &Part<Row>| Item::Tuples(ctx.clone(), *n, c.clone()),
            ),
            Item::Morphisms(p) => self.part(
                p,
                &|me: &mut Printer, m: &Morphism| me.morphism(m),
                &|_: &mut Printer| every_morphism(),
                &|c: &Part<Morphism>| Item::Morphisms(c.clone()),
            ),
        }
    }

    fn ty(&mut self, ctx: &Ctx, t: &Type) -> Text {
        if let Node::Rec(r) = &*t.0 {
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
                Text::joined(items, " | ", At::Union, Class::Union, "!_")
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
                Text::joined(items, " | ", At::Union, Class::Union, "!_")
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
            let mut except = Vec::new();
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
            None => items.push(self.refer(Item::Morphisms(p.morphisms.clone()))),
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
                None => items.push(self.refer(Item::Tuples(ctx.clone(), *n, part.clone()))),
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
            class: match ctx {
                None => Class::Tuple,
                Some(_) => Class::Prim,
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

    /// A part: a diagram from its decision list ([`Printer::list`]), or an expression's
    /// connective, its operands in any order.
    fn part<A: super::bdd::Literal>(
        &mut self,
        p: &Part<A>,
        lit: &dyn Fn(&mut Printer, &A) -> Text,
        all: &dyn Fn(&mut Printer) -> Text,
        item: &dyn Fn(&Part<A>) -> Item,
    ) -> Text {
        // An operand: a leaf as text, otherwise a node of its own.
        let operand = |me: &mut Printer, q: &Part<A>| match q.is_leaf() {
            Some(true) => all(me),
            Some(false) => Text::word("!_", Class::Prim),
            None => me.refer(item(q)),
        };
        match p.view() {
            Ok(b) => self.list(b, lit, all),
            Err(Form::Not(q)) => {
                let q = operand(self, q);
                let mut segs = Vec::new();
                put(&mut segs, all(self), At::DiffLeft);
                segs.push(Seg::Str(" \\ ".into()));
                put(&mut segs, q, At::Prim);
                Text {
                    segs,
                    class: Class::Diff,
                }
            }
            Err(Form::Or(x, y)) => {
                let x = operand(self, x);
                let y = operand(self, y);
                Text::group(vec![x, y], " | ", At::Union, Class::Union)
            }
            Err(Form::And(x, y)) => {
                let x = operand(self, x);
                let y = operand(self, y);
                Text::group(vec![x, y], " & ", At::And, Class::And)
            }
        }
    }

    /// A diagram from its decision list in its one form (module `bdd::list`), which does not
    /// depend on the order of the atoms. A block of value `true` is the union of its literals
    /// and the rest, `a | (all \ b) | rest`; a block of value `false` is the rest without its
    /// literals, `b & rest \ a`, `a` an atom the block's literals take and `b` one they refuse.
    /// The literals of a block are a group. The text is written from the first block on into
    /// one list of segments, with a stack of what closes the blocks begun, so that no block's
    /// text is copied into the text before it.
    // Complexity tradeoff: each diagram prints its own list, so the text is linear in the
    // lists of the distinct parts printed, where printing nodes was linear in their union.
    fn list<A: super::bdd::Literal>(
        &mut self,
        b: &Bdd<A>,
        lit: &dyn Fn(&mut Printer, &A) -> Text,
        all: &dyn Fn(&mut Printer) -> Text,
    ) -> Text {
        let list = b.list();
        let m = list.blocks.len();
        let every = list.tail;
        let mut tail = every.then(|| all(self));
        // The texts of each block's literals: of value `true`, `a` and `all \ b` in the order
        // of the literals; of value `false`, the atoms refused and those taken.
        let mut texts: Vec<(Vec<Text>, Vec<Text>)> = Vec::with_capacity(m);
        for (value, lits) in list.blocks.iter().rev() {
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
        texts.reverse();
        // The class of the text from each block on, `None` where it has no value.
        let mut class = vec![None; m + 1];
        class[m] = tail.as_ref().map(|t| t.class);
        for k in (0..m).rev() {
            let (first, taken) = &texts[k];
            let next = class[k + 1];
            class[k] = match list.blocks[k].0 {
                true => Some(match (first.len(), next) {
                    (1, None) => first[0].class,
                    _ => Class::Union,
                }),
                // A block of value `false` before no value leaves no value.
                false => next.map(|n| match (taken.is_empty(), first.len()) {
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
        for (k, (first, taken)) in texts.into_iter().enumerate() {
            if class[k].is_none() {
                break;
            }
            let last = class[k + 1].is_none();
            if list.blocks[k].0 {
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

    fn render(&self, root: Text) -> Surface {
        let mut named: Vec<Option<String>> = vec![None; self.texts.len()];
        let mut defs = Vec::new();
        let mut k = 0;
        for &i in &self.post {
            if self.named(i) {
                k += 1;
                named[i] = Some(format!("T{k}"));
            }
        }
        for &i in &self.post {
            if let Some(name) = &named[i] {
                let mut body = String::new();
                self.write(
                    &self.texts[i].as_ref().expect("visited").segs,
                    &named,
                    &mut body,
                );
                defs.push((name.clone(), body));
            }
        }
        let mut out = String::new();
        self.write(&root.segs, &named, &mut out);
        Surface {
            defs,
            root: out,
            exact: self.exact,
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
            let taken = Text::joined(each().collect(), " | ", At::Union, Class::Union, "!_");
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

/// Every morphism: no key promised, any key permitted, any value.
fn every_morphism() -> Text {
    Text::word("!_ .. _ -> _", Class::Arrow)
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
}
