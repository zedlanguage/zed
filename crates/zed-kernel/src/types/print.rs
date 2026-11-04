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
        p.render(Text {
            segs: vec![Seg::Node(i, at)],
            class: root.class,
        })
    }
}

/// How a text binds, for parenthesizing it as an operand.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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
    /// A recursive type, named however often it is used.
    forced: Vec<bool>,
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
                self.forced.push(false);
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
                    stack.extend(text.segs.iter().rev().filter_map(|s| match s {
                        Seg::Node(j, _) => Some(Step::Enter(*j)),
                        Seg::Str(_) => None,
                    }));
                    self.texts[i] = Some(text);
                }
            }
        }
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
            self.forced[i] = true;
            let body = r.body.get_or_init(|| (r.make)()).clone();
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

    /// A part: a diagram node as `a & hi | (lo \ a)`, or an expression's connective.
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
        let b = match p.view() {
            Err(form) => {
                return match form {
                    Form::Not(q) => {
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
                    Form::Or(x, y) => {
                        let x = operand(self, x);
                        let y = operand(self, y);
                        Text::joined(vec![x, y], " | ", At::Union, Class::Union, "!_")
                    }
                    Form::And(x, y) => {
                        let x = operand(self, x);
                        let y = operand(self, y);
                        Text::joined(vec![x, y], " & ", At::And, Class::And, "_")
                    }
                };
            }
            Ok(b) => b,
        };
        let Ok((_, a, hi, lo)) = b.branch() else {
            unreachable!("a leaf part is printed by its parent")
        };
        let side = |me: &mut Printer, d: &Bdd<A>| match d.branch() {
            Err(true) => all(me),
            Err(false) => Text::word("!_", Class::Prim),
            Ok(_) => me.refer(item(&Part::Bdd(d.clone()))),
        };
        let taken = |me: &mut Printer| lit(me, a);
        let (hi_leaf, lo_leaf) = (hi.branch().err(), lo.branch().err());
        // `a & hi`, or `a` when `hi` is every value.
        let with = |me: &mut Printer| match hi_leaf {
            Some(true) => taken(me),
            _ => {
                let a = taken(me);
                let h = side(me, hi);
                Text::joined(vec![a, h], " & ", At::And, Class::And, "_")
            }
        };
        // `lo \ a`.
        let without = |me: &mut Printer| {
            let l = side(me, lo);
            let a = taken(me);
            let mut segs = Vec::new();
            put(&mut segs, l, At::DiffLeft);
            segs.push(Seg::Str(" \\ ".into()));
            put(&mut segs, a, At::Prim);
            Text {
                segs,
                class: Class::Diff,
            }
        };
        match (hi_leaf, lo_leaf) {
            (_, Some(false)) => with(self),
            (Some(false), _) => without(self),
            (Some(true), _) => {
                let a = taken(self);
                let l = side(self, lo);
                Text::joined(vec![a, l], " | ", At::Union, Class::Union, "!_")
            }
            _ => {
                let w = with(self);
                let wo = without(self);
                Text::joined(vec![w, wo], " | ", At::Union, Class::Union, "!_")
            }
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
            let text = self.texts[i].as_ref().expect("visited");
            let token = matches!(&text.segs[..], [Seg::Str(s)] if !s.contains([' ', '(', ',']));
            if self.forced[i] || (self.uses[i] >= 2 && !token) {
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
        enum W<'a> {
            Segs(std::slice::Iter<'a, Seg>),
            Close,
        }
        let mut stack = vec![W::Segs(segs.iter())];
        while let Some(top) = stack.last_mut() {
            let W::Segs(it) = top else {
                out.push(')');
                stack.pop();
                continue;
            };
            let Some(seg) = it.next() else {
                stack.pop();
                continue;
            };
            match seg {
                Seg::Str(s) => out.push_str(s),
                Seg::Node(i, at) => match &named[*i] {
                    Some(name) => out.push_str(name),
                    None => {
                        let wrap = !at.admits(self.class(*i, named));
                        if wrap {
                            out.push('(');
                            stack.push(W::Close);
                        }
                        let text = self.texts[*i].as_ref().expect("visited");
                        stack.push(W::Segs(text.segs.iter()));
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
