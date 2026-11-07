//! `Debug` of [`Type`], and of the rows, morphisms, parts and diagrams it holds, written from
//! one stack of what is left to write, so a type nested to any depth is written on a small
//! stack. The text is the one line the derived `Debug`s write for `{:?}`, under `{:#?}` too,
//! but for what is reached by two edges or more: a type that holds other types, and a diagram
//! node or expression of a part. Such a node is written once, numbered, as `#k=Type(..)`,
//! `#k=Node(..)` or `#k=Expr(..)`, and after that as `#k#`, the notation of Common Lisp's
//! `*print-circle*`, so the text is linear in the nodes written, not in their paths. The numbers
//! count from 0 in the order the nodes are written. Types are told apart by value, so two equal
//! types are written once whether or not they share one node, and the text of a type is a
//! function of its value; diagram nodes and expressions by id, within one part.

use std::collections::{HashMap, HashSet};
use std::fmt;

use super::bdd::{Bdd, Form, Literal, Part};
use super::{Morphism, Node, Row, Type};

/// What is left to write.
#[derive(Clone, Copy)]
pub(super) enum Show<'a> {
    Text(&'static str),
    /// A part that holds no type, written by its own `Debug`.
    Leaf(&'a dyn fmt::Debug),
    /// A part that holds types, which queues its own text.
    Item(&'a dyn Queue),
    /// A type, written once if it is reached twice and holds other types.
    Type(&'a Type),
    /// A part or diagram, whose shared nodes are numbered apart from any other's.
    Graph(&'a dyn Vertex),
    /// A node of the part or diagram whose shared nodes are those of this scope.
    Below(&'a dyn Vertex, usize),
}

/// A part whose text is queued on the stack of what is left to write.
pub(super) trait Queue {
    /// Pushes the text of `self` onto `todo`, its first piece last.
    fn queue<'a>(&'a self, todo: &mut Vec<Show<'a>>);
}

/// A node of a part: a diagram node or leaf, an expression, or a part that is a diagram.
pub(super) trait Vertex {
    /// The node's id, unique in the process, if it can be shared.
    fn id(&self) -> Option<u64>;
    /// The nodes below it.
    fn children(&self) -> [Option<&dyn Vertex>; 2];
    /// Pushes the text of `self` onto `todo`, its nodes in `scope`, its first piece last.
    fn layout<'a>(&'a self, scope: usize, todo: &mut Vec<Show<'a>>);
}

/// The nodes of one part reached by two edges or more, keyed by id, each with its number once
/// it is written.
struct Scope {
    shared: HashMap<u64, Option<usize>>,
}

impl Scope {
    /// One pass over the nodes below `root`, each visited once.
    fn of(root: &dyn Vertex) -> Scope {
        let mut seen = HashSet::new();
        let mut shared = HashMap::new();
        seen.extend(root.id());
        let mut stack = vec![root];
        while let Some(v) = stack.pop() {
            for c in v.children().into_iter().flatten() {
                match c.id() {
                    Some(id) if !seen.insert(id) => {
                        shared.insert(id, None);
                    }
                    _ => stack.push(c),
                }
            }
        }
        Scope { shared }
    }
}

/// Whether the text of `t` holds the text of another type: an atom's payload, a row of a tuple
/// part, or a morphism. Only such a type is numbered; one that holds none is written in full at
/// each use, as a leaf of a diagram is.
fn holds_types(t: &Type) -> bool {
    match &*t.0 {
        Node::Rec(_) => false,
        Node::Parts(p, _) => {
            !p.atoms.names.is_empty()
                || p.tuples.lens.values().any(|q| q.is_leaf().is_none())
                || p.morphisms.is_leaf().is_none()
        }
    }
}

/// The types below `first` that are reached by two edges or more of the text and hold other
/// types, each with its number once it is written: one pass that queues the text as [`run`]
/// does, writing nothing, and queues each type and each node of a part once.
fn shared_types<'a>(first: Show<'a>) -> HashMap<&'a Type, Option<usize>> {
    let mut seen: HashSet<&Type> = HashSet::new();
    let mut shared = HashMap::new();
    let mut scopes: Vec<HashSet<u64>> = Vec::new();
    let mut todo = vec![first];
    while let Some(s) = todo.pop() {
        match s {
            Show::Text(_) | Show::Leaf(_) => {}
            Show::Item(x) => x.queue(&mut todo),
            Show::Type(t) => {
                if !holds_types(t) {
                    continue;
                }
                if seen.insert(t) {
                    t.queue(&mut todo);
                } else {
                    shared.insert(t, None);
                }
            }
            Show::Graph(v) => {
                scopes.push(HashSet::new());
                todo.push(Show::Below(v, scopes.len() - 1));
            }
            Show::Below(v, s) => {
                if v.id().is_none_or(|id| scopes[s].insert(id)) {
                    v.layout(s, &mut todo);
                }
            }
        }
    }
    shared
}

/// Pushes `parts`, to be written in the order given.
fn put<'a>(todo: &mut Vec<Show<'a>>, parts: Vec<Show<'a>>) {
    todo.extend(parts.into_iter().rev());
}

/// Writes `#k=` and gives `mark` the next number if it has none; writes `#k#` and answers
/// `false`, nothing more to write, if it has one.
fn number(
    mark: &mut Option<usize>,
    next: &mut usize,
    f: &mut fmt::Formatter<'_>,
) -> Result<bool, fmt::Error> {
    if let Some(k) = mark {
        write!(f, "#{k}#")?;
        return Ok(false);
    }
    let k = *next;
    *next += 1;
    *mark = Some(k);
    write!(f, "#{k}=")?;
    Ok(true)
}

/// Writes `first` and all it holds.
pub(super) fn run(first: Show<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut types = shared_types(first);
    let mut todo = vec![first];
    let mut scopes: Vec<Scope> = Vec::new();
    let mut next = 0;
    while let Some(s) = todo.pop() {
        match s {
            Show::Text(s) => f.write_str(s)?,
            Show::Leaf(x) => write!(f, "{x:?}")?,
            Show::Item(x) => x.queue(&mut todo),
            Show::Type(t) => {
                let more = match types.get_mut(t) {
                    Some(mark) => number(mark, &mut next, f)?,
                    None => true,
                };
                if more {
                    t.queue(&mut todo);
                }
            }
            Show::Graph(v) => {
                scopes.push(Scope::of(v));
                todo.push(Show::Below(v, scopes.len() - 1));
            }
            Show::Below(v, s) => {
                let more = match v.id().and_then(|id| scopes[s].shared.get_mut(&id)) {
                    Some(mark) => number(mark, &mut next, f)?,
                    None => true,
                };
                if more {
                    v.layout(s, &mut todo);
                }
            }
        }
    }
    Ok(())
}

impl Queue for Type {
    fn queue<'a>(&'a self, todo: &mut Vec<Show<'a>>) {
        put(
            todo,
            vec![Show::Text("Type("), Show::Item(&*self.0), Show::Text(")")],
        );
    }
}

impl Queue for Node {
    fn queue<'a>(&'a self, todo: &mut Vec<Show<'a>>) {
        use Show::{Leaf, Text};
        let p = match self {
            Node::Rec(r) => return put(todo, vec![Text("Rec("), Leaf(r), Text(")")]),
            Node::Parts(p, _) => p,
        };
        let mut w = vec![
            Text("Parts(Parts { digest: "),
            Leaf(&p.digest),
            Text(", bools: "),
            Leaf(&p.bools),
            Text(", ints: "),
            Leaf(&p.ints),
            Text(", rats: "),
            Leaf(&p.rats),
            Text(", floats: "),
            Leaf(&p.floats),
            Text(", strings: "),
            Leaf(&p.strings),
            Text(", atoms: Atoms { cofinite: "),
            Leaf(&p.atoms.cofinite),
            Text(", names: {"),
        ];
        for (i, (name, a)) in p.atoms.names.iter().enumerate() {
            if i > 0 {
                w.push(Text(", "));
            }
            w.extend([
                Leaf(name),
                Text(": AtomPart { bare: "),
                Leaf(&a.bare),
                Text(", payload: "),
                Show::Type(&a.payload),
                Text(" }"),
            ]);
        }
        w.extend([
            Text("}, sum: "),
            Leaf(&p.atoms.sum),
            Text(" }, tuples: Tuples { rest: "),
            Leaf(&p.tuples.rest),
            Text(", lens: {"),
        ]);
        for (i, (len, part)) in p.tuples.lens.iter().enumerate() {
            if i > 0 {
                w.push(Text(", "));
            }
            w.extend([Leaf(len), Text(": "), Show::Graph(part)]);
        }
        w.extend([
            Text("} }, structs: "),
            Leaf(&p.structs),
            Text(", morphisms: "),
            Show::Graph(&p.morphisms),
            Text(" })"),
        ]);
        put(todo, w);
    }
}

impl Queue for Row {
    fn queue<'a>(&'a self, todo: &mut Vec<Show<'a>>) {
        let mut w = vec![Show::Text("[")];
        for (i, t) in self.0.items.iter().enumerate() {
            if i > 0 {
                w.push(Show::Text(", "));
            }
            w.push(Show::Type(t));
        }
        w.push(Show::Text("]"));
        put(todo, w);
    }
}

impl Queue for Morphism {
    fn queue<'a>(&'a self, todo: &mut Vec<Show<'a>>) {
        put(
            todo,
            vec![
                Show::Text("Morphism { guarantee: "),
                Show::Type(&self.guarantee),
                Show::Text(", permission: "),
                Show::Type(&self.permission),
                Show::Text(", value: "),
                Show::Type(&self.value),
                Show::Text(" }"),
            ],
        );
    }
}

impl<A: Literal> Vertex for Part<A> {
    fn id(&self) -> Option<u64> {
        self.expr_id()
    }

    fn children(&self) -> [Option<&dyn Vertex>; 2] {
        match self.view() {
            Ok(b) => [Some(b), None],
            Err(Form::Not(p)) => [Some(p), None],
            Err(Form::Or(p, q) | Form::And(p, q)) => [Some(p), Some(q)],
        }
    }

    fn layout<'a>(&'a self, s: usize, todo: &mut Vec<Show<'a>>) {
        use Show::{Below, Text};
        put(
            todo,
            match self.view() {
                Ok(b) => vec![Text("Bdd("), Below(b, s), Text(")")],
                Err(Form::Not(p)) => vec![Text("Expr(Not("), Below(p, s), Text("))")],
                Err(Form::Or(p, q)) => {
                    vec![
                        Text("Expr(Or("),
                        Below(p, s),
                        Text(", "),
                        Below(q, s),
                        Text("))"),
                    ]
                }
                Err(Form::And(p, q)) => {
                    vec![
                        Text("Expr(And("),
                        Below(p, s),
                        Text(", "),
                        Below(q, s),
                        Text("))"),
                    ]
                }
            },
        );
    }
}

impl<A: Literal> Vertex for Bdd<A> {
    fn id(&self) -> Option<u64> {
        self.branch().ok().map(|(id, ..)| id)
    }

    fn children(&self) -> [Option<&dyn Vertex>; 2] {
        match self.branch() {
            Ok((_, _, hi, lo)) => [Some(hi), Some(lo)],
            Err(_) => [None, None],
        }
    }

    fn layout<'a>(&'a self, s: usize, todo: &mut Vec<Show<'a>>) {
        use Show::{Below, Item, Text};
        match self.branch() {
            Err(b) => todo.push(Text(if b { "true" } else { "false" })),
            Ok((_, atom, hi, lo)) => put(
                todo,
                vec![
                    Text("Node("),
                    Item(atom),
                    Text(", "),
                    Below(hi, s),
                    Text(", "),
                    Below(lo, s),
                    Text(")"),
                ],
            ),
        }
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(Show::Type(self), f)
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(Show::Item(self), f)
    }
}

impl fmt::Debug for Row {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(Show::Item(self), f)
    }
}

impl fmt::Debug for Morphism {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(Show::Item(self), f)
    }
}

impl<A: Literal> fmt::Debug for Part<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(Show::Graph(self), f)
    }
}

impl<A: Literal> fmt::Debug for Bdd<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(Show::Graph(self), f)
    }
}
