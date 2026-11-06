//! `Debug` of [`Type`], and of the rows, morphisms, parts and diagrams it holds, written from
//! one stack of what is left to write, so a type nested to any depth is written on a small
//! stack. The text is the one line the derived `Debug`s write for `{:?}`, under `{:#?}` too,
//! but for the diagram nodes and expressions of a part reached by two edges or more: such a
//! node is written once, numbered, as `#k=Node(..)` or `#k=Expr(..)`, and after that as `#k#`,
//! the notation of Common Lisp's `*print-circle*`, so the text of a part is linear in its nodes,
//! not in its paths. The numbers count from 0 in each part, in the order the nodes are written,
//! so equal parts have equal texts and the text names the part.

use std::collections::{HashMap, HashSet};
use std::fmt;

use super::bdd::{Bdd, Form, Literal, Part};
use super::{Morphism, Node, Row, Type};

/// What is left to write.
pub(super) enum Show<'a> {
    Text(&'static str),
    /// A part that holds no type, written by its own `Debug`.
    Leaf(&'a dyn fmt::Debug),
    /// A part that holds types, which queues its own text.
    Item(&'a dyn Queue),
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
/// it is written, and the next number.
struct Scope {
    shared: HashMap<u64, Option<usize>>,
    next: usize,
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
        Scope { shared, next: 0 }
    }
}

/// Pushes `parts`, to be written in the order given.
fn put<'a>(todo: &mut Vec<Show<'a>>, parts: Vec<Show<'a>>) {
    todo.extend(parts.into_iter().rev());
}

/// Writes `first` and all it holds.
pub(super) fn run(first: Show<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut todo = vec![first];
    let mut scopes: Vec<Scope> = Vec::new();
    while let Some(s) = todo.pop() {
        match s {
            Show::Text(s) => f.write_str(s)?,
            Show::Leaf(x) => write!(f, "{x:?}")?,
            Show::Item(x) => x.queue(&mut todo),
            Show::Graph(v) => {
                scopes.push(Scope::of(v));
                todo.push(Show::Below(v, scopes.len() - 1));
            }
            Show::Below(v, s) => {
                let scope = &mut scopes[s];
                match v.id().and_then(|id| scope.shared.get_mut(&id)) {
                    Some(Some(k)) => {
                        write!(f, "#{k}#")?;
                        continue;
                    }
                    Some(mark) => {
                        let k = scope.next;
                        scope.next += 1;
                        *mark = Some(k);
                        write!(f, "#{k}=")?;
                    }
                    None => {}
                }
                v.layout(s, &mut todo);
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
        use Show::{Item, Leaf, Text};
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
                Item(&a.payload),
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
        for (i, t) in self.0.1.iter().enumerate() {
            if i > 0 {
                w.push(Show::Text(", "));
            }
            w.push(Show::Item(t));
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
                Show::Item(&self.guarantee),
                Show::Text(", permission: "),
                Show::Item(&self.permission),
                Show::Text(", value: "),
                Show::Item(&self.value),
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
        run(Show::Item(self), f)
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
