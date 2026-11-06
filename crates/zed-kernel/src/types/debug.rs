//! `Debug` of [`Type`], and of the rows, morphisms, parts and diagrams it holds, written from
//! one stack of what is left to write, so a type nested to any depth is written on a small
//! stack. The text is the one line the derived `Debug`s write for `{:?}`, under `{:#?}` too.

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
    /// A diagram.
    Diagram(&'a dyn Diagram),
}

/// A part whose text is queued on the stack of what is left to write.
pub(super) trait Queue {
    /// Pushes the text of `self` onto `todo`, its first piece last.
    fn queue<'a>(&'a self, todo: &mut Vec<Show<'a>>);
}

/// A diagram node's id, atom, `hi` and `lo`.
type Split<'a> = (u64, &'a dyn Queue, &'a dyn Diagram, &'a dyn Diagram);

/// A diagram of any universe, seen as a node or a leaf.
pub(super) trait Diagram {
    /// The node's id, atom, `hi` and `lo`, or the leaf's value.
    fn split(&self) -> Result<Split<'_>, bool>;
}

/// Pushes `parts`, to be written in the order given.
fn put<'a>(todo: &mut Vec<Show<'a>>, parts: Vec<Show<'a>>) {
    todo.extend(parts.into_iter().rev());
}

/// Writes `first` and all it holds.
pub(super) fn run(first: Show<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut todo = vec![first];
    while let Some(s) = todo.pop() {
        match s {
            Show::Text(s) => f.write_str(s)?,
            Show::Leaf(x) => write!(f, "{x:?}")?,
            Show::Item(x) => x.queue(&mut todo),
            Show::Diagram(d) => match d.split() {
                Err(b) => write!(f, "{b}")?,
                Ok((_, atom, hi, lo)) => put(
                    &mut todo,
                    vec![
                        Show::Text("Node("),
                        Show::Item(atom),
                        Show::Text(", "),
                        Show::Diagram(hi),
                        Show::Text(", "),
                        Show::Diagram(lo),
                        Show::Text(")"),
                    ],
                ),
            },
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
            w.extend([Leaf(len), Text(": "), Item(part)]);
        }
        w.extend([
            Text("} }, structs: "),
            Leaf(&p.structs),
            Text(", morphisms: "),
            Item(&p.morphisms),
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

impl<A: Literal> Queue for Part<A> {
    fn queue<'a>(&'a self, todo: &mut Vec<Show<'a>>) {
        put(
            todo,
            match self.view() {
                Ok(b) => vec![Show::Text("Bdd("), Show::Diagram(b), Show::Text(")")],
                Err(form) => vec![Show::Text("Expr("), Show::Item(form), Show::Text(")")],
            },
        );
    }
}

impl<A: Literal> Queue for Form<A> {
    fn queue<'a>(&'a self, todo: &mut Vec<Show<'a>>) {
        use Show::{Item, Text};
        put(
            todo,
            match self {
                Form::Not(p) => vec![Text("Not("), Item(p), Text(")")],
                Form::Or(p, q) => vec![Text("Or("), Item(p), Text(", "), Item(q), Text(")")],
                Form::And(p, q) => vec![Text("And("), Item(p), Text(", "), Item(q), Text(")")],
            },
        );
    }
}

impl<A: Literal> Diagram for Bdd<A> {
    fn split(&self) -> Result<Split<'_>, bool> {
        self.branch().map(|(id, atom, hi, lo)| {
            (
                id,
                atom as &dyn Queue,
                hi as &dyn Diagram,
                lo as &dyn Diagram,
            )
        })
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
        run(Show::Item(self), f)
    }
}

impl<A: Literal> fmt::Debug for Form<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(Show::Item(self), f)
    }
}

impl<A: Literal> fmt::Debug for Bdd<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(Show::Diagram(self), f)
    }
}
