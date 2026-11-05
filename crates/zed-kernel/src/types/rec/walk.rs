//! `Clone`, `==` and `Debug` of [`Expr`], and `==` and `Debug` of a body's tree ([`Node`]), each
//! keeping its own stack on the heap, so an expression of any depth is copied, compared and
//! written on a small stack (COMPLEXITY.md K39). Each costs O(size). `Debug` writes the one line
//! a derived `Debug` writes for `{:?}`, under `{:#?}` too.

use std::fmt;
use std::sync::Arc;

use super::{Expr, Node, Shape};

/// An expression or tree: its parts below, and what it holds besides them.
pub(super) trait Tree: Sized {
    /// The parts directly below, in order.
    fn kids(&self) -> impl DoubleEndedIterator<Item = &Self>;

    /// Whether the two hold the same besides their parts below, and as many of those.
    fn same_head(&self, other: &Self) -> bool;

    /// Writes the text before the parts below, and gives the text after them.
    fn open(&self, f: &mut fmt::Formatter<'_>) -> Result<&'static str, fmt::Error>;
}

impl Expr {
    /// The parts of `self` directly below it, in order.
    pub(super) fn kids(&self) -> impl DoubleEndedIterator<Item = &Expr> {
        let (list, boxes): (&[Expr], [Option<&Expr>; 3]) = match self {
            Expr::Param(_) | Expr::Type(_) => (&[], [None; 3]),
            Expr::Ref(_, xs)
            | Expr::Union(xs)
            | Expr::And(xs)
            | Expr::Tuple(xs)
            | Expr::Atom(_, xs) => (xs, [None; 3]),
            Expr::Not(a) => (&[], [Some(a), None, None]),
            Expr::Diff(a, b) => (&[], [Some(a), Some(b), None]),
            Expr::Morphism(l, u, v) => (&[], [Some(l), Some(u), Some(v)]),
        };
        list.iter().chain(boxes.into_iter().flatten())
    }
}

impl Shape {
    /// The trees directly below `self`, in order.
    pub(super) fn kids(&self) -> impl DoubleEndedIterator<Item = &Arc<Node>> {
        let (list, boxes): (&[Arc<Node>], [Option<&Arc<Node>>; 3]) = match self {
            Shape::Param(_) | Shape::Type(_) => (&[], [None; 3]),
            Shape::Ref(_, xs)
            | Shape::Union(xs)
            | Shape::And(xs)
            | Shape::Tuple(xs)
            | Shape::Atom(_, xs) => (xs, [None; 3]),
            Shape::Not(a) => (&[], [Some(a), None, None]),
            Shape::Diff(a, b) => (&[], [Some(a), Some(b), None]),
            Shape::Morphism(l, u, v) => (&[], [Some(l), Some(u), Some(v)]),
        };
        list.iter().chain(boxes.into_iter().flatten())
    }

    fn same_head(&self, other: &Shape) -> bool {
        match (self, other) {
            (Shape::Param(i), Shape::Param(j)) => i == j,
            (Shape::Ref(i, xs), Shape::Ref(j, ys)) => i == j && xs.len() == ys.len(),
            (Shape::Type(s), Shape::Type(t)) => s == t,
            (Shape::Union(xs), Shape::Union(ys))
            | (Shape::And(xs), Shape::And(ys))
            | (Shape::Tuple(xs), Shape::Tuple(ys)) => xs.len() == ys.len(),
            (Shape::Atom(m, xs), Shape::Atom(n, ys)) => m == n && xs.len() == ys.len(),
            (Shape::Not(_), Shape::Not(_))
            | (Shape::Diff(..), Shape::Diff(..))
            | (Shape::Morphism(..), Shape::Morphism(..)) => true,
            _ => false,
        }
    }

    fn open(&self, f: &mut fmt::Formatter<'_>) -> Result<&'static str, fmt::Error> {
        Ok(match self {
            Shape::Param(i) => {
                write!(f, "Param({i:?}")?;
                ")"
            }
            Shape::Type(t) => {
                write!(f, "Type({t:?}")?;
                ")"
            }
            Shape::Ref(i, _) => {
                write!(f, "Ref({i:?}, [")?;
                "])"
            }
            Shape::Union(_) => {
                f.write_str("Union([")?;
                "])"
            }
            Shape::And(_) => {
                f.write_str("And([")?;
                "])"
            }
            Shape::Tuple(_) => {
                f.write_str("Tuple([")?;
                "])"
            }
            Shape::Atom(name, _) => {
                write!(f, "Atom({name:?}, [")?;
                "])"
            }
            Shape::Not(_) => {
                f.write_str("Not(")?;
                ")"
            }
            Shape::Diff(..) => {
                f.write_str("Diff(")?;
                ")"
            }
            Shape::Morphism(..) => {
                f.write_str("Morphism(")?;
                ")"
            }
        })
    }
}

impl Tree for Expr {
    fn kids(&self) -> impl DoubleEndedIterator<Item = &Expr> {
        Expr::kids(self)
    }

    fn same_head(&self, other: &Expr) -> bool {
        match (self, other) {
            (Expr::Param(i), Expr::Param(j)) => i == j,
            (Expr::Ref(i, xs), Expr::Ref(j, ys)) => i == j && xs.len() == ys.len(),
            (Expr::Type(s), Expr::Type(t)) => s == t,
            (Expr::Union(xs), Expr::Union(ys))
            | (Expr::And(xs), Expr::And(ys))
            | (Expr::Tuple(xs), Expr::Tuple(ys)) => xs.len() == ys.len(),
            (Expr::Atom(m, xs), Expr::Atom(n, ys)) => m == n && xs.len() == ys.len(),
            (Expr::Not(_), Expr::Not(_))
            | (Expr::Diff(..), Expr::Diff(..))
            | (Expr::Morphism(..), Expr::Morphism(..)) => true,
            _ => false,
        }
    }

    fn open(&self, f: &mut fmt::Formatter<'_>) -> Result<&'static str, fmt::Error> {
        Ok(match self {
            Expr::Param(i) => {
                write!(f, "Param({i:?}")?;
                ")"
            }
            Expr::Type(t) => {
                write!(f, "Type({t:?}")?;
                ")"
            }
            Expr::Ref(i, _) => {
                write!(f, "Ref({i:?}, [")?;
                "])"
            }
            Expr::Union(_) => {
                f.write_str("Union([")?;
                "])"
            }
            Expr::And(_) => {
                f.write_str("And([")?;
                "])"
            }
            Expr::Tuple(_) => {
                f.write_str("Tuple([")?;
                "])"
            }
            Expr::Atom(name, _) => {
                write!(f, "Atom({name:?}, [")?;
                "])"
            }
            Expr::Not(_) => {
                f.write_str("Not(")?;
                ")"
            }
            Expr::Diff(..) => {
                f.write_str("Diff(")?;
                ")"
            }
            Expr::Morphism(..) => {
                f.write_str("Morphism(")?;
                ")"
            }
        })
    }
}

impl Tree for Node {
    fn kids(&self) -> impl DoubleEndedIterator<Item = &Node> {
        self.e.kids().map(|n| &**n)
    }

    fn same_head(&self, other: &Node) -> bool {
        self.digest == other.digest
            && self.recursive == other.recursive
            && self.open == other.open
            && self.e.same_head(&other.e)
    }

    fn open(&self, f: &mut fmt::Formatter<'_>) -> Result<&'static str, fmt::Error> {
        write!(
            f,
            "Node {{ digest: {:?}, recursive: {:?}, open: {:?}, e: ",
            self.digest, self.recursive, self.open
        )?;
        Ok(match self.e.open(f)? {
            ")" => ") }",
            _ => "]) }",
        })
    }
}

/// Whether `a` and `b` are equal, part by part, from a stack of pairs. A pair that is one
/// value twice is equal unread. A body's tree is a tree, built by `Node::of` from an expression,
/// so no pair is met twice.
pub(super) fn equal<T: Tree>(a: &T, b: &T) -> bool {
    let mut pairs = vec![(a, b)];
    while let Some((a, b)) = pairs.pop() {
        if std::ptr::eq(a, b) {
            continue;
        }
        if !a.same_head(b) {
            return false;
        }
        pairs.extend(a.kids().zip(b.kids()));
    }
    true
}

/// What is left to write.
enum Task<'a, T> {
    Text(&'static str),
    Tree(&'a T),
}

/// Writes `t`, each part when its turn comes, from a stack of what is left.
fn show<T: Tree>(t: &T, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut todo = vec![Task::Tree(t)];
    while let Some(task) = todo.pop() {
        match task {
            Task::Text(s) => f.write_str(s)?,
            Task::Tree(t) => {
                todo.push(Task::Text(t.open(f)?));
                let mut first = true;
                for k in t.kids().rev() {
                    if !first {
                        todo.push(Task::Text(", "));
                    }
                    first = false;
                    todo.push(Task::Tree(k));
                }
            }
        }
    }
    Ok(())
}

impl PartialEq for Expr {
    fn eq(&self, other: &Expr) -> bool {
        equal(self, other)
    }
}

impl Eq for Expr {}

impl PartialEq for Node {
    fn eq(&self, other: &Node) -> bool {
        equal(self, other)
    }
}

impl PartialEq for Shape {
    fn eq(&self, other: &Shape) -> bool {
        self.same_head(other)
            && self
                .kids()
                .zip(other.kids())
                .all(|(a, b)| equal(&**a, &**b))
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        show(self, f)
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        show(self, f)
    }
}

/// The last of the copied parts, boxed.
fn last(parts: &mut Vec<Expr>) -> Box<Expr> {
    Box::new(parts.pop().expect("each part was copied"))
}

impl Clone for Expr {
    /// Copies the parts in a loop: each expression with parts is rebuilt once they are copied.
    fn clone(&self) -> Expr {
        enum Step<'a> {
            Copy(&'a Expr),
            Rebuild(&'a Expr),
        }
        let mut todo = vec![Step::Copy(self)];
        let mut done: Vec<Expr> = Vec::new();
        while let Some(step) = todo.pop() {
            match step {
                Step::Copy(e) => match e {
                    Expr::Param(i) => done.push(Expr::Param(*i)),
                    Expr::Type(t) => done.push(Expr::Type(t.clone())),
                    _ => {
                        todo.push(Step::Rebuild(e));
                        todo.extend(e.kids().rev().map(Step::Copy));
                    }
                },
                Step::Rebuild(e) => {
                    let n = e.kids().count();
                    let mut parts = done.split_off(done.len() - n);
                    let built = match e {
                        Expr::Ref(i, _) => Expr::Ref(*i, parts),
                        Expr::Union(_) => Expr::Union(parts),
                        Expr::And(_) => Expr::And(parts),
                        Expr::Tuple(_) => Expr::Tuple(parts),
                        Expr::Atom(name, _) => Expr::Atom(name.clone(), parts),
                        Expr::Not(_) => Expr::Not(last(&mut parts)),
                        Expr::Diff(..) => {
                            let b = last(&mut parts);
                            Expr::Diff(last(&mut parts), b)
                        }
                        Expr::Morphism(..) => {
                            let v = last(&mut parts);
                            let u = last(&mut parts);
                            Expr::Morphism(last(&mut parts), u, v)
                        }
                        Expr::Param(_) | Expr::Type(_) => {
                            unreachable!("an expression with no parts is copied whole")
                        }
                    };
                    done.push(built);
                }
            }
        }
        done.pop().expect("the copy of the expression")
    }
}
