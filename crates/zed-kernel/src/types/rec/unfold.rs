//! The unfolding of a recursive type: the units of work that keep and free its instances'
//! members, and the evaluation and naming of a definition's body at its arguments.

use std::cell::RefCell;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock, PoisonError, Weak};

use super::{At, Def, Env, Key, Node, Shape, same};
use crate::types::print::Class;
use crate::types::{self, Piece, Rope, TextPlace as Place, Type};

/// The units begun, over all threads.
static UNITS: AtomicU64 = AtomicU64::new(0);

/// The threads that began a unit.
static THREADS: AtomicU64 = AtomicU64::new(0);

/// The instances made, over all threads: each instance's number ([`Key::group`]).
pub(super) static ENVS: AtomicU64 = AtomicU64::new(0);

/// A thread's unit of work under way, from the end of the last (`Type::forget_emptiness`, which
/// a unit's checker calls first, or the thread's start) to the next: its number, and the
/// instances whose recursive members it made. A recursive member's unfolding holds the member,
/// and the member holds its instance, which holds its members: a cycle of strong handles,
/// which the end of the unit breaks ([`end_unit`]). The instances a unit made are its arena.
// Complexity tradeoff: a recursive type kept past the end of its unit makes its unfolding
// again, in the size of its body, when next read, and keeps it until the end of that unit. A
// group no one holds past its unit is made, instantiated and decided again by the next unit
// that names it; before, every group was kept, since no instance was freed. A cycle collector
// would free a cycle as soon as no holder is left, but cannot see who holds a type: the maps of
// atoms (`imbl::OrdMap`) share their nodes between types (`M | x` holds the map of `M`'s
// unfolding), and those nodes' counts cannot be read, so a collector would free types still
// held, or keep every recursive type with atoms. COMPLEXITY.md K68.
struct Unit {
    number: u64,
    /// The thread's number, under which its instances are in `group::INSTANCES`.
    thread: u64,
    made: Vec<Weak<Env>>,
}

thread_local! {
    static UNIT: RefCell<Unit> = RefCell::new(Unit {
        number: UNITS.fetch_add(1, Ordering::Relaxed),
        thread: THREADS.fetch_add(1, Ordering::Relaxed),
        made: Vec::new(),
    });
}

/// A thread's last unit ends when the thread does.
impl Drop for Unit {
    fn drop(&mut self) {
        forget(std::mem::take(&mut self.made));
    }
}

/// The number of this thread's unit under way.
pub(super) fn unit() -> u64 {
    // Thread-locals first used after this call are dropped before the queues that free types.
    super::hold();
    UNIT.with_borrow(|u| u.number)
}

/// The number of this thread ([`Unit::thread`]).
pub(super) fn thread() -> u64 {
    super::hold();
    UNIT.with_borrow(|u| u.thread)
}

/// Ends this thread's unit: breaks the cycle of each instance whose recursive members it made,
/// so that an instance no one holds is dropped, and begins the next unit. A type held past the
/// end still denotes what it did, and is unfolded again when read. Time linear in the instances
/// the unit made and their members, besides what is dropped.
pub(in crate::types) fn end_unit() {
    let made = UNIT.try_with(|u| {
        let mut u = u.borrow_mut();
        u.number = UNITS.fetch_add(1, Ordering::Relaxed);
        std::mem::take(&mut u.made)
    });
    if let Ok(made) = made {
        forget(made);
    }
}

/// Breaks the cycle of each instance of `made` still alive ([`Env::forget`]).
fn forget(made: Vec<Weak<Env>>) {
    for env in made.iter().filter_map(Weak::upgrade) {
        env.forget();
    }
}

impl Env {
    pub(super) fn ground(args: Vec<Type>) -> Env {
        Env {
            id: ENVS.fetch_add(1, Ordering::Relaxed),
            thread: u64::MAX,
            registered: AtomicU64::new(u64::MAX),
            group: None,
            digest: 0,
            args,
            members: Vec::new(),
            judged: OnceLock::new(),
        }
    }

    /// The members of an instance.
    pub(super) fn members(self: &Arc<Env>) -> Vec<Type> {
        (0..self.members.len()).map(|i| self.member(i)).collect()
    }

    pub(super) fn cell(&self, i: usize) -> std::sync::MutexGuard<'_, Option<Type>> {
        self.members[i]
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// Member `i`: a recursive member is a node that unfolds to its body, made when first read
    /// in a unit, and kept, by the instance, until the unit ends. Another thread that made it
    /// at the same time may have kept its own first, which is then the one.
    fn member(self: &Arc<Env>, i: usize) -> Type {
        if let Some(t) = &*self.cell(i) {
            return t.clone();
        }
        // A plain member is set when the instance is made, so this one is recursive.
        let (e, named) = (self.clone(), self.clone());
        let made = Type::rec(
            Key::new(self.clone(), At::Member(i)),
            move || named.name(i),
            move || eval(&e.group().0.bodies[i], &e),
        );
        let kept = self.cell(i).get_or_insert_with(|| made.clone()).clone();
        if kept.node_addr() == made.node_addr() {
            self.register();
        }
        // `made` is dropped here, after the lock, when another thread kept its own.
        drop(made);
        kept
    }

    /// Puts the instance in this thread's unit, once per unit, which breaks its cycle when it
    /// ends.
    fn register(self: &Arc<Env>) {
        let number = unit();
        if self.registered.swap(number, Ordering::Relaxed) != number {
            UNIT.with_borrow_mut(|u| u.made.push(Arc::downgrade(self)));
        }
    }

    /// Drops the recursive members it keeps, and their unfoldings, which hold the members: what
    /// is not held elsewhere is dropped. A member held elsewhere unfolds again when read, to the
    /// members made again then.
    fn forget(&self) {
        let plain = &self.group().0.plain;
        let kept: Vec<Type> = (0..self.members.len())
            .filter(|&i| !plain[i])
            .filter_map(|i| self.cell(i).take())
            .collect();
        for m in &kept {
            m.forget_unfolding();
        }
        drop(kept);
    }

    /// The name of definition `i` at the arguments: `Tree(int)`.
    fn name(&self, i: usize) -> Rope {
        let d = &self.group().0.defs[i];
        match self.args.is_empty() {
            true => Rope::cat([Piece::from(d.name.as_str())]),
            false => Rope::joined(
                &format!("{}(", d.name),
                self.args.iter().map(Type::rope),
                ", ",
                ")",
            ),
        }
    }
}

impl Key {
    /// The recursive members of the group, in definition order, when the key names a member.
    fn members(&self) -> Option<Vec<Type>> {
        let At::Member(_) = self.at else {
            return None;
        };
        let plain = &self.env.group().0.plain;
        Some(
            (0..plain.len())
                .filter(|&i| !plain[i])
                .map(|i| self.env.member(i))
                .collect(),
        )
    }
}

impl Type {
    /// The recursive members of the group of a recursive member, in definition order.
    pub(crate) fn group_members(&self) -> Option<Vec<Type>> {
        match &*self.0 {
            types::Node::Parts(..) => None,
            types::Node::Rec(r) => r.key.members(),
        }
    }
}

/// The type `e` denotes in `env`. Each expression's type is built once its parts' are, from a
/// stack; a part of a constructor is evaluated as [`component`] says.
pub(in crate::types) fn eval(e: &Node, env: &Arc<Env>) -> Type {
    enum Step<'a> {
        Eval(&'a Node),
        Component(&'a Arc<Node>),
        Build(&'a Node),
    }
    let mut todo = vec![Step::Eval(e)];
    let mut done: Vec<Type> = Vec::new();
    while let Some(step) = todo.pop() {
        let t = match step {
            Step::Component(e) if eager(e) => {
                todo.push(Step::Eval(e));
                continue;
            }
            Step::Component(e) => component(e, env),
            Step::Eval(e) => match &e.e {
                Shape::Param(i) => env.args[*i].clone(),
                Shape::Ref(i, _) => env.member(*i),
                Shape::Type(t) => t.clone(),
                Shape::Union(_) | Shape::And(_) | Shape::Not(_) | Shape::Diff(..) => {
                    todo.push(Step::Build(e));
                    todo.extend(e.e.kids().rev().map(|c| Step::Eval(c)));
                    continue;
                }
                Shape::Tuple(_) | Shape::Atom(..) | Shape::Morphism(..) => {
                    todo.push(Step::Build(e));
                    todo.extend(e.e.kids().rev().map(Step::Component));
                    continue;
                }
            },
            Step::Build(e) => {
                let mut parts = done.split_off(done.len() - e.e.kids().count());
                match &e.e {
                    Shape::Union(_) => Type::union_all(parts),
                    Shape::And(_) => Type::meet_all(parts),
                    Shape::Tuple(_) => Type::tuple(parts),
                    Shape::Atom(name, _) => Type::atom_with(name, &Type::tuple(parts)),
                    Shape::Not(_) => !parts.pop().expect("the part"),
                    Shape::Diff(..) => {
                        let b = parts.pop().expect("the right part");
                        parts.pop().expect("the left part") - &b
                    }
                    Shape::Morphism(..) => {
                        let v = parts.pop().expect("the value type");
                        let u = parts.pop().expect("the permission");
                        Type::morphism(parts.pop().expect("the guarantee"), u, v)
                    }
                    Shape::Param(_) | Shape::Ref(..) | Shape::Type(_) => {
                        unreachable!("a leaf is not built")
                    }
                }
            }
        };
        done.push(t);
    }
    done.pop().expect("the type of the expression")
}

/// Whether `e`, in a constructor, is evaluated now: it names a definition, or names none that
/// is not plain.
fn eager(e: &Node) -> bool {
    matches!(e.e, Shape::Ref(..)) || !e.open
}

/// `e` in a constructor: when it names a definition that is not plain and is more than one
/// occurrence, it is kept as a node evaluated on first use, since evaluating it now could need
/// the parts of the type being built.
fn component(e: &Arc<Node>, env: &Arc<Env>) -> Type {
    if eager(e) {
        return eval(e, env);
    }
    let (named, at) = (e.clone(), env.clone());
    let key = Key::new(env.clone(), At::Part(e.at));
    let (e, env) = (e.clone(), env.clone());
    Type::rec(
        key,
        move || {
            Show {
                defs: &at.group().0.defs,
                params: &[],
                args: Some(&at.args),
                e: &named,
                surface: false,
            }
            .rope()
        },
        move || eval(&e, &env),
    )
}

/// An expression in the surface syntax, its parameters by name or, with `args`, by value.
pub(super) struct Show<'a> {
    pub(super) defs: &'a [Def],
    pub(super) params: &'a [String],
    pub(super) args: Option<&'a [Type]>,
    pub(super) e: &'a Node,
    /// Whether a type that does not mention the group is written in the surface syntax (module
    /// `print`), as a message writes it, rather than by its name ([`Type::rope`]). A recursive
    /// type in it is written by its name, with its arguments in the surface syntax too.
    pub(super) surface: bool,
}

impl Show<'_> {
    /// The text as a rope, which holds the texts of the types it names without copying them,
    /// so that the name of `Tree(Tree(..))` takes time linear in its text.
    /// Each expression's rope is built once its parts' are, from a stack. Each part is
    /// parenthesized only where the type grammar (DESIGN.md sec:grammar) would not read it as
    /// one operand of the part around it.
    fn rope(&self) -> Rope {
        self.rope_with(&mut |t, _| t.rope())
    }

    /// The rope of the expression, each type in it given by `leaf` from the type and its place,
    /// called on the types in the order they are written.
    fn rope_with(&self, leaf: &mut dyn FnMut(&Type, Place) -> Rope) -> Rope {
        enum Step<'a> {
            Visit(&'a Node, Place),
            Build(&'a Node, Place),
        }
        let mut todo = vec![Step::Visit(self.e, Place::Any)];
        let mut done: Vec<Rope> = Vec::new();
        while let Some(step) = todo.pop() {
            let r = match step {
                Step::Visit(e, at) => match &e.e {
                    Shape::Param(i) => match self.args {
                        Some(args) => args[*i].rope(),
                        None => Rope::cat([Piece::from(self.params[*i].as_str())]),
                    },
                    Shape::Ref(i, args) if args.is_empty() => {
                        Rope::cat([Piece::from(self.defs[*i].name.as_str())])
                    }
                    Shape::Type(t) => leaf(t, at),
                    _ => {
                        todo.push(Step::Build(e, at));
                        let n = e.e.kids().count();
                        todo.extend(
                            (e.e.kids().rev().zip((0..n).rev()))
                                .map(|(c, i)| Step::Visit(c, kid_place(&e.e, i))),
                        );
                        continue;
                    }
                },
                Step::Build(e, at) => {
                    let parts = done.split_off(done.len() - e.e.kids().count());
                    let r = if let Shape::Ref(i, _) = &e.e {
                        Rope::joined(&format!("{}(", self.defs[*i].name), parts, ", ", ")")
                    } else {
                        let mut parts = parts;
                        match &e.e {
                            Shape::Union(_) => Rope::joined("", parts, " | ", ""),
                            Shape::And(_) => Rope::joined("", parts, " & ", ""),
                            Shape::Not(_) => Rope::joined("!", parts, "", ""),
                            Shape::Diff(..) => Rope::joined("", parts, " \\ ", ""),
                            // A tuple of one component is written `(T,)`: `(T)` is `T`.
                            Shape::Tuple(_) if parts.len() == 1 => {
                                Rope::joined("(", parts, "", ",)")
                            }
                            Shape::Tuple(_) => Rope::joined("(", parts, ", ", ")"),
                            Shape::Atom(name, _) => {
                                Rope::joined(&format!("#{name}("), parts, ", ", ")")
                            }
                            Shape::Morphism(l, u, _) => {
                                let v = parts.pop().expect("the value type");
                                let u_rope = parts.pop().expect("the permission");
                                let l_rope = parts.pop().expect("the guarantee");
                                if same(l, u) {
                                    Rope::joined("(", [l_rope, v], ") -> ", "")
                                } else if l.e == Shape::Type(Type::empty()) {
                                    Rope::joined("", [u_rope, v], " ->? ", "")
                                } else {
                                    Rope::cat([
                                        Piece::from(l_rope),
                                        Piece::from(" .. "),
                                        Piece::from(u_rope),
                                        Piece::from(" -> "),
                                        Piece::from(v),
                                    ])
                                }
                            }
                            Shape::Param(_) | Shape::Ref(..) | Shape::Type(_) => {
                                unreachable!("a leaf is not built")
                            }
                        }
                    };
                    match at.admits(class(&e.e)) {
                        true => r,
                        false => Rope::joined("(", [r], "", ")"),
                    }
                }
            };
            done.push(r);
        }
        done.pop().expect("the rope of the expression")
    }
}

/// How the text of an expression of shape `s` that is not a leaf binds, for parenthesizing it
/// as an operand: a leaf's text is parenthesized where it stands as it is made.
fn class(s: &Shape) -> Class {
    match s {
        Shape::Union(_) => Class::Union,
        Shape::And(_) => Class::And,
        Shape::Diff(..) => Class::Diff,
        Shape::Morphism(..) => Class::Arrow,
        // `(T,)` cannot read as parameters, so it is a primary even as a key.
        Shape::Tuple(ps) if ps.len() != 1 => Class::Tuple,
        Shape::Tuple(_)
        | Shape::Not(_)
        | Shape::Atom(..)
        | Shape::Ref(..)
        | Shape::Param(_)
        | Shape::Type(_) => Class::Prim,
    }
}

/// Where part `i` of the parts directly below an expression of shape `s` stands: `\` takes no `&` or `|` on either side and no `\` on its right, an arrow's key no
/// arrow and no tuple, which would read as its parameters, and its bounds no arrow (DESIGN.md
/// sec:grammar). A guarantee equal to the permission is written in parentheses, `(K) -> V`,
/// so it may be any type.
fn kid_place(s: &Shape, i: usize) -> Place {
    let (each, fixed): (Place, [Option<Place>; 3]) = match s {
        Shape::Union(_) => (Place::Union, [None; 3]),
        Shape::And(_) => (Place::And, [None; 3]),
        Shape::Not(_) => (Place::Prim, [None; 3]),
        Shape::Diff(..) => (Place::Any, [Some(Place::DiffLeft), Some(Place::Prim), None]),
        Shape::Morphism(l, u, _) if same(l, u) => (Place::Any, [None; 3]),
        Shape::Morphism(l, _, _) if l.e == Shape::Type(Type::empty()) => (
            Place::Any,
            [Some(Place::Any), Some(Place::Key), Some(Place::Any)],
        ),
        Shape::Morphism(..) => (
            Place::Any,
            [Some(Place::Bound), Some(Place::Bound), Some(Place::Any)],
        ),
        Shape::Tuple(_) | Shape::Atom(..) | Shape::Ref(..) | Shape::Param(_) | Shape::Type(_) => {
            (Place::Any, [None; 3])
        }
    };
    fixed.get(i).copied().flatten().unwrap_or(each)
}

/// In the surface syntax, the types the expression holds are written together by name
/// ([`Type::surfaces_by_name`]): a part used more than once among them gets a definition, written
/// before the whole expression, so the text is linear in the expression and the types' graph.
impl fmt::Display for Show<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.surface {
            return self.rope().strs().try_for_each(|s| f.write_str(s));
        }
        let mut leaves = Vec::new();
        self.rope_with(&mut |t, at| {
            leaves.push((t.clone(), at));
            Rope::cat([])
        });
        let texts = Type::surfaces_by_name(&leaves);
        for (name, body) in &texts.defs {
            write!(f, "type {name} = {body}; ")?;
        }
        let mut roots = texts.roots.into_iter();
        self.rope_with(&mut |_, _| {
            Rope::cat([Piece::from(roots.next().expect("a text for each type"))])
        })
        .strs()
        .try_for_each(|s| f.write_str(s))
    }
}
